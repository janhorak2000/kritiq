"""
Resumable, day-by-day version of fetch_data.py — run it once a day (manually,
or via Task Scheduler / cron) and it keeps adding new real titles to data.json
instead of re-downloading what it already has.

Why this exists: a single TMDb search can only page 500 pages deep (~10,000
results), no matter how it's sorted. To collect tens of thousands of titles,
this script walks backwards through release years and paginates within each
year — each year gets its own fresh 10k allowance. Each run covers a fixed
WINDOW of years (--years-per-run, default 5) rather than a fixed item count,
so a run always makes forward progress even in years with very few results.
Progress (which year it reached, and which title IDs it already has) is
saved in fetch_state.json, so the next run picks up right where this one
stopped instead of starting over.

Crash safety: data.json and fetch_state.json are saved after EVERY category
(movies, then shows, then games) and after every single year within a
category — not just once at the very end. If something goes wrong partway
through, everything collected up to that point is already safely on disk.

QUALITY FILTERING (new): raw API discover results include a lot of noise —
unreviewed indie/no-name entries, and (especially on RAWG) tiny-sample
ratings that can show something like 99/100 based on 2 votes. This version
filters more seriously:

  Movies/shows — a tiered minimum vote-count, based on where/what language
  the title is in, since that's the best cheap signal for how likely a title
  is to be something people have actually heard of:
    tier 1 (lenient,  --min-votes as-is):        American movies / US or
                                                   Czech shows
    tier 2 (medium,   --min-votes x3):            English, French, German,
                                                   or Spanish
    tier 3 (strict,   --min-votes x8):            everything else
  Movies don't expose a country field cheaply, so "American" is approximated
  as original_language == "en" — not perfect (also catches UK/Australia/etc.)
  but a reasonable proxy without extra API calls. Shows DO get a real
  origin_country check.

  Games — by default, a game is only included if it has a real Metacritic
  score attached (RAWG's own "metacritic" field). That score is then used
  directly as Kritiq's score instead of RAWG's own small-sample user rating,
  since Metacritic aggregation is far more trustworthy than "5.0 stars from
  2 people". Pass --allow-no-metacritic to include Metacritic-less games
  too, gated instead by --min-ratings-count (RAWG's own rating-sample size).

  Nothing unreleased: any movie, show, or game whose release date is in the
  future (relative to today) is skipped entirely — no scores get attached to
  announced-but-unreleased titles (this is what was pulling in things like
  an unreleased GTA sequel with an early "score").

LANGUAGE: movies and shows are now fetched with language=cs-CZ, so titles
and genre names come back in Czech when TMDb has that translation (falling
back to the original title otherwise). Games stay in English — RAWG doesn't
have solid Czech localization to pull from.

REVIEWS: by default, fetched titles get NO reviews attached (Kritiq shows
them with zero reviews rather than inventing anything). Pass --fetch-reviews
to additionally pull a few genuine user reviews per movie/show from TMDb
(real author names, real text, and a real 0-100 score wherever the reviewer
left a numeric rating) — this costs one extra API call per title, so it's
off by default to keep runs quick.

Setup:
  pip install requests
  Get a free TMDb API key:  https://www.themoviedb.org/settings/api
  Get a free RAWG API key:  https://rawg.io/apidocs

Usage (run this once a day):
  python fetch_data_daily.py --tmdb-key YOUR_TMDB_KEY --rawg-key YOUR_RAWG_KEY

That covers 5 years per category per run by default (2026-2022 on day 1,
2021-2017 on day 2, and so on) down to --floor-year (default 1888).

Staying current: every run ALSO does a separate, fast "recent refresh" pass
over the current year (for anything newly added), independent of wherever
the historical backfill has gotten to. Once you've fully backfilled to
--floor-year, add --skip-backfill so future days only run this fast pass.

Output:
  data.json         merged with everything fetched so far — drop next to kritiq.html
  fetch_state.json  progress tracker — do NOT delete this between runs, or it
                    will start over from the current year and re-fetch titles
                    you already have (harmless, just wasteful of time)

To reset and start completely fresh, delete both data.json and fetch_state.json.

IMPORTANT: poster/gallery images only display when kritiq.html is opened
outside the Claude-hosted preview link (e.g. opened locally as a file, or
hosted on your own site) — the hosted preview blocks loading images from
other sites for security reasons.
"""

import argparse
import csv
import datetime
import gzip
import json
import os
import sys
import time
import urllib.request
import requests

TMDB_BASE = "https://api.themoviedb.org/3"
TMDB_IMG_BASE = "https://image.tmdb.org/t/p/w500"
RAWG_BASE = "https://api.rawg.io/api"
FLOOR_YEAR_DEFAULT = 1888
YEARS_PER_RUN_DEFAULT = 5
CURRENT_YEAR_DEFAULT = 2026
TMDB_LANG = "cs-CZ"

TIER_MULT = {1: 1, 2: 3, 3: 8}
TIER2_LANGS = {"en", "fr", "de", "es"}
IMDB_RATINGS_URL = "https://datasets.imdbws.com/title.ratings.tsv.gz"
IMDB_CACHE_MAX_AGE_HOURS = 24
MIN_IMDB_VOTES_DEFAULT = 100


def today_str():
    return datetime.date.today().isoformat()


def is_released(date_str, today):
    return bool(date_str) and date_str <= today


def tmdb_get(path, key, params=None):
    params = dict(params or {})
    params["api_key"] = key
    last_exc = None
    for attempt in range(3):
        try:
            r = requests.get(f"{TMDB_BASE}{path}", params=params, timeout=20)
            if r.status_code == 429:
                time.sleep(2)
                continue
            r.raise_for_status()
            return r.json()
        except requests.RequestException as e:
            last_exc = e
            time.sleep(2)
    raise last_exc


def rawg_get(path, key, params=None):
    params = dict(params or {})
    params["key"] = key
    last_exc = None
    for attempt in range(3):
        try:
            r = requests.get(f"{RAWG_BASE}{path}", params=params, timeout=20)
            if r.status_code == 429:
                time.sleep(2)
                continue
            r.raise_for_status()
            return r.json()
        except requests.RequestException as e:
            last_exc = e
            time.sleep(2)
    raise last_exc


def genre_map(key, media):
    try:
        data = tmdb_get(f"/genre/{media}/list", key, {"language": TMDB_LANG})
        return {g["id"]: g["name"] for g in data.get("genres", [])}
    except Exception as e:
        print(f"  warning: could not fetch genre list ({e}) — genres will be blank this run", file=sys.stderr)
        return {}


def load_imdb_ratings(cache_path, max_age_hours):
    """Downloads (and caches for max_age_hours) IMDb's free non-commercial bulk ratings
    dataset — real audience rating + real vote count for every IMDb title, independent
    of TMDb's own numbers. Returns {imdb_id: (average_rating_0_to_10, num_votes)}.
    Used to cross-check/override TMDb's score, since TMDb's vote_average can run hot on
    titles with an active fanbase (or review-bombing) in a way IMDb's much larger sample
    usually doesn't. This dataset is IMDb's non-commercial dataset — fine for a personal
    project like this; check IMDb's terms again first if this ever becomes a commercial
    product."""
    need_download = True
    if os.path.exists(cache_path):
        age_hours = (time.time() - os.path.getmtime(cache_path)) / 3600
        need_download = age_hours >= max_age_hours
    if need_download:
        print("Refreshing IMDb ratings dataset (cached ~1x/day)...", file=sys.stderr)
        try:
            tmp = cache_path + ".tmp"
            urllib.request.urlretrieve(IMDB_RATINGS_URL, tmp)
            os.replace(tmp, cache_path)
        except Exception as e:
            print(f"  warning: could not download IMDb ratings ({e}) — falling back to TMDb's own scores this run", file=sys.stderr)
    ratings = {}
    if not os.path.exists(cache_path):
        return ratings
    try:
        with gzip.open(cache_path, "rt", encoding="utf-8") as f:
            for row in csv.DictReader(f, delimiter="\t"):
                try:
                    ratings[row["tconst"]] = (float(row["averageRating"]), int(row["numVotes"]))
                except Exception:
                    continue
    except Exception as e:
        print(f"  warning: could not read IMDb ratings cache ({e}) — falling back to TMDb's own scores this run", file=sys.stderr)
    print(f"  IMDb ratings loaded: {len(ratings)} titles", file=sys.stderr)
    return ratings


def get_imdb_id(key, media, tmdb_id):
    try:
        data = tmdb_get(f"/{media}/{tmdb_id}/external_ids", key)
        return data.get("imdb_id")
    except Exception:
        return None


def imdb_score_for(key, media, tmdb_id, imdb_ratings, min_imdb_votes, fallback_score):
    """Returns (score, used_imdb_bool). Falls back to TMDb's own score when there's no
    IMDb match, or the match doesn't have enough votes to be trustworthy either."""
    if not imdb_ratings:
        return fallback_score, False
    imdb_id = get_imdb_id(key, media, tmdb_id)
    if not imdb_id:
        return fallback_score, False
    match = imdb_ratings.get(imdb_id)
    if not match or match[1] < min_imdb_votes:
        return fallback_score, False
    return round(match[0] * 10), True


def load_json(path, default):
    if os.path.exists(path):
        with open(path, "r", encoding="utf-8") as f:
            return json.load(f)
    return default


def save_json(path, obj):
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(obj, f, ensure_ascii=False, indent=2)
    os.replace(tmp, path)  # atomic-ish: never leaves a half-written data.json


def movie_quality_tier(m):
    lang = m.get("original_language")
    if lang == "en" or lang == "cs":
        return 1
    if lang in TIER2_LANGS:
        return 2
    return 3


def show_quality_tier(s):
    oc = s.get("origin_country") or []
    if "US" in oc or "CZ" in oc:
        return 1
    if s.get("original_language") in TIER2_LANGS or s.get("original_language") == "en":
        return 2
    return 3


def passes_quality(item, tier_fn, min_votes):
    tier = tier_fn(item)
    required = min_votes * TIER_MULT[tier]
    return (item.get("vote_count") or 0) >= required


def fetch_real_reviews(key, media, tmdb_id, cap=5):
    """Pulls a handful of genuine TMDb user reviews (real author, real text).
    Only ones with a numeric rating get a score (x10 to fit Kritiq's 0-100 scale);
    reviews without a rating are skipped rather than guessing a score for them."""
    out = []
    try:
        data = tmdb_get(f"/{media}/{tmdb_id}/reviews", key, {"language": "en-US"})
        for r in data.get("results", [])[:cap]:
            rating = (r.get("author_details") or {}).get("rating")
            if rating is None:
                continue
            text = (r.get("content") or "").strip()
            if not text:
                continue
            out.append({
                "author": r.get("author") or "TMDb user",
                "score": round(float(rating) * 10),
                "text": text[:600],
            })
    except Exception:
        pass
    return out


def movie_record(m, key, genres, fetch_galleries, fetch_reviews, imdb_ratings, min_imdb_votes):
    director = composer = writer = ""
    actors = []
    try:
        credits = tmdb_get(f"/movie/{m['id']}/credits", key)
        director = next((c["name"] for c in credits.get("crew", []) if c["job"] == "Director"), "")
        composer = next((c["name"] for c in credits.get("crew", []) if c["job"] == "Original Music Composer"), "")
        writer = next((c["name"] for c in credits.get("crew", []) if c["job"] in ("Screenplay", "Writer")), "")
        actors = [c["name"] for c in credits.get("cast", [])[:4]]
    except Exception as e:
        print(f"    warning: credits fetch failed for movie {m.get('id')} ({e}) — leaving crew blank", file=sys.stderr)
    genre = genres.get((m.get("genre_ids") or [None])[0], "")
    poster = f"{TMDB_IMG_BASE}{m['poster_path']}" if m.get("poster_path") else ""
    gallery = [f"{TMDB_IMG_BASE}{m['backdrop_path']}"] if m.get("backdrop_path") else []
    if fetch_galleries:
        try:
            imgs = tmdb_get(f"/movie/{m['id']}/images", key)
            gallery = [f"{TMDB_IMG_BASE}{b['file_path']}" for b in imgs.get("backdrops", [])[:6]]
        except Exception:
            pass
    reviews = fetch_real_reviews(key, "movie", m["id"]) if fetch_reviews else []
    fallback_score = round(m.get("vote_average", 0) * 10)
    score, used_imdb = imdb_score_for(key, "movie", m["id"], imdb_ratings, min_imdb_votes, fallback_score)
    return {
        "title": m["title"],
        "year": int(m["release_date"][:4]),
        "date": m["release_date"],
        "score": score,
        "box": round(m.get("popularity", 0) * 3),
        "genre": genre,
        "poster": poster,
        "gallery": gallery,
        "director": director, "composer": composer, "writer": writer, "actors": actors,
        "reviews": reviews,
    }


def show_record(s, key, genres, fetch_galleries, fetch_reviews, imdb_ratings, min_imdb_votes):
    director = composer = writer = ""
    actors = []
    try:
        credits = tmdb_get(f"/tv/{s['id']}/credits", key)
        director = next((c["name"] for c in credits.get("crew", []) if c["job"] in ("Director", "Series Director")), "")
        composer = next((c["name"] for c in credits.get("crew", []) if c["job"] == "Original Music Composer"), "")
        writer = next((c["name"] for c in credits.get("crew", []) if c["job"] in ("Writer", "Creator")), "")
        actors = [c["name"] for c in credits.get("cast", [])[:4]]
    except Exception as e:
        print(f"    warning: credits fetch failed for show {s.get('id')} ({e}) — leaving crew blank", file=sys.stderr)
    genre = genres.get((s.get("genre_ids") or [None])[0], "")
    poster = f"{TMDB_IMG_BASE}{s['poster_path']}" if s.get("poster_path") else ""
    gallery = [f"{TMDB_IMG_BASE}{s['backdrop_path']}"] if s.get("backdrop_path") else []
    if fetch_galleries:
        try:
            imgs = tmdb_get(f"/tv/{s['id']}/images", key)
            gallery = [f"{TMDB_IMG_BASE}{b['file_path']}" for b in imgs.get("backdrops", [])[:6]]
        except Exception:
            pass
    reviews = fetch_real_reviews(key, "tv", s["id"]) if fetch_reviews else []
    fallback_score = round(s.get("vote_average", 0) * 10)
    score, used_imdb = imdb_score_for(key, "tv", s["id"], imdb_ratings, min_imdb_votes, fallback_score)
    return {
        "title": s["name"],
        "year": int(s["first_air_date"][:4]),
        "date": s["first_air_date"],
        "score": score,
        "genre": genre,
        "poster": poster,
        "gallery": gallery,
        "director": director, "composer": composer, "writer": writer, "actors": actors,
        "reviews": reviews,
    }


def game_record(g):
    devs = ", ".join(d["name"] for d in (g.get("developers") or [])[:1]) or "Neznámý vývojář"
    genre = ", ".join(x["name"] for x in (g.get("genres") or [])[:1])
    poster = g.get("background_image") or ""
    gallery = [s["image"] for s in (g.get("short_screenshots") or []) if s.get("image") and s.get("image") != poster][:6]
    metacritic = g.get("metacritic")
    score = metacritic if metacritic is not None else round((g.get("rating") or 0) * 20)
    return {
        "title": g["name"],
        "year": int(g["released"][:4]),
        "date": g["released"],
        "score": score,
        "genre": genre,
        "poster": poster,
        "gallery": gallery,
        "developer": devs,
        "reviews": [],
    }


def game_passes_quality(g, require_metacritic, min_ratings_count):
    if g.get("metacritic") is not None:
        return True
    if require_metacritic:
        return False
    return (g.get("ratings_count") or 0) >= min_ratings_count


def fetch_movie_window(key, state, years_per_run, floor_year, min_votes, genres, seen_ids, fetch_galleries, fetch_reviews, imdb_ratings, min_imdb_votes, today, checkpoint):
    year_end = state.get("year", state["start_year"])
    year_start = max(floor_year, year_end - years_per_run + 1)
    collected = []
    year = year_end
    page = state.get("page", 1)
    while year >= year_start:
        try:
            data = tmdb_get("/discover/movie", key, {
                "primary_release_year": year, "page": page, "language": TMDB_LANG,
                "sort_by": "vote_count.desc", "vote_count.gte": min_votes,
            })
        except Exception as e:
            print(f"  movies: error on year {year} page {page} ({e}) — stopping movies for this run, progress so far is saved", file=sys.stderr)
            break
        results = data.get("results", [])
        total_pages = min(data.get("total_pages", 1), 500)
        if not results:
            year -= 1
            page = 1
            state["year"] = year
            state["page"] = page
            checkpoint()
            continue
        kept = 0
        for m in results:
            if m["id"] in seen_ids or not m.get("release_date") or not m.get("title"):
                continue
            if not is_released(m["release_date"], today):
                continue
            if not passes_quality(m, movie_quality_tier, min_votes):
                continue
            seen_ids.add(m["id"])
            try:
                collected.append(movie_record(m, key, genres, fetch_galleries, fetch_reviews, imdb_ratings, min_imdb_votes))
                kept += 1
            except Exception as e:
                print(f"    warning: skipped a movie due to error ({e})", file=sys.stderr)
        print(f"  movies: year {year} page {page}/{total_pages} -> {len(collected)} collected so far ({kept} kept this page)", file=sys.stderr)
        page += 1
        if page > total_pages:
            year -= 1
            page = 1
        state["year"] = year
        state["page"] = page
        checkpoint(collected)
    else:
        state["year"] = year_start - 1
        state["page"] = 1
        checkpoint(collected)
    return collected


def fetch_show_window(key, state, years_per_run, floor_year, min_votes, genres, seen_ids, fetch_galleries, fetch_reviews, imdb_ratings, min_imdb_votes, today, checkpoint):
    year_end = state.get("year", state["start_year"])
    year_start = max(floor_year, year_end - years_per_run + 1)
    collected = []
    year = year_end
    page = state.get("page", 1)
    while year >= year_start:
        try:
            data = tmdb_get("/discover/tv", key, {
                "first_air_date_year": year, "page": page, "language": TMDB_LANG,
                "sort_by": "vote_count.desc", "vote_count.gte": min_votes,
            })
        except Exception as e:
            print(f"  shows: error on year {year} page {page} ({e}) — stopping shows for this run, progress so far is saved", file=sys.stderr)
            break
        results = data.get("results", [])
        total_pages = min(data.get("total_pages", 1), 500)
        if not results:
            year -= 1
            page = 1
            state["year"] = year
            state["page"] = page
            checkpoint(collected)
            continue
        kept = 0
        for s in results:
            if s["id"] in seen_ids or not s.get("first_air_date") or not s.get("name"):
                continue
            if not is_released(s["first_air_date"], today):
                continue
            if not passes_quality(s, show_quality_tier, min_votes):
                continue
            seen_ids.add(s["id"])
            try:
                collected.append(show_record(s, key, genres, fetch_galleries, fetch_reviews, imdb_ratings, min_imdb_votes))
                kept += 1
            except Exception as e:
                print(f"    warning: skipped a show due to error ({e})", file=sys.stderr)
        print(f"  shows: year {year} page {page}/{total_pages} -> {len(collected)} collected so far ({kept} kept this page)", file=sys.stderr)
        page += 1
        if page > total_pages:
            year -= 1
            page = 1
        state["year"] = year
        state["page"] = page
        checkpoint(collected)
    else:
        state["year"] = year_start - 1
        state["page"] = 1
        checkpoint(collected)
    return collected


def fetch_game_window(key, state, years_per_run, floor_year, seen_ids, require_metacritic, min_ratings_count, today, checkpoint):
    year_end = state.get("year", state["start_year"])
    year_start = max(floor_year, year_end - years_per_run + 1)
    collected = []
    year = year_end
    page = state.get("page", 1)
    while year >= year_start:
        try:
            data = rawg_get("/games", key, {
                "dates": f"{year}-01-01,{year}-12-31",
                "page": page, "page_size": 40, "ordering": "-added",
            })
        except Exception as e:
            print(f"  games: error on year {year} page {page} ({e}) — stopping games for this run, progress so far is saved", file=sys.stderr)
            break
        results = data.get("results", [])
        if not results or page > 250:  # RAWG also caps deep pagination
            year -= 1
            page = 1
            state["year"] = year
            state["page"] = page
            checkpoint(collected)
            continue
        kept = 0
        for g in results:
            if g["id"] in seen_ids or not g.get("released") or not g.get("name"):
                continue
            if not is_released(g["released"], today):
                continue
            if not game_passes_quality(g, require_metacritic, min_ratings_count):
                continue
            seen_ids.add(g["id"])
            try:
                collected.append(game_record(g))
                kept += 1
            except Exception as e:
                print(f"    warning: skipped a game due to error ({e})", file=sys.stderr)
        print(f"  games: year {year} page {page} -> {len(collected)} collected so far ({kept} kept this page)", file=sys.stderr)
        page += 1
        state["year"] = year
        state["page"] = page
        checkpoint(collected)
    else:
        state["year"] = year_start - 1
        state["page"] = 1
        checkpoint(collected)
    return collected


def fetch_movies_recent(key, genres, seen_ids, fetch_galleries, fetch_reviews, imdb_ratings, min_imdb_votes, years, min_votes, max_pages, today, checkpoint):
    """Runs every single time, independent of the historical backfill cursor — catches
    brand-new ALREADY-RELEASED titles TMDb added since the last run. Unreleased/future
    titles are filtered out entirely, same as the historical backfill."""
    collected = []
    for year in years:
        page = 1
        while page <= max_pages:
            try:
                data = tmdb_get("/discover/movie", key, {
                    "primary_release_year": year, "page": page, "language": TMDB_LANG,
                    "sort_by": "popularity.desc", "vote_count.gte": min_votes,
                })
            except Exception as e:
                print(f"  movies (recent): error on year {year} page {page} ({e}) — stopping recent refresh, progress so far is saved", file=sys.stderr)
                break
            results = data.get("results", [])
            total_pages = min(data.get("total_pages", 1), 500)
            if not results:
                break
            for m in results:
                if m["id"] in seen_ids or not m.get("release_date") or not m.get("title"):
                    continue
                if not is_released(m["release_date"], today):
                    continue
                if not passes_quality(m, movie_quality_tier, min_votes):
                    continue
                seen_ids.add(m["id"])
                try:
                    collected.append(movie_record(m, key, genres, fetch_galleries, fetch_reviews, imdb_ratings, min_imdb_votes))
                except Exception as e:
                    print(f"    warning: skipped a movie due to error ({e})", file=sys.stderr)
            print(f"  movies (recent): year {year} page {page}/{total_pages} -> {len(collected)} new so far", file=sys.stderr)
            checkpoint(collected)
            page += 1
            if page > total_pages:
                break
    return collected


def fetch_shows_recent(key, genres, seen_ids, fetch_galleries, fetch_reviews, imdb_ratings, min_imdb_votes, years, min_votes, max_pages, today, checkpoint):
    collected = []
    for year in years:
        page = 1
        while page <= max_pages:
            try:
                data = tmdb_get("/discover/tv", key, {
                    "first_air_date_year": year, "page": page, "language": TMDB_LANG,
                    "sort_by": "popularity.desc", "vote_count.gte": min_votes,
                })
            except Exception as e:
                print(f"  shows (recent): error on year {year} page {page} ({e}) — stopping recent refresh, progress so far is saved", file=sys.stderr)
                break
            results = data.get("results", [])
            total_pages = min(data.get("total_pages", 1), 500)
            if not results:
                break
            for s in results:
                if s["id"] in seen_ids or not s.get("first_air_date") or not s.get("name"):
                    continue
                if not is_released(s["first_air_date"], today):
                    continue
                if not passes_quality(s, show_quality_tier, min_votes):
                    continue
                seen_ids.add(s["id"])
                try:
                    collected.append(show_record(s, key, genres, fetch_galleries, fetch_reviews, imdb_ratings, min_imdb_votes))
                except Exception as e:
                    print(f"    warning: skipped a show due to error ({e})", file=sys.stderr)
            print(f"  shows (recent): year {year} page {page}/{total_pages} -> {len(collected)} new so far", file=sys.stderr)
            checkpoint(collected)
            page += 1
            if page > total_pages:
                break
    return collected


def fetch_games_recent(key, seen_ids, years, max_pages, require_metacritic, min_ratings_count, today, checkpoint):
    collected = []
    for year in years:
        page = 1
        while page <= max_pages:
            try:
                data = rawg_get("/games", key, {
                    "dates": f"{year}-01-01,{year}-12-31",
                    "page": page, "page_size": 40, "ordering": "-added",
                })
            except Exception as e:
                print(f"  games (recent): error on year {year} page {page} ({e}) — stopping recent refresh, progress so far is saved", file=sys.stderr)
                break
            results = data.get("results", [])
            if not results:
                break
            for g in results:
                if g["id"] in seen_ids or not g.get("released") or not g.get("name"):
                    continue
                if not is_released(g["released"], today):
                    continue
                if not game_passes_quality(g, require_metacritic, min_ratings_count):
                    continue
                seen_ids.add(g["id"])
                try:
                    collected.append(game_record(g))
                except Exception as e:
                    print(f"    warning: skipped a game due to error ({e})", file=sys.stderr)
            print(f"  games (recent): year {year} page {page} -> {len(collected)} new so far", file=sys.stderr)
            checkpoint(collected)
            page += 1
    return collected


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--tmdb-key", required=True)
    ap.add_argument("--rawg-key", required=True)
    ap.add_argument("--years-per-run", type=int, default=YEARS_PER_RUN_DEFAULT, help="how many release years to cover per run, per category")
    ap.add_argument("--min-votes", type=int, default=30, help="tier-1 (US/Czech) TMDb vote_count floor; tier 2 needs x3 this, tier 3 needs x8 this")
    ap.add_argument("--floor-year", type=int, default=FLOOR_YEAR_DEFAULT, help="stop walking backwards once past this year")
    ap.add_argument("--galleries", action="store_true", help="also fetch a small photo gallery per movie/show (1 extra API call per title)")
    ap.add_argument("--fetch-reviews", action="store_true", help="also fetch a few genuine TMDb user reviews per movie/show (1 extra API call per title)")
    ap.add_argument("--allow-no-metacritic", action="store_true", help="include games without a Metacritic score too, gated by --min-ratings-count instead")
    ap.add_argument("--min-ratings-count", type=int, default=50, help="RAWG rating-sample floor used only when --allow-no-metacritic is set")
    ap.add_argument("--recent-pages", type=int, default=10, help="pages to scan per year in the always-on recent-titles refresh")
    ap.add_argument("--recent-min-votes", type=int, default=5, help="lower vote floor for the recent refresh, since brand-new titles have few votes yet")
    ap.add_argument("--skip-recent", action="store_true", help="skip the recent-titles refresh (only do historical backfill)")
    ap.add_argument("--skip-backfill", action="store_true", help="skip the historical backfill (only refresh recent titles — fast, good once backfill is done)")
    ap.add_argument("--no-imdb-ratings", action="store_true", help="don't cross-check scores against IMDb's real ratings — use TMDb's own vote_average as-is")
    ap.add_argument("--min-imdb-votes", type=int, default=MIN_IMDB_VOTES_DEFAULT, help="only trust an IMDb rating match if it has at least this many IMDb votes")
    ap.add_argument("--imdb-cache-file", default="imdb_ratings_cache.tsv.gz")
    ap.add_argument("--data-file", default="data.json")
    ap.add_argument("--state-file", default="fetch_state.json")
    args = ap.parse_args()
    today = today_str()
    real_year = datetime.date.today().year
    recent_years = [real_year]  # only the current year — unreleased/future titles are filtered out anyway

    imdb_ratings = {} if args.no_imdb_ratings else load_imdb_ratings(args.imdb_cache_file, IMDB_CACHE_MAX_AGE_HOURS)

    data = load_json(args.data_file, {"movies": [], "shows": [], "games": []})
    state = load_json(args.state_file, {
        "movie": {"start_year": CURRENT_YEAR_DEFAULT},
        "show": {"start_year": CURRENT_YEAR_DEFAULT},
        "game": {"start_year": CURRENT_YEAR_DEFAULT},
        "movie_seen": [], "show_seen": [], "game_seen": [],
    })

    movie_seen = set(state.get("movie_seen", []))
    show_seen = set(state.get("show_seen", []))
    game_seen = set(state.get("game_seen", []))

    def make_checkpoint(category, base_list, seen_set, seen_key):
        """Returns a function that saves data.json + fetch_state.json right now,
        combining what was already on disk with whatever this category has
        collected so far. Called frequently (every page/year), not just at the end."""
        def checkpoint(collected_so_far=None):
            snapshot = dict(data)
            snapshot[category] = base_list + (collected_so_far or [])
            save_json(args.data_file, snapshot)
            state[seen_key] = list(seen_set)
            save_json(args.state_file, state)
        return checkpoint

    print("Fetching movies...", file=sys.stderr)
    movie_genres = {}
    try:
        movie_genres = genre_map(args.tmdb_key, "movie")
        if not args.skip_backfill:
            cp = make_checkpoint("movies", data["movies"], movie_seen, "movie_seen")
            new_movies = fetch_movie_window(args.tmdb_key, state["movie"], args.years_per_run, args.floor_year, args.min_votes, movie_genres, movie_seen, args.galleries, args.fetch_reviews, imdb_ratings, args.min_imdb_votes, today, cp)
            data["movies"].extend(new_movies)
    except Exception as e:
        print(f"movies: unexpected error, stopping this category ({e})", file=sys.stderr)
    save_json(args.data_file, data)
    state["movie_seen"] = list(movie_seen)
    save_json(args.state_file, state)
    if not args.skip_recent:
        try:
            cp = make_checkpoint("movies", data["movies"], movie_seen, "movie_seen")
            new_recent_movies = fetch_movies_recent(args.tmdb_key, movie_genres, movie_seen, args.galleries, args.fetch_reviews, imdb_ratings, args.min_imdb_votes, recent_years, args.recent_min_votes, args.recent_pages, today, cp)
            data["movies"].extend(new_recent_movies)
        except Exception as e:
            print(f"movies (recent): unexpected error ({e})", file=sys.stderr)
        save_json(args.data_file, data)
        state["movie_seen"] = list(movie_seen)
        save_json(args.state_file, state)
    print(f"  -> saved. movies total so far: {len(data['movies'])}", file=sys.stderr)

    print("Fetching shows...", file=sys.stderr)
    show_genres = {}
    try:
        show_genres = genre_map(args.tmdb_key, "tv")
        if not args.skip_backfill:
            cp = make_checkpoint("shows", data["shows"], show_seen, "show_seen")
            new_shows = fetch_show_window(args.tmdb_key, state["show"], args.years_per_run, args.floor_year, args.min_votes, show_genres, show_seen, args.galleries, args.fetch_reviews, imdb_ratings, args.min_imdb_votes, today, cp)
            data["shows"].extend(new_shows)
    except Exception as e:
        print(f"shows: unexpected error, stopping this category ({e})", file=sys.stderr)
    save_json(args.data_file, data)
    state["show_seen"] = list(show_seen)
    save_json(args.state_file, state)
    if not args.skip_recent:
        try:
            cp = make_checkpoint("shows", data["shows"], show_seen, "show_seen")
            new_recent_shows = fetch_shows_recent(args.tmdb_key, show_genres, show_seen, args.galleries, args.fetch_reviews, imdb_ratings, args.min_imdb_votes, recent_years, args.recent_min_votes, args.recent_pages, today, cp)
            data["shows"].extend(new_recent_shows)
        except Exception as e:
            print(f"shows (recent): unexpected error ({e})", file=sys.stderr)
        save_json(args.data_file, data)
        state["show_seen"] = list(show_seen)
        save_json(args.state_file, state)
    print(f"  -> saved. shows total so far: {len(data['shows'])}", file=sys.stderr)

    print("Fetching games...", file=sys.stderr)
    try:
        if not args.skip_backfill:
            cp = make_checkpoint("games", data["games"], game_seen, "game_seen")
            new_games = fetch_game_window(args.rawg_key, state["game"], args.years_per_run, args.floor_year, game_seen, not args.allow_no_metacritic, args.min_ratings_count, today, cp)
            data["games"].extend(new_games)
    except Exception as e:
        print(f"games: unexpected error, stopping this category ({e})", file=sys.stderr)
    save_json(args.data_file, data)
    state["game_seen"] = list(game_seen)
    save_json(args.state_file, state)
    if not args.skip_recent:
        try:
            cp = make_checkpoint("games", data["games"], game_seen, "game_seen")
            new_recent_games = fetch_games_recent(args.rawg_key, game_seen, recent_years, args.recent_pages, not args.allow_no_metacritic, args.min_ratings_count, today, cp)
            data["games"].extend(new_recent_games)
        except Exception as e:
            print(f"games (recent): unexpected error ({e})", file=sys.stderr)
        save_json(args.data_file, data)
        state["game_seen"] = list(game_seen)
        save_json(args.state_file, state)
    print(f"  -> saved. games total so far: {len(data['games'])}", file=sys.stderr)

    print(f"\nRunning totals: {len(data['movies'])} movies, {len(data['shows'])} shows, {len(data['games'])} games", file=sys.stderr)


if __name__ == "__main__":
    main()
