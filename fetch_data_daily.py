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
  data.json         merged with everything fetched so far — drop next to kritiq.html.
                    Each entry stores its source id (tmdb_id or rawg_id) — every run,
                    the script rebuilds its "already have this" tracking directly from
                    whatever's actually in data.json (in addition to fetch_state.json's
                    own record), so it can't silently duplicate entries even if the two
                    files ever drift out of sync with each other.
  fetch_state.json  progress tracker (which year each category is up to) — do NOT
                    delete this alone between runs, or it will think years it's
                    already scanned still need scanning, which is harmless but slow.

IMPORTANT — data.json and fetch_state.json are a PAIR: delete them BOTH together for a
genuine fresh start, or leave them BOTH alone. Deleting only one (especially data.json
while keeping fetch_state.json) will make the script think it already has titles that
no longer actually exist in your data file, and it'll collect nothing new for whichever
years it believes are already done.

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

STRICT_GENRE_MULT = 5     # CZ/EN content that's a documentary/concert/music special: tightened
UNSCORED_INCLUDE_MULT = 10  # non-CZ/EN content: much stricter bar just to be included at all
STRICT_GENRES = {"movie": {10402, 99}, "tv": {99}}  # 10402=Music, 99=Documentary (TMDb genre ids)
COUNTRY_BLOCKLIST = {"IN", "CN", "RU", "CO", "MX", "BR"}  # India, China, Russia, Colombia, Mexico, Brazil
SOAP_GENRE_ID = 10766
REALITY_GENRE_ID = 10764
# "Special tier" = content that needs to be exceptionally popular to earn a real score,
# same 3-way benchmark logic as originally built for anime: TMDb genre 16 (Animation) and
# 10770 (TV Movie) — the latter is where WWE events, stand-up specials, and pop-star concert
# films typically get tagged, which is what was showing up ranked among genuine films.
SPECIAL_TIER_GENRES = {"movie": {16, 10770}, "tv": {16}}
ANIME_BENCHMARK_VOTES_DEFAULT = 800  # rough placeholder for "as popular as Blue Eyed Samurai" —
                                       # check its actual TMDb vote count and adjust via
                                       # --anime-benchmark-votes if this doesn't feel right
COUNTRY_NAMES_CS = {
    "US": "USA", "CZ": "Česko", "GB": "Velká Británie", "FR": "Francie", "DE": "Německo",
    "ES": "Španělsko", "IT": "Itálie", "CA": "Kanada", "AU": "Austrálie", "JP": "Japonsko",
    "KR": "Jižní Korea", "IN": "Indie", "CN": "Čína", "RU": "Rusko", "BR": "Brazílie",
    "MX": "Mexiko", "CO": "Kolumbie", "SE": "Švédsko", "NO": "Norsko", "DK": "Dánsko",
    "FI": "Finsko", "PL": "Polsko", "AT": "Rakousko", "CH": "Švýcarsko", "BE": "Belgie",
    "NL": "Nizozemsko", "IE": "Irsko", "NZ": "Nový Zéland", "SK": "Slovensko", "HU": "Maďarsko",
    "PT": "Portugalsko", "GR": "Řecko", "TR": "Turecko", "ZA": "Jihoafrická republika",
    "AR": "Argentina", "IL": "Izrael", "TH": "Thajsko", "HK": "Hongkong", "TW": "Tchaj-wan",
}


def country_name_cs(code):
    return COUNTRY_NAMES_CS.get(code, code)


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
            if r.status_code == 404:
                # RAWG returns a plain 404 once you page past its available results for a
                # given query (unlike TMDb, which just returns an empty results list) —
                # treat that the same way: no more results here, not a real error.
                return {"results": []}
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
    """Returns (score, used_imdb_bool, imdb_id). imdb_id is fetched and returned even
    when IMDb score cross-referencing is off (--no-imdb-ratings) — it's also stored on
    the record so other scripts (like fetch_czech_wikidata.py) can deduplicate against
    this title without pulling in a second copy of it."""
    imdb_id = get_imdb_id(key, media, tmdb_id)
    if not imdb_ratings or not imdb_id:
        return fallback_score, False, imdb_id
    match = imdb_ratings.get(imdb_id)
    if not match or match[1] < min_imdb_votes:
        return fallback_score, False, imdb_id
    return round(match[0] * 10), True, imdb_id


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


def movie_lang_ok(m):
    """True if a genuine Czech translation exists (localized title differs from the
    original) or the title is originally in English — these are eligible for a real
    numeric score, subject to the further country/genre checks below. Everything else
    (Korean, Chinese, Japanese, Spanish, etc. with no Czech translation) still gets
    collected under a stricter bar, but is never given a numeric score."""
    return m.get("title") != m.get("original_title") or m.get("original_language") in ("en", "cs")


def show_lang_ok(s):
    return s.get("name") != s.get("original_name") or s.get("original_language") in ("en", "cs")


def is_strict_genre(item, media):
    gids = set(item.get("genre_ids") or [])
    return bool(gids & STRICT_GENRES.get(media, set()))


def is_special_tier(item, media):
    gids = set(item.get("genre_ids") or [])
    return bool(gids & SPECIAL_TIER_GENRES.get(media, set()))


def show_is_soap_or_reality(s):
    return bool(set(s.get("genre_ids") or []) & {SOAP_GENRE_ID, REALITY_GENRE_ID})


def show_is_czech(s):
    return "CZ" in (s.get("origin_country") or [])


def get_movie_details(key, movie_id):
    """One call gives us everything extra a movie needs: production countries (for the
    blocklist check AND the "country of production" field) and revenue (for a real
    worldwide box-office figure instead of the old popularity-based guess)."""
    try:
        data = tmdb_get(f"/movie/{movie_id}", key, {"language": "en-US"})
        countries = [c.get("iso_3166_1") for c in (data.get("production_countries") or [])]
        revenue = data.get("revenue") or None  # TMDb uses 0 for "no data" — treat as missing
        return {"countries": countries, "revenue": revenue}
    except Exception:
        return {"countries": [], "revenue": None}


def evaluate_movie(key, m, min_votes, special_benchmark):
    """Returns (include, scored, details). include=False means skip entirely; scored=False
    means include it but with score=null (an "N" badge in Kritiq). details is the result of
    get_movie_details (country + revenue), fetched at most once, only for included movies."""
    lang_ok = movie_lang_ok(m)
    vote_count = m.get("vote_count") or 0

    if not lang_ok:
        if vote_count < min_votes * UNSCORED_INCLUDE_MULT:
            return (False, False, None)
        return (True, False, get_movie_details(key, m["id"]))

    special = is_special_tier(m, "movie")
    if special:
        if vote_count >= special_benchmark:
            pass  # popular enough — fall through to the remaining checks below
        elif vote_count >= special_benchmark / 2:
            return (True, False, get_movie_details(key, m["id"]))
        else:
            return (False, False, None)
    elif is_strict_genre(m, "movie") and vote_count < min_votes * STRICT_GENRE_MULT:
        return (False, False, None)

    if vote_count < min_votes:
        return (False, False, None)

    details = get_movie_details(key, m["id"])
    if set(details["countries"]) & COUNTRY_BLOCKLIST:
        return (True, False, details)

    return (True, True, details)


def evaluate_show(key, s, min_votes, special_benchmark):
    """Returns (include, scored, countries). origin_country is free in the discover
    response for shows, so no extra API call is needed here at all."""
    lang_ok = show_lang_ok(s)
    vote_count = s.get("vote_count") or 0
    czech = show_is_czech(s)
    countries = s.get("origin_country") or []

    if not lang_ok:
        return (vote_count >= min_votes * UNSCORED_INCLUDE_MULT, False, countries)

    special = is_special_tier(s, "tv")
    if special:
        if vote_count >= special_benchmark:
            pass
        elif vote_count >= special_benchmark / 2:
            return (True, False, countries)
        else:
            return (False, False, countries)

    if show_is_soap_or_reality(s) and not czech:
        return (vote_count >= min_votes, False, countries)

    if is_strict_genre(s, "tv") and vote_count < min_votes * STRICT_GENRE_MULT:
        return (False, False, countries)

    if vote_count < min_votes:
        return (False, False, countries)

    if not czech and bool(set(countries) & COUNTRY_BLOCKLIST):
        return (True, False, countries)

    return (True, True, countries)


def get_person_info(key, person_id, people_cache):
    """Fetches an actor's birthday/deathday once per person, ever — cached in
    people_cache (persisted to people.json) so an actor who appears in dozens of
    titles across many runs only costs one API call, not one per appearance."""
    pid = str(person_id)
    if pid in people_cache:
        return people_cache[pid]
    try:
        data = tmdb_get(f"/person/{person_id}", key, {"language": "en-US"})
        info = {"birthday": data.get("birthday"), "deathday": data.get("deathday")}
    except Exception:
        info = {"birthday": None, "deathday": None}
    people_cache[pid] = info
    return info


def compute_age(birthday, deathday, today):
    if not birthday:
        return None
    try:
        b = datetime.date.fromisoformat(birthday)
        end = datetime.date.fromisoformat(deathday) if deathday else datetime.date.fromisoformat(today)
        return end.year - b.year - ((end.month, end.day) < (b.month, b.day))
    except Exception:
        return None


def build_actor_list(key, cast, people_cache, today, cap=8):
    actors = []
    for c in cast[:cap]:
        pid = c.get("id")
        info = get_person_info(key, pid, people_cache) if pid else {"birthday": None, "deathday": None}
        actors.append({
            "name": c.get("name", ""),
            "birthday": info.get("birthday"),
            "deathday": info.get("deathday"),
            "age": compute_age(info.get("birthday"), info.get("deathday"), today),
        })
    return actors


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


def movie_record(m, key, genres, fetch_galleries, fetch_reviews, imdb_ratings, min_imdb_votes, scored, details, people_cache, today):
    director = composer = writer = ""
    actors = []
    try:
        credits = tmdb_get(f"/movie/{m['id']}/credits", key)
        director = next((c["name"] for c in credits.get("crew", []) if c["job"] == "Director"), "")
        composer = next((c["name"] for c in credits.get("crew", []) if c["job"] == "Original Music Composer"), "")
        writer = next((c["name"] for c in credits.get("crew", []) if c["job"] in ("Screenplay", "Writer")), "")
        actors = build_actor_list(key, credits.get("cast", []), people_cache, today)
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
    imdb_id = None
    if scored:
        fallback_score = round(m.get("vote_average", 0) * 10)
        score, used_imdb, imdb_id = imdb_score_for(key, "movie", m["id"], imdb_ratings, min_imdb_votes, fallback_score)
    else:
        score = None  # not in Czech or English — shown as an "N" badge in Kritiq, no invented score
        imdb_id = get_imdb_id(key, "movie", m["id"])
    details = details or {"countries": [], "revenue": None}
    country = country_name_cs(details["countries"][0]) if details["countries"] else ""
    # Real estimated worldwide gross from TMDb (revenue field), not the old popularity-based
    # guess — TMDb reports this as a single worldwide figure, not split US/international.
    # Left out entirely (rather than shown as $0) when TMDb has no reliable figure for it.
    box = round(details["revenue"] / 1_000_000) if details["revenue"] else None
    return {
        "title": m["title"],
        "tmdb_id": m["id"],
        "imdb_id": imdb_id,
        "year": int(m["release_date"][:4]),
        "date": m["release_date"],
        "score": score,
        "box": box,
        "box_currency": "USD" if box is not None else None,
        "country": country,
        "genre": genre,
        "poster": poster,
        "gallery": gallery,
        "summary": (m.get("overview") or "").strip(),
        "director": director, "composer": composer, "writer": writer, "actors": actors,
        "reviews": reviews,
    }


def show_record(s, key, genres, fetch_galleries, fetch_reviews, imdb_ratings, min_imdb_votes, scored, countries, people_cache, today):
    director = composer = writer = ""
    actors = []
    try:
        # The plain /tv/{id}/credits endpoint often has no "Director"/"Writer" job at all for
        # shows (TV doesn't really have a single per-series director the way movies do) —
        # aggregate_credits rolls up crew roles across every episode/season instead, which
        # actually has them. created_by (on the main details object) is a reliable writer
        # fallback too. append_to_response bundles all of this into one API call.
        details = tmdb_get(f"/tv/{s['id']}", key, {"append_to_response": "aggregate_credits"})
        agg = details.get("aggregate_credits") or {}
        crew = agg.get("crew", [])
        cast = agg.get("cast", [])

        def find_job(job_names):
            for c in crew:
                jobs = {j.get("job") for j in (c.get("jobs") or [])}
                if jobs & job_names:
                    return c["name"]
            return ""

        director = find_job({"Director", "Series Director"})
        composer = find_job({"Original Music Composer", "Music", "Composer"})
        writer = find_job({"Writer", "Story Editor", "Teleplay"})
        if not writer:
            creators = details.get("created_by") or []
            if creators:
                writer = creators[0].get("name", "")
        actors = build_actor_list(key, cast, people_cache, today)
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
    imdb_id = None
    if scored:
        fallback_score = round(s.get("vote_average", 0) * 10)
        score, used_imdb, imdb_id = imdb_score_for(key, "tv", s["id"], imdb_ratings, min_imdb_votes, fallback_score)
    else:
        score = None  # not in Czech or English — shown as an "N" badge in Kritiq, no invented score
        imdb_id = get_imdb_id(key, "tv", s["id"])
    country = country_name_cs(countries[0]) if countries else ""
    return {
        "title": s["name"],
        "country": country,
        "tmdb_id": s["id"],
        "imdb_id": imdb_id,
        "year": int(s["first_air_date"][:4]),
        "date": s["first_air_date"],
        "score": score,
        "genre": genre,
        "poster": poster,
        "gallery": gallery,
        "summary": (s.get("overview") or "").strip(),
        "director": director, "composer": composer, "writer": writer, "actors": actors,
        "reviews": reviews,
    }


def is_mostly_latin(text):
    """RAWG has no language/translation metadata for games (unlike TMDb for movies/shows),
    so this is the best cheap proxy available: is the title written in Latin script at all.
    Catches cases like Chinese/Japanese/Korean titles; won't distinguish a Spanish-titled
    game from an English one since both use the Latin alphabet — RAWG mostly lists a single
    global title anyway, so that's a smaller gap in practice."""
    letters = [c for c in text if c.isalpha()]
    if not letters:
        return True
    latin = sum(1 for c in letters if ord(c) < 0x0250 or 0x1E00 <= ord(c) <= 0x1EFF)
    return (latin / len(letters)) >= 0.7


def game_record(g, key):
    try:
        details = rawg_get(f"/games/{g['id']}", key)
    except Exception as e:
        print(f"    warning: detail fetch failed for game {g.get('id')} ({e}) — developer may be blank", file=sys.stderr)
        details = {}
    devs_list = details.get("developers") or g.get("developers") or []
    pubs_list = details.get("publishers") or g.get("publishers") or []
    devs = ", ".join(d["name"] for d in devs_list[:1]) or ", ".join(p["name"] for p in pubs_list[:1]) or "Neznámý vývojář"
    genre = ", ".join(x["name"] for x in (g.get("genres") or details.get("genres") or [])[:1])
    poster = g.get("background_image") or ""
    gallery = [s["image"] for s in (g.get("short_screenshots") or []) if s.get("image") and s.get("image") != poster][:6]
    if is_mostly_latin(g["name"]):
        metacritic = g.get("metacritic")
        score = metacritic if metacritic is not None else round((g.get("rating") or 0) * 20)
    else:
        score = None  # title not available in Latin script (Czech/English) — "N" badge, no invented score
    return {
        "title": g["name"],
        "rawg_id": g["id"],
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
    lang_ok = is_mostly_latin(g.get("name") or "")
    if not lang_ok:
        # not scored either way, so just keep out the very obscure ones
        return (g.get("ratings_count") or 0) >= min_ratings_count * 3
    if g.get("metacritic") is not None:
        return True
    if require_metacritic:
        return False
    return (g.get("ratings_count") or 0) >= min_ratings_count


def fetch_movie_window(key, state, years_per_run, floor_year, min_votes, genres, seen_ids, fetch_galleries, fetch_reviews, imdb_ratings, min_imdb_votes, anime_benchmark, people_cache, today, checkpoint):
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
            include, scored, details = evaluate_movie(key, m, min_votes, anime_benchmark)
            if not include:
                continue
            seen_ids.add(m["id"])
            try:
                collected.append(movie_record(m, key, genres, fetch_galleries, fetch_reviews, imdb_ratings, min_imdb_votes, scored, details, people_cache, today))
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


def fetch_show_window(key, state, years_per_run, floor_year, min_votes, genres, seen_ids, fetch_galleries, fetch_reviews, imdb_ratings, min_imdb_votes, anime_benchmark, people_cache, today, checkpoint):
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
            include, scored, countries = evaluate_show(key, s, min_votes, anime_benchmark)
            if not include:
                continue
            seen_ids.add(s["id"])
            try:
                collected.append(show_record(s, key, genres, fetch_galleries, fetch_reviews, imdb_ratings, min_imdb_votes, scored, countries, people_cache, today))
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
                "page": page, "page_size": 40, "ordering": "-metacritic,-added",
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
        with_mc = sum(1 for g in results if g.get("metacritic") is not None)
        for g in results:
            if g["id"] in seen_ids or not g.get("released") or not g.get("name"):
                continue
            if not is_released(g["released"], today):
                continue
            if not game_passes_quality(g, require_metacritic, min_ratings_count):
                continue
            seen_ids.add(g["id"])
            try:
                collected.append(game_record(g, key))
                kept += 1
            except Exception as e:
                print(f"    warning: skipped a game due to error ({e})", file=sys.stderr)
        print(f"  games: year {year} page {page} -> {len(collected)} collected so far ({kept} kept, {with_mc}/{len(results)} on this page had Metacritic)", file=sys.stderr)
        page += 1
        state["year"] = year
        state["page"] = page
        checkpoint(collected)
    else:
        state["year"] = year_start - 1
        state["page"] = 1
        checkpoint(collected)
    return collected


def fetch_movies_recent(key, genres, seen_ids, fetch_galleries, fetch_reviews, imdb_ratings, min_imdb_votes, anime_benchmark, people_cache, years, min_votes, max_pages, today, checkpoint):
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
                include, scored, details = evaluate_movie(key, m, min_votes, anime_benchmark)
                if not include:
                    continue
                seen_ids.add(m["id"])
                try:
                    collected.append(movie_record(m, key, genres, fetch_galleries, fetch_reviews, imdb_ratings, min_imdb_votes, scored, details, people_cache, today))
                except Exception as e:
                    print(f"    warning: skipped a movie due to error ({e})", file=sys.stderr)
            print(f"  movies (recent): year {year} page {page}/{total_pages} -> {len(collected)} new so far", file=sys.stderr)
            checkpoint(collected)
            page += 1
            if page > total_pages:
                break
    return collected


def fetch_shows_recent(key, genres, seen_ids, fetch_galleries, fetch_reviews, imdb_ratings, min_imdb_votes, anime_benchmark, people_cache, years, min_votes, max_pages, today, checkpoint):
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
                include, scored, countries = evaluate_show(key, s, min_votes, anime_benchmark)
                if not include:
                    continue
                seen_ids.add(s["id"])
                try:
                    collected.append(show_record(s, key, genres, fetch_galleries, fetch_reviews, imdb_ratings, min_imdb_votes, scored, countries, people_cache, today))
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
                    "page": page, "page_size": 40, "ordering": "-metacritic,-added",
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
                    collected.append(game_record(g, key))
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
    ap.add_argument("--anime-benchmark-votes", type=int, default=ANIME_BENCHMARK_VOTES_DEFAULT, help="animated/wrestling/stand-up/concert-special movies-shows need this many votes to be scored; half this to be included at all (unranked); check a title like Blue Eyed Samurai's real TMDb vote count and adjust")
    ap.add_argument("--people-cache-file", default="people.json", help="cache of actor birthday/deathday, so the same actor isn't re-fetched across many titles")
    ap.add_argument("--data-file", default="data.json")
    ap.add_argument("--state-file", default="fetch_state.json")
    args = ap.parse_args()
    today = today_str()
    real_year = datetime.date.today().year
    recent_years = [real_year]  # only the current year — unreleased/future titles are filtered out anyway

    imdb_ratings = {} if args.no_imdb_ratings else load_imdb_ratings(args.imdb_cache_file, IMDB_CACHE_MAX_AGE_HOURS)
    people_cache = load_json(args.people_cache_file, {})

    data = load_json(args.data_file, {"movies": [], "shows": [], "games": []})
    state = load_json(args.state_file, {
        "movie": {"start_year": CURRENT_YEAR_DEFAULT},
        "show": {"start_year": CURRENT_YEAR_DEFAULT},
        "game": {"start_year": CURRENT_YEAR_DEFAULT},
        "movie_seen": [], "show_seen": [], "game_seen": [],
    })

    movie_seen = set(state.get("movie_seen", [])) | {m["tmdb_id"] for m in data["movies"] if m.get("tmdb_id")}
    show_seen = set(state.get("show_seen", [])) | {s["tmdb_id"] for s in data["shows"] if s.get("tmdb_id")}
    game_seen = set(state.get("game_seen", [])) | {g["rawg_id"] for g in data["games"] if g.get("rawg_id")}

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
            save_json(args.people_cache_file, people_cache)
        return checkpoint

    print("Fetching movies...", file=sys.stderr)
    movie_genres = {}
    try:
        movie_genres = genre_map(args.tmdb_key, "movie")
        if not args.skip_backfill:
            cp = make_checkpoint("movies", data["movies"], movie_seen, "movie_seen")
            new_movies = fetch_movie_window(args.tmdb_key, state["movie"], args.years_per_run, args.floor_year, args.min_votes, movie_genres, movie_seen, args.galleries, args.fetch_reviews, imdb_ratings, args.min_imdb_votes, args.anime_benchmark_votes, people_cache, today, cp)
            data["movies"].extend(new_movies)
    except Exception as e:
        print(f"movies: unexpected error, stopping this category ({e})", file=sys.stderr)
    save_json(args.data_file, data)
    state["movie_seen"] = list(movie_seen)
    save_json(args.state_file, state)
    save_json(args.people_cache_file, people_cache)
    if not args.skip_recent:
        try:
            cp = make_checkpoint("movies", data["movies"], movie_seen, "movie_seen")
            new_recent_movies = fetch_movies_recent(args.tmdb_key, movie_genres, movie_seen, args.galleries, args.fetch_reviews, imdb_ratings, args.min_imdb_votes, args.anime_benchmark_votes, people_cache, recent_years, args.recent_min_votes, args.recent_pages, today, cp)
            data["movies"].extend(new_recent_movies)
        except Exception as e:
            print(f"movies (recent): unexpected error ({e})", file=sys.stderr)
        save_json(args.data_file, data)
        state["movie_seen"] = list(movie_seen)
        save_json(args.state_file, state)
        save_json(args.people_cache_file, people_cache)
    print(f"  -> saved. movies total so far: {len(data['movies'])}", file=sys.stderr)

    print("Fetching shows...", file=sys.stderr)
    show_genres = {}
    try:
        show_genres = genre_map(args.tmdb_key, "tv")
        if not args.skip_backfill:
            cp = make_checkpoint("shows", data["shows"], show_seen, "show_seen")
            new_shows = fetch_show_window(args.tmdb_key, state["show"], args.years_per_run, args.floor_year, args.min_votes, show_genres, show_seen, args.galleries, args.fetch_reviews, imdb_ratings, args.min_imdb_votes, args.anime_benchmark_votes, people_cache, today, cp)
            data["shows"].extend(new_shows)
    except Exception as e:
        print(f"shows: unexpected error, stopping this category ({e})", file=sys.stderr)
    save_json(args.data_file, data)
    state["show_seen"] = list(show_seen)
    save_json(args.state_file, state)
    save_json(args.people_cache_file, people_cache)
    if not args.skip_recent:
        try:
            cp = make_checkpoint("shows", data["shows"], show_seen, "show_seen")
            new_recent_shows = fetch_shows_recent(args.tmdb_key, show_genres, show_seen, args.galleries, args.fetch_reviews, imdb_ratings, args.min_imdb_votes, args.anime_benchmark_votes, people_cache, recent_years, args.recent_min_votes, args.recent_pages, today, cp)
            data["shows"].extend(new_recent_shows)
        except Exception as e:
            print(f"shows (recent): unexpected error ({e})", file=sys.stderr)
        save_json(args.data_file, data)
        state["show_seen"] = list(show_seen)
        save_json(args.state_file, state)
        save_json(args.people_cache_file, people_cache)
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
