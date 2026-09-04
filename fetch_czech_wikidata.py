"""
Pulls thousands of additional Czech-origin films and TV series from Wikidata — a free,
public-domain (CC0) structured database with a proper bulk-query API (SPARQL) — to fill
in what TMDb is missing. TMDb strongly favors internationally popular titles, so most
smaller/older Czech productions just aren't there at all. Wikidata is community-
maintained specifically for completeness rather than popularity, so its Czech film/TV
coverage is far broader.

I checked: ČSFD (the best Czech-specific film database) has no public API, and scraping
it would go against its terms of use, so it's not used here — Wikidata is the
legitimate, ToS-compliant path to real bulk Czech coverage.

DEDUPLICATION: fetch_data_daily.py now stores each TMDb-derived record's IMDb ID
(imdb_id field) — this script only adds a Wikidata title if its IMDb ID isn't already
present in data.json, so a film TMDb already gave you never gets added twice. As a
fallback for older entries collected before that field existed (which won't have an
imdb_id stored), it also skips exact (title, year) matches as a safety net. Run
fetch_data_daily.py's newest version at least once BEFORE this script so there's
something to deduplicate against.

SCORING: Wikidata itself has no rating data. This reuses the same local IMDb ratings
cache fetch_data_daily.py already downloads (imdb_ratings_cache.tsv.gz) — wherever a
Wikidata title has a linked IMDb ID with enough votes, that becomes its score;
otherwise it's included unscored (an "N" badge in Kritiq), the same policy used
everywhere else on the site for untrustworthy/missing rating data.

METADATA IS SPARSER THAN TMDB: Wikidata reliably has title, year, and often a director,
but rarely has composer, screenwriter, full cast, poster images, or a plot summary for
smaller Czech titles. That's an expected tradeoff for getting real bulk coverage TMDb
doesn't have — these entries will look "thinner" on Kritiq than TMDb-sourced ones.

IMPORTANT — UNTESTED LIVE: I wrote this SPARQL query against Wikidata's documented
schema (P31/instance-of, P495/country-of-origin, P345/IMDb ID, P57/director, P577/
publication date) but couldn't run it against the live endpoint from where this was
written (no network access in that environment). It should work, but if it errors out
or returns something unexpected, paste the FILM_QUERY / SHOW_QUERY text into
https://query.wikidata.org/ directly — it has a friendly query editor that shows
exactly what's wrong.

Usage:
  pip install requests
  python fetch_czech_wikidata.py

Run this AFTER fetch_data_daily.py has run at least once (so the IMDb ratings cache
file exists locally, and so there's existing data to deduplicate against).
"""

import argparse
import csv
import gzip
import json
import os
import sys
import requests

WIKIDATA_SPARQL_URL = "https://query.wikidata.org/sparql"
USER_AGENT = "KritiqCzechFilmFetcher/1.0 (personal hobby project)"

# Czech Republic (Q213), Czechoslovakia (Q33946)
CZECH_COUNTRIES = "wd:Q213 wd:Q33946"

FILM_QUERY = f"""
SELECT DISTINCT ?film ?filmLabel ?year ?imdb ?directorLabel ?boxOfficeAmount ?boxOfficeUnitLabel WHERE {{
  VALUES ?country {{ {CZECH_COUNTRIES} }}
  ?film wdt:P31 wd:Q11424 .
  ?film wdt:P495 ?country .
  OPTIONAL {{ ?film wdt:P577 ?date . BIND(YEAR(?date) AS ?year) }}
  OPTIONAL {{ ?film wdt:P345 ?imdb . }}
  OPTIONAL {{ ?film wdt:P57 ?director . }}
  OPTIONAL {{
    ?film p:P2142 ?boxOfficeStatement .
    ?boxOfficeStatement psv:P2142 ?boxOfficeValue .
    ?boxOfficeValue wikibase:quantityAmount ?boxOfficeAmount .
    ?boxOfficeValue wikibase:quantityUnit ?boxOfficeUnit .
  }}
  SERVICE wikibase:label {{ bd:serviceParam wikibase:language "cs,en". }}
}}
"""

SHOW_QUERY = f"""
SELECT DISTINCT ?show ?showLabel ?year ?imdb ?directorLabel WHERE {{
  VALUES ?country {{ {CZECH_COUNTRIES} }}
  ?show wdt:P31 wd:Q5398426 .
  ?show wdt:P495 ?country .
  OPTIONAL {{ ?show wdt:P580 ?date . BIND(YEAR(?date) AS ?year) }}
  OPTIONAL {{ ?show wdt:P345 ?imdb . }}
  OPTIONAL {{ ?show wdt:P57 ?director . }}
  SERVICE wikibase:label {{ bd:serviceParam wikibase:language "cs,en". }}
}}
"""


def run_sparql(query):
    headers = {"Accept": "application/sparql-results+json", "User-Agent": USER_AGENT}
    r = requests.get(WIKIDATA_SPARQL_URL, params={"query": query}, headers=headers, timeout=180)
    r.raise_for_status()
    return r.json()["results"]["bindings"]


def load_json(path, default):
    if os.path.exists(path):
        with open(path, "r", encoding="utf-8") as f:
            return json.load(f)
    return default


def save_json(path, obj):
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(obj, f, ensure_ascii=False, indent=2)
    os.replace(tmp, path)


def load_imdb_ratings(cache_path):
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
        print(f"warning: could not read IMDb ratings cache ({e}) — everything will be unscored", file=sys.stderr)
    return ratings


def collapse_rows(rows, item_key, label_key):
    """Wikidata returns one row per (title, director) combination when a title has
    multiple credited directors — collapse back down to one entry per title. Box office
    is only kept when Wikidata reports it in Czech koruna specifically — other-currency
    figures are dropped rather than converted, to avoid guessing at exchange rates."""
    by_uri = {}
    for row in rows:
        uri = row[item_key]["value"]
        title = row.get(label_key, {}).get("value", "")
        year = row.get("year", {}).get("value")
        imdb = row.get("imdb", {}).get("value")
        director = row.get("directorLabel", {}).get("value", "")
        box_amount = row.get("boxOfficeAmount", {}).get("value")
        box_unit = (row.get("boxOfficeUnitLabel", {}).get("value") or "").lower()
        if uri not in by_uri:
            by_uri[uri] = {"title": title, "year": year, "imdb": imdb, "director": director, "box_czk": None}
        entry = by_uri[uri]
        if director and not entry["director"]:
            entry["director"] = director
        if entry["box_czk"] is None and box_amount and ("koruna" in box_unit or "czk" in box_unit or "kč" in box_unit):
            try:
                entry["box_czk"] = float(box_amount)
            except Exception:
                pass
    return list(by_uri.values())


def build_record(entry, min_year, min_imdb_votes, imdb_ratings, genre_default):
    year = entry["year"]
    if not year:
        return None
    try:
        year = int(float(year))
    except Exception:
        return None
    if year < min_year:
        return None
    imdb_id = entry["imdb"]
    score = None
    if imdb_id and imdb_ratings:
        match = imdb_ratings.get(imdb_id)
        if match and match[1] >= min_imdb_votes:
            score = round(match[0] * 10)
    box_czk = entry.get("box_czk")
    box = round(box_czk / 1_000_000, 1) if box_czk else None  # displayed as "X mil. Kč" in Kritiq
    return {
        "title": entry["title"],
        "imdb_id": imdb_id,
        "year": year,
        "date": f"{year}-01-01",  # Wikidata is usually year-only precision for older titles
        "score": score,
        "genre": genre_default,
        "country": "Česko",
        "box": box,
        "box_currency": "CZK" if box is not None else None,
        "poster": "",
        "gallery": [],
        "summary": "",
        "director": entry["director"] or "",
        "composer": "",
        "writer": "",
        "actors": [],
        "reviews": [],
    }


def dedupe_and_collect(entries, min_year, min_imdb_votes, imdb_ratings, genre_default, known_imdb, known_title_year):
    out = []
    for e in entries:
        rec = build_record(e, min_year, min_imdb_votes, imdb_ratings, genre_default)
        if not rec:
            continue
        if rec["imdb_id"] and rec["imdb_id"] in known_imdb:
            continue
        ty_key = (rec["title"].strip().lower(), rec["year"])
        if ty_key in known_title_year:
            continue
        out.append(rec)
        if rec["imdb_id"]:
            known_imdb.add(rec["imdb_id"])
        known_title_year.add(ty_key)
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--min-year", type=int, default=1898)
    ap.add_argument("--min-imdb-votes", type=int, default=20, help="lower than fetch_data_daily.py's default — these are niche/older Czech titles by nature, so demanding as many votes would leave almost everything unscored")
    ap.add_argument("--imdb-cache-file", default="imdb_ratings_cache.tsv.gz")
    ap.add_argument("--data-file", default="data.json")
    args = ap.parse_args()

    imdb_ratings = load_imdb_ratings(args.imdb_cache_file)
    if not imdb_ratings:
        print("warning: no local IMDb ratings cache found at " + args.imdb_cache_file +
              " — run fetch_data_daily.py first (it downloads this automatically), "
              "or every Czech title added here will be unscored.", file=sys.stderr)

    data = load_json(args.data_file, {"movies": [], "shows": [], "games": []})
    known_imdb_movie = {m["imdb_id"] for m in data["movies"] if m.get("imdb_id")}
    known_imdb_show = {s["imdb_id"] for s in data["shows"] if s.get("imdb_id")}
    known_ty_movie = {(m["title"].strip().lower(), m["year"]) for m in data["movies"]}
    known_ty_show = {(s["title"].strip().lower(), s["year"]) for s in data["shows"]}

    print("Querying Wikidata for Czech films (this can take a minute or two)...", file=sys.stderr)
    try:
        film_rows = run_sparql(FILM_QUERY)
    except Exception as e:
        print(f"Wikidata film query failed: {e}", file=sys.stderr)
        print("Try pasting FILM_QUERY into https://query.wikidata.org/ to debug.", file=sys.stderr)
        film_rows = []
    try:
        film_entries = collapse_rows(film_rows, "film", "filmLabel")
    except Exception as e:
        print(f"warning: could not parse film results ({e}) — skipping films this run", file=sys.stderr)
        film_entries = []
    print(f"  {len(film_entries)} unique films from Wikidata", file=sys.stderr)

    new_movies = dedupe_and_collect(film_entries, args.min_year, args.min_imdb_votes, imdb_ratings, "Film", known_imdb_movie, known_ty_movie)
    print(f"  {len(new_movies)} new (non-duplicate) Czech films to add", file=sys.stderr)
    data["movies"].extend(new_movies)
    save_json(args.data_file, data)

    print("Querying Wikidata for Czech TV series...", file=sys.stderr)
    try:
        show_rows = run_sparql(SHOW_QUERY)
    except Exception as e:
        print(f"Wikidata show query failed: {e}", file=sys.stderr)
        print("Try pasting SHOW_QUERY into https://query.wikidata.org/ to debug.", file=sys.stderr)
        show_rows = []
    try:
        show_entries = collapse_rows(show_rows, "show", "showLabel")
    except Exception as e:
        print(f"warning: could not parse show results ({e}) — skipping shows this run", file=sys.stderr)
        show_entries = []
    print(f"  {len(show_entries)} unique shows from Wikidata", file=sys.stderr)

    new_shows = dedupe_and_collect(show_entries, args.min_year, args.min_imdb_votes, imdb_ratings, "Seriál", known_imdb_show, known_ty_show)
    print(f"  {len(new_shows)} new (non-duplicate) Czech shows to add", file=sys.stderr)
    data["shows"].extend(new_shows)
    save_json(args.data_file, data)

    print(f"\nDone. movies now: {len(data['movies'])}, shows now: {len(data['shows'])}", file=sys.stderr)


if __name__ == "__main__":
    main()
