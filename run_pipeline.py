#!/usr/bin/env python3
"""Souss-Massa political news monitor.

Collects selected local news sources, classifies relevant articles, updates
JSON/CSV storage, clusters near-duplicate events, and rebuilds a standalone
HTML dashboard. Full article text is processed transiently and is not stored.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import html
import json
import os
import re
import sys
import time
import unicodedata
import urllib.robotparser
from collections import Counter, defaultdict
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Any, Iterable
from urllib.parse import parse_qsl, urlencode, urljoin, urlparse, urlunparse

import dateparser
import pandas as pd
import requests
import trafilatura
from bs4 import BeautifulSoup
from rapidfuzz.fuzz import ratio as fuzzy_ratio


APP_VERSION = "2.0.0"
DEFAULT_USER_AGENT = (
    "Mozilla/5.0 (compatible; SoussMassaMonitor/2.0; "
    "+political-news-research)"
)

ARABIC_DIACRITICS = re.compile(r"[\u0610-\u061A\u064B-\u065F\u0670\u06D6-\u06ED]")
ARABIC_LETTER = r"\u0621-\u064A\u066E-\u06D3\u06FA-\u06FF"

EXCLUDED_PATH_PARTS = (
    "/category/",
    "/tag/",
    "/author/",
    "/page/",
    "/feed/",
    "/search/",
    "/contact",
    "/privacy",
    "/login",
    "/register",
    "/wp-admin",
    "/wp-login",
    "/cdn-cgi/",
    "/ads/",
)
EXCLUDED_EXTENSIONS = (
    ".jpg",
    ".jpeg",
    ".png",
    ".gif",
    ".webp",
    ".svg",
    ".pdf",
    ".mp3",
    ".mp4",
    ".zip",
)


def now_utc() -> datetime:
    return datetime.now(timezone.utc)


def iso_now() -> str:
    return now_utc().isoformat()


def load_json(path: Path, default: Any = None) -> Any:
    if not path.exists():
        if default is not None:
            return default
        raise FileNotFoundError(f"Missing required file: {path}")
    with path.open("r", encoding="utf-8") as handle:
        return json.load(handle)


def atomic_write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temp_path = path.with_suffix(path.suffix + ".tmp")
    temp_path.write_text(content, encoding="utf-8")
    temp_path.replace(path)


def atomic_write_json(path: Path, data: Any) -> None:
    atomic_write_text(
        path,
        json.dumps(data, ensure_ascii=False, indent=2),
    )


def normalize_text(value: Any) -> str:
    text = unicodedata.normalize("NFKC", str(value or ""))
    text = ARABIC_DIACRITICS.sub("", text)
    text = text.replace("ـ", "")
    text = text.translate(
        str.maketrans(
            {
                "أ": "ا",
                "إ": "ا",
                "آ": "ا",
                "ٱ": "ا",
                "ى": "ي",
                "ؤ": "و",
                "ئ": "ي",
            }
        )
    )
    text = re.sub(r"\s+", " ", text).strip().lower()
    return text


def compact_text(value: Any) -> str:
    return re.sub(r"\s+", " ", str(value or "")).strip()


def alias_pattern(alias: str) -> re.Pattern[str]:
    normalized = normalize_text(alias)
    escaped = re.escape(normalized).replace(r"\ ", r"\s+")
    # Arabic conjunctions and prepositions can be attached to the first word.
    if re.search(f"[{ARABIC_LETTER}]", normalized):
        prefix = r"(?:و|ف|ب|ك|ل|بال|فال|وال|لل)?"
        return re.compile(
            rf"(?<![{ARABIC_LETTER}0-9A-Za-z]){prefix}{escaped}"
            rf"(?![{ARABIC_LETTER}0-9A-Za-z])",
            re.IGNORECASE,
        )
    return re.compile(rf"(?<!\w){escaped}(?!\w)", re.IGNORECASE)


_PATTERN_CACHE: dict[str, re.Pattern[str]] = {}


def contains_alias(text: str, alias: str) -> bool:
    key = normalize_text(alias)
    if len(key) < 2:
        return False
    pattern = _PATTERN_CACHE.get(key)
    if pattern is None:
        pattern = alias_pattern(alias)
        _PATTERN_CACHE[key] = pattern
    return bool(pattern.search(normalize_text(text)))


def matched_aliases(text: str, aliases: Iterable[str]) -> list[str]:
    matches: list[str] = []
    seen: set[str] = set()
    for alias in aliases:
        clean = compact_text(alias)
        normalized = normalize_text(clean)
        if normalized in seen or len(normalized) < 2:
            continue
        if contains_alias(text, clean):
            seen.add(normalized)
            matches.append(clean)
    return matches


def clean_domain(url: str) -> str:
    return urlparse(url).netloc.lower().replace("www.", "")


def canonicalize_url(url: str) -> str:
    parsed = urlparse(url)
    query = [
        (key, value)
        for key, value in parse_qsl(parsed.query, keep_blank_values=True)
        if not key.lower().startswith("utm_")
        and key.lower() not in {"fbclid", "gclid", "output", "amp"}
    ]
    path = re.sub(r"/{2,}", "/", parsed.path or "/")
    if path != "/":
        path = path.rstrip("/")
    return urlunparse(
        (
            parsed.scheme.lower() or "https",
            parsed.netloc.lower(),
            path,
            "",
            urlencode(query, doseq=True),
            "",
        )
    )


def stable_id(prefix: str, value: str, length: int = 16) -> str:
    digest = hashlib.sha256(value.encode("utf-8")).hexdigest()[:length]
    return f"{prefix}{digest}"


def detect_language(text: str) -> str:
    arabic_count = len(re.findall(f"[{ARABIC_LETTER}]", text))
    latin_count = len(re.findall(r"[A-Za-zÀ-ÿ]", text))
    if arabic_count > max(20, latin_count * 1.25):
        return "ar"
    if latin_count > max(20, arabic_count * 1.25):
        return "fr"
    return "mixed"


def parse_date(value: Any) -> str | None:
    raw = compact_text(value)
    if not raw:
        return None
    parsed = dateparser.parse(
        raw,
        languages=["ar", "fr", "en"],
        settings={
            "RETURN_AS_TIMEZONE_AWARE": True,
            "TIMEZONE": "Africa/Casablanca",
            "TO_TIMEZONE": "UTC",
            "PREFER_DATES_FROM": "past",
        },
    )
    if parsed is None:
        return None
    if parsed.tzinfo is None:
        parsed = parsed.replace(tzinfo=timezone.utc)
    if parsed > now_utc() + timedelta(days=3):
        return None
    return parsed.date().isoformat()


def sentence_split(text: str) -> list[str]:
    clean = compact_text(text)
    if not clean:
        return []
    parts = re.split(r"(?<=[.!؟?؛])\s+|\n+", clean)
    return [part.strip() for part in parts if len(part.strip()) >= 15]


def first_words(text: str, maximum: int = 25) -> str:
    return " ".join(compact_text(text).split()[:maximum])


def find_first_list(container: Any, keys: Iterable[str]) -> list[Any]:
    if isinstance(container, list):
        return container
    if isinstance(container, dict):
        for key in keys:
            value = container.get(key)
            if isinstance(value, list):
                return value
    return []


class Monitor:
    def __init__(self, root: Path, reprocess_existing: bool = False):
        self.root = root
        self.config_dir = root / "config"
        self.data_dir = root / "data"
        self.output_dir = root / "output"
        self.logs_dir = root / "logs"
        for directory in (
            self.config_dir,
            self.data_dir,
            self.output_dir,
            self.logs_dir,
        ):
            directory.mkdir(parents=True, exist_ok=True)

        self.settings = load_json(self.config_dir / "settings.json", {})
        source_v2 = self.config_dir / "sources_local_v2.json"
        source_legacy = self.config_dir / "sources.json"
        source_data = load_json(source_v2 if source_v2.exists() else source_legacy, [])
        self.sources = find_first_list(source_data, ("sources",))
        self.sources = [source for source in self.sources if source.get("enabled", True)]

        self.geography = load_json(self.config_dir / "geography.json", {})
        self.parties = load_json(self.config_dir / "parties.json", [])
        self.topics = load_json(self.config_dir / "topics.json", [])
        self.persons = load_json(self.config_dir / "persons.json", [])
        self.stance_rules = load_json(self.config_dir / "stance_rules.json", {})

        self.news_path = self.data_dir / "news.json"
        self.csv_path = self.data_dir / "news.csv"
        self.crawl_state_path = self.data_dir / "crawl_state.json"
        self.run_status_path = self.data_dir / "run_status.json"
        self.html_path = self.output_dir / "index.html"
        # Keep the experimental notebook log untouched because its columns may
        # differ from the unified pipeline log.
        self.collection_log_path = self.logs_dir / "collection_log_v2.csv"
        self.source_health_path = self.logs_dir / "source_health.csv"

        self.news: list[dict[str, Any]] = load_json(self.news_path, [])
        self.crawl_state: dict[str, Any] = load_json(self.crawl_state_path, {})
        if not isinstance(self.crawl_state, dict):
            self.crawl_state = {}
        self.by_url = {
            canonicalize_url(item.get("url", "")): item
            for item in self.news
            if item.get("url")
        }
        self.reprocess_existing = reprocess_existing

        rules = self.settings.get("collection_rules", {})
        self.timeout = int(rules.get("request_timeout_seconds", 20))
        self.delay = float(rules.get("delay_between_requests_seconds", 2))
        self.maximum_per_source = int(rules.get("maximum_articles_per_source_per_run", 100))
        self.respect_robots = bool(rules.get("respect_robots_txt", True))
        self.headers = {
            "User-Agent": DEFAULT_USER_AGENT,
            "Accept-Language": "ar,fr;q=0.9,en;q=0.7",
        }
        self.run_at = iso_now()

        self.discovery_political_aliases = self._build_political_aliases()
        self.discovery_geo_aliases = self._build_geo_aliases()

    def _build_political_aliases(self) -> list[str]:
        aliases: list[str] = []
        for party in self.parties:
            aliases.extend(party.get("strong_aliases", []))
            aliases.extend(party.get("acronyms", []))
        for topic in self.topics:
            aliases.extend(topic.get("keywords", []))
        for person in self.persons:
            aliases.append(person.get("canonical_name", ""))
            aliases.extend(person.get("aliases", []))
        aliases.extend(
            [
                "حزب",
                "سياسة",
                "سياسي",
                "انتخاب",
                "انتخابات",
                "اقتراع",
                "ترشح",
                "تزكية",
                "استقالة",
                "مجلس جماعي",
                "مجلس إقليمي",
                "conseil communal",
                "élection",
                "parti",
                "candidat",
            ]
        )
        return [alias for alias in aliases if compact_text(alias)]

    def _build_geo_aliases(self) -> list[str]:
        aliases: list[str] = []
        region = self.geography.get("region", {})
        aliases.extend(region.get("aliases", []))
        aliases.extend([region.get("name_ar", ""), region.get("name_fr", "")])
        for province in self.geography.get("provinces", []):
            aliases.extend(province.get("aliases", []))
            aliases.extend([province.get("name_ar", ""), province.get("name_fr", "")])
            for place in province.get("places", []):
                aliases.extend(place.get("aliases", []))
                aliases.extend(
                    [
                        place.get("name_ar", ""),
                        place.get("name_fr", ""),
                        place.get("name", ""),
                    ]
                )
        return [alias for alias in aliases if compact_text(alias)]

    def inspect_robots(
        self, session: requests.Session, source: dict[str, Any]
    ) -> tuple[urllib.robotparser.RobotFileParser | None, int | str]:
        if not self.respect_robots:
            return None, "disabled"
        robots_url = urljoin(source["base_url"], "/robots.txt")
        try:
            response = session.get(robots_url, headers=self.headers, timeout=self.timeout)
            if response.status_code == 404:
                return None, 404
            if response.status_code != 200:
                return None, response.status_code
            parser = urllib.robotparser.RobotFileParser()
            parser.parse(response.text.splitlines())
            return parser, 200
        except Exception:
            return None, "error"

    def allowed_by_robots(
        self,
        parser: urllib.robotparser.RobotFileParser | None,
        robots_status: int | str,
        url: str,
    ) -> bool:
        if not self.respect_robots or robots_status in {404, "disabled"}:
            return True
        if parser is None:
            return False
        return parser.can_fetch(DEFAULT_USER_AGENT, url)

    @staticmethod
    def extract_link_title(tag: Any) -> str:
        candidates = [
            tag.get_text(" ", strip=True),
            tag.get("title", ""),
            tag.get("aria-label", ""),
        ]
        image = tag.find("img")
        if image:
            candidates.extend([image.get("alt", ""), image.get("title", "")])
        candidates = [compact_text(value) for value in candidates if compact_text(value)]
        return max(candidates, key=len, default="")

    def title_is_potentially_relevant(self, title: str, source: dict[str, Any]) -> bool:
        start_text = " ".join(
            source.get(
                "start_urls",
                source.get("section_urls", []),
            )
        )

        political_section = any(
            marker in normalize_text(start_text)
            for marker in (
                "politique",
                "سياس",
                "انتخاب",
                "agadir-politique",
            )
        )

        political = any(
            contains_alias(title, alias)
            for alias in self.discovery_political_aliases
        )

        geographic = any(
            contains_alias(title, alias)
            for alias in self.discovery_geo_aliases
        )

        # في المصادر الوطنية يجب أن يحمل العنوان
        # إشارة سياسية أو جغرافية قبل فتح المقال.
        if source.get("scope") == "national":
            return political or geographic

        # المصادر المحلية ذات القسم السياسي
        # يمكن قبول عناوينها مبدئياً.
        if political_section:
            return True

        if political:
            return True

        council_signal = any(
            contains_alias(title, term)
            for term in (
                "مجلس",
                "جماعة",
                "منتخب",
                "رئيس",
                "استقال",
                "تصويت",
                "conseil",
                "commune",
                "élu",
                "président",
                "démission",
                "vote",
            )
        )

        return geographic and council_signal

    def discover_links(
        self,
        html_text: str,
        page_url: str,
        source: dict[str, Any],
    ) -> list[dict[str, str]]:

        soup = BeautifulSoup(
            html_text,
            "lxml",
        )

        allowed_domains = {
            clean_domain(
                value
                if "://" in value
                else "https://" + value
            )
            for value in source.get(
                "allowed_domains",
                [],
            )
            if value
        }

        if not allowed_domains:
            allowed_domains = {
                clean_domain(
                    source["base_url"]
                )
            }

        prefixes = [
            normalize_text(value)
            for value in source.get(
                "article_path_prefixes",
                [],
            )
        ]

        start_urls = {
            canonicalize_url(value)
            for value in source.get(
                "start_urls",
                source.get(
                    "section_urls",
                    [],
                ),
            )
        }

        selectors = (
            "article h1 a[href], "
            "article h2 a[href], "
            "article h3 a[href], "
            "article a[href], "
            ".post h2 a[href], "
            ".post h3 a[href], "
            ".entry-title a[href], "
            ".td-module-title a[href], "
            ".jeg_post_title a[href], "
            "h2 a[href], "
            "h3 a[href]"
        )

        tags = soup.select(selectors)

        if len(tags) < 5:
            tags.extend(
                soup.select("a[href]")
            )

        output: list[dict[str, str]] = []
        seen: set[str] = set()

        for tag in tags:

            href = tag.get("href", "")

            url = canonicalize_url(
                urljoin(page_url, href)
            )

            parsed = urlparse(url)
            path = normalize_text(parsed.path)

            if clean_domain(url) not in allowed_domains:
                continue

            if url in start_urls or url in seen:
                continue

            if parsed.path.lower().endswith(
                EXCLUDED_EXTENSIONS
            ):
                continue

            if any(
                part in parsed.path.lower()
                for part in EXCLUDED_PATH_PARTS
            ):
                continue

            if (
                prefixes
                and not any(
                    path.startswith(prefix)
                    for prefix in prefixes
                )
            ):
                continue

            title = self.extract_link_title(tag)

            if (
                len(title) < 18
                or not self.title_is_potentially_relevant(
                    title,
                    source,
                )
            ):
                continue

            seen.add(url)

            output.append(
                {
                    "title": title,
                    "url": url,
                }
            )

        # Do not truncate here. The per-source limit must be applied only after
        # already inspected URLs are removed; otherwise the monitor can keep
        # revisiting the same first links and never reach newer links below.
        return output

    def fallback_extract(self, html_text: str, url: str) -> dict[str, Any] | None:
        soup = BeautifulSoup(html_text, "lxml")
        title = ""
        title_meta = soup.select_one('meta[property="og:title"], meta[name="twitter:title"]')
        if title_meta:
            title = compact_text(title_meta.get("content"))
        if not title:
            heading = soup.select_one("article h1, main h1, h1")
            title = compact_text(heading.get_text(" ", strip=True) if heading else "")
        paragraphs = soup.select("article p") or soup.select("main p")
        text = "\n".join(
            compact_text(paragraph.get_text(" ", strip=True))
            for paragraph in paragraphs
            if len(compact_text(paragraph.get_text(" ", strip=True))) >= 30
        )
        if len(text.split()) < 80:
            return None
        published = None
        date_meta = soup.select_one(
            'meta[property="article:published_time"], meta[name="date"], time[datetime]'
        )
        if date_meta:
            published = date_meta.get("content") or date_meta.get("datetime")
        author = None
        author_meta = soup.select_one('meta[name="author"], [rel="author"]')
        if author_meta:
            author = author_meta.get("content") or author_meta.get_text(" ", strip=True)
        return {
            "title": title,
            "text": text,
            "date": published,
            "author": compact_text(author),
            "url": url,
        }

    def extract_article(
        self,
        session: requests.Session,
        article: dict[str, str],
        source: dict[str, Any],
        parser: urllib.robotparser.RobotFileParser | None,
        robots_status: int | str,
    ) -> tuple[dict[str, Any] | None, str | None]:
        url = canonicalize_url(article["url"])
        if not self.allowed_by_robots(parser, robots_status, url):
            return None, "robots_disallowed"
        try:
            response = session.get(
                url,
                headers=self.headers,
                timeout=self.timeout,
                allow_redirects=True,
            )
        except Exception as error:
            return None, f"request_error:{type(error).__name__}"
        if response.status_code != 200:
            return None, f"http_{response.status_code}"
        final_url = canonicalize_url(response.url)
        try:
            extracted = trafilatura.extract(
                response.text,
                output_format="json",
                with_metadata=True,
                include_comments=False,
                include_tables=False,
                favor_precision=True,
            )
            data = json.loads(extracted) if extracted else None
        except Exception:
            data = None
        if not data or len(compact_text(data.get("text")).split()) < 80:
            data = self.fallback_extract(response.text, final_url)
        if not data:
            return None, "extraction_failed"
        text = compact_text(data.get("text"))
        title = compact_text(data.get("title") or article.get("title"))
        if not title or len(text.split()) < 80:
            return None, "insufficient_content"
        return (
            {
                "source_id": source["id"],
                "source_name": source["name"],
                "title": title,
                "url": final_url,
                "author": compact_text(data.get("author")) or None,
                "published_at": parse_date(data.get("date")),
                "language": detect_language(f"{title} {text[:1500]}"),
                "full_text": text,
                "word_count": len(text.split()),
            },
            None,
        )

    @staticmethod
    def weighted_alias_score(title: str, lead: str, body: str, aliases: Iterable[str]) -> tuple[int, list[str]]:
        score = 0
        hits: list[str] = []
        seen: set[str] = set()
        for alias in aliases:
            alias = compact_text(alias)
            key = normalize_text(alias)
            if not alias or len(key) < 2 or key in seen:
                continue
            weight = 0
            if contains_alias(title, alias):
                weight = 3
            elif contains_alias(lead, alias):
                weight = 2
            elif contains_alias(body, alias):
                weight = 1
            if weight:
                seen.add(key)
                score += weight
                hits.append(alias)
        return score, hits

    def classify_geography(self, title: str, text: str) -> dict[str, Any]:
        words = text.split()
        lead = " ".join(words[:90])
        body = " ".join(words[90:])
        province_results: list[dict[str, Any]] = []
        place_results: list[dict[str, Any]] = []
        for province in self.geography.get("provinces", []):
            aliases = province.get("aliases", []) + [
                province.get("name_ar", ""),
                province.get("name_fr", ""),
            ]
            province_score, province_hits = self.weighted_alias_score(title, lead, body, aliases)
            best_place_score = 0
            for place in province.get("places", []):
                place_name = (
                    place.get("name_ar")
                    or place.get("name")
                    or place.get("name_fr")
                    or ""
                )
                place_aliases = place.get("aliases", []) + [
                    place.get("name_ar", ""),
                    place.get("name_fr", ""),
                    place.get("name", ""),
                ]
                place_score, place_hits = self.weighted_alias_score(
                    title, lead, body, place_aliases
                )
                if place_score:
                    place_results.append(
                        {
                            "name": place_name,
                            "province": province.get("name_ar"),
                            "score": place_score,
                            "hits": place_hits,
                        }
                    )
                    best_place_score = max(best_place_score, place_score)
            combined = province_score + (1 if best_place_score else 0)
            if combined:
                province_results.append(
                    {
                        "name": province.get("name_ar"),
                        "score": combined,
                        "hits": province_hits,
                    }
                )

        province_results.sort(key=lambda item: (-item["score"], item["name"] or ""))
        place_results.sort(key=lambda item: (-item["score"], item["name"] or ""))
        primary_provinces: list[str] = []
        secondary_provinces: list[str] = []
        if province_results:
            highest = province_results[0]["score"]
            primary_provinces = [
                item["name"] for item in province_results if item["score"] == highest
            ][:2]
            secondary_provinces = [
                item["name"]
                for item in province_results
                if item["name"] not in primary_provinces
            ][:4]
        primary_places: list[str] = []
        secondary_places: list[str] = []
        if place_results:
            eligible = [
                item for item in place_results if item["province"] in primary_provinces
            ] or place_results
            highest_place = eligible[0]["score"]
            primary_places = [
                item["name"] for item in eligible if item["score"] == highest_place
            ][:2]
            secondary_places = [
                item["name"]
                for item in place_results
                if item["name"] not in primary_places
            ][:5]

        region = self.geography.get("region", {})
        region_aliases = region.get("aliases", []) + [
            region.get("name_ar", ""),
            region.get("name_fr", ""),
        ]
        region_hit = bool(matched_aliases(f"{title} {lead} {body}", region_aliases))
        return {
            "region": region.get("name_ar") if (province_results or place_results or region_hit) else None,
            "primary_provinces": primary_provinces,
            "primary_places": primary_places,
            "secondary_provinces": secondary_provinces,
            "secondary_places": secondary_places,
        }

    def classify_parties(self, title: str, text: str) -> dict[str, list[dict[str, str]]]:
        words = text.split()
        lead = " ".join(words[:90])
        body = " ".join(words[90:])
        political_context = any(
            contains_alias(f"{title} {lead}", term)
            for term in ("حزب", "انتخاب", "سياس", "مرشح", "مجلس", "parti", "élection")
        )
        results: list[dict[str, Any]] = []
        for party in self.parties:
            strong = (
                party.get("strong_aliases", [])
                + party.get("acronyms", [])
                + [party.get("name_ar", ""), party.get("name_fr", "")]
            )
            score, hits = self.weighted_alias_score(title, lead, body, strong)
            if political_context:
                context_score, context_hits = self.weighted_alias_score(
                    title, lead, body, party.get("context_aliases", [])
                )
                score += context_score
                hits.extend(context_hits)
            if score:
                results.append(
                    {
                        "id": party.get("id"),
                        "name": party.get("name_ar"),
                        "score": score,
                        "hits": list(dict.fromkeys(hits)),
                    }
                )
        results.sort(key=lambda item: (-item["score"], item["name"] or ""))
        return {
            "primary": [
                {"id": item["id"], "name": item["name"]}
                for item in results
                if item["score"] >= 2
            ],
            "secondary": [
                {"id": item["id"], "name": item["name"]}
                for item in results
                if item["score"] == 1
            ],
        }

    def classify_persons(self, title: str, text: str) -> dict[str, list[dict[str, str]]]:
        words = text.split()
        lead = " ".join(words[:90])
        body = " ".join(words[90:])
        results: list[dict[str, Any]] = []
        for person in self.persons:
            aliases = person.get("aliases", []) + [person.get("canonical_name", "")]
            score, hits = self.weighted_alias_score(title, lead, body, aliases)
            if score:
                results.append(
                    {
                        "id": person.get("id"),
                        "name": person.get("canonical_name"),
                        "tier": person.get("tier", "secondary"),
                        "score": score,
                        "hits": hits,
                    }
                )
        results.sort(
            key=lambda item: (
                -item["score"],
                0 if item["tier"] == "priority" else 1,
                item["name"] or "",
            )
        )
        return {
            "primary": [
                {"id": item["id"], "name": item["name"], "tier": item["tier"]}
                for item in results
                if item["score"] >= 2
            ],
            "secondary": [
                {"id": item["id"], "name": item["name"], "tier": item["tier"]}
                for item in results
                if item["score"] == 1
            ],
        }

    def classify_topics(self, title: str, text: str) -> dict[str, list[dict[str, Any]]]:
        words = text.split()
        lead = " ".join(words[:90])
        body = " ".join(words[90:])
        results: list[dict[str, Any]] = []
        for topic in self.topics:
            title_hits = matched_aliases(title, topic.get("keywords", []))
            lead_hits = matched_aliases(lead, topic.get("keywords", []))
            body_hits = matched_aliases(body, topic.get("keywords", []))
            hits = list(dict.fromkeys(title_hits + lead_hits + body_hits))
            score = len(title_hits) * 3 + len(lead_hits) * 2 + len(body_hits)
            if score:
                results.append(
                    {
                        "id": topic.get("id"),
                        "name": topic.get("name_ar"),
                        "score": score,
                        "hits": hits[:5],
                        "priority": topic.get("priority", 99),
                    }
                )
        results.sort(key=lambda item: (-item["score"], item["priority"]))
        return {
            "primary": [
                {"id": item["id"], "name": item["name"], "hits": item["hits"]}
                for item in results
                if item["score"] >= 3
            ],
            "secondary": [
                {"id": item["id"], "name": item["name"], "hits": item["hits"]}
                for item in results
                if 0 < item["score"] < 3
            ],
        }

    def evaluate_relevance(
        self,
        geography: dict[str, Any],
        parties: dict[str, Any],
        persons: dict[str, Any],
        topics: dict[str, Any],
    ) -> dict[str, Any]:
        geographic_score = 0
        geographic_reasons: list[str] = []
        if geography.get("primary_provinces"):
            geographic_score += 3
            geographic_reasons.append("إقليم رئيسي داخل سوس ماسة")
        if geography.get("primary_places"):
            geographic_score += 1
            geographic_reasons.append("مدينة أو مكان رئيسي داخل سوس ماسة")
        if not geographic_score and geography.get("region"):
            geographic_score = 2
            geographic_reasons.append("ذكر جهة سوس ماسة")

        political_score = 0
        political_reasons: list[str] = []
        if parties.get("primary"):
            political_score += 2
            political_reasons.append(
                "أحزاب رئيسية: " + ", ".join(item["name"] for item in parties["primary"][:4])
            )
        if persons.get("primary"):
            political_score += 1
            political_reasons.append(
                "شخصيات رئيسية: " + ", ".join(item["name"] for item in persons["primary"][:4])
            )
        primary_topics = topics.get("primary", [])
        if primary_topics:
            political_score += min(3, len(primary_topics) + 1)
            political_reasons.append(
                "مواضيع سياسية: " + ", ".join(item["name"] for item in primary_topics[:4])
            )
        if any(
            item.get("id") in {"elections", "candidacy_nomination", "party_activity"}
            for item in primary_topics
        ):
            political_score += 1

        accepted = geographic_score >= 2 and political_score >= 2
        if accepted and geographic_score >= 3 and political_score >= 4:
            level = "strong"
            reason = "صلة جغرافية وسياسية قوية"
        elif accepted:
            level = "medium"
            reason = "صلة جغرافية وسياسية مقبولة"
        elif geographic_score < 2:
            level = "excluded"
            reason = "لا توجد صلة كافية بسوس ماسة"
        else:
            level = "excluded"
            reason = "لا توجد إشارة سياسية كافية"
        return {
            "level": level,
            "geographic_score": geographic_score,
            "political_score": political_score,
            "decision_reason": reason,
            "geographic_reasons": geographic_reasons,
            "political_reasons": political_reasons,
            "accepted": accepted,
        }

    def target_alias_map(
        self, parties: dict[str, Any], persons: dict[str, Any]
    ) -> list[dict[str, Any]]:
        targets: list[dict[str, Any]] = []
        party_by_id = {party.get("id"): party for party in self.parties}
        person_by_id = {person.get("id"): person for person in self.persons}
        for entity in parties.get("primary", []) + parties.get("secondary", []):
            party = party_by_id.get(entity.get("id"), {})
            targets.append(
                {
                    "id": entity.get("id"),
                    "type": "party",
                    "name": entity.get("name"),
                    "aliases": party.get("strong_aliases", [])
                    + party.get("acronyms", [])
                    + [party.get("name_ar", ""), party.get("name_fr", "")],
                }
            )
        for entity in persons.get("primary", []) + persons.get("secondary", []):
            person = person_by_id.get(entity.get("id"), {})
            targets.append(
                {
                    "id": entity.get("id"),
                    "type": "person",
                    "name": entity.get("name"),
                    "aliases": person.get("aliases", []) + [person.get("canonical_name", "")],
                }
            )
        unique: dict[tuple[str, str], dict[str, Any]] = {}
        for target in targets:
            if target.get("id"):
                unique[(target["type"], target["id"])] = target
        return list(unique.values())

    def analyze_stances(
        self,
        title: str,
        text: str,
        parties: dict[str, Any],
        persons: dict[str, Any],
    ) -> list[dict[str, Any]]:
        positive_terms = self.stance_rules.get("positive_terms", [])
        negative_terms = self.stance_rules.get("negative_terms", [])
        reporting_terms = self.stance_rules.get("reporting_terms", [])
        event_terms = self.stance_rules.get("event_terms_not_editorial_stance", [])
        labels = self.stance_rules.get("labels", {})
        scoring = self.stance_rules.get("scoring", {})
        clear_minimum = int(scoring.get("clear_stance_minimum_score", 2))
        mixed_minimum = int(scoring.get("mixed_minimum_each_side", 2))
        title_weight = int(scoring.get("title_weight", 3))
        lead_weight = int(scoring.get("lead_weight", 2))
        body_weight = int(scoring.get("body_weight", 1))

        sentences = sentence_split(text)
        lead_sentences = set(sentences[:3])
        output: list[dict[str, Any]] = []
        for target in self.target_alias_map(parties, persons):
            aliases = [alias for alias in target["aliases"] if compact_text(alias)]
            positive_score = 0
            negative_score = 0
            mention_count = 0
            editorial_segments = 0
            reported_segments = 0
            evidence: list[str] = []
            segments = [(title, title_weight, "title")]
            for sentence in sentences:
                weight = lead_weight if sentence in lead_sentences else body_weight
                segments.append((sentence, weight, "body"))

            for segment, weight, location in segments:
                if not any(contains_alias(segment, alias) for alias in aliases):
                    continue
                mention_count += 1
                positive_hits = matched_aliases(segment, positive_terms)
                negative_hits = matched_aliases(segment, negative_terms)
                event_hits = matched_aliases(segment, event_terms)
                negative_hits = [
                    hit
                    for hit in negative_hits
                    if normalize_text(hit) not in {normalize_text(term) for term in event_hits}
                ]
                reported = bool(matched_aliases(segment, reporting_terms))
                if location != "title" and any(mark in segment for mark in ("\"", "“", "”", "«", "»")):
                    reported = True
                if reported:
                    reported_segments += 1
                    continue
                editorial_segments += 1
                positive_score += len(positive_hits) * weight
                negative_score += len(negative_hits) * weight
                if (positive_hits or negative_hits) and len(evidence) < 3:
                    terms = list(dict.fromkeys(positive_hits + negative_hits))
                    evidence.extend(terms[: 3 - len(evidence)])

            if positive_score >= mixed_minimum and negative_score >= mixed_minimum:
                label = "mixed"
            elif positive_score >= clear_minimum and negative_score == 0:
                label = "favorable"
            elif negative_score >= clear_minimum and positive_score == 0:
                label = "critical"
            elif positive_score == 0 and negative_score == 0:
                label = "neutral"
            else:
                label = "unclear"

            strongest = max(positive_score, negative_score)
            if label in {"favorable", "critical", "mixed"} and strongest >= 6 and editorial_segments >= 2:
                confidence = "high"
            elif label in {"favorable", "critical", "mixed"} and strongest >= 2:
                confidence = "medium"
            elif label == "neutral" and (mention_count >= 2 or any(contains_alias(title, alias) for alias in aliases)):
                confidence = "medium"
            else:
                confidence = "low"

            output.append(
                {
                    "target_id": target["id"],
                    "target_type": target["type"],
                    "target_name": target["name"],
                    "label": label,
                    "label_ar": labels.get(label, label),
                    "confidence": confidence,
                    "positive_score": positive_score,
                    "negative_score": negative_score,
                    "mention_count": mention_count,
                    "editorial_segment_count": editorial_segments,
                    "reported_segment_count": reported_segments,
                    "evidence": evidence,
                }
            )
        return output

    def process_extracted(self, extracted: dict[str, Any]) -> dict[str, Any]:
        title = extracted["title"]
        text = extracted.pop("full_text")
        geography = self.classify_geography(title, text)
        parties = self.classify_parties(title, text)
        persons = self.classify_persons(title, text)
        topics = self.classify_topics(title, text)
        relevance = self.evaluate_relevance(geography, parties, persons, topics)
        stances = self.analyze_stances(title, text, parties, persons) if relevance["accepted"] else []
        article_id = stable_id("", canonicalize_url(extracted["url"]))
        return {
            "id": article_id,
            "source_id": extracted["source_id"],
            "source_name": extracted["source_name"],
            "title": title,
            "url": canonicalize_url(extracted["url"]),
            "author": extracted.get("author"),
            "published_at": extracted.get("published_at"),
            "first_seen_at": self.run_at,
            "last_checked_at": self.run_at,
            "language": extracted.get("language"),
            "excerpt": first_words(text, 25),
            "word_count": extracted.get("word_count", len(text.split())),
            "geography": geography,
            "parties": parties,
            "persons": persons,
            "topics": topics,
            "relevance": relevance,
            "stances": stances,
            "event_id": None,
            "stance_analyzed_at": self.run_at if relevance["accepted"] else None,
        }

    def collect_source(self, source: dict[str, Any]) -> dict[str, Any]:
        started = time.time()
        session = requests.Session()
        parser, robots_status = self.inspect_robots(session, source)
        start_urls = source.get("start_urls", source.get("section_urls", []))
        result: dict[str, Any] = {
            "source_id": source.get("id"),
            "source_name": source.get("name"),
            "robots_status": robots_status,
            "pages_opened": 0,
            "links_discovered": 0,
            "known_skipped": 0,
            "new_candidates": 0,
            "extraction_success": 0,
            "extraction_failed": 0,
            "accepted": 0,
            "excluded": 0,
            "articles": [],
            "crawl_updates": [],
            "errors": [],
        }
        try:
            discovered: list[dict[str, str]] = []
            seen: set[str] = set()
            for start_url in start_urls:
                if not self.allowed_by_robots(parser, robots_status, start_url):
                    result["errors"].append(f"robots_disallowed:{start_url}")
                    continue
                try:
                    response = session.get(
                        start_url,
                        headers=self.headers,
                        timeout=self.timeout,
                        allow_redirects=True,
                    )
                except Exception as error:
                    result["errors"].append(f"start_request:{type(error).__name__}")
                    continue
                if response.status_code != 200:
                    result["errors"].append(f"start_http_{response.status_code}:{start_url}")
                    continue
                result["pages_opened"] += 1
                for item in self.discover_links(response.text, response.url, source):
                    canonical = canonicalize_url(item["url"])
                    if canonical not in seen:
                        seen.add(canonical)
                        discovered.append({"title": item["title"], "url": canonical})
            result["links_discovered"] = len(discovered)

            candidates: list[dict[str, str]] = []
            for article in discovered:
                canonical = canonicalize_url(article["url"])
                existing = self.by_url.get(canonical)
                inspected = canonical in self.crawl_state
                if (existing or inspected) and not self.reprocess_existing:
                    result["known_skipped"] += 1
                    continue
                candidates.append(article)

            result["new_candidates"] = len(candidates)

            # The configured limit applies to genuinely new candidates, not to
            # the complete page that is mostly made of already known links.
            for article in candidates[: self.maximum_per_source]:
                canonical = canonicalize_url(article["url"])
                extracted, error = self.extract_article(
                    session, article, source, parser, robots_status
                )
                if not extracted:
                    result["extraction_failed"] += 1
                    if error:
                        result["errors"].append(f"{error}:{canonical}")
                    continue
                result["extraction_success"] += 1
                processed = self.process_extracted(extracted)
                if processed["relevance"]["accepted"]:
                    result["accepted"] += 1
                    result["articles"].append(processed)
                    crawl_status = "accepted"
                else:
                    result["excluded"] += 1
                    crawl_status = "excluded"
                result["crawl_updates"].append(
                    {
                        "url": canonical,
                        "source_id": source.get("id"),
                        "source_name": source.get("name"),
                        "title": processed.get("title") or article.get("title"),
                        "status": crawl_status,
                        "checked_at": self.run_at,
                    }
                )
                if self.delay > 0:
                    time.sleep(self.delay)
        finally:
            session.close()
            result["elapsed_seconds"] = round(time.time() - started, 2)
        return result

    @staticmethod
    def entity_ids(article: dict[str, Any], field: str) -> set[str]:
        container = article.get(field, {})
        items = container.get("primary", []) + container.get("secondary", [])
        return {str(item.get("id")) for item in items if item.get("id")}

    @staticmethod
    def province_names(article: dict[str, Any]) -> set[str]:
        geography = article.get("geography", {})
        return set(geography.get("primary_provinces", []) + geography.get("secondary_provinces", []))

    @staticmethod
    def article_date(article: dict[str, Any]) -> datetime | None:
        raw = article.get("published_at") or article.get("first_seen_at")
        if not raw:
            return None
        try:
            return datetime.fromisoformat(str(raw).replace("Z", "+00:00"))
        except ValueError:
            return None

    def same_event(self, left: dict[str, Any], right: dict[str, Any]) -> bool:
        left_title = normalize_text(left.get("title"))
        right_title = normalize_text(right.get("title"))
        similarity = fuzzy_ratio(left_title, right_title)
        if similarity < 72:
            return False
        left_date = self.article_date(left)
        right_date = self.article_date(right)
        if left_date and right_date:
            if left_date.tzinfo is None:
                left_date = left_date.replace(tzinfo=timezone.utc)
            if right_date.tzinfo is None:
                right_date = right_date.replace(tzinfo=timezone.utc)
            if abs((left_date - right_date).days) > 7:
                return False
        shared_geo = bool(self.province_names(left) & self.province_names(right))
        shared_party = bool(self.entity_ids(left, "parties") & self.entity_ids(right, "parties"))
        shared_person = bool(self.entity_ids(left, "persons") & self.entity_ids(right, "persons"))
        shared_topic = bool(self.entity_ids(left, "topics") & self.entity_ids(right, "topics"))
        if similarity >= 90 and shared_geo:
            return True
        return similarity >= 78 and shared_geo and (shared_party or shared_person or shared_topic)

    def assign_events(self) -> None:
        ordered = sorted(
            self.news,
            key=lambda article: article.get("published_at") or article.get("first_seen_at") or "",
        )
        representatives: list[dict[str, Any]] = []
        for article in ordered:
            chosen_event = None
            for representative in reversed(representatives[-250:]):
                if self.same_event(article, representative):
                    chosen_event = representative.get("event_id")
                    break
            if not chosen_event:
                chosen_event = stable_id("evt_", article.get("url") or article.get("title", ""), 12)
                article["event_id"] = chosen_event
                representatives.append(article)
            else:
                article["event_id"] = chosen_event

    def merge_articles(self, source_results: list[dict[str, Any]]) -> tuple[int, int]:
        new_count = 0
        updated_count = 0
        index = {canonicalize_url(item.get("url", "")): pos for pos, item in enumerate(self.news)}
        for source_result in source_results:
            for article in source_result.get("articles", []):
                key = canonicalize_url(article["url"])
                if key in index:
                    existing = self.news[index[key]]
                    first_seen = existing.get("first_seen_at") or article["first_seen_at"]
                    event_id = existing.get("event_id")
                    existing.update(article)
                    existing["first_seen_at"] = first_seen
                    existing["event_id"] = event_id
                    updated_count += 1
                else:
                    index[key] = len(self.news)
                    self.news.append(article)
                    self.by_url[key] = article
                    new_count += 1
        self.news.sort(
            key=lambda item: item.get("published_at") or item.get("first_seen_at") or "",
            reverse=True,
        )
        return new_count, updated_count

    def save_csv(self) -> None:
        rows: list[dict[str, Any]] = []
        nested_fields = {"geography", "parties", "persons", "topics", "relevance", "stances"}
        for article in self.news:
            row: dict[str, Any] = {}
            for key, value in article.items():
                row[key] = (
                    json.dumps(value, ensure_ascii=False)
                    if key in nested_fields
                    else value
                )
            rows.append(row)
        pd.DataFrame(rows).to_csv(self.csv_path, index=False, encoding="utf-8-sig")

    @staticmethod
    def append_csv(path: Path, row: dict[str, Any]) -> None:
        path.parent.mkdir(parents=True, exist_ok=True)
        exists = path.exists() and path.stat().st_size > 0
        with path.open("a", encoding="utf-8-sig", newline="") as handle:
            writer = csv.DictWriter(handle, fieldnames=list(row.keys()))
            if not exists:
                writer.writeheader()
            writer.writerow(row)

    def save_logs(
        self,
        source_results: list[dict[str, Any]],
        new_count: int,
        updated_count: int,
    ) -> None:
        total_links = sum(item.get("links_discovered", 0) for item in source_results)
        known_skipped = sum(item.get("known_skipped", 0) for item in source_results)
        new_candidates = sum(item.get("new_candidates", 0) for item in source_results)
        extraction_success = sum(item.get("extraction_success", 0) for item in source_results)
        extraction_failed = sum(item.get("extraction_failed", 0) for item in source_results)
        excluded = sum(item.get("excluded", 0) for item in source_results)
        errors = sum(len(item.get("errors", [])) for item in source_results)
        self.append_csv(
            self.collection_log_path,
            {
                "run_at": self.run_at,
                "version": APP_VERSION,
                "sources": len(source_results),
                "links_discovered": total_links,
                "known_skipped": known_skipped,
                "new_candidates": new_candidates,
                "extraction_success": extraction_success,
                "extraction_failed": extraction_failed,
                "new_articles": new_count,
                "updated_articles": updated_count,
                "excluded_articles": excluded,
                "total_saved": len(self.news),
                "errors": errors,
            },
        )
        for item in source_results:
            self.append_csv(
                self.source_health_path,
                {
                    "run_at": self.run_at,
                    "source_id": item.get("source_id"),
                    "source_name": item.get("source_name"),
                    "robots_status": item.get("robots_status"),
                    "pages_opened": item.get("pages_opened", 0),
                    "links_discovered": item.get("links_discovered", 0),
                    "known_skipped": item.get("known_skipped", 0),
                    "new_candidates": item.get("new_candidates", 0),
                    "extraction_success": item.get("extraction_success", 0),
                    "extraction_failed": item.get("extraction_failed", 0),
                    "accepted": item.get("accepted", 0),
                    "excluded": item.get("excluded", 0),
                    "elapsed_seconds": item.get("elapsed_seconds"),
                    "errors": " | ".join(item.get("errors", [])[:5]),
                },
            )

    def generate_dashboard(self, run_status: dict[str, Any]) -> None:
        safe_json = json.dumps(self.news, ensure_ascii=False).replace("</", "<\\/")
        safe_status = json.dumps(run_status, ensure_ascii=False).replace("</", "<\\/")
        generated = html.escape(self.run_at)
        template_path = self.root / "templates" / "dashboard.html"
        template_source = (
            template_path.read_text(encoding="utf-8")
            if template_path.exists()
            else DASHBOARD_TEMPLATE
        )
        template = (
            template_source.replace("__NEWS_JSON__", safe_json)
            .replace("__RUN_STATUS_JSON__", safe_status)
            .replace("__GENERATED_AT__", generated)
        )
        atomic_write_text(self.html_path, template)

    def run(self) -> dict[str, Any]:
        if not self.sources:
            raise RuntimeError("No enabled sources were found in the source configuration.")
        print(f"🚀 تشغيل SoussMassaMonitor {APP_VERSION}")
        print(f"• المصادر المفعلة: {len(self.sources)}")
        source_results: list[dict[str, Any]] = []
        max_workers = min(4, max(1, len(self.sources)))
        with ThreadPoolExecutor(max_workers=max_workers) as executor:
            futures = {
                executor.submit(self.collect_source, source): source
                for source in self.sources
            }
            for future in as_completed(futures):
                source = futures[future]
                try:
                    result = future.result()
                except Exception as error:
                    result = {
                        "source_id": source.get("id"),
                        "source_name": source.get("name"),
                        "links_discovered": 0,
                        "extraction_success": 0,
                        "extraction_failed": 0,
                        "accepted": 0,
                        "excluded": 0,
                        "articles": [],
                        "errors": [f"fatal:{type(error).__name__}:{error}"],
                    }
                source_results.append(result)
                symbol = "✅" if not result.get("errors") else "⚠️"
                print(
                    f"{symbol} {result.get('source_name')}: "
                    f"روابط {result.get('links_discovered', 0)} | "
                    f"جديد محتمل {result.get('extraction_success', 0)} | "
                    f"مقبول {result.get('accepted', 0)} | "
                    f"مستبعد {result.get('excluded', 0)}"
                )

        new_count, updated_count = self.merge_articles(source_results)
        self.assign_events()

        for result in source_results:
            for item in result.get("crawl_updates", []):
                canonical = canonicalize_url(item.get("url", ""))
                if canonical:
                    self.crawl_state[canonical] = {
                        key: value for key, value in item.items() if key != "url"
                    }

        summary = {
            "run_at": self.run_at,
            "sources": len(source_results),
            "links_discovered": sum(item.get("links_discovered", 0) for item in source_results),
            "known_skipped": sum(item.get("known_skipped", 0) for item in source_results),
            "new_candidates": sum(item.get("new_candidates", 0) for item in source_results),
            "extraction_success": sum(item.get("extraction_success", 0) for item in source_results),
            "extraction_failed": sum(item.get("extraction_failed", 0) for item in source_results),
            "new_articles": new_count,
            "updated_articles": updated_count,
            "excluded": sum(item.get("excluded", 0) for item in source_results),
            "total_saved": len(self.news),
            "events": len({item.get("event_id") for item in self.news if item.get("event_id")}),
            "errors": sum(len(item.get("errors", [])) for item in source_results),
            "source_details": [
                {
                    "source_name": item.get("source_name"),
                    "links_discovered": item.get("links_discovered", 0),
                    "known_skipped": item.get("known_skipped", 0),
                    "new_candidates": item.get("new_candidates", 0),
                    "extraction_success": item.get("extraction_success", 0),
                    "accepted": item.get("accepted", 0),
                    "excluded": item.get("excluded", 0),
                    "errors": len(item.get("errors", [])),
                }
                for item in sorted(
                    source_results,
                    key=lambda value: str(value.get("source_name", "")),
                )
            ],
        }

        atomic_write_json(self.news_path, self.news)
        atomic_write_json(self.crawl_state_path, self.crawl_state)
        atomic_write_json(self.run_status_path, summary)
        self.save_csv()
        self.generate_dashboard(summary)
        self.save_logs(source_results, new_count, updated_count)
        print("\n" + "=" * 72)
        print("✅ انتهى التشغيل الموحد")
        print(f"• الروابط المكتشفة: {summary['links_discovered']}")
        print(f"• الروابط المعروفة المتجاوزة: {summary['known_skipped']}")
        print(f"• الروابط الجديدة المرشحة: {summary['new_candidates']}")
        print(f"• نجح استخراجها: {summary['extraction_success']}")
        print(f"• فشل استخراجها: {summary['extraction_failed']}")
        print(f"• أخبار جديدة: {summary['new_articles']}")
        print(f"• أخبار محدثة: {summary['updated_articles']}")
        print(f"• مقالات مستبعدة: {summary['excluded']}")
        print(f"• إجمالي الأخبار: {summary['total_saved']}")
        print(f"• إجمالي الأحداث: {summary['events']}")
        print(f"• HTML: {self.html_path}")
        return summary


DASHBOARD_TEMPLATE = r'''<!doctype html>
<html lang="ar" dir="rtl">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width,initial-scale=1">
  <title>مرصد سوس ماسة السياسي</title>
  <style>
    :root{--bg:#f3f6fa;--card:#fff;--ink:#152033;--muted:#687386;--line:#dfe5ee;--brand:#165d73;--brand2:#d99c30;--good:#137a55;--bad:#b23a48;--neutral:#667085;--mixed:#7c3aed}
    *{box-sizing:border-box}body{margin:0;background:var(--bg);color:var(--ink);font-family:Tahoma,Arial,sans-serif;line-height:1.65}
    header{background:linear-gradient(125deg,#0d4052,#19728a);color:#fff;padding:24px 5vw}header h1{margin:0 0 4px;font-size:clamp(23px,4vw,38px)}header p{margin:0;opacity:.87}
    main{max-width:1450px;margin:auto;padding:20px}.stats{display:grid;grid-template-columns:repeat(5,minmax(120px,1fr));gap:12px;margin-bottom:16px}.stat,.panel,.article{background:var(--card);border:1px solid var(--line);border-radius:14px;box-shadow:0 5px 18px rgba(26,40,60,.05)}.stat{padding:14px}.stat strong{display:block;font-size:25px;color:var(--brand)}.stat span{font-size:13px;color:var(--muted)}
    .panel{padding:16px;margin-bottom:16px}.filters{display:grid;grid-template-columns:repeat(6,minmax(145px,1fr));gap:10px}.filters input,.filters select{width:100%;border:1px solid var(--line);border-radius:9px;padding:10px;background:#fff;color:var(--ink)}.filters input{grid-column:span 2}.actions{display:flex;gap:8px;align-items:center;margin-top:12px}.actions button{border:0;border-radius:9px;padding:9px 14px;cursor:pointer;background:var(--brand);color:#fff}.actions button.secondary{background:#e9eef4;color:var(--ink)}#resultCount{color:var(--muted);margin-inline-start:auto}
    .trend-wrap{overflow:auto}.trend{width:100%;border-collapse:collapse;min-width:720px}.trend th,.trend td{padding:9px;border-bottom:1px solid var(--line);text-align:right}.trend th{background:#f8fafc}.note{color:var(--muted);font-size:13px}
    .articles{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:14px}.article{padding:17px}.article h2{font-size:18px;line-height:1.5;margin:0 0 8px}.article h2 a{color:var(--ink);text-decoration:none}.article h2 a:hover{color:var(--brand)}.meta{display:flex;gap:9px;flex-wrap:wrap;color:var(--muted);font-size:12px;margin-bottom:9px}.excerpt{margin:8px 0 11px;color:#344054}.tags,.stances{display:flex;gap:6px;flex-wrap:wrap;margin-top:8px}.tag,.stance{display:inline-flex;border-radius:99px;padding:3px 9px;font-size:12px;background:#edf2f7}.stance.favorable{background:#dcfce7;color:#11603f}.stance.critical{background:#fee2e2;color:#912c38}.stance.neutral{background:#eef2f6;color:#4b5563}.stance.mixed{background:#ede9fe;color:#6d28d9}.stance.unclear{background:#fff4d6;color:#845a00}.empty{text-align:center;padding:45px;color:var(--muted);background:#fff;border-radius:14px}.section-title{display:flex;justify-content:space-between;align-items:center;gap:10px}.section-title h2{margin:0 0 9px;font-size:19px}
    @media(max-width:1050px){.filters{grid-template-columns:repeat(3,1fr)}.stats{grid-template-columns:repeat(3,1fr)}}@media(max-width:720px){main{padding:12px}.articles{grid-template-columns:1fr}.filters{grid-template-columns:1fr 1fr}.filters input{grid-column:span 2}.stats{grid-template-columns:1fr 1fr}.actions{flex-wrap:wrap}#resultCount{width:100%;margin:0}}
  </style>
</head>
<body>
<header><h1>مرصد سوس ماسة السياسي</h1><p>رصد الصحافة المحلية والوطنية حول السياسة والانتخابات والأحزاب في جهة سوس ماسة</p></header>
<main>
  <section class="stats">
    <div class="stat"><strong id="statArticles">0</strong><span>الأخبار المعروضة</span></div>
    <div class="stat"><strong id="statSources">0</strong><span>المصادر</span></div>
    <div class="stat"><strong id="statEvents">0</strong><span>الأحداث</span></div>
    <div class="stat"><strong id="statFavorable">0</strong><span>اتجاهات داعمة</span></div>
    <div class="stat"><strong id="statCritical">0</strong><span>اتجاهات ناقدة</span></div>
  </section>
  <section class="panel">
    <div class="filters">
      <input id="search" type="search" placeholder="ابحث في العنوان والمقتطف والشخصيات...">
      <select id="source"><option value="">كل المصادر</option></select>
      <select id="province"><option value="">كل الأقاليم</option></select>
      <select id="party"><option value="">كل الأحزاب</option></select>
      <select id="topic"><option value="">كل المواضيع</option></select>
      <select id="target"><option value="">كل أهداف التغطية</option></select>
      <select id="stance"><option value="">كل الاتجاهات</option><option value="favorable">إيجابي أو داعم</option><option value="critical">ناقد أو سلبي</option><option value="neutral">محايد أو إخباري</option><option value="mixed">مختلط</option><option value="unclear">غير واضح</option></select>
      <select id="confidence"><option value="">كل درجات الثقة</option><option value="high">مرتفعة</option><option value="medium">متوسطة</option><option value="low">منخفضة</option></select>
      <select id="language"><option value="">كل اللغات</option><option value="ar">العربية</option><option value="fr">الفرنسية</option><option value="mixed">مختلطة</option></select>
      <select id="period"><option value="all">كل المدة</option><option value="1h">آخر ساعة</option><option value="24h">آخر 24 ساعة</option><option value="3d">آخر 3 أيام</option><option value="7d">آخر أسبوع</option><option value="30d">آخر شهر</option></select>
    </div>
    <div class="actions"><button id="apply">تطبيق الفلاتر</button><button id="reset" class="secondary">مسح الفلاتر</button><span id="resultCount"></span></div>
  </section>
  <section class="panel">
    <div class="section-title"><h2>اتجاه التغطية حسب المصدر والهدف</h2></div>
    <p class="note">لا يظهر استنتاج عن الخط التحريري إلا بعد 5 مقالات على الأقل للهدف نفسه، وتُستبعد النتائج منخفضة الثقة.</p>
    <div id="trendContainer" class="trend-wrap"></div>
  </section>
  <section id="articles" class="articles"></section>
  <p class="note">آخر تحديث: __GENERATED_AT__</p>
</main>
<script id="newsData" type="application/json">__NEWS_JSON__</script>
<script>
const NEWS=JSON.parse(document.getElementById('newsData').textContent||'[]');
const $=id=>document.getElementById(id);const esc=v=>String(v??'').replace(/[&<>'"]/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;',"'":'&#39;','"':'&quot;'}[c]));
const allEntities=(a,key)=>[...((a[key]||{}).primary||[]),...((a[key]||{}).secondary||[])];
const uniq=arr=>[...new Set(arr.filter(Boolean))].sort((a,b)=>String(a).localeCompare(String(b),'ar'));
function fill(id,values){const el=$(id);values.forEach(v=>{const o=document.createElement('option');o.value=v;o.textContent=v;el.appendChild(o)})}
fill('source',uniq(NEWS.map(a=>a.source_name)));fill('province',uniq(NEWS.flatMap(a=>(a.geography||{}).primary_provinces||[])));fill('party',uniq(NEWS.flatMap(a=>allEntities(a,'parties').map(x=>x.name))));fill('topic',uniq(NEWS.flatMap(a=>allEntities(a,'topics').map(x=>x.name))));fill('target',uniq(NEWS.flatMap(a=>(a.stances||[]).map(x=>x.target_name))));
function articleDate(a){const raw=a.published_at||a.first_seen_at;if(!raw)return null;const d=new Date(raw.length===10?raw+'T00:00:00':raw);return isNaN(d)?null:d}
function inPeriod(a,p){if(p==='all')return true;const d=articleDate(a);if(!d)return false;const map={"1h":1/24,"24h":1,"3d":3,"7d":7,"30d":30};return (Date.now()-d.getTime())<=map[p]*86400000}
function filtered(){const q=$('search').value.trim().toLowerCase(),src=$('source').value,prov=$('province').value,party=$('party').value,topic=$('topic').value,target=$('target').value,stance=$('stance').value,conf=$('confidence').value,lang=$('language').value,period=$('period').value;return NEWS.filter(a=>{const parties=allEntities(a,'parties'),topics=allEntities(a,'topics'),people=allEntities(a,'persons'),stances=a.stances||[];const hay=[a.title,a.excerpt,a.source_name,...parties.map(x=>x.name),...topics.map(x=>x.name),...people.map(x=>x.name)].join(' ').toLowerCase();return(!q||hay.includes(q))&&(!src||a.source_name===src)&&(!prov||((a.geography||{}).primary_provinces||[]).includes(prov))&&(!party||parties.some(x=>x.name===party))&&(!topic||topics.some(x=>x.name===topic))&&(!target||stances.some(x=>x.target_name===target))&&(!stance||stances.some(x=>x.label===stance))&&(!conf||stances.some(x=>x.confidence===conf))&&(!lang||a.language===lang)&&inPeriod(a,period)})}
function tags(a){const g=(a.geography||{}).primary_provinces||[],p=allEntities(a,'parties').map(x=>x.name),t=allEntities(a,'topics').slice(0,3).map(x=>x.name);return uniq([...g,...p,...t]).map(x=>`<span class="tag">${esc(x)}</span>`).join('')}
function stanceHtml(a){return(a.stances||[]).map(s=>`<span class="stance ${esc(s.label)}">${esc(s.target_name)}: ${esc(s.label_ar)} · ${esc(s.confidence)}</span>`).join('')}
function renderArticles(data){$('articles').innerHTML=data.length?data.map(a=>`<article class="article"><h2><a href="${esc(a.url)}" target="_blank" rel="noopener">${esc(a.title)}</a></h2><div class="meta"><span>${esc(a.source_name)}</span><span>${esc(a.published_at||'تاريخ غير محدد')}</span><span>حدث: ${esc(a.event_id||'—')}</span></div><p class="excerpt">${esc(a.excerpt||'')}</p><div class="tags">${tags(a)}</div><div class="stances">${stanceHtml(a)}</div></article>`).join(''):'<div class="empty">لا توجد نتائج مطابقة للفلاتر الحالية.</div>'}
function renderTrend(data){const groups={};data.forEach(a=>(a.stances||[]).forEach(s=>{if(s.confidence==='low'||s.label==='unclear')return;const k=a.source_name+'||'+s.target_name;if(!groups[k])groups[k]={source:a.source_name,target:s.target_name,total:0,favorable:0,critical:0,neutral:0,mixed:0};groups[k].total++;groups[k][s.label]=(groups[k][s.label]||0)+1}));const rows=Object.values(groups).filter(x=>x.total>=5).sort((a,b)=>b.total-a.total);$('trendContainer').innerHTML=rows.length?`<table class="trend"><thead><tr><th>المصدر</th><th>الهدف</th><th>المقالات</th><th>داعم</th><th>ناقد</th><th>محايد</th><th>مختلط</th></tr></thead><tbody>${rows.map(x=>`<tr><td>${esc(x.source)}</td><td>${esc(x.target)}</td><td>${x.total}</td><td>${x.favorable}</td><td>${x.critical}</td><td>${x.neutral}</td><td>${x.mixed}</td></tr>`).join('')}</tbody></table>`:'<p class="note">لا تتوفر بعد عينة من 5 مقالات موثوقة للمصدر والهدف نفسيهما.</p>'}
function render(){const data=filtered();$('resultCount').textContent=`${data.length} نتيجة`;$('statArticles').textContent=data.length;$('statSources').textContent=new Set(data.map(a=>a.source_id)).size;$('statEvents').textContent=new Set(data.map(a=>a.event_id).filter(Boolean)).size;$('statFavorable').textContent=data.reduce((n,a)=>n+(a.stances||[]).filter(s=>s.label==='favorable').length,0);$('statCritical').textContent=data.reduce((n,a)=>n+(a.stances||[]).filter(s=>s.label==='critical').length,0);renderTrend(data);renderArticles(data)}
$('apply').addEventListener('click',render);$('search').addEventListener('input',render);$('reset').addEventListener('click',()=>{document.querySelectorAll('.filters input,.filters select').forEach(el=>el.value=el.id==='period'?'all':'');render()});document.querySelectorAll('.filters select').forEach(el=>el.addEventListener('change',render));render();
</script>
</body></html>'''


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Run the Souss-Massa news monitor")
    parser.add_argument(
        "--root",
        type=Path,
        default=Path(os.environ.get("SOUSS_MONITOR_DIR", Path(__file__).resolve().parent)),
        help="Project root containing config/, data/, output/, and logs/",
    )
    parser.add_argument(
        "--reprocess-existing",
        action="store_true",
        help="Download and reclassify URLs that are already saved",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    try:
        monitor = Monitor(args.root.resolve(), args.reprocess_existing)
        monitor.run()
        return 0
    except Exception as error:
        print(f"❌ فشل التشغيل: {type(error).__name__}: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
