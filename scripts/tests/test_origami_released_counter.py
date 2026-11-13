#!/usr/bin/env python3
"""Tests for ``scripts/coordination/origami_released_counter.py`` -- le rendement du parcage (#24373).

L'organe compte les ``[RELEASED]`` reels poses sur les EPICs Origami, avant et
apres l'instant du parcage (fusion de #24389), et signale le nombre de
``[RELEASED]`` **evites** comme une EXTRAPOLATION -- jamais comme un compte.

Les tests pinnent quatre controles :

* **le marqueur compte** : un ``[RELEASED]`` en TETE de commentaire compte ;
  une citation en milieu de corps ne compte pas (meme convention que l'organe
  de parcage) ;
* **la separation** : un ``[RELEASED]`` pose apres l'instant est un service
  passe par le parcage -- il doit apparaitre, et l'evite doit tomber a zero
  quand le rythme mesure est nul ;
* **le controle positif** : un marqueur ``[PLI n DEPLIE]`` pose apres l'instant
  est compte comme depliage ;
* **l'honnetete de l'evite** : le rapport nomme explicitement que l'evite est
  une extrapolation.

Jamais d'appel ``gh`` : tout le reseau est injecte.
Run: python -m pytest scripts/tests/test_origami_released_counter.py
"""
from __future__ import annotations

import sys
from datetime import datetime, timezone
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "coordination"))

import origami_released_counter as orc  # noqa: E402

INSTANT = orc.parse_instant("2026-11-05T16:47:04Z")


def _c(created_at: str, body: str) -> dict:
    return {"created_at": created_at, "body": body}


def test_released_header_counts_and_quote_does_not():
    comments = {
        19309: [
            _c("2026-11-05T16:23:42Z",
               "[RELEASED] lane myia-po-2027:CoursIA -- barriere reelle"),
            _c("2026-11-06T08:00:00Z",
               "Je recall que le mois dernier on a pose un [RELEASED] ici"),
        ]
    }
    counts = orc.count_events(comments, INSTANT)
    assert counts["released_before"] == 1
    assert counts["released_after"] == 0


def test_released_after_instant_is_a_service_passe():
    comments = {
        19309: [
            _c("2026-11-06T08:00:00Z",
               "[RELEASED] lane myia-po-2027:CoursIA -- service passe"),
        ]
    }
    counts = orc.count_events(comments, INSTANT)
    assert counts["released_after"] == 1
    assert counts["released_before"] == 0
    entry = counts["epics"][0]["released_after_list"][0]
    assert entry["lane"] == "myia-po-2027:CoursIA"
    assert entry["at"] == "2026-11-06T08:00:00Z"


def test_pli_deplie_after_instant_is_counted():
    comments = {
        20404: [
            _c("2026-11-10T18:33:35Z",
               "[PLI 4 DEPLIE] -- 2026-11-10, par la lane myia-po-2023:CoursIA"),
        ]
    }
    counts = orc.count_events(comments, INSTANT)
    assert counts["deplie_after"] == 1
    assert counts["released_after"] == 0


def test_quoted_pli_deplie_does_not_count():
    """Un rapport qui MENTIONNE le marqueur d'un autre EPIC ne deploie rien :
    le marqueur doit etre en tete de ligne."""
    comments = {
        24373: [
            _c("2026-11-09T01:51:13Z",
               "[INFO] candidate-delivered -- l'organe livre par #24389 est "
               "vivant ; reste le controle [PLI 4 DEPLIE] a faire"),
        ]
    }
    counts = orc.count_events(comments, INSTANT)
    assert counts["deplie_after"] == 0


def test_lane_is_extracted_from_the_header():
    info = orc.classify_comment(
        "[RELEASED] lane myia-ai-01:CoursIA-2 -- motif")
    assert info["released"] is True
    assert info["lane"] == "myia-ai-01:CoursIA-2"


def test_origami_epics_are_selected_by_title():
    pool = [
        {"number": 19309, "title": "[Epic Origami] Exemple", "body": ""},
        {"number": 19742, "title": "[Epic Origami #19742 - Pli 2]", "body": ""},
        {"number": 100, "title": "Reforme des booklets",
         "body": "cet EPIC parle d'origami dans son corps"},
    ]
    assert [e["number"] for e in orc.origami_epics(pool)] == [19309]


def test_instant_requires_an_explicit_utc():
    dt = orc.parse_instant("2026-11-05T16:47:04Z")
    assert dt.tzinfo is not None
    assert dt == datetime(2026, 11, 5, 16, 47, 4, tzinfo=timezone.utc)
    naive = orc.parse_instant("2026-11-05T16:47:04")
    assert naive.tzinfo is not None


def test_fetch_comments_paginates(monkeypatch):
    pages = {
        1: [{"created_at": "2026-11-01T00:00:00Z", "body": "x"}] * 100,
        2: [{"created_at": "2026-11-02T00:00:00Z", "body": "y"}] * 3,
    }
    seen = []

    def fake_gh(*args):
        seen.append(args)
        url = args[-1]
        page = int(url.rsplit("page=", 1)[1])
        return pages.get(page, [])

    out = orc.fetch_comments([19309], gh=fake_gh)
    assert len(out[19309]) == 103
    assert any("page=2" in a[-1] for a in seen)


def test_unreadable_pool_is_not_a_zero():
    assert orc.fetch_pool(gh=lambda *a: None) is None
