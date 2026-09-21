"""Tests for the bounded raw-payload cache used by pick_idle_grain."""

from __future__ import annotations

import datetime as dt
import json
import os
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from gh_payload_cache import (  # noqa: E402
    PayloadCache,
    cache_key,
    default_cache_dir,
)
import pick_idle_grain as pig  # noqa: E402
import series_saturation as series  # noqa: E402


def test_cache_key_changes_with_query_and_repository():
    first = cache_key("owner/repo", "pool", ["gh", "issue", "list"])
    assert first == cache_key("owner/repo", "pool", ["gh", "issue", "list"])
    assert first != cache_key("owner/repo", "pool", ["gh", "pr", "list"])
    assert first != cache_key("other/repo", "pool", ["gh", "issue", "list"])


def test_default_cache_dir_uses_localappdata_on_windows(monkeypatch, tmp_path):
    monkeypatch.setenv("LOCALAPPDATA", str(tmp_path))
    assert default_cache_dir("nt") == tmp_path / "CoursIA" / "cache" / "pick_idle_grain"


def test_miss_then_hit_does_not_refetch(tmp_path):
    now = [100.0]
    calls = []
    cache = PayloadCache(tmp_path, clock=lambda: now[0])

    def fetch():
        calls.append(True)
        return [{"number": 1}]

    first = cache.get_or_fetch("pool", 60, fetch)
    now[0] = 120.0
    second = cache.get_or_fetch("pool", 60, fetch)
    assert first.status == "miss"
    assert second.status == "hit"
    assert second.payload == first.payload
    assert second.age_seconds == 20.0
    assert len(calls) == 1


def test_expired_entry_is_refetched(tmp_path):
    now = [100.0]
    cache = PayloadCache(tmp_path, clock=lambda: now[0])
    values = iter([[1], [2]])
    assert cache.get_or_fetch("pool", 10, lambda: next(values)).payload == [1]
    now[0] = 111.0
    result = cache.get_or_fetch("pool", 10, lambda: next(values))
    assert result.status == "miss"
    assert result.payload == [2]


def test_refresh_forces_fetch_even_when_entry_is_fresh(tmp_path):
    now = [100.0]
    cache = PayloadCache(tmp_path, clock=lambda: now[0])
    cache.get_or_fetch("pool", 60, lambda: [1])
    now[0] = 101.0
    result = cache.get_or_fetch("pool", 60, lambda: [2], mode="refresh")
    assert result.status == "refresh"
    assert result.payload == [2]


def test_off_bypasses_all_disk_io(tmp_path):
    cache = PayloadCache(tmp_path)
    result = cache.get_or_fetch("pool", 60, lambda: [1], mode="off")
    assert result.status == "bypass"
    assert result.payload == [1]
    assert list(tmp_path.iterdir()) == []


def test_stale_fallback_is_explicit_after_fetch_failure(tmp_path):
    now = [100.0]
    cache = PayloadCache(tmp_path, clock=lambda: now[0])
    cache.get_or_fetch("pool", 10, lambda: [1])
    now[0] = 200.0

    def fail():
        raise RuntimeError("GitHub unavailable")

    result = cache.get_or_fetch("pool", 10, fail)
    assert result.status == "stale"
    assert result.payload == [1]
    assert result.age_seconds == 100.0
    assert result.error == "RuntimeError: GitHub unavailable"
    assert result.as_dict()["status"] == "stale"


def test_fetch_failure_without_stale_entry_propagates(tmp_path):
    cache = PayloadCache(tmp_path)
    with pytest.raises(RuntimeError, match="offline"):
        cache.get_or_fetch("pool", 10, lambda: (_ for _ in ()).throw(RuntimeError("offline")))


def test_corrupt_entry_is_treated_as_miss_and_replaced(tmp_path):
    (tmp_path / "pool.json").write_text("{broken", encoding="utf-8")
    cache = PayloadCache(tmp_path, clock=lambda: 100.0)
    result = cache.get_or_fetch("pool", 60, lambda: {"fresh": True})
    assert result.status == "miss"
    assert result.payload == {"fresh": True}
    envelope = json.loads((tmp_path / "pool.json").read_text(encoding="utf-8"))
    assert envelope["payload"] == {"fresh": True}


def test_unwritable_cache_returns_fresh_payload_as_bypass(monkeypatch, tmp_path):
    cache = PayloadCache(tmp_path, clock=lambda: 100.0)

    def denied(*args, **kwargs):
        raise PermissionError("read-only cache")

    monkeypatch.setattr(cache, "_write", denied)
    result = cache.get_or_fetch("pool", 60, lambda: [1])
    assert result.status == "bypass"
    assert result.payload == [1]
    assert "PermissionError" in result.error


def test_retention_keeps_only_newest_entries(tmp_path):
    now = [100.0]
    cache = PayloadCache(tmp_path, max_entries=2, clock=lambda: now[0])
    for index in range(3):
        now[0] += 1
        cache.get_or_fetch(f"key-{index}", 60, lambda index=index: [index])
        os.utime(tmp_path / f"key-{index}.json", (now[0], now[0]))
    assert sorted(path.name for path in tmp_path.glob("*.json")) == [
        "key-1.json",
        "key-2.json",
    ]


def test_atomic_write_leaves_no_temp_files(tmp_path):
    cache = PayloadCache(tmp_path, clock=lambda: 100.0)
    cache.get_or_fetch("pool", 60, lambda: [1])
    assert [path.name for path in tmp_path.iterdir()] == ["pool.json"]


class _Completed:
    def __init__(self, payload):
        self.stdout = json.dumps(payload)
        self.returncode = 0


def test_three_shared_payloads_are_reused_without_changing_derivations(
    monkeypatch, tmp_path
):
    issue = {
        "number": 13920,
        "title": "perf: picker cache",
        "labels": [{"name": "performance"}],
        "body": "",
        "createdAt": "2026-08-01T00:00:00Z",
        "updatedAt": "2026-08-15T00:00:00Z",
    }
    visit_pr = {
        "number": 14000,
        "title": "perf(picker): cache (#13920)",
        "body": "See #13920",
        # #13386 : fixture mergedAt relatif (NOW - 1h) pour eviter la derive
        # temporelle -- hardcoder une date absolue ("2026-09-01T00:00:00Z")
        # faisait sortir la PR de la fenetre de 24 h apres 24h d'horloge.
        "mergedAt": (pig.NOW - dt.timedelta(hours=1)).strftime("%Y-%m-%dT%H:%M:%SZ"),
    }
    series_pr = {
        **visit_pr,
        "files": [{
            "path": "MyIA.AI.Notebooks/Search/Part4-Metaheuristics/demo.ipynb",
            "additions": 400,
            "deletions": 0,
        }],
    }
    calls = []

    def run(command, **kwargs):
        calls.append(command)
        fields = command[command.index("--json") + 1]
        if command[1:3] == ["issue", "list"]:
            return _Completed([issue])
        if "files" in fields:
            return _Completed([series_pr])
        return _Completed([visit_pr])

    monkeypatch.setattr(pig.subprocess, "run", run)
    monkeypatch.setattr(series.subprocess, "run", run)
    cache = PayloadCache(tmp_path, clock=lambda: 100.0)

    first_status = {}
    # `probe=None` : ce test isole la REUTILISATION des trois payloads (l'intention
    # de `len(calls) == 3`). La verification de fraicheur (#17096) ajoute une
    # sonde reseau et a ses propres tests ; la laisser active ici melangerait
    # deux comptes et ferait dire au test autre chose que ce qu'il epingle.
    first = (
        pig.fetch_pool(
            cache=cache, cache_mode="auto", cache_status=first_status, probe=None
        ),
        pig.fetch_visits(cache=cache, cache_mode="auto", cache_status=first_status),
        series.fetch_series_visits(
            cache=cache, cache_mode="auto", cache_status=first_status
        ),
    )
    second_status = {}
    second = (
        pig.fetch_pool(
            cache=cache, cache_mode="auto", cache_status=second_status, probe=None
        ),
        pig.fetch_visits(cache=cache, cache_mode="auto", cache_status=second_status),
        series.fetch_series_visits(
            cache=cache, cache_mode="auto", cache_status=second_status
        ),
    )

    assert first == second
    assert len(calls) == 3
    assert {entry["status"] for entry in first_status.values()} == {"miss"}
    assert {entry["status"] for entry in second_status.values()} == {"hit"}
    # Un hit SANS sonde n'est pas une mesure : la suite doit pouvoir le dire.
    assert second_status["pool"]["verified"] is False
    assert first[1] == ({13920: 1}, None)
    zones, issue_to_family, error = first[2]
    assert error is None
    assert zones["MyIA.AI.Notebooks/Search/Part4-Metaheuristics"]["new_notebooks"] == 1
    assert issue_to_family[13920] == "MyIA.AI.Notebooks/Search/Part4-Metaheuristics"


def test_stale_visits_are_used_but_reported_as_unmeasured(monkeypatch, tmp_path):
    now = [100.0]
    cache = PayloadCache(tmp_path, clock=lambda: now[0])
    # #13386 : fixture mergedAt relatif (NOW - 1h) pour eviter la derive
    # temporelle -- hardcoder une date absolue ("2026-09-01T00:00:00Z")
    # faisait sortir la PR de la fenetre de 24 h apres 24h d'horloge,
    # vidant le compteur `{}` et cassant le test pour toute PR ouverte
    # apres cette date.
    _now_dt = pig.NOW - dt.timedelta(hours=1)
    success = _Completed([{
        "number": 14000,
        "title": "See #13920",
        "body": "See #13920",
        "mergedAt": _now_dt.strftime("%Y-%m-%dT%H:%M:%SZ"),
    }])
    monkeypatch.setattr(pig.subprocess, "run", lambda *args, **kwargs: success)
    pig.fetch_visits(cache=cache, cache_mode="auto", cache_status={})
    now[0] += pig.VISITS_CACHE_TTL_SECONDS + 1

    def fail(*args, **kwargs):
        raise RuntimeError("GitHub unavailable")

    monkeypatch.setattr(pig.subprocess, "run", fail)
    status = {}
    counts, error = pig.fetch_visits(
        cache=cache, cache_mode="auto", cache_status=status
    )
    assert counts == {13920: 1}
    assert status["visits"]["status"] == "stale"
    assert "GitHub unavailable" in error


# --- #17096 : sonde de fraicheur, hit non verifie, et non-silence --------------
#
# Le defaut : `--cache auto` servait une entree TTL-valide en silence, sans jamais
# la confronter au distant. Un payload gele pouvait donc circuler comme s'il avait
# ete verifie. Ces tests epinglent les deux moities de la parade -- la sonde qui
# PROUVE (et rafraichit), et l'aveu explicite quand la preuve manque.
#
# Horloge realiste : la sonde compare un timestamp DISTANT (`updatedAt`) a
# `fetched_at`, ecrit par `PayloadCache.clock`. Les deux doivent donc etre sur la
# meme echelle -- une horloge a 100.0 (1970) rendrait toute date reelle
# « posterieure » et ferait conclure a tort que le distant a bouge.


class _Raw:
    """Sortie brute de `gh` (la sonde rend une date nue, pas du JSON)."""

    def __init__(self, text):
        self.stdout = text
        self.returncode = 0


FETCHED_AT = 1_780_000_000.0  # 2026-06-07, echelle `time.time()`


def _iso(epoch):
    return dt.datetime.fromtimestamp(epoch, dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def test_sonde_sans_mouvement_verifie_le_hit(tmp_path):
    """La sonde a parle et confirme : le hit est servi ET marque verifie."""
    calls = []
    cache = PayloadCache(tmp_path, clock=lambda: FETCHED_AT)
    cache.get_or_fetch("pool", 60, lambda: [1])
    result = cache.get_or_fetch(
        "pool", 60, lambda: calls.append(True) or [2],
        probe=lambda: FETCHED_AT - 300.0,
    )
    assert result.status == "hit"
    assert result.payload == [1]
    assert result.verified is True
    assert result.probe_delta_seconds == -300.0
    assert calls == [], "un hit verifie ne doit declencher aucun fetch"


def test_sonde_qui_prouve_le_mouvement_declenche_un_refresh(tmp_path):
    """La sonde PROUVE que le distant a bouge apres le snapshot : on rafraichit sans operateur."""
    cache = PayloadCache(tmp_path, clock=lambda: FETCHED_AT)
    cache.get_or_fetch("pool", 60, lambda: [1])
    result = cache.get_or_fetch(
        "pool", 60, lambda: [2],
        probe=lambda: FETCHED_AT + 45.0,
    )
    assert result.status == "miss"
    assert result.payload == [2]
    assert result.verified is True
    assert result.probe_delta_seconds == 45.0


def test_sonde_muette_laisse_le_hit_mais_le_marque_non_verifie(tmp_path):
    """Sonde qui ne sait pas mesurer : le payload reste utilisable, la confiance non."""
    cache = PayloadCache(tmp_path, clock=lambda: FETCHED_AT)
    cache.get_or_fetch("pool", 60, lambda: [1])
    result = cache.get_or_fetch("pool", 60, lambda: [2], probe=lambda: None)
    assert result.status == "hit"
    assert result.payload == [1]
    assert result.verified is False
    assert result.probe_delta_seconds is None


def test_sonde_qui_leve_ne_casse_pas_le_picker(tmp_path):
    """Une sonde en echec ne doit jamais faire tomber le tirage de grains."""
    cache = PayloadCache(tmp_path, clock=lambda: FETCHED_AT)
    cache.get_or_fetch("pool", 60, lambda: [1])

    def boom():
        raise OSError("gh absent")

    result = cache.get_or_fetch("pool", 60, lambda: [2], probe=boom)
    assert result.status == "hit"
    assert result.verified is False


def test_sonde_ignoree_en_mode_off_et_refresh(tmp_path):
    """`off` fait un fetch neuf, `refresh` force le fetch : aucun des deux ne consulte la sonde."""
    probed = []
    cache = PayloadCache(tmp_path, clock=lambda: FETCHED_AT)
    cache.get_or_fetch("pool", 60, lambda: [1])

    off = cache.get_or_fetch(
        "pool", 60, lambda: [2], mode="off", probe=lambda: probed.append(1) or FETCHED_AT
    )
    forced = cache.get_or_fetch(
        "pool", 60, lambda: [3], mode="refresh",
        probe=lambda: probed.append(1) or FETCHED_AT,
    )
    assert off.status == "bypass" and off.verified is True
    assert forced.status == "refresh" and forced.verified is True
    assert probed == []


def test_notice_signale_un_hit_non_verifie_meme_sans_cache_status():
    """#17096 : le silence est le defaut. Un hit non verifie doit sortir SANS le drapeau."""
    lines = pig.cache_notice_lines({
        "pool": {"status": "hit", "verified": False, "age_seconds": 42.0,
                 "probe_delta_seconds": None, "fetched_at": FETCHED_AT, "error": None},
    })
    assert len(lines) == 2
    assert "CACHE HIT NON RE-VERIFIE" in lines[1]
    assert "42 s de cache" in lines[1]
    assert "sonde distante muette" in lines[1]
    assert "pool=hit" in lines[0] and "age=42s" in lines[0]


def test_notice_signale_le_mouvement_mesure_par_la_sonde():
    lines = pig.cache_notice_lines({
        "pool": {"status": "hit", "verified": False, "age_seconds": 10.0,
                 "probe_delta_seconds": 5.0, "fetched_at": FETCHED_AT, "error": None},
    })
    assert "sonde a +5 s" in lines[1]


def test_notice_muette_quand_tout_est_verifie_et_que_le_drapeau_est_absent():
    """Le pendant du test precedent : une cache saine ne doit pas bavarder sans --cache-status."""
    assert pig.cache_notice_lines({
        "pool": {"status": "hit", "verified": True, "age_seconds": 12.0,
                 "probe_delta_seconds": -3.0, "fetched_at": FETCHED_AT, "error": None},
        "visits": {"status": "miss", "verified": True, "age_seconds": 0.0,
                   "probe_delta_seconds": None, "fetched_at": FETCHED_AT, "error": None},
    }) == []
    assert pig.cache_notice_lines({}, show_all=True) == []


def test_notice_stale_reste_annonce_et_distingue_du_hit_non_verifie():
    lines = pig.cache_notice_lines({
        "pool": {"status": "stale", "verified": False, "age_seconds": 900.0,
                 "probe_delta_seconds": None, "fetched_at": FETCHED_AT,
                 "error": "RuntimeError: GitHub unavailable"},
    })
    assert any("STALE explicite" in line for line in lines)
    assert any("GitHub unavailable" in line for line in lines)
    assert not any("CACHE HIT NON RE-VERIFIE" in line for line in lines)


def test_pool_gele_depuis_24h_n_est_pas_perime_s_il_n_a_pas_bouge(tmp_path, monkeypatch):
    """Acceptance #17096 : 5 issues gelees >24 h sans mutation -> candidat servi, etat FACTUEL.

    Une issue gelee n'est pas une issue perimee : la sonde mesure l'absence de
    mouvement, donc le pool est servi comme courant. Ce qui change par rapport au
    defaut, c'est que l'etat est desormais etabli au lieu d'etre suppose.
    """
    frozen = [
        {
            "number": 19100 + index,
            "title": f"[bug] sujet gele {index}",
            "labels": [],
            "body": "",
            "createdAt": _iso(FETCHED_AT - 40 * 3600),
            "updatedAt": _iso(FETCHED_AT - 30 * 3600),  # > 24 h sans mutation
        }
        for index in range(5)
    ]

    def run(command, **kwargs):
        if command[1] == "api":
            return _Raw(_iso(FETCHED_AT - 30 * 3600))  # rien de plus recent
        return _Completed(frozen)

    monkeypatch.setattr(pig.subprocess, "run", run)
    cache = PayloadCache(tmp_path, clock=lambda: FETCHED_AT)
    status = {}
    pig.fetch_pool(cache=cache, cache_mode="auto", cache_status=status)

    second = {}
    pool = pig.fetch_pool(cache=cache, cache_mode="auto", cache_status=second)
    assert len(pool) == 5, "le pool gele doit rester servi"
    assert second["pool"]["status"] == "hit"
    assert second["pool"]["verified"] is True, "la sonde a mesure : le hit est etabli"
    assert second["pool"]["probe_delta_seconds"] == -30 * 3600
    assert pig.cache_notice_lines(second) == [], "un hit verifie ne doit pas alerter"
    assert status["pool"]["status"] == "miss"


def test_pool_perime_et_refresh_impossible_sort_un_stale_explicite(tmp_path, monkeypatch):
    """La sonde prouve le mouvement, le refresh echoue : STALE explicite, jamais un silence."""
    stale_pool = [{
        "number": 19200, "title": "[bug] deja pris ailleurs", "labels": [], "body": "",
        "createdAt": _iso(FETCHED_AT - 3600), "updatedAt": _iso(FETCHED_AT - 3600),
    }]
    state = {"fetched": False}

    def run(command, **kwargs):
        if command[1] == "api":
            return _Raw(_iso(FETCHED_AT + 60.0))  # le distant a bouge
        if not state["fetched"]:
            state["fetched"] = True
            return _Completed(stale_pool)
        raise RuntimeError("GitHub unavailable")

    monkeypatch.setattr(pig.subprocess, "run", run)
    cache = PayloadCache(tmp_path, clock=lambda: FETCHED_AT)
    pig.fetch_pool(cache=cache, cache_mode="auto", cache_status={})

    status = {}
    pool = pig.fetch_pool(cache=cache, cache_mode="auto", cache_status=status)
    assert status["pool"]["status"] == "stale"
    # `fetch_pool` rend des entrees DERIVEES (age, genre, polarite...), pas le
    # payload brut : la comparaison porte sur l'identite du candidat, qui est ce
    # que la lane lit pour decider -- l'ancien payload reste exploitable.
    assert [item["number"] for item in pool] == [19200]
    lines = pig.cache_notice_lines(status)
    assert any("STALE explicite" in line for line in lines)
