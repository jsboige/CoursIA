"""Tests du harnais de validation charge bornee (T5a, #15666).

Proprietes sous test, dans l'ordre de ce qu'elles protegent :

1. **Un verdict propre cite ses mesures** -- chaque critere dur PASS/FAIL
   porte le chiffre qui le fonde (population max vs cap, p95 vs borne),
   jamais un aveu nu.
2. **Le regime de l'incident echoue** -- population au-dessus du cap, sonde
   DriveFS en timeout, spawn etouffe, organe refuse ou orphelins : chacun
   de ces visages de l'asphyxie de septembre doit casser un critere NOMME.
3. **Pas de faux pass** -- sonde DriveFS indisponible n'est pas un succes
   de sonde ; zero echantillon pendant la charge n'est pas une population
   conforme ; un enregistrement d'organe absent ne valide rien.
4. **Le harnais ne se bloque pas** -- la sonde DriveFS abandonnee au bout
   de son timeout rend la main ; l'echantillonneur s'arrete a la mort de
   la charge et respecte son propre mur.

Aucun lake ni lean requis : le verdict est une fonction pure sur des
echantillons fabriques, l'echantillonneur se teste sur un enfant python.
"""

from __future__ import annotations

import os
import subprocess
import sys
import textwrap
import time
from pathlib import Path

LEAN_DIR = Path(__file__).resolve().parents[1] / "lean"
sys.path.insert(0, str(LEAN_DIR))

import validate_bounded_load as vbl  # noqa: E402


def _sample(phase="load", population=0, spawn_ms=100.0,
            drivefs="ok", drivefs_ms=40.0, ram=8000.0) -> dict:
    return {
        "t": 0.0, "phase": phase, "population": population,
        "population_src": "test", "spawn_ms": spawn_ms,
        "drivefs": drivefs, "drivefs_ms": drivefs_ms,
        "ram_free_mb": ram,
    }


def _organ_ok() -> dict:
    return {"status": "ok", "orphans": [], "exit_code": 0,
            "cmd": ["lake", "build"], "duration_s": 60.0}


def _evaluate(baseline, load, organ=_organ_ok(), cap=8):
    return vbl.evaluate(baseline, load, organ, cap,
                        spawn_ratio=5.0, spawn_floor_ms=5000.0)


def _check(verdict, name):
    return next(c for c in verdict["checks"] if c["criterion"] == name)


# --- 1. verdict propre ------------------------------------------------------

def test_verdict_propre_quatre_criteres_cites():
    baseline = [_sample("baseline") for _ in range(3)]
    load = [_sample(population=5) for _ in range(20)]
    verdict = _evaluate(baseline, load)
    assert verdict["pass"] is True
    assert len(verdict["checks"]) == 4
    assert all(c["pass"] for c in verdict["checks"])
    pop = _check(verdict, "population_cap")
    assert "5 <= cap 8" in pop["detail"] and "20 echantillons" in pop["detail"]
    spawn = _check(verdict, "spawn_p95")
    assert "5000.0 ms" in spawn["detail"]  # plancher, baseline basse


def test_p95_connu():
    assert vbl._p95([1, 2, 3, 4, 5, 6, 7, 8, 9, 100]) == 100
    assert vbl._p95([5]) == 5
    assert vbl._p95([]) is None


# --- 2. le regime de l'incident echoue --------------------------------------

def test_population_hors_cap_echoue_et_cite_les_nombres():
    load = [_sample(population=5), _sample(population=12), _sample()]
    verdict = _evaluate([_sample("baseline")], load, cap=8)
    assert verdict["pass"] is False
    pop = _check(verdict, "population_cap")
    assert pop["pass"] is False
    assert "12" in pop["detail"] and "cap 8" in pop["detail"]


def test_sonde_drivefs_en_timeout_echoue():
    load = [_sample(drivefs="ok"), _sample(drivefs="timeout", drivefs_ms=None),
            _sample()]
    verdict = _evaluate([_sample("baseline")], load)
    drivefs = _check(verdict, "drivefs_alive")
    assert drivefs["pass"] is False
    assert "1 sonde" in drivefs["detail"]


def test_spawn_etouffe_au_dela_de_la_borne_echoue():
    baseline = [_sample("baseline", spawn_ms=100.0) for _ in range(4)]
    load = [_sample(spawn_ms=40000.0) for _ in range(10)]
    verdict = _evaluate(baseline, load)
    spawn = _check(verdict, "spawn_p95")
    assert spawn["pass"] is False
    assert "40000.0 ms" in spawn["detail"]


def test_spawn_eleve_mais_sous_plancher_passe():
    # Baseline lente (2000 ms) : borne = max(5 x 2000, 5000) = 10000.
    # La charge a 8000 ms est degradée mais SOUS la borne -> PASS : la borne
    # est relative a la machine, pas un absolu invente.
    baseline = [_sample("baseline", spawn_ms=2000.0) for _ in range(4)]
    load = [_sample(spawn_ms=8000.0) for _ in range(10)]
    verdict = _evaluate(baseline, load)
    assert _check(verdict, "spawn_p95")["pass"] is True


def test_organ_refuse_ou_orphelins_echoue():
    refused = _evaluate([_sample("baseline")], [_sample()],
                        organ={"status": "refused", "orphans": []})
    assert _check(refused, "organ_postcondition")["pass"] is False
    assert "refused" in _check(refused, "organ_postcondition")["detail"]

    orphans = _evaluate([_sample("baseline")], [_sample()],
                        organ={"status": "ok", "orphans": [4242]})
    detail = _check(orphans, "organ_postcondition")["detail"]
    assert _check(orphans, "organ_postcondition")["pass"] is False
    assert "1" in detail  # un orphelin, compte


def test_enregistrement_organ_absent_ne_valide_rien():
    verdict = _evaluate([_sample("baseline")], [_sample()], organ=None)
    assert _check(verdict, "organ_postcondition")["pass"] is False


# --- 3. pas de faux pass ----------------------------------------------------

def test_sonde_indisponible_nest_pas_un_succes_mais_pas_un_echec():
    load = [_sample(drivefs="unavailable", drivefs_ms=None) for _ in range(5)]
    verdict = _evaluate([_sample("baseline", drivefs="unavailable",
                                 drivefs_ms=None)], load)
    drivefs = _check(verdict, "drivefs_alive")
    assert drivefs["pass"] is True
    assert "5 sonde(s) unavailable" in drivefs["detail"]  # note honnete


def test_zero_echantillon_de_charge_est_non_verifiable():
    verdict = _evaluate([_sample("baseline")], [])
    pop = _check(verdict, "population_cap")
    assert pop["pass"] is False
    assert "non verifiable" in pop["detail"]


# --- 4. le harnais ne se bloque pas -----------------------------------------

def test_sonde_drivefs_abandonnee_rend_la_main(monkeypatch, tmp_path):
    def _hanging_listdir(_root):
        time.sleep(5.0)

    monkeypatch.setattr(os, "listdir", _hanging_listdir)
    t0 = time.monotonic()
    state, ms = vbl.probe_drivefs(str(tmp_path), timeout_s=0.3)
    elapsed = time.monotonic() - t0
    assert state == vbl.DRIVEFS_TIMEOUT
    assert ms is None
    assert elapsed < 3.0  # rendu la main au timeout, pas au bout des 5 s


def test_sonde_drivefs_hors_racine_indisponible():
    state, ms = vbl.probe_drivefs(None, timeout_s=1.0)
    assert state == vbl.DRIVEFS_UNAVAILABLE
    assert ms is None


def test_sampler_echantillonne_pendant_la_vie_arrete_a_la_mort():
    calls = []

    def fake_sample(phase):
        calls.append(phase)
        return _sample(phase)

    sampler = vbl.Sampler(None, 1.0, sample_fn=fake_sample)
    proc = subprocess.Popen(
        [sys.executable, "-c", "import time; time.sleep(1.2)"],
        stdout=subprocess.DEVNULL,
    )
    try:
        samples, wall_exceeded = sampler.collect(proc, interval=0.15,
                                                 max_wall=30.0)
    finally:
        if proc.poll() is None:
            proc.kill()
    assert wall_exceeded is False
    assert len(samples) >= 3
    assert proc.poll() == 0  # collect a rendu la main APRES la mort


def test_sampler_renvoie_le_mur_depasse():
    sampler = vbl.Sampler(None, 1.0, sample_fn=_sample)
    proc = subprocess.Popen(
        [sys.executable, "-c", "import time; time.sleep(5)"],
        stdout=subprocess.DEVNULL,
    )
    try:
        _, wall_exceeded = sampler.collect(proc, interval=0.1, max_wall=0.01)
        assert wall_exceeded is True
    finally:
        proc.kill()
        proc.wait()


# --- charge : touch de modules ----------------------------------------------

def test_touch_own_modules_exclut_lake_et_bump_seulement_les_n(tmp_path):
    lake = tmp_path / "mylake"
    (lake / "Beta").mkdir(parents=True)
    (lake / ".lake" / "packages" / "x").mkdir(parents=True)
    files = {
        "lakefile.lean": lake / "lakefile.lean",
        "Alpha.lean": lake / "Alpha.lean",
        "Beta/B.lean": lake / "Beta" / "B.lean",
        "vendored": lake / ".lake" / "packages" / "x" / "X.lean",
    }
    old = 1000000000
    for path in files.values():
        path.write_text("-- stub\n", encoding="utf-8")
        os.utime(path, (old, old))

    touched = vbl.touch_own_modules(lake, 2)

    assert len(touched) == 2
    assert "vendored" not in str(touched)
    assert "lakefile.lean" not in touched
    for key in ("Alpha.lean", "Beta/B.lean"):
        assert key in touched
        assert files[key].stat().st_mtime > old
    assert files["vendored"].stat().st_mtime == old  # .lake intouché


def test_cli_exige_un_lakefile(tmp_path):
    import pytest
    with pytest.raises(SystemExit):
        vbl.main(["--lake-dir", str(tmp_path)])


def test_read_organ_record_rejette_le_stale(tmp_path, monkeypatch):
    import json
    state = tmp_path / "state"
    monkeypatch.setattr(
        vbl.lean_exec, "state_dir", lambda: state, raising=True
    )
    state.mkdir()
    (state / "last_run.json").write_text(
        json.dumps({"cmd": ["lake", "build"], "status": "ok"}), encoding="utf-8"
    )
    # cmd differente : enregistrement d'un AUTRE run -> None, pas de
    # validation sur du stale.
    assert vbl.read_organ_record(["lake", "exe", "cache", "get"]) is None
    assert vbl.read_organ_record(["lake", "build"]) is not None
