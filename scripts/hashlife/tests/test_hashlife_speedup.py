"""Tests pli 3 Origami -- rapport d'acceleration HashLife par classe de motif.

Couvre :
- l'organe est bien celui de conway_lean (pas de reimplementation locale)
- la ligne de base naive est correcte (glider : translation de 4 generations)
- accord de population naive / HashLife sur chaque motif mesure
- la pente log-log retrouve un exposant connu sur des series fabriquees
- la classification est celle des seuils declares
- le registre de motifs est coherent (generations croissantes, motifs deterministes)
- le worker isole rend un point complet (cache froid, processus neuf)
"""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

SCRIPTS = Path(__file__).resolve().parents[1]
REPO_ROOT = SCRIPTS.parent
SCRIPT = SCRIPTS / "hashlife_speedup.py"

sys.path.insert(0, str(SCRIPTS))

import hashlife_speedup as hs  # noqa: E402


def test_l_organe_est_celui_de_conway_lean():
    """Organ-first : la mesure importe l'organe prouve, elle ne le reecrit pas."""
    assert hs.ORGAN_FILE.is_file(), f"organe absent : {hs.ORGAN_FILE}"
    source = hs.ORGAN_FILE.read_text(encoding="utf-8")
    assert "def construct(" in source
    assert "def advance(" in source
    # Le module de mesure ne definit ni construct ni advance : aucun doublon.
    own = SCRIPT.read_text(encoding="utf-8")
    assert "def construct(" not in own
    assert "def advance(" not in own


def test_la_ligne_de_base_translate_un_glider():
    """Le planeur revient translate de (1,1) apres 4 generations."""
    start = hs.build_motif("glider")
    after = hs.naive_run(start, 4)
    assert after == {(x + 1, y + 1) for x, y in start}


def test_la_ligne_de_base_conserve_les_motifs_stables():
    assert hs.naive_run(hs.build_motif("block"), 7) == hs.build_motif("block")
    assert hs.naive_run(hs.build_motif("blinker"), 2) == hs.build_motif("blinker")


@pytest.mark.parametrize("name", ["blinker", "glider", "acorn"])
def test_accord_de_population_naive_et_hashlife(name):
    """Controle de correction : les deux moteurs doivent rendre la meme population."""
    point = hs.measure_point(name, 64)
    assert point["populations_agree"] is True
    assert point["naive_population"] == point["hashlife_population"] > 0


def test_pente_log_log_sur_series_fabriquees():
    lineaire = [(g, 3.0 * g) for g in (64, 128, 256, 512)]
    assert hs.log_log_slope(lineaire) == pytest.approx(1.0, abs=1e-9)
    constante = [(g, 0.004) for g in (64, 128, 256, 512)]
    assert hs.log_log_slope(constante) == pytest.approx(0.0, abs=1e-9)
    carre = [(g, 0.001 * g * g) for g in (64, 128, 256, 512)]
    assert hs.log_log_slope(carre) == pytest.approx(2.0, abs=1e-9)
    assert hs.log_log_slope([(256, 1.0)]) == 0.0  # moins de deux points


def test_classification_est_celle_des_seuils_declares():
    assert hs.ALPHA_REDUCIBLE_MAX < hs.ALPHA_IRREDUCIBLE_MIN
    assert hs.classify(0.0) == "REDUCIBLE"
    assert hs.classify(hs.ALPHA_REDUCIBLE_MAX - 1e-9) == "REDUCIBLE"
    assert hs.classify(hs.ALPHA_REDUCIBLE_MAX) == "AMBIGUOUS"
    assert hs.classify(hs.ALPHA_IRREDUCIBLE_MIN - 1e-9) == "AMBIGUOUS"
    assert hs.classify(hs.ALPHA_IRREDUCIBLE_MIN) == "IRREDUCIBLE"


def test_le_registre_de_motifs_est_coherent():
    for name, (generations, anatomy) in hs.MOTIFS.items():
        assert generations == sorted(set(generations)), name
        assert len(generations) >= 2, name
        assert anatomy, name
        cells = hs.build_motif(name)
        assert cells and all(isinstance(c, tuple) and len(c) == 2 for c in cells)


def test_les_soupes_sont_deterministes():
    """Un motif non reproductible rendrait la mesure non comparable entre runs."""
    assert hs.build_motif("soup-64-d30") == hs.build_motif("soup-64-d30")
    assert hs.build_motif("soup-128-d35") == hs.build_motif("soup-128-d35")
    assert hs.build_motif("soup-64-d30") != hs.build_motif("soup-128-d35")


def test_le_worker_isole_rend_un_point_complet():
    """Le worker tourne dans un processus neuf : cache de l'organe froid par construction."""
    proc = subprocess.run(
        [sys.executable, str(SCRIPT), "--worker", "blinker", "32"],
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        cwd=str(REPO_ROOT),
        timeout=120,
    )
    assert proc.returncode == 0, proc.stderr[-1500:]
    point = json.loads(proc.stdout.strip().splitlines()[-1])
    assert point["motif"] == "blinker"
    assert point["generations"] == 32
    assert point["populations_agree"] is True
    assert point["hashlife_s"] > 0 and point["naive_s"] > 0


def test_aggregate_prend_la_mediane_et_rend_le_verdict():
    rows = [
        {"motif": "blinker", "generations": 64, "naive_s": 0.010,
         "hashlife_s": 0.010, "naive_population": 3, "hashlife_population": 3,
         "populations_agree": True},
        {"motif": "blinker", "generations": 64, "naive_s": 0.012,
         "hashlife_s": 0.030, "naive_population": 3, "hashlife_population": 3,
         "populations_agree": True},
        {"motif": "blinker", "generations": 4096, "naive_s": 0.400,
         "hashlife_s": 0.002, "naive_population": 3, "hashlife_population": 3,
         "populations_agree": True},
    ]
    report = hs.aggregate(rows, repeats=2)
    entry = report["motifs"][0]
    assert entry["points"][0]["naive_s"] == pytest.approx(0.011)  # mediane
    assert entry["points"][0]["samples"] == 2
    assert entry["alpha_hashlife"] < hs.ALPHA_REDUCIBLE_MAX
    assert entry["verdict"] == "REDUCIBLE"
