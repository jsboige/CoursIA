"""Tests pli 3 Origami -- rapport d'acceleration HashLife par classe de motif.

Couvre :
- l'organe est bien celui de conway_lean (pas de reimplementation locale)
- la ligne de base naive est correcte (glider : translation de 4 generations)
- accord de population naive / HashLife sur chaque motif mesure
- accord d'etat final (empreinte) naive / HashLife -- et le temoin discrimine
  vraiment, puisqu'il distingue deux etats de meme cardinal
- la pente log-log retrouve un exposant connu sur des series fabriquees, avec
  son R2
- un verdict n'est declare robuste que si son enveloppe tient dans sa bande et
  si la loi de puissance decrit la serie
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


def test_le_pulsar_est_bien_un_oscillateur_de_periode_3():
    """Le pulsar revient exactement sur lui-meme a la generation 3, et seulement la.

    Ce temoin manquait : le motif n'etait declare « periodique p3 » que par son
    etiquette d'anatomie. La version a 36 cellules sur 48 se comportait en
    emetteur, ses quatre points de mesure tombaient sur des etats tous differents
    et l'alpha ajuste decrivait autre chose que ce que la colonne annoncait.
    """
    pulsar = hs.build_motif("pulsar")
    assert hs.naive_run(pulsar, 3) == pulsar
    assert hs.naive_run(pulsar, 1) != pulsar
    assert hs.naive_run(pulsar, 2) != pulsar
    assert len(pulsar) == 48


@pytest.mark.parametrize("name", ["blinker", "glider", "acorn", "pulsar"])
def test_accord_de_population_naive_et_hashlife(name):
    """Controle de correction : les deux moteurs doivent rendre la meme population."""
    point = hs.measure_point(name, 64)
    assert point["populations_agree"] is True
    assert point["naive_population"] == point["hashlife_population"] > 0


@pytest.mark.parametrize("name", ["blinker", "glider", "acorn", "pulsar"])
def test_accord_d_etat_final_naive_et_hashlife(name):
    """Le cardinal ne suffit pas : c'est la configuration qui doit coincider."""
    point = hs.measure_point(name, 64)
    assert point["states_agree"] is True
    assert point["naive_state"] == point["hashlife_state"]


def test_empreinte_est_invariante_par_translation():
    """Les deux voies n'ont pas la meme origine : l'empreinte doit l'ignorer."""
    cells = hs.build_motif("glider")
    shifted = {(x + 37, y - 11) for x, y in cells}
    assert hs.state_fingerprint(cells) == hs.state_fingerprint(shifted)


def test_empreinte_discrimine_deux_etats_de_meme_population():
    """Temoin negatif du controle : trois cellules alignees != trois en equerre.

    Un accord de population rendrait ces deux etats « egaux » ; le temoin
    d'etat doit les separer, sinon il n'apporte rien au controle.
    """
    ligne = {(0, 0), (1, 0), (2, 0)}
    equerre = {(0, 0), (1, 0), (0, 1)}
    assert len(ligne) == len(equerre) == 3
    assert hs.state_fingerprint(ligne) != hs.state_fingerprint(equerre)
    assert hs.state_fingerprint(set()) != hs.state_fingerprint(ligne)


def test_pente_log_log_sur_series_fabriquees():
    lineaire = [(g, 3.0 * g) for g in (64, 128, 256, 512)]
    assert hs.log_log_slope(lineaire) == pytest.approx(1.0, abs=1e-9)
    constante = [(g, 0.004) for g in (64, 128, 256, 512)]
    assert hs.log_log_slope(constante) == pytest.approx(0.0, abs=1e-9)
    carre = [(g, 0.001 * g * g) for g in (64, 128, 256, 512)]
    assert hs.log_log_slope(carre) == pytest.approx(2.0, abs=1e-9)
    assert hs.log_log_slope([(256, 1.0)]) == 0.0  # moins de deux points


def test_l_ajustement_rend_un_r2_qui_note_la_loi_de_puissance():
    exacte = hs.log_log_fit([(g, 0.001 * g**1.7) for g in (64, 128, 256, 512)])
    assert exacte["slope"] == pytest.approx(1.7, abs=1e-9)
    assert exacte["r2"] == pytest.approx(1.0, abs=1e-12)
    assert exacte["n"] == 4
    # Meme pente moyenne, mais la loi de puissance ne decrit plus la serie :
    # c'est exactement ce que R2 doit signaler.
    bruitee = hs.log_log_fit(
        [(64, 0.001), (128, 0.500), (256, 0.002), (512, 1.000)]
    )
    assert bruitee["r2"] < hs.R2_MIN_FOR_LINEARITY
    assert hs.log_log_fit([(256, 1.0)])["n"] == 1


def test_le_verdict_n_est_robuste_que_dans_sa_bande_et_sous_bonne_linearite():
    bon_r2 = hs.R2_MIN_FOR_LINEARITY + 0.05
    assert hs.verdict_is_robust("REDUCIBLE", [0.10, 0.20], bon_r2) is True
    assert hs.verdict_is_robust("REDUCIBLE", [0.30, 0.62], bon_r2) is False
    assert hs.verdict_is_robust("IRREDUCIBLE", [0.85, 1.40], bon_r2) is True
    assert hs.verdict_is_robust("IRREDUCIBLE", [0.76, 1.40], bon_r2) is False
    assert hs.verdict_is_robust("AMBIGUOUS", [0.55, 0.70], bon_r2) is True
    assert hs.verdict_is_robust("AMBIGUOUS", [0.45, 0.90], bon_r2) is False
    # Sans enveloppe ni linearite, aucune robustesse n'est revendiquee.
    assert hs.verdict_is_robust("REDUCIBLE", None, bon_r2) is False
    assert hs.verdict_is_robust("REDUCIBLE", [0.10, 0.20], 0.4) is False


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
    assert point["states_agree"] is True
    assert point["naive_state"] == point["hashlife_state"]
    assert point["hashlife_s"] > 0 and point["naive_s"] > 0


def test_aggregate_prend_la_mediane_et_rend_le_verdict():
    def row(gen, naive_s, hash_s):
        return {
            "motif": "blinker", "generations": gen, "naive_s": naive_s,
            "hashlife_s": hash_s, "naive_population": 3, "hashlife_population": 3,
            "populations_agree": True, "naive_state": "aa", "hashlife_state": "aa",
            "states_agree": True,
        }

    rows = [
        row(64, 0.010, 0.010),
        row(64, 0.012, 0.030),
        row(4096, 0.400, 0.002),
    ]
    report = hs.aggregate(rows, repeats=2)
    entry = report["motifs"][0]
    assert entry["points"][0]["naive_s"] == pytest.approx(0.011)  # mediane
    assert entry["points"][0]["samples"] == 2
    assert entry["points"][0]["states_agree"] is True
    assert entry["alpha_hashlife"] < hs.ALPHA_REDUCIBLE_MAX
    assert entry["r2_hashlife"] == pytest.approx(1.0, abs=1e-12)
    assert entry["verdict"] == "REDUCIBLE"
    # G=4096 n'a qu'une mesure : pas d'enveloppe, donc pas de robustesse.
    assert entry["repetitions_used"] == 1
    assert entry["alpha_envelope"] is None
    assert entry["verdict_robust"] is False
    assert report["thresholds"]["r2_min_for_linearity"] == hs.R2_MIN_FOR_LINEARITY


def test_aggregate_mesure_l_enveloppe_des_repetitions():
    """Deux repetitions completes suffisent a porter une enveloppe."""
    rows = []
    for hash_s in (0.010, 0.012):
        rows.append({
            "motif": "blinker", "generations": 64, "naive_s": 0.010,
            "hashlife_s": hash_s, "naive_population": 3, "hashlife_population": 3,
            "populations_agree": True, "naive_state": "aa", "hashlife_state": "aa",
            "states_agree": True,
        })
    for hash_s in (0.002, 0.001):
        rows.append({
            "motif": "blinker", "generations": 4096, "naive_s": 0.400,
            "hashlife_s": hash_s, "naive_population": 3, "hashlife_population": 3,
            "populations_agree": True, "naive_state": "aa", "hashlife_state": "aa",
            "states_agree": True,
        })
    entry = hs.aggregate(rows, repeats=2)["motifs"][0]
    assert entry["repetitions_used"] == 2
    assert entry["alpha_envelope"] is not None
    lo, hi = entry["alpha_envelope"]
    assert lo <= entry["alpha_hashlife"] <= hi
