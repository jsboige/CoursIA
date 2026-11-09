#!/usr/bin/env python3
"""Tests de l'instrument de mesure du test externe humain (#20222, grain 2).

L'alpha et l'intervalle de Wilson sont verifies contre des valeurs calculees a
la main, pas contre eux-memes : le cas a quatre items porte un alpha exact de
7/18, et l'intervalle de Wilson sur 50 succes / 100 essais est la valeur
classique [0,404 ; 0,596].
"""

from __future__ import annotations

import json
import math
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import score_external_eval as scorer  # noqa: E402


def write_jsonl(path: Path, records: list[dict]) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        "\n".join(json.dumps(record, ensure_ascii=False) for record in records) + "\n",
        encoding="utf-8",
    )
    return path


def make_key(tmp_path: Path, items: dict[str, str]) -> Path:
    """item_id -> noeud."""
    return write_jsonl(
        tmp_path / "key.jsonl",
        [{"item_id": item_id, "node": node} for item_id, node in items.items()],
    )


def make_rater(tmp_path: Path, name: str, ratings: dict[str, str], folder: str = "pass1") -> Path:
    return write_jsonl(
        tmp_path / folder / f"{name}.jsonl",
        [{"item_id": item_id, "node": node} for item_id, node in ratings.items()],
    )


# ---------------------------------------------------------------- alpha


def test_alpha_cas_calcule_a_la_main():
    """Quatre items, trois evaluateurs, deux valeurs : alpha exact = 7/18.

    Matrice de coincidence (m=3 partout) : o_AA = o_BB = 4, o_AB = o_BA = 2,
    n_A = n_B = 6, n = 12. D_o = 4/12, D_e = 6/11, alpha = 1 - 11/18.
    """
    units = [["A", "A", "A"], ["A", "A", "B"], ["A", "B", "B"], ["B", "B", "B"]]
    result = scorer.krippendorff_alpha(units)
    assert result["alpha"] == pytest.approx(7 / 18)
    assert result["dropped"] == 0
    assert result["pairable_values"] == 12
    assert result["observed_disagreement"] == pytest.approx(1 / 3)
    assert result["expected_disagreement"] == pytest.approx(6 / 11)


def test_alpha_accord_parfait_vaut_un():
    units = [["A", "A", "A"], ["B", "B", "B"], ["C", "C", "C"]]
    assert scorer.krippendorff_alpha(units)["alpha"] == pytest.approx(1.0)


def test_alpha_sans_variation_vaut_un_par_convention():
    """Toutes les notations identiques : accord attendu nul, alpha = 1."""
    units = [["A", "A"], ["A", "A", "A"]]
    result = scorer.krippendorff_alpha(units)
    assert result["alpha"] == pytest.approx(1.0)
    assert result["expected_disagreement"] == 0


def test_alpha_ecarte_et_compte_les_unites_non_appariables():
    """Un item note par un seul evaluateur sort du calcul -- et il est compte."""
    units = [["A", "A"], ["B", "B"], ["A"]]
    result = scorer.krippendorff_alpha(units)
    assert result["dropped"] == 1
    assert result["pairable_values"] == 4
    # Sans l'item ecarte, l'accord est parfait sur les deux items restants.
    assert result["alpha"] == pytest.approx(1.0)


def test_alpha_indetermine_si_aucune_unite_appariable():
    result = scorer.krippendorff_alpha([["A"], ["B"]])
    assert result["alpha"] is None
    assert result["dropped"] == 2


# ---------------------------------------------------------------- Wilson


def test_wilson_valeur_classique_50_sur_100():
    low, high = scorer.wilson_interval(50, 100)
    assert low == pytest.approx(0.4038, abs=1e-3)
    assert high == pytest.approx(0.5962, abs=1e-3)


def test_wilson_reste_dans_les_bornes_aux_extremites():
    """La raison d'etre de Wilson : l'intervalle normal sortirait de [0, 1]."""
    low, high = scorer.wilson_interval(0, 100)
    assert low == 0.0
    assert 0.0 < high < 0.05

    low, high = scorer.wilson_interval(100, 100)
    assert high == 1.0
    assert 0.9 < low < 1.0


def test_wilson_contient_toujours_la_proportion():
    for successes in range(0, 21):
        low, high = scorer.wilson_interval(successes, 20)
        assert low <= successes / 20 <= high


def test_wilson_refuse_zero_essai():
    with pytest.raises(SystemExit):
        scorer.wilson_interval(0, 0)


# ---------------------------------------------------------- majorite


def test_majorite_stricte():
    assert scorer.strict_majority(["A", "A", "B"]) == "A"
    assert scorer.strict_majority(["A", "A", "A"]) == "A"
    assert scorer.strict_majority(["A", "B", "C"]) is None
    assert scorer.strict_majority(["A", "A", "B", "B"]) is None
    assert scorer.strict_majority(["A", "A", "A", "B"]) == "A"


# ------------------------------------------------------- bout en bout


def test_bout_en_bout_rapport_et_scores(tmp_path):
    """Corpus a 5 items, 3 evaluateurs ; la couverture est complete."""
    key = make_key(tmp_path, {
        "eval-0001": "attaque/ad hominem",
        "eval-0002": "attaque/ad hominem",
        "eval-0003": "appel/a l autorite",
        "eval-0004": "appel/a l autorite",
        "eval-0005": "flou/equivoque",
    })
    # r1 et r2 : parfaits sur les 5 items. r3 : se trompe sur deux items.
    perfect = {
        "eval-0001": "attaque/ad hominem",
        "eval-0002": "attaque/ad hominem",
        "eval-0003": "appel/a l autorite",
        "eval-0004": "appel/a l autorite",
        "eval-0005": "flou/equivoque",
    }
    third = dict(perfect)
    # Erreur qui change la BRANCHE : eval-0001 passe de 'attaque' a 'appel'.
    third["eval-0001"] = "appel/a l autorite"
    # Erreur qui reste DANS la branche : eval-0004 reste 'appel', le noeud change.
    third["eval-0004"] = "appel/a la popularite"
    make_rater(tmp_path, "r1", perfect)
    make_rater(tmp_path, "r2", perfect)
    make_rater(tmp_path, "r3", third)

    out_dir = tmp_path / "report"
    rc = scorer.main([
        "--key", str(key), "--annotations", str(tmp_path / "pass1"), "--out-dir", str(out_dir),
    ])
    assert rc == 0

    scores = json.loads((out_dir / "scores.json").read_text(encoding="utf-8"))
    assert scores["raters"] == ["r1", "r2", "r3"]
    assert scores["key_items"] == 5

    node = scores["levels"]["node"]
    # Chaque evaluateur note les 5 items : moyenne et taux groupe coincident.
    assert node["mean_equals_pooled"] is True
    assert node["pooled"]["rated"] == 15
    assert node["pooled"]["correct"] == 13
    assert node["mean_of_raters"] == pytest.approx(13 / 15)
    assert node["per_rater"]["r3"]["correct"] == 3
    assert node["per_rater"]["r1"]["coverage"] == 1.0

    branch = scores["levels"]["branch"]
    # Au niveau branche, r3 ne se trompe que sur eval-0001 : 14/15.
    assert branch["pooled"]["correct"] == 14
    assert branch["alpha"] > node["alpha"]

    # Aucun item sans majorite : r1 et r2 s'accordent toujours.
    assert scores["agreement"]["disagreements"] == 0
    assert scores["agreement"]["unanimous"] == 3
    assert (out_dir / "report.md").read_text(encoding="utf-8").startswith("# Mesure du test externe")


def test_item_sans_majorite_part_en_revue(tmp_path):
    key = make_key(tmp_path, {"eval-0001": "attaque/ad hominem", "eval-0002": "appel/a l autorite"})
    make_rater(tmp_path, "r1", {"eval-0001": "attaque/ad hominem", "eval-0002": "appel/a l autorite"})
    make_rater(tmp_path, "r2", {"eval-0001": "appel/a l autorite", "eval-0002": "appel/a l autorite"})
    make_rater(tmp_path, "r3", {"eval-0001": "flou/equivoque", "eval-0002": "appel/a l autorite"})

    out_dir = tmp_path / "report"
    scorer.main(["--key", str(key), "--annotations", str(tmp_path / "pass1"), "--out-dir", str(out_dir)])
    scores = json.loads((out_dir / "scores.json").read_text(encoding="utf-8"))

    assert scores["agreement"]["disagreements"] == 1
    item = scores["disagreement_items"][0]
    assert item["item_id"] == "eval-0001"
    assert item["reference_node"] == "attaque/ad hominem"
    assert item["counts"] == {"appel/a l autorite": 1, "attaque/ad hominem": 1, "flou/equivoque": 1}


def test_seuil_annonce_decide_du_verdict(tmp_path):
    """Le meme jeu, deux seuils : le verdict bascule -- le seuil est bien un parametre."""
    key = make_key(tmp_path, {"eval-0001": "attaque/ad hominem", "eval-0002": "appel/a l autorite"})
    make_rater(tmp_path, "r1", {"eval-0001": "attaque/ad hominem", "eval-0002": "appel/a l autorite"})
    make_rater(tmp_path, "r2", {"eval-0001": "flou/equivoque", "eval-0002": "appel/a l autorite"})

    out_dir = tmp_path / "report"
    scorer.main([
        "--key", str(key), "--annotations", str(tmp_path / "pass1"), "--out-dir", str(out_dir),
        "--alpha-node-threshold", "0.99", "--alpha-branch-threshold", "0.10",
    ])
    scores = json.loads((out_dir / "scores.json").read_text(encoding="utf-8"))
    assert scores["verdicts"]["alpha_node"] == "SEUIL NON ATTEINT"
    assert scores["verdicts"]["alpha_branch"] == "SEUIL ATTEINT"
    assert scores["thresholds"] == {"alpha_node": 0.99, "alpha_branch": 0.10}


def test_empreintes_des_entrees_consignees(tmp_path):
    key = make_key(tmp_path, {"eval-0001": "attaque/ad hominem", "eval-0002": "appel/a l autorite"})
    make_rater(tmp_path, "r1", {"eval-0001": "attaque/ad hominem", "eval-0002": "appel/a l autorite"})
    make_rater(tmp_path, "r2", {"eval-0001": "attaque/ad hominem", "eval-0002": "appel/a l autorite"})

    out_dir = tmp_path / "report"
    scorer.main(["--key", str(key), "--annotations", str(tmp_path / "pass1"), "--out-dir", str(out_dir)])
    scores = json.loads((out_dir / "scores.json").read_text(encoding="utf-8"))

    assert scores["inputs"]["key"]["sha256"] == scorer.sha256_of(key)
    assert set(scores["inputs"]["annotations"]) == {"r1", "r2"}
    assert scores["inputs"]["annotations"]["r1"]["sha256"] == scorer.sha256_of(tmp_path / "pass1" / "r1.jsonl")


# ------------------------------------------------------- fail-closed


def test_refuse_un_item_absent_de_la_cle(tmp_path):
    key = make_key(tmp_path, {"eval-0001": "attaque/ad hominem"})
    make_rater(tmp_path, "r1", {"eval-0001": "attaque/ad hominem"})
    make_rater(tmp_path, "r2", {"eval-9999": "attaque/ad hominem"})

    with pytest.raises(SystemExit) as excinfo:
        scorer.load_raters(tmp_path / "pass1", scorer.load_key(key, "/"), "/")
    assert "eval-9999" in str(excinfo.value)


def test_refuse_un_item_note_deux_fois(tmp_path):
    key = make_key(tmp_path, {"eval-0001": "attaque/ad hominem"})
    write_jsonl(tmp_path / "pass1" / "r1.jsonl", [
        {"item_id": "eval-0001", "node": "attaque/ad hominem"},
        {"item_id": "eval-0001", "node": "appel/a l autorite"},
    ])
    with pytest.raises(SystemExit) as excinfo:
        scorer.load_raters(tmp_path / "pass1", scorer.load_key(key, "/"), "/")
    assert "deux fois" in str(excinfo.value)


def test_refuse_une_famille_declaree_contredisant_le_noeud(tmp_path):
    """Colonnes transposees : la famille declaree doit etre la tete du noeud."""
    key = make_key(tmp_path, {"eval-0001": "attaque/ad hominem"})
    write_jsonl(tmp_path / "pass1" / "r1.jsonl", [
        {"item_id": "eval-0001", "family": "appel", "node": "attaque/ad hominem"},
    ])
    with pytest.raises(SystemExit) as excinfo:
        scorer.load_raters(tmp_path / "pass1", scorer.load_key(key, "/"), "/")
    assert "contredit" in str(excinfo.value)


def test_refuse_un_evaluateur_unique(tmp_path):
    key = make_key(tmp_path, {"eval-0001": "attaque/ad hominem"})
    make_rater(tmp_path, "r1", {"eval-0001": "attaque/ad hominem"})
    with pytest.raises(SystemExit) as excinfo:
        scorer.main([
            "--key", str(key), "--annotations", str(tmp_path / "pass1"),
            "--out-dir", str(tmp_path / "report"),
        ])
    assert "au moins deux evaluateurs" in str(excinfo.value)


def test_refuse_un_repertoire_sans_feuille(tmp_path):
    key = make_key(tmp_path, {"eval-0001": "attaque/ad hominem"})
    (tmp_path / "pass1").mkdir()
    with pytest.raises(SystemExit) as excinfo:
        scorer.main([
            "--key", str(key), "--annotations", str(tmp_path / "pass1"),
            "--out-dir", str(tmp_path / "report"),
        ])
    assert "rien a mesurer" in str(excinfo.value)


def test_refuse_un_noeud_sans_branche():
    """Un noeud qui commence par le separateur n'a pas de branche de premier niveau."""
    with pytest.raises(SystemExit) as excinfo:
        scorer.branch_of("/ad hominem", "/")
    assert "branche de premier niveau vide" in str(excinfo.value)


def test_alpha_est_borne(tmp_path):
    """Garde-fou de vraisemblance : l'alpha nominal reste dans [-1, 1]."""
    units = [["A", "B"], ["B", "A"], ["A", "B"], ["B", "A"]]
    alpha = scorer.krippendorff_alpha(units)["alpha"]
    assert -1.0 <= alpha <= 1.0
    assert math.isfinite(alpha)
