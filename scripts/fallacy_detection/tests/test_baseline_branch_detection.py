#!/usr/bin/env python3
"""Tests de l'instrument de baselines de la Phase 3.

Le test decisif est `test_controle_de_fuite_detecte_une_fuite_construite` : il batit un
corpus ou l'etiquette est **entierement determinee par le scenario**, et exige que le
protocole groupe rende 0 la ou le protocole naif rend 1. Une implementation qui
ignorerait les groupes passerait tous les autres tests et echouerait celui-la.
"""

from __future__ import annotations

import json
import sys
from collections import Counter
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import baseline_branch_detection as bbd  # noqa: E402


def write_corpus(tmp_path: Path, rows: list[dict], name: str = "corpus.jsonl") -> Path:
    path = tmp_path / name
    path.write_text(
        "\n".join(json.dumps(row, ensure_ascii=False) for row in rows) + "\n",
        encoding="utf-8",
    )
    return path


def rows_for(families: dict[str, list[tuple[str, str]]]) -> list[dict]:
    """`{etiquette: [(scenario, texte), ...]}` -> lignes de corpus."""
    return [
        {"text": text, "family": label, "node_key": f"{label}-{i}", "scenario_path": group}
        for label, pairs in families.items()
        for i, (group, text) in enumerate(pairs)
    ]


# --- Macro-F1 : la mesure elle-meme ------------------------------------------------


def test_macro_f1_calcul_a_la_main():
    """Cas calcule a la main : F1(A) = 2/3, F1(B) = 0,8, macro = 11/15."""
    score, per_label = bbd.macro_f1(["a", "a", "b", "b"], ["a", "b", "b", "b"])
    assert per_label["a"] == pytest.approx(2 / 3)
    assert per_label["b"] == pytest.approx(0.8)
    assert score == pytest.approx(11 / 15)


def test_macro_f1_etiquette_inventee_dilue():
    """Une etiquette predite absente du vrai jeu compte 0 et dilue la moyenne."""
    score, per_label = bbd.macro_f1(["a", "a"], ["a", "z"])
    assert per_label["z"] == 0.0
    assert score == pytest.approx(1 / 3)


# --- Plis : le protocole -----------------------------------------------------------


def test_plis_groupes_ne_separent_jamais_un_scenario(tmp_path):
    """Propriete du protocole : chaque scenario tombe entierement dans un seul pli."""
    items = bbd.load_corpus(
        write_corpus(tmp_path, rows_for({
            "A": [("s1", "texte un"), ("s1", "texte deux"), ("s2", "texte trois")],
            "B": [("s3", "texte quatre"), ("s3", "texte cinq"), ("s4", "texte six")],
        })),
        "branch",
    )
    folds = bbd.grouped_folds(items, 2)
    assert sorted(i for fold in folds for i in fold) == list(range(len(items)))
    # Un scenario peut porter plusieurs paires, donc apparaitre plusieurs fois DANS un
    # pli : ce qui est interdit est qu'il apparaisse dans PLUSIEURS plis.
    folds_of_group: dict[str, set[int]] = {}
    for number, fold in enumerate(folds):
        for index in fold:
            folds_of_group.setdefault(items[index]["group"], set()).add(number)
    for group, numbers in folds_of_group.items():
        assert len(numbers) == 1, f"le scenario {group} est scinde sur les plis {sorted(numbers)}"
    seen = [items[i]["group"] for fold in folds for i in fold]
    assert Counter(seen) == Counter(item["group"] for item in items)


def test_plis_naifs_separent_bien_un_scenario_controle_positif():
    """Controle positif : le decoupage naif, lui, met un meme scenario des deux cotes.

    Sans ce test, rien ne prouve que les deux protocoles different -- et un protocole
    naif confondu avec le groupe rendrait le controle de fuite muet.
    """
    # Les scenarios sont volontairement groupes par blocs (deux premiers/trois derniers
    # items), jamais sur la parite : une alternance reglerait les groupes sur le
    # decoupage round-robin et aucun scenario ne serait scinde.
    items = [
        {"text": f"texte {i}", "label": "A" if i < 6 else "B", "group": "s1" if i < 6 else "s2"}
        for i in range(12)
    ]
    naive = bbd.stratified_folds(items, 2)
    folds_of_group: dict[str, set[int]] = {}
    for number, fold in enumerate(naive):
        for index in fold:
            folds_of_group.setdefault(items[index]["group"], set()).add(number)
    assert len(folds_of_group) == 2, "le pli naif doit couvrir tous les scenarios"
    for group, numbers in folds_of_group.items():
        assert len(numbers) == 2, f"le pli naif doit scinder le scenario {group}"


def test_plis_deterministes(tmp_path):
    """Deux appels sur le meme corpus rendent les memes plis, sans graine."""
    items = bbd.load_corpus(
        write_corpus(tmp_path, rows_for({
            "A": [(f"s{i % 3}", f"texte {i}") for i in range(6)],
            "B": [(f"s{i % 3 + 3}", f"autre {i}") for i in range(6)],
        })),
        "branch",
    )
    assert bbd.grouped_folds(items, 3) == bbd.grouped_folds(items, 3)
    assert bbd.stratified_folds(items, 3) == bbd.stratified_folds(items, 3)


# --- Le refus du niveau non mesurable ----------------------------------------------


def test_refuse_niveau_non_mesurable_en_nommant_le_deficit():
    """Le cas reel : 280 etiquettes, une paire chacune -> macro-F1 non mesurable."""
    support = Counter({f"noeud-{i}": 1 for i in range(280)})
    with pytest.raises(SystemExit) as excinfo:
        bbd.require_measurable(support, "node")
    message = str(excinfo.value)
    assert "non mesurable" in message
    assert "280 etiquettes" in message
    assert "support maximal 1" in message
    assert "plancher exige 2" in message


def test_accepte_niveau_au_support_suffisant():
    """Le meme plancher ne refuse pas un niveau ou chaque etiquette porte deux paires."""
    bbd.require_measurable(Counter({"A": 20, "B": 2}), "branch")


# --- Le controle de fuite : le test decisif ----------------------------------------


def test_controle_de_fuite_detecte_une_fuite_construite(tmp_path):
    """Corpus ou l'etiquette est determinee par le scenario : le groupe doit rendre 0.

    Chaque scenario porte sa propre etiquette ET son propre vocabulaire. Le pli naif
    retrouve donc l'etiquette par la formulation du scenario (macro-F1 = 1) ; le pli
    groupe voit des etiquettes jamais vues a l'entrainement (macro-F1 = 0). Un ecart
    plein est le signal que l'instrument doit produire.
    """
    rows = [
        {"text": f"jeton{g} mot commun numero {i}", "family": f"L{g}", "node_key": f"n{g}-{i}",
         "scenario_path": f"s{g}"}
        for g in range(4) for i in range(6)
    ]
    items = bbd.load_corpus(write_corpus(tmp_path, rows), "branch")
    grouped = bbd.evaluate(bbd.predictor_lexical, items, bbd.grouped_folds(items, 2))
    naive = bbd.evaluate(bbd.predictor_lexical, items, bbd.stratified_folds(items, 2))
    assert naive["macro_f1_mean"] == pytest.approx(1.0)
    assert grouped["macro_f1_mean"] == pytest.approx(0.0)
    assert naive["macro_f1_mean"] - grouped["macro_f1_mean"] == pytest.approx(1.0)


def test_baseline_lexicale_reussit_sur_corpus_separable_par_etiquette(tmp_path):
    """Controle positif du modele : deux etiquettes a vocabulaires disjoints, plis groupes."""
    rows = []
    for group, label, words in (("s0", "A", "alpha beta"), ("s1", "A", "alpha beta"),
                                ("s2", "B", "gamma delta"), ("s3", "B", "gamma delta")):
        for i in range(4):
            rows.append({"text": f"{words} remplissage {i}", "family": label,
                         "node_key": f"n-{group}-{i}", "scenario_path": group})
    items = bbd.load_corpus(write_corpus(tmp_path, rows), "branch")
    result = bbd.evaluate(bbd.predictor_lexical, items, bbd.grouped_folds(items, 2))
    assert result["macro_f1_mean"] == pytest.approx(1.0)


# --- Les baselines triviales -------------------------------------------------------


def test_majoritaire_ex_aequo_par_ordre_alphabetique():
    """Determinisme : a egalite de comptes, l'etiquette alphabetiquement premiere gagne."""
    items = [{"text": "x", "label": "b", "group": "s"}, {"text": "x", "label": "b", "group": "s"},
             {"text": "y", "label": "a", "group": "t"}, {"text": "y", "label": "a", "group": "t"}]
    assert bbd.predictor_majority(items, items, 0) == ["a", "a", "a", "a"]
    strong = [{"text": "x", "label": "b", "group": "s"}] * 3 + [{"text": "y", "label": "a", "group": "t"}]
    assert bbd.predictor_majority(strong, strong, 0) == ["b"] * 4


def test_aleatoire_reproductible_et_quantiles_ordonnes(tmp_path):
    """Meme graine = meme tirage ; l'intervalle publie est ordonne."""
    items = bbd.load_corpus(
        write_corpus(tmp_path, rows_for({
            "A": [(f"s{i}", f"texte {i}") for i in range(6)],
            "B": [(f"t{i}", f"autre {i}") for i in range(6)],
        })),
        "branch",
    )
    folds = bbd.grouped_folds(items, 3)
    first = bbd.evaluate(bbd.predictor_random(0, 1, 0), items, folds)
    second = bbd.evaluate(bbd.predictor_random(0, 1, 0), items, folds)
    other = bbd.evaluate(bbd.predictor_random(1, 1, 0), items, folds)
    assert first["macro_f1_mean"] == second["macro_f1_mean"]
    assert first["macro_f1_mean"] != other["macro_f1_mean"]
    scores = sorted([0.1, 0.2, 0.3, 0.4])
    assert bbd.quantile(scores, 0.025) <= bbd.quantile(scores, 0.975)


# --- Chargement et bout en bout ----------------------------------------------------


def test_load_corpus_fail_closed(tmp_path):
    """Champ manquant et texte vide font echouer le chargement, en nommant la ligne."""
    broken = write_corpus(tmp_path, [{"text": "ok", "family": "A", "scenario_path": "s"},
                                     {"text": "sans famille", "scenario_path": "s"}], name="broken.jsonl")
    with pytest.raises(SystemExit) as excinfo:
        bbd.load_corpus(broken, "branch")
    assert "family" in str(excinfo.value) and "Ligne 2" in str(excinfo.value)

    empty = write_corpus(tmp_path, [{"text": "   ", "family": "A", "scenario_path": "s"}], name="empty.jsonl")
    with pytest.raises(SystemExit) as excinfo:
        bbd.load_corpus(empty, "branch")
    assert "texte vide" in str(excinfo.value)


def test_bout_en_bout_ecrit_les_deux_rapports(tmp_path):
    """main() produit le JSON et la table markdown, avec l'ecart de fuite calcule."""
    corpus = write_corpus(tmp_path, rows_for({
        "A": [(f"s{i % 2}", f"alpha beta texte {i}") for i in range(8)],
        "B": [(f"t{i % 2}", f"gamma delta texte {i}") for i in range(8)],
    }))
    out_dir = tmp_path / "out"
    assert bbd.main(["--corpus", str(corpus), "--out-dir", str(out_dir),
                     "--folds", "2", "--random-draws", "5", "--seed", "7"]) == 0
    report = json.loads((out_dir / "baselines_branch.json").read_text(encoding="utf-8"))
    assert report["structure"]["rows"] == 16
    assert report["structure"]["node_labels"] == 16
    assert report["leakage"]["gap"] is not None
    assert report["baselines"]["majority_grouped"]["macro_f1_mean"] is not None
    assert report["baselines"]["random_grouped"]["draws"] == 5
    table = (out_dir / "baselines_branch.md").read_text(encoding="utf-8")
    assert "Ecart de fuite mesure" in table
    assert "non mesurable" in table


def test_bout_en_bout_refuse_le_niveau_noeud_sur_corpus_a_un_exemple(tmp_path):
    """Le niveau nœud est refuse des que chaque etiquette ne porte qu'une paire."""
    corpus = write_corpus(tmp_path, rows_for({
        "A": [("s0", "alpha beta"), ("s1", "alpha gamma")],
        "B": [("s2", "delta epsilon"), ("s3", "delta zeta")],
    }))
    out_dir = tmp_path / "out_node"
    with pytest.raises(SystemExit) as excinfo:
        bbd.main(["--corpus", str(corpus), "--out-dir", str(out_dir), "--level", "node"])
    assert "non mesurable" in str(excinfo.value)
    assert not out_dir.exists(), "rien ne doit etre ecrit quand la mesure est refusee"
