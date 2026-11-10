#!/usr/bin/env python3
"""Tests de l'instrument de baselines de la Phase 3.

Le test decisif est `test_controle_de_fuite_detecte_une_fuite_construite` : il batit un
corpus ou l'etiquette est **entierement determinee par le scenario**, et exige que le
protocole groupe rende 0 la ou le protocole naif rend 1. Une implementation qui
ignorerait les groupes passerait tous les autres tests et echouerait celui-la.
"""

from __future__ import annotations

import builtins
import csv
import json
import math
import random
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
    assert "280 sous le plancher de 2 paires" in message
    assert "support minimal 1" in message
    assert "Etiquettes en deca" in message
    assert "noeud-0 (1)" in message


def test_refus_nomme_le_support_minimal_et_non_le_maximal():
    """Un corpus refuse pour une etiquette pauvre ne doit pas annoncer un support eleve.

    Le message d'origine annoncait le support *maximal* : pour un corpus dont
    une etiquette porte 1 paire et dont les autres en portent 14, il lisait
    « support maximal 14, plancher exige 2 » -- un refus qui se contredit.
    """
    support = Counter({"noeud-riche": 14, "noeud-pauvre": 1})
    with pytest.raises(SystemExit) as excinfo:
        bbd.require_measurable(support, "node")
    message = str(excinfo.value)
    assert "support minimal 1" in message
    assert "support maximal 14" in message
    assert "noeud-pauvre (1)" in message


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


# --- Baseline a regles : dictionnaires de taxonomie ---------------------------------


def write_taxonomy(tmp_path: Path, rows: list[dict], name: str = "taxo.csv") -> Path:
    """Taxonomie synthetique au schema sophismes (colonnes requises par detect_schema)."""
    path = tmp_path / name
    fields = ["PK", "Famille", "nom_vulgarisé", "desc_fr", "example_fr"]
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        for row in rows:
            writer.writerow({f: row.get(f, "") for f in fields})
    return path


def test_lit_taxonomie_et_exclut_les_exemples(tmp_path):
    """Le dictionnaire prend titres et definitions, et **jamais** les champs example_*.

    Le jeton `zorglub` ne vit que dans `example_fr` : s'il apparait dans le
    dictionnaire, la regle d'anti-circularite de la tranche A est enfreinte.
    """
    taxo = write_taxonomy(tmp_path, [
        {"PK": "1", "Famille": "A", "nom_vulgarisé": "Appel au tiroir",
         "desc_fr": "Vous inventez un tiroir", "example_fr": "zorglub zorglub"},
        {"PK": "2", "Famille": "B", "nom_vulgarisé": "Erreur de comptage",
         "desc_fr": "Vous comptez mal", "example_fr": "zorglub"},
    ])
    lexicon, report = bbd.load_lexicon([taxo], {"A", "B"})
    assert "tiroir" in lexicon["A"] and "comptage" in lexicon["B"] or "comptez" in lexicon["B"]
    assert "zorglub" not in lexicon["A"] and "zorglub" not in lexicon["B"]
    assert report["A"]["nodes"] == 1 and report["B"]["nodes"] == 1


def test_schema_de_taxonomie_inconnu_refuse(tmp_path):
    """Un CSV sans les colonnes d'une taxonomie Argumentum est refuse, pas devine."""
    path = tmp_path / "inconnu.csv"
    path.write_text("a,b\n1,2\n", encoding="utf-8")
    with pytest.raises(SystemExit) as excinfo:
        bbd.load_lexicon([path], {"A"})
    assert "schema inconnu" in str(excinfo.value)


def test_dictionnaire_vide_refuse_en_nommant_la_famille(tmp_path):
    """Une famille sans aucun jeton de regle est nommee, elle ne passe pas inapercue."""
    taxo = write_taxonomy(tmp_path, [
        {"PK": "1", "Famille": "A", "nom_vulgarisé": "Titre A", "desc_fr": "Definition A"},
    ])
    with pytest.raises(SystemExit) as excinfo:
        bbd.load_lexicon([taxo], {"A", "Sans_regle"})
    assert "Sans_regle" in str(excinfo.value)
    assert "Dictionnaire vide" in str(excinfo.value)


def test_baseline_a_regles_choisit_par_couverture_ponderee(tmp_path):
    """Le texte partageant le vocabulaire d'une famille est attribue a cette famille."""
    taxo = write_taxonomy(tmp_path, [
        {"PK": "1", "Famille": "A", "nom_vulgarisé": "Tiroir", "desc_fr": "Vous inventez un tiroir secret"},
        {"PK": "2", "Famille": "B", "nom_vulgarisé": "Comptage", "desc_fr": "Vous comptez mal les votes"},
    ])
    lexicon, _ = bbd.load_lexicon([taxo], {"A", "B"})
    predict = bbd.make_rules_predictor(lexicon, bbd.idf_over_families(lexicon), ["A", "B"])
    assert predict("tu inventez un tiroir secret dans ton raisonnement") == "A"
    assert predict("tu comptes mal les votes") == "B"


def test_baseline_a_regles_sans_entrainement():
    """Le predicteur de regles ignore l'entrainement : la mesure porte sur le corpus entier."""
    predict = bbd.make_rules_predictor({"A": {"alpha"}, "B": {"beta"}},
                                       {"alpha": 1.0, "beta": 1.0}, ["A", "B"])
    items = [{"text": "alpha alpha", "label": "A", "group": "s"},
             {"text": "beta", "label": "B", "group": "t"}]
    result = bbd.evaluate_whole(lambda text: predict(text), items)
    assert result["macro_f1"] == pytest.approx(1.0)
    assert result["accuracy"] == pytest.approx(1.0)
    assert result["n"] == 2


def test_bout_en_bout_ecrit_les_deux_rapports(tmp_path):
    """main() produit le JSON et la table markdown, avec l'ecart de fuite calcule."""
    corpus = write_corpus(tmp_path, rows_for({
        "A": [(f"s{i % 2}", f"alpha beta texte {i}") for i in range(8)],
        "B": [(f"t{i % 2}", f"gamma delta texte {i}") for i in range(8)],
    }))
    taxo = write_taxonomy(tmp_path, [
        {"PK": "1", "Famille": "A", "nom_vulgarisé": "Alpha", "desc_fr": "alpha beta"},
        {"PK": "2", "Famille": "B", "nom_vulgarisé": "Gamma", "desc_fr": "gamma delta"},
    ])
    out_dir = tmp_path / "out"
    assert bbd.main(["--corpus", str(corpus), "--out-dir", str(out_dir), "--taxonomy", str(taxo),
                     "--folds", "2", "--random-draws", "5", "--seed", "7"]) == 0
    report = json.loads((out_dir / "baselines_branch.json").read_text(encoding="utf-8"))
    assert report["structure"]["rows"] == 16
    assert report["structure"]["node_labels"] == 16
    assert report["leakage"]["gap"] is not None
    assert report["baselines"]["majority_grouped"]["macro_f1_mean"] is not None
    assert report["baselines"]["random_grouped"]["draws"] == 5
    assert report["baselines"]["rules_full"]["accuracy"] == pytest.approx(1.0)
    assert report["lexicon"]["families"]["A"]["nodes"] == 1
    table = (out_dir / "baselines_branch.md").read_text(encoding="utf-8")
    assert "Ecart de fuite mesure" in table
    assert "non mesurable" in table
    assert "Ce que la baseline a regles a montre, contre l'attente" in table
    assert "Dictionnaires de la baseline a regles" in table


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


# --- Le rendu : la prose suit les donnees, jamais l'inverse -------------------------
#
# Les trois rendus ci-dessous ont ete trouves par la prevalidation adjointe sur #20234 :
# la prose de render_report etait gelee (verdict « inferieur a l'aleatoire », familles
# citees en dur, « non mesurable » inconditionnel), si bien qu'un corpus aux valeurs
# inverses produisait un rapport faux sans qu'aucun test ne le voie. Ces tests portent
# sur des rapports synthetiques : ils eprouvent le rendu, pas la mesure.


def _synthetic_report() -> dict:
    """Rapport minimal consommable par render_report, a surcharger par test."""
    return {
        "corpus": {"path": "corpus.jsonl", "sha256": "0" * 64},
        "level": "branch",
        "structure": {"rows": 40, "labels": 14, "support_min": 2, "support_max": 4,
                      "groups": 25, "group_max_reuse": 3,
                      "node_labels": 28, "node_support_max": 1},
        "node_level": {"measurable": False, "labels": 28, "support_max": 1, "floor": 2},
        "lexicon": {"taxonomies": ["taxo.csv"], "families": {
            "Grande famille": {"nodes": 30, "tokens": 1816},
            "Moyenne": {"nodes": 10, "tokens": 500},
            "Petite famille": {"nodes": 3, "tokens": 146},
        }},
        "baselines": {
            "majority_grouped": {"n": 40, "macro_f1_mean": 0.05, "macro_f1_std": 0.01},
            "random_grouped": {"draws": 200, "macro_f1_mean": 0.0628,
                               "macro_f1_p2_5": 0.0371, "macro_f1_p97_5": 0.0919},
            "lexical_centroid_grouped": {"macro_f1_mean": 0.2198, "macro_f1_std": 0.02},
            "lexical_centroid_naive": {"macro_f1_mean": 0.2291, "macro_f1_std": 0.02},
            "rules_full": {"n": 40, "macro_f1": 0.0328, "accuracy": 0.075,
                           "labels_never_predicted": ["Argument pertinent",
                                                      "Honnêteté intellectuelle"],
                           "worst_labels": ["Argument pertinent"]},
        },
        "leakage": {"grouped_mean": 0.2198, "naive_mean": 0.2291, "gap": 0.0093},
    }


def test_rendu_verdict_regles_calcule_depuis_les_valeurs():
    """Un corpus ou la regle bat l'aleatoire ne doit pas rendre « inferieure »/« battue ».

    La prose gelee affirmait l'echec quel que soit le corpus : inverser la comparaison
    devait suffire a faire mentir le rapport.
    """
    report = _synthetic_report()
    report["baselines"]["rules_full"]["macro_f1"] = 0.5
    table = bbd.render_report(report)
    assert "superieure a l'aleatoire" in table
    assert "inferieur a l'aleatoire" not in table
    assert "battue par le tirage uniforme" not in table

    report["baselines"]["rules_full"]["macro_f1"] = 0.01
    table = bbd.render_report(report)
    assert "inferieure a l'aleatoire" in table
    assert "battue par le tirage uniforme" in table
    assert "superieure a l'aleatoire" not in table


def test_rendu_familles_citees_viennent_des_dictionnaires():
    """Les familles citees en exemple sont les extremes mesures, pas des noms en dur."""
    table = bbd.render_report(_synthetic_report())
    assert "`Grande famille`" in table and "1816 jetons" in table
    assert "`Petite famille`" in table and "146 jetons" in table
    assert "Influence" not in table
    assert "Justesse lexicale" not in table
    assert "sept familles" not in table


def test_rendu_niveau_noeud_suit_le_temoin_mesurable():
    """« mesurable » du JSON commande la prose — dans les deux sens, sans « None »."""
    report = _synthetic_report()
    report["node_level"] = {"measurable": True, "labels": 10, "support_max": 2, "floor": 2}
    table = bbd.render_report(report)
    assert "**mesurable**" in table
    assert "non mesurable" not in table
    assert "None etiquettes" not in table

    report["node_level"] = {"measurable": False, "labels": 28, "support_max": 1, "floor": 2}
    table = bbd.render_report(report)
    assert "non mesurable" in table
    assert "None etiquettes" not in table
    assert "28 etiquettes pour 40 paires" in table


def test_run_niveau_noeud_rend_des_etiquettes_comptees(tmp_path):
    """Une passe --level node qui a mesure ne rend ni « None etiquettes » ni « non mesurable »."""
    rows = [
        {"text": f"alpha beta texte {i}", "family": "A", "node_key": f"n{g}",
         "scenario_path": f"s{g}"}
        for g in range(4) for i in range(2)
    ] + [
        {"text": f"gamma delta texte {i}", "family": "B", "node_key": f"m{g}",
         "scenario_path": f"t{g}"}
        for g in range(4) for i in range(2)
    ]
    # Au niveau nœud, les etiquettes du corpus SONT les cles de nœud : la taxonomie
    # doit donc couvrir les huit nœuds, pas les deux familles.
    nodes = [(f"n{g}", "alpha beta") for g in range(4)] + [(f"m{g}", "gamma delta") for g in range(4)]
    taxo = write_taxonomy(tmp_path, [
        {"PK": str(index + 1), "Famille": node,
         "nom_vulgarisé": f"Titre {node}", "desc_fr": definition}
        for index, (node, definition) in enumerate(nodes)
    ])
    report = bbd.run(write_corpus(tmp_path, rows), "node", 2, 3, 7, [taxo])
    assert report["node_level"]["measurable"] is True
    assert report["node_level"]["labels"] == report["structure"]["labels"] == 8
    assert report["node_level"]["support_max"] == 2
    table = bbd.render_report(report)
    assert "nœud" in table.splitlines()[0]
    assert "**mesurable**" in table
    assert "non mesurable" not in table
    assert "None etiquettes" not in table


def test_rendu_ecart_de_fuite_distingue_observation_et_attribution():
    """L'ecart mesure est rapporte ; l'attribution entiere au recouvrement ne l'est plus.

    Un temoin a scenarios singletons (aucun recouvrement possible) reproduit un ecart de
    la meme famille : la difference de protocole n'attribue pas le gap a elle seule.
    """
    table = bbd.render_report(_synthetic_report())
    assert "0.0093" in table
    assert "ecart observe" in table
    assert "attribuables au recouvrement de scenario" not in table
    assert "une cause possible" in table


def test_rendu_en_tete_dit_le_niveau_reel():
    """L'en-tete suit report['level'] : « branche » n'est plus ecrit en dur."""
    report = _synthetic_report()
    assert "branche" in bbd.render_report(report).splitlines()[0]

    report["level"] = "node"
    assert "nœud" in bbd.render_report(report).splitlines()[0]


# --- Equivalence des versions indexees ----------------------------------------------
# Les deux chemins predits par l'instrument ont une version de reference (balayage de
# toutes les etiquettes) et une version indexee (index inverse). Elles doivent rendre
# le meme label, au bit pres : sinon les chiffres publies ne sont pas reproductibles.


def _reference_rules(lexicon, weights, labels):
    """Reference de la baseline a regles : balayage de toutes les etiquettes."""
    def predict_one(text: str) -> str:
        tokens = sorted(set(bbd.tokenize(text)))
        best_label, best_score = None, None
        for label in labels:
            score = sum(weights.get(term, 0.0) for term in tokens if term in lexicon[label])
            if best_score is None or score > best_score:
                best_label, best_score = label, score
        return best_label
    return predict_one


def test_regles_indexees_equivalent_au_balayage():
    """L'index inverse ne change aucune prediction, y compris sur les ex aequo."""
    lexicon = {"A": {"alpha", "beta"}, "B": {"beta", "gamma"}, "C": {"gamma"}}
    weights = {"alpha": 2.0, "beta": 1.0, "gamma": 1.0}
    labels = ["A", "B", "C"]
    rapide = bbd.make_rules_predictor(lexicon, weights, labels)
    reference = _reference_rules(lexicon, weights, labels)
    for text in ("alpha", "beta", "gamma", "alpha beta", "gamma gamma", "rien du tout",
                 "beta gamma", "alpha gamma"):
        assert rapide(text) == reference(text), text


def test_regles_indexees_equivalence_avec_ordre_d_etiquettes_non_trie():
    """Le departage suit l'ordre donne des etiquettes, pas l'ordre alphabétique."""
    lexicon = {"A": {"alpha"}, "B": {"alpha"}}
    weights = {"alpha": 1.0}
    for labels in (["A", "B"], ["B", "A"]):
        rapide = bbd.make_rules_predictor(lexicon, weights, labels)
        reference = _reference_rules(lexicon, weights, labels)
        assert rapide("alpha") == reference("alpha") == labels[0]


def test_centroide_indexe_equivalent_a_la_reference():
    """`predict_indexed` rend le meme label que `predict`, au bit pres."""
    rng = random.Random(7)
    centroids = {
        label: {feature: rng.random() for feature in range(rng.randint(1, 6))}
        for label in ("A", "B", "C", "D")
    }
    index = bbd.TfidfCentroids.index(centroids)
    for _ in range(200):
        vector = {feature: rng.random()
                  for feature in range(10) if rng.random() < 0.4}
        assert (bbd.TfidfCentroids.predict_indexed(vector, centroids, index)
                == bbd.TfidfCentroids.predict(vector, centroids))


def test_centroide_indexe_ex_aequo_garde_la_premiere_etiquette():
    """A score egal, la premiere etiquette en ordre alphabetique reste la meilleure."""
    centroids = {"A": {0: 1.0}, "B": {0: 1.0}, "C": {1: 1.0}}
    index = bbd.TfidfCentroids.index(centroids)
    assert bbd.TfidfCentroids.predict_indexed({0: 1.0}, centroids, index) == "A"
    assert bbd.TfidfCentroids.predict({0: 1.0}, centroids) == "A"


def test_dictionnaire_de_noeud_joint_par_famille_et_cle(tmp_path):
    """Un noeud se rattache a sa ligne de taxonomie par (famille, cle)."""
    taxo = write_taxonomy(tmp_path, [
        {"PK": "798", "Famille": "Abus de langage", "nom_vulgarisé": "Appel au Emotionnel",
         "desc_fr": "Vous validez une affirmation par son ton", "example_fr": "zorglub"},
        {"PK": "12", "Famille": "Influence", "nom_vulgarisé": "Appel a l'autorite",
         "desc_fr": "Vous invoquez une autorite", "example_fr": "zorglub"},
    ])
    lexicon, report = bbd.load_lexicon(
        [taxo], {"F798", "V12"}, "node",
        {"F798": "Abus de langage", "V12": "Influence"},
        {"F798": "798", "V12": "12"},
    )
    assert "emotionnel" in lexicon["F798"]
    assert "autorite" in lexicon["V12"]
    assert "zorglub" not in lexicon["F798"] and "zorglub" not in lexicon["V12"]
    assert report["F798"]["nodes"] == 1


def test_dictionnaire_de_noeud_introuvable_refuse_en_nommant_le_noeud(tmp_path):
    """Un noeud absent des taxonomies est nomme, il ne passe pas inapercu."""
    taxo = write_taxonomy(tmp_path, [
        {"PK": "1", "Famille": "A", "nom_vulgarisé": "Titre A", "desc_fr": "Definition A"},
    ])
    with pytest.raises(SystemExit) as excinfo:
        bbd.load_lexicon([taxo], {"F999"}, "node", {"F999": "A"}, {"F999": "999"})
    assert "F999" in str(excinfo.value)


def test_macro_f1_un_passage_equivalent_au_temoin():
    """Le comptage en un passage rend le meme score, au bit pres, que le temoin."""
    rng = random.Random(7)
    for taille, etiquettes in ((40, 5), (300, 37)):
        vrais = [f"L{i % etiquettes}" for i in range(taille)]
        predits = [rng.choice([f"L{i % etiquettes}" for i in range(etiquettes)] + ["L999"])
                   for _ in range(taille)]
        score, par_etiquette = bbd.macro_f1(vrais, predits)
        score_ref, par_etiquette_ref = bbd.macro_f1_reference(vrais, predits)
        assert score == score_ref
        assert par_etiquette == par_etiquette_ref


def test_macro_f1_etiquette_absente_du_test_comptabilisee():
    """Une etiquette predite mais jamais vraie dilue la moyenne (par convention)."""
    score, par_etiquette = bbd.macro_f1(["A", "A"], ["A", "B"])
    assert par_etiquette["B"] == 0.0
    # A : tp=1, fp=0, fn=1 -> F1 = 2/3 ; B : predit mais jamais vrai -> 0.
    assert score == pytest.approx(1 / 3)


def test_niveau_branche_identique_a_la_reference_commitee(monkeypatch):
    """La non-regression du niveau branche est portee par la CI, pas affirmee.

    `data/teacher/baselines_branch.json` est le rapport produit par l'instrument
    sur le corpus commite, avant la refonte de la macro-F1. Ce test rejoue
    l'instrument sur ce meme corpus et exige l'egalite stricte des rapports :
    toute derive du niveau branche (comptage, plis, lexique, fuite) fait
    echouer la CI au lieu de reposer sur une affirmation de la lane.
    """
    racine = Path(__file__).resolve().parents[3]
    corpus = "MyIA.AI.Notebooks/GenAI/FallacyDetection/data/teacher/val_fr.jsonl"
    reference = racine / ("MyIA.AI.Notebooks/GenAI/FallacyDetection/data/teacher/"
                          "baselines_branch.json")
    monkeypatch.chdir(racine)
    rapport = bbd.run(Path(corpus), "branch", 5, 200, 42, None)
    attendu = json.loads(reference.read_text(encoding="utf-8"))
    # Le corpus est celui de la reference : un corpus change invalide la comparaison.
    assert rapport["corpus"]["sha256"] == attendu["corpus"]["sha256"]
    assert rapport == attendu


# --- Semantique de sommation : le rapport ne doit dependre d'aucune version de CPython --


def _somme_sous_semantique(elements, semantique: str):
    """Somme de flottants sous une semantique imposee (CPython 3.11 / 3.12+ / exacte).

    Les entiers restent exacts dans les trois cas : seule la somme de flottants change.
    """
    valeurs = list(elements)
    if semantique == "fsum" and any(isinstance(valeur, float) for valeur in valeurs):
        return math.fsum(valeurs)
    total = 0
    compensation = 0.0
    for element in valeurs:
        if semantique == "neumaier" and isinstance(total, float) and isinstance(element, float):
            somme = total + element
            if abs(total) >= abs(element):
                compensation += (total - somme) + element
            else:
                compensation += (element - somme) + total
            total = somme
        else:
            total = total + element
    return total + compensation if semantique == "neumaier" else total


def test_le_rapport_ne_depend_pas_de_la_semantique_de_sum(monkeypatch):
    """`sum` sur les flottants a change de semantique en CPython 3.12 (compensation).

    Le test rejoue la baseline a regles sous trois semantiques emulees -- naive
    (3.11), compensee (3.12+), exacte (`math.fsum`) -- et exige le meme rapport.
    L'instrument ne doit donc dependre d'aucune d'elles : sinon le meme corpus
    donne un rapport different selon la version de l'interpreteur, et le garde de
    non-regression ne peut pas passer a la fois en local et en CI.
    """
    lexique = {"A": {"t1", "t2", "t3"}, "B": {"t4"}}
    # 1e16 + 1,0 - 1e16 : la somme naive rend 0,0, la somme exacte rend 1,0.
    poids = {"t1": 1e16, "t2": 1.0, "t3": -1e16, "t4": 0.5}
    items = [{"text": "t1 t2 t3 t4", "label": "A", "node_key": "A-0", "scenario_path": "s1"}]
    rapports = {}
    for semantique in ("naive", "neumaier", "fsum"):
        monkeypatch.setattr(
            builtins, "sum",
            lambda elements, semantique=semantique: _somme_sous_semantique(elements, semantique),
        )
        predicteur = bbd.make_rules_predictor(lexique, poids, ["A", "B"])
        rapports[semantique] = bbd.evaluate_whole(predicteur, items)
    assert rapports["naive"] == rapports["neumaier"] == rapports["fsum"]
