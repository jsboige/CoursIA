"""Tests de l'organe factual-mislabel (#18354 tranche 2).

Canon mesure sur App-5-Timetabling : « 3 salles » (x2, cellules 2 et 4)
et « (3 \\times 20)^8 » contredits par le stream committé
« Salles : 4 » / « (4 x 20)^8 = 1.68e+15 ». Echantillon sain : 0 FP / 30
carnets (GenAI/ML/GameTheory/IIT/Probas, seed 42).
"""

import json
import subprocess
import sys
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "check_factual_mislabel.py"


def _nb(cells):
    return {"cells": cells, "metadata": {}, "nbformat": 4, "nbformat_minor": 5}


def _md(src):
    return {"cell_type": "markdown", "metadata": {}, "source": src}


def _code(out_text):
    return {
        "cell_type": "code", "execution_count": 1, "metadata": {},
        "outputs": [{"output_type": "stream", "name": "stdout", "text": out_text}],
        "source": "print(1)",
    }


def _run(cells, tmp_path, *, units=None):
    p = tmp_path / "fixture.ipynb"
    p.write_text(json.dumps(_nb(cells), ensure_ascii=False), encoding="utf-8")
    args = [sys.executable, str(SCRIPT), "--json"]
    if units is not None:
        args.extend(["--units", units])
    args.append(str(p))
    r = subprocess.run(args, capture_output=True, text=True, encoding="utf-8")
    return r.returncode, json.loads(r.stdout)


DATA_STREAM = (
    "Donnees du probleme\n=======================\n"
    "Cours       : 8\nSalles      : 4\nCreneaux    : 20 (5 jours x 4 creneaux)\n"
    "Enseignants : 4\nEspace brut : (4 x 20)^8 = 1.68e+15\n"
)


def test_canonical_salle_contradiction(tmp_path):
    rc, out = _run(
        [_code("Imports OK"),
         _md("$$\\text{Espace brut} = (3 \\times 20)^8 = 60^8$$"),
         _md("## 2. Donnees"),
         _code(DATA_STREAM),
         _md("instance maitrisee : 8 cours, 3 salles, 20 creneaux.")],
        tmp_path,
    )
    assert rc == 1
    units = [f for f in out["findings"] if f["kind"] == "unit-count"]
    assert any(f["claimed"] == "3" and f["stream"] == [4] for f in units)
    tuples = [f for f in out["findings"] if f["kind"] == "tuple-formula"]
    assert tuples and tuples[0]["claimed"] == "(3 x 20)^"


def test_consistent_counts_pass(tmp_path):
    rc, out = _run(
        [_code(DATA_STREAM),
         _md("instance maitrisee : 8 cours, 4 salles, 20 creneaux, 4 enseignants.")],
        tmp_path,
    )
    assert rc == 0 and out["anomaly_count"] == 0


def test_subcount_not_contradiction(tmp_path):
    # « Dupont enseigne 2 cours » : sous-compte par entite, le total 8
    # du stream ne le contredit pas (3 faux positifs tues par cette
    # garde, mesures App-5 c.6)
    rc, out = _run(
        [_code(DATA_STREAM),
         _md("| Dupont enseigne 2 cours | Idem |\n| Martin enseigne 2 cours | Idem |\n3. Dupont et Martin ont chacun 2 cours.")],
        tmp_path,
    )
    assert rc == 0


def test_hyphen_compound_and_ratio_guarded(tmp_path):
    rc, out = _run(
        [_code(DATA_STREAM),
         _md("petites instances : 8 cours x 80 creneaux-salles theoriques, 4 creneaux/jour.")],
        tmp_path,
    )
    assert rc == 0


def test_absent_number_not_flagged_here(tmp_path):
    # l'absence pure (nombre introuvable) releve de stale-claim, pas de
    # factual-mislabel : aucun stream => aucune contradiction possible
    rc, out = _run(
        [_code("done"),
         _md("il y aurait 12 solutions au total environ.")],
        tmp_path,
    )
    assert rc == 0


# === #20035 : UNITS_EXTENDED -- la liste etendue ajoute des substantifs
# de comptage trouves sur les cotes hors-App-5 (carnet, lemme, modele,
# ...). Le scope `extended` est un opt-in explicite ; le defaut est `core`.


def test_20035_carnet_contradiction_in_extended(tmp_path):
    """Le cas fondateur #19918 : 8 carnets en prose vs 15 dans le stream.

    Le scope `extended` (opt-in explicite) doit attraper la contradiction --
    la liste UNITS historique (App-5) ne contient pas `carnet`, l'extension
    l'ajoute. La garde SUBCOUNT_CONTEXT_RE ne filtre pas (pas de mot
    `chacun`/`par`/...).
    """
    rc, out = _run(
        [_code("Listing de Serre100/\n================\n"
               "Carnets : 15\n"),
         _md("## Section 2\n\nLes 8 carnets couvrent les theoremes.")],
        tmp_path,
        units="extended",
    )
    assert rc == 1, (
        f"l'organe etendu DOIT attraper 8 vs 15 carnets : rc={rc}, out={out!r}")
    units = [f for f in out["findings"] if f["kind"] == "unit-count"]
    assert any(f["unit"] == "carnet" and f["claimed"] == "8"
               and f["stream"] == [15] for f in units), (
        f"finding carnet 8 vs 15 absent : {units!r}")


def test_20035_carnet_ignored_in_core_scope(tmp_path):
    """Le scope `core` NE doit PAS attraper le carnet -- c'est la
    portee historique d'App-5, qui n'a pas la couverture `carnet`.

    Ce test verifie que le garde-fou `--units core` fonctionne : un
    audit cible App-5 reste sur la portee d'origine, sans regression
    silencieuse introduite par l'extension.
    """
    rc, out = _run(
        [_code("Listing de Serre100/\n================\n"
               "Carnets : 15\n"),
         _md("## Section 2\n\nLes 8 carnets couvrent les theoremes.")],
        tmp_path,
        units="core",
    )
    assert rc == 0, (
        f"le scope core NE doit PAS attraper carnet (hors-App-5) : "
        f"rc={rc}, out={out!r}")
    assert out["anomaly_count"] == 0


def test_20035_subcount_guard_still_works_on_extended(tmp_path):
    """SUBCOUNT_CONTEXT_RE doit continuer a filtrer les sous-comptes
    pour les nouvelles unites (chacun, par, ...). Sans cette garde,
    l'extension ferait exploser le taux de FP.

    Cas verifie : la prose dit « dans chacun des 6 carnets, 3 lemmes »,
    le stream dit `Carnets : 15`. La garde `chacun` filtre la mention
    de 6, qui n'est PAS le total.
    """
    rc, out = _run(
        [_code("Carnets : 15\nLemmes par carnet : 3\n"),
         _md("Dans chacun des 6 carnets, on compte 3 lemmes par section.")],
        tmp_path,
        units="extended",
    )
    assert rc == 0, (
        f"les sous-comptes filtres par SUBCOUNT_CONTEXT_RE ne doivent "
        f"pas etre releves en `extended` : rc={rc}, out={out!r}")


def test_20035_lemme_count_contradiction(tmp_path):
    """Compteur Lean : 12 lemmes stream vs 9 lemmes prose.

    Cas de la serie Lean : un carnet de comptage peut imprimer
    `Lemmes : 12` (re-execution d'un script). Si la prose dit
    `9 lemmes`, c'est une derive.
    """
    rc, out = _run(
        [_code("Resultat du compteur :\nLemmes : 12\n"),
         _md("## Synthese\n\nLes 9 lemmes sont les suivants :\n")],
        tmp_path,
        units="extended",
    )
    assert rc == 1
    units = [f for f in out["findings"] if f["kind"] == "unit-count"]
    assert any(f["unit"] == "lemme" and f["claimed"] == "9"
               and f["stream"] == [12] for f in units), (
        f"finding lemme 9 vs 12 absent : {units!r}")


def test_20035_core_scope_is_default(tmp_path):
    """Le defaut (sans --units) est `core` : le cas carnet n'est PAS attrape.

    Pin structurel : l'arbitrage du coordinateur du 2026-10-21 fait du
    scope `core` le defaut (`extended` devient un opt-in explicite).
    Sur le corpus mesure, `extended` rend 36 findings pour 0 vrai
    positif : un defaut qui amplifie le bruit n'est pas un defaut.

    Ce test echoue si une future PR re-bascule le defaut sans un nouvel
    arbitrage explicite.
    """
    rc, out = _run(
        [_code("Carnets : 15\n"),
         _md("Les 8 carnets suivants ...")],
        tmp_path,
        # PAS d'argument --units : on teste le defaut.
    )
    assert rc == 0, (
        f"le scope par defaut DOIT etre `core` (cas carnet NON attrape) : "
        f"rc={rc}, out={out!r}")
    assert out["anomaly_count"] == 0


def test_20035_extended_scope_is_still_an_explicit_opt_in(tmp_path):
    """`--units extended` reste disponible et attrape toujours le cas carnet.

    L'arbitrage change le DEFAUT, pas la capacite : le scope etendu
    reste jouable explicitement pour un audit qui veut la detection
    large (et assume son bruit).
    """
    rc, out = _run(
        [_code("Carnets : 15\n"),
         _md("Les 8 carnets suivants ...")],
        tmp_path,
        units="extended",
    )
    assert rc == 1, (
        f"`--units extended` DOIT attraper le cas carnet : rc={rc}, out={out!r}")


def test_20956_numbered_list_not_misread_for_etapes(tmp_path):
    """Regression #20956 (Hermes FP 2026-10-15) : un stream qui imprime
    une liste numerotee sous un titre `Etapes:` ne doit PAS etre lu
    comme `etapes = N` ou N = 1 (le premier digit de la liste).

    Cas fondateur : `GenAI/Texte/03_Structured_Outputs.ipynb` cellule
    md 19, stream `Etapes:\\n  1. Preparer les ingredients\\n  2. ...`,
    prose `Les 10 etapes numerotees ...`. Avant fix, l'organe rendait
    `etapes = 1` (faux positif, classe nouvelle dans UNITS_EXTENDED).
    Apres fix (anchoring `[ \\t]*` autour du separateur), l'organe
    ne matche plus la classe FP et ne contredit pas la prose.

    Echantillon de garde : 1/9 carnets touches (Hermes, scope
    `extended`). Les streams `Etapes: 10` et `Etapes = 10` sur la
    meme ligne continuent d'attraper une contradiction reelle.
    """
    rc, out = _run(
        [_code("Etapes:\n  1. Preparer les ingredients\n  2. Melanger\n"
               "  3. Cuire 10 minutes\n  ...\n  10. Servir\n"),
         _md("## Section 3\n\nLes 10 etapes numerotees ci-dessus "
             "couvrent le protocole complet.")],
        tmp_path,
        units="extended",
    )
    assert rc == 0, (
        f"liste numerotee `Etapes:\\n  1.` NE doit PAS etre lue comme "
        f"`etapes = 1` (FP #20956 Hermes) : rc={rc}, out={out!r}")
    assert out["anomaly_count"] == 0
    # Sanity : sur la meme ligne, le pattern fonctionne toujours.
    rc_ok, out_ok = _run(
        [_code("Etapes: 10\n"),
         _md("Les 10 etapes numerotees ...")],
        tmp_path,
        units="extended",
    )
    # Cas ok : meme chiffre (10 == 10) -> pas de contradiction
    assert rc_ok == 0, (
        f"meme-ligne `Etapes: 10` / prose `10 etapes` : rc={rc_ok}, "
        f"out={out_ok!r}")
    # Sanity : contradiction reelle sur la meme ligne
    rc_contradict, out_contradict = _run(
        [_code("Etapes: 5\n"),
         _md("Les 10 etapes numerotees ...")],
        tmp_path,
        units="extended",
    )
    assert rc_contradict == 1, (
        f"contradiction reelle meme-ligne `Etapes: 5` vs prose `10 "
        f"etapes` DOIT etre attrapee : rc={rc_contradict}, "
        f"out={out_contradict!r}")


# === #20956 : confusion COMPTE / VALEUR -----------------------------------
#
# Un nombre suivi d'une partie decimale est une VALEUR, pas un compte.
# Sans garde, le stream « Recompense moyenne sur 10 episodes: 465.1 »
# donnait `episodes = 465`, contredit par les « 10 episodes » de la prose
# -- faux positif mesure sur
# RL/RL-02-Wrappers-Sauvegarde-Callbacks-Python.ipynb (cellule md 12),
# signale par la lane adjointe (cycle c2204).


def test_20956_valeur_decimale_nest_pas_un_compte(tmp_path):
    """LE cas fondateur : la prose dit « 10 episodes », le stream imprime
    une moyenne decimale. L'organe NE DOIT PAS relever de contradiction.

    Avant fix : le stream pattern lisait `episodes = 465` et l'organe
    rendait un FACTUAL_MISLABEL (claimed=10, stream=[465]) -- un FP pur,
    la prose etant la source de verite.
    """
    rc, out = _run(
        [_code("Recompense moyenne sur 10 episodes: 465.1\n"
               "Entropie finale : 0.82\n"),
         _md("## Resultats\n\nLa recompense moyenne sur 10 episodes est "
             "de 465.1 points.")],
        tmp_path,
        units="extended",
    )
    assert rc == 0, (
        f"une valeur decimale n'est PAS un compte : rc={rc}, out={out!r}")
    assert out["anomaly_count"] == 0


def test_20956_compte_entier_reste_un_compte(tmp_path):
    """CONTROLE POSITIF : la garde ne doit pas neutraliser un compte
    entier reel -- une contradiction reste attrapee."""
    rc, out = _run(
        [_code("Episodes: 7\n"),
         _md("La recompense moyenne est mesuree sur 10 episodes.")],
        tmp_path,
        units="extended",
    )
    assert rc == 1, (
        f"un compte entier reel reste un compte : rc={rc}, out={out!r}")
    units = [f for f in out["findings"] if f["kind"] == "unit-count"]
    assert any(f["unit"] == "episode" and f["claimed"] == "10"
               and f["stream"] == [7] for f in units), (
        f"finding episode 10 vs 7 absent : {units!r}")


def test_20956_compte_entier_coherent_ne_donne_rien(tmp_path):
    """Meme classe, chiffres concordants : aucun finding."""
    rc, out = _run(
        [_code("Episodes: 10\n"),
         _md("La recompense moyenne est mesuree sur 10 episodes.")],
        tmp_path,
        units="extended",
    )
    assert rc == 0, (
        f"10 episodes / 10 episodes : aucune contradiction : rc={rc}, "
        f"out={out!r}")


def test_20956_virgule_decimale_nest_pas_un_compte(tmp_path):
    """La meme garde doit couvrir la virgule decimale (format FR)."""
    rc, out = _run(
        [_code("Score moyen sur 12 iterations: 87,4\n"),
         _md("Le score moyen sur 12 iterations vaut 87,4 points.")],
        tmp_path,
        units="extended",
    )
    assert rc == 0, (
        f"virgule decimale : meme traitement que le point : rc={rc}, "
        f"out={out!r}")


# === #20956 (suite) : la reprise APRES le separateur ----------------------
#
# Le lookahead `(?!\d*[.,]\d)` refusait le nombre decimal, mais le moteur
# REPRENAIT apres le separateur : le `\b` entre « . » et « 1 » est une
# frontiere de mot. Mesure du 2026-10-21 (reserve du coordinateur sur
# #20956, point 2) :
#     '465.1 episodes'   -> ('1', 'episodes')
#     '87,4 iterations'  -> ('4', 'iterations')
# Le motif MD relisait donc un compte FABRIQUE a partir de la partie
# decimale d'une valeur. La borne gauche `(?<![\d.,])` le ferme.


def test_20956_reprise_apres_separateur_point_nest_pas_un_compte(tmp_path):
    """« 465.1 episodes » cote PROSE ne doit pas produire le compte 1.

    Avant fix : le motif MD relisait `(1, episodes)`, contredit par le
    « Episodes: 10 » du stream -- une contradiction FABRIQUEE.
    """
    rc, out = _run(
        [_code("Episodes: 10\n"),
         _md("La recompense moyenne sur 465.1 episodes vaut 465.1 points.")],
        tmp_path,
        units="extended",
    )
    assert rc == 0, (
        f"une valeur decimale relue comme un compte : rc={rc}, out={out!r}")
    assert out["anomaly_count"] == 0


def test_20956_reprise_apres_separateur_virgule_nest_pas_un_compte(tmp_path):
    """Meme cas avec la virgule decimale (format FR)."""
    rc, out = _run(
        [_code("Iterations: 12\n"),
         _md("Le score moyen sur 87,4 iterations vaut 87,4 points.")],
        tmp_path,
        units="extended",
    )
    assert rc == 0, (
        f"virgule decimale relue comme un compte : rc={rc}, out={out!r}")
    assert out["anomaly_count"] == 0


def test_20956_borne_gauche_ne_neutralise_pas_le_compte_entier(tmp_path):
    """CONTROLE POSITIF : la borne gauche ne doit pas neutraliser un
    compte entier reel cote prose -- une contradiction reste attrapee."""
    rc, out = _run(
        [_code("Episodes: 7\n"),
         _md("La recompense moyenne est mesuree sur 10 episodes.")],
        tmp_path,
        units="extended",
    )
    assert rc == 1, (
        f"un compte entier reel reste un compte : rc={rc}, out={out!r}")
    units = [f for f in out["findings"] if f["kind"] == "unit-count"]
    assert any(f["unit"] == "episode" and f["claimed"] == "10"
               and f["stream"] == [7] for f in units), (
        f"finding episode 10 vs 7 absent : {units!r}")
