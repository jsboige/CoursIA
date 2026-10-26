#!/usr/bin/env python3
"""Garde d'integrite STRUCTURELLE de la taxonomie Argumentum vendorisee.

POURQUOI CET ORGANE EXISTE
--------------------------
`test_argumentum_snapshot_integrity.py` certifie que la copie locale du CSV
est **octet pour octet** celle du pin declare. C'est la garantie de
provenance. Mais la provenance ne dit rien de la **coherence interne** du
fichier, et la coherence interne est ce que les carnets de la serie
consomment reellement :

- `argumentum_taxonomy_explorer.py` monte l'arbre des sophismes a partir de
  la colonne `path` et descend la hierarchie ;
- `Argumentation-Onto-02-CrossLinks-CSV-Python.ipynb` lit les huit colonnes
  `crossLink_*` comme les aretes d'un graphe ;
- `cartesian_dataset_builder.py` echantillonne des noeuds par famille.

Un CSV peut etre fidele a son pin et structuralement casse : une cible
`crossLink_*` qui ne designe aucun noeud disparait **silencieusement** de
tous les carnets (le lien ne resolve vers rien, et rien ne dit que rien ne
resolvait), une famille sans parent disparait de la hierarchie, un `depth`
faux deplace un noeud d'un niveau dans les sorties.

C'est la meme famille de panne que celle documentee dans le module voisin
(sept semaines de derive silencieuse), prise par l'autre bout : non pas
« le fichier a change », mais « le fichier ne se tient pas lui-meme ».

CE QUE CHAQUE TEST ATTRAPE
--------------------------
1. ``test_cles_primaires_uniques`` / ``test_chemins_uniques`` -- les
   identifiants du graphe (PK et `path`) designent-ils un noeud unique ?
   Un `path` duplique rend l'arbre ambigu : deux noeuds se partagent une
   place, et la descendee des enfants les confond.
2. ``test_cibles_crosslink_resolues`` -- chaque cible d'une relation
   `crossLink_*` designe-t-elle un noeud de l'arbre ? C'est l'integrite
   referentielle du graphe, la propriete la plus utile aux carnets.
3. ``test_arbre_ferme`` -- chaque noeud a-t-il un parent present ? Les sept
   familles de premier niveau se rattachent a la racine `0`, pas a une
   chaine vide : le test verifie les deux cas.
4. ``test_absence_boucle_directe`` -- un noeud ne se lie-t-il pas a lui-meme ?
5. ``test_profondeur_coherente`` -- la colonne `depth` porte-t-elle le
   nombre de segments du `path` ? La copie amont en porte une deviation
   documentee (PK 824) : la tolerance (1 %) laisse passer cet ecart lais
   rouge une corruption systematique.
6. ``test_cellule_multi_cibles_decoupee`` -- une cellule portant plusieurs
   cibles separees par `;` donne-t-elle **une arete par cible** ? (40
   cellules de la copie courante.)
7. ``test_reciprocite_calculee_sur_un_graphe_minimal`` -- la reciprocite
   mesure-t-elle bien une arete inverse, et pas l'arete elle-meme ?

LES INVARIANTS SONT INDEPENDANTS DU CONTENU
-------------------------------------------
Aucun test ne fige un compte de lignes, de colonnes ou d'aretes : ces
comptes changent a chaque resynchronisation amont (PR #22415 en cours), et
un test qui les fige rougit sur un CSV sain. Ce qui est fige, ce sont les
**relations** entre ces comptes -- et les invariants de coherence, qui
doivent tenir sur toute revision de la taxonomie.

QUE FAIRE QUAND C'EST ROUGE
---------------------------
Ne pas « reparer » en editant l'assertion. Un rouge signifie que la copie
locale n'est plus coherente : verifier d'abord l'amont
(`git show <pin>:"Cards/Fallacies/Argumentum Fallacies - Taxonomy.csv"`),
puis resynchroniser, regenerer le manifeste, et re-executer les carnets
dont les sorties sont indexees sur ces donnees. Si l'amont lui-meme porte
l'anomalie, c'est une correction amont qui s'impose, pas un contournement
local.

Hermetique : stdlib only, aucun acces reseau, aucun appel a git.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
_SCRIPTS = HERE.parent.parent
if str(_SCRIPTS) not in sys.path:
    sys.path.insert(0, str(_SCRIPTS))

from fallacy_detection.argumentum_taxonomy_integrity import (  # noqa: E402
    ROOT_PATH,
    check_invariants,
    format_report,
    load_rows,
    main,
    parse_edges,
    structural_profile,
)


@pytest.fixture(scope="module")
def rows() -> list[dict[str, str]]:
    """Les lignes de la taxonomie locale (lecture unique pour le module)."""
    return load_rows()


@pytest.fixture(scope="module")
def profile(rows: list[dict[str, str]]) -> dict:
    """Le profil structurel mesure sur la taxonomie locale."""
    return structural_profile(rows)


def test_cles_primaires_uniques(profile: dict) -> None:
    """Chaque PK designe un noeud unique."""
    assert not profile["duplicate_pks"], f"PK dupliques : {profile['duplicate_pks']}"


def test_chemins_uniques(profile: dict) -> None:
    """Chaque `path` designe un noeud unique."""
    assert not profile["duplicate_paths"], f"paths dupliques : {profile['duplicate_paths']}"


def test_cibles_crosslink_resolues(profile: dict) -> None:
    """Chaque cible d'une relation `crossLink_*` designe un noeud de l'arbre."""
    assert profile["edges"] > 0, "le CSV ne porte aucune relation crossLink : le test est aveugle"
    assert not profile["dangling_targets"], (
        f"cibles crossLink sans noeud : {profile['dangling_targets']}"
    )


def test_arbre_ferme(profile: dict) -> None:
    """Chaque noeud a un parent present dans le CSV."""
    assert not profile["orphan_paths"], f"chemins sans parent : {profile['orphan_paths']}"


def test_les_familles_de_premier_niveau_pendent_a_la_racine() -> None:
    """Les sept familles (`path` d'un segment) se rattachent a la racine `0`.

    La convention est celle de l'explorateur de la serie, qui reparente les
    noeuds de profondeur 1 sous `0` : sans elle, l'arbre aurait sept racines
    au lieu d'une.
    """
    rows = [
        {"PK": "0", "path": ROOT_PATH, "depth": "0"},
        {"PK": "1", "path": "1", "depth": "1"},
        {"PK": "2", "path": "1.1", "depth": "2"},
    ]
    profile = structural_profile(rows)
    assert not profile["orphan_paths"], (
        f"un path sans parent est signale comme orphelin : {profile['orphan_paths']}"
    )


def test_absence_boucle_directe(profile: dict) -> None:
    """Un noeud ne se lie pas a lui-meme."""
    assert not profile["self_loops"], f"boucles directes : {profile['self_loops']}"


def test_profondeur_coherente(profile: dict) -> None:
    """La colonne `depth` porte le nombre de segments du `path` (aux écarts admis)."""
    invariants = {inv.name: inv for inv in check_invariants(profile)}
    invariant = invariants["profondeur_coherente"]
    assert invariant.ok, invariant.detail


def test_cellule_multi_cibles_decoupee() -> None:
    """Une cellule portant plusieurs cibles donne une arete par cible."""
    rows = [
        {"PK": "10", "path": "1.1", "depth": "2", "crossLink_Leverages": "1.2;1.3"},
        {"PK": "11", "path": "1.2", "depth": "2"},
        {"PK": "12", "path": "1.3", "depth": "2"},
    ]
    edges = parse_edges(rows)
    assert len(edges) == 2, f"deux cibles attendues, {len(edges)} aretes rendues"
    assert {edge.target_path for edge in edges} == {"1.2", "1.3"}
    assert all(edge.relation == "Leverages" for edge in edges)


def test_reciprocite_calculee_sur_un_graphe_minimal() -> None:
    """La reciprocite compte une arete inverse, pas l'arete elle-meme."""
    rows = [
        {"PK": "10", "path": "1.1", "depth": "2", "crossLink_Opposes": "1.2", "crossLink_Leverages": ""},
        {"PK": "11", "path": "1.2", "depth": "2", "crossLink_Opposes": "1.1", "crossLink_Leverages": ""},
        {"PK": "12", "path": "1.3", "depth": "2", "crossLink_Opposes": "", "crossLink_Leverages": "1.1"},
    ]
    profile = structural_profile(rows)
    opposes = profile["relations"]["Opposes"]
    assert opposes["edges"] == 2
    assert opposes["reciprocal"] == 2, "les deux aretes Opposes sont mutuelles"
    leverages = profile["relations"]["Leverages"]
    assert leverages["edges"] == 1
    assert leverages["reciprocal"] == 0, "une arete a sens unique n'est pas reciproque"


def test_une_copie_abimee_fait_rougir_les_invariants() -> None:
    """Controle positif : une copie cassee fait rougir l'organe.

    Une garde qui ne peut pas rougir n'est pas une garde. Le jeu synthetique
    ci-dessous cumule quatre defauts distincts, et l'on verifie que chacun
    fait basculer **son** invariant -- et lui seul : la profondeur reste
    correcte sur ce jeu, l'organe doit donc la declarer verte.
    """
    rows = [
        {"PK": "0", "path": ROOT_PATH, "depth": "0", "crossLink_Leverages": ""},
        {"PK": "1", "path": "1", "depth": "1", "crossLink_Leverages": "9.9"},
        {"PK": "2", "path": "2.1", "depth": "2", "crossLink_Leverages": ""},
        {"PK": "3", "path": "3", "depth": "1", "crossLink_Leverages": "3"},
        {"PK": "4", "path": "4", "depth": "1", "crossLink_Leverages": ""},
        {"PK": "5", "path": "4", "depth": "1", "crossLink_Leverages": ""},
    ]
    invariants = {inv.name: inv for inv in check_invariants(structural_profile(rows))}
    assert not invariants["cibles_resolues"].ok, "une cible fantome doit rougir"
    assert not invariants["arbre_ferme"].ok, "un chemin sans parent doit rougir"
    assert not invariants["absence_boucle_directe"].ok, "une boucle directe doit rougir"
    assert not invariants["chemins_uniques"].ok, "un path duplique doit rougir"
    assert invariants["profondeur_coherente"].ok, (
        "la profondeur est correcte sur ce jeu : l'organe ne doit pas l'inventer rouge"
    )


def test_invariants_tiennent_sur_la_copie_locale(profile: dict) -> None:
    """Tous les invariants structurels tiennent sur la copie locale."""
    failures = [inv for inv in check_invariants(profile) if not inv.ok]
    assert not failures, "\n".join(f"{inv.name} : {inv.detail}" for inv in failures)


def test_le_profil_recense_toutes_les_aretes(profile: dict) -> None:
    """Le total des aretes par relation egale le nombre d'aretes mesure."""
    total = sum(stats["edges"] for stats in profile["relations"].values())
    assert total == profile["edges"]
    assert profile["nodes_with_edges"] <= profile["nodes"]


def test_rapport_rend_les_compteurs(profile: dict) -> None:
    """Le rapport textuel porte les memes nombres que le profil."""
    report = format_report(profile)
    assert str(profile["edges"]) in report
    assert str(profile["nodes"]) in report
    assert "cibles non resolues" in report


def test_sortie_json_expose_les_invariants(capsys: pytest.CaptureFixture[str]) -> None:
    """La sortie machine porte le profil et ses invariants, et sort en 0."""
    code = main(["--json"])
    payload = json.loads(capsys.readouterr().out)
    assert code == 0, "la copie locale viole un invariant structurel"
    assert payload["nodes"] > 0
    assert payload["edges"] > 0
    assert {inv["name"] for inv in payload["invariants"]} == {
        "cles_primaires_uniques",
        "chemins_uniques",
        "cibles_resolues",
        "arbre_ferme",
        "absence_boucle_directe",
        "profondeur_coherente",
    }
