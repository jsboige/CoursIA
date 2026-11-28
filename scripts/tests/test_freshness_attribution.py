#!/usr/bin/env python3
"""Attribution d'une derive de page a proprietaire (#28841).

Ce que ce fichier garde
-----------------------
Les pages a proprietaire (census Pyodide, pages Lean derivees) sont comparees
en CI a leur generateur. Tant que la comparaison etait **absolue**, une PR
longue rougissait des que `main` bougeait : le retard venait de la base, la PR
n'y etait pour rien. `scripts/ci/freshness_attribution.py` tranche : une derive
n'est imputable a la PR que si ses **commits propres** ecrivent une entree de la
page.

Le mecanisme se valide par ses faux negatifs, pas par ses hits
-------------------------------------------------------------
Un predicat d'attribution qui rend toujours `causee` se lit comme un garde qui
fonctionne (il rougit) alors qu'il n'a rien mesure. Les tests negatifs sont donc
les plus importants, et chacun tient un cas reel des deux issues :

- **controle negatif** -- une PR qui **ajoute un carnet** sans regenerer le
  census touche un `*.ipynb` : elle est `causee`, la jambe reste rouge. Un
  predicat qui absoudrait ecrasant les carnets ne servirait a rien ;
- **controle positif** -- une PR qui **fusionne une base perimee** sans rien
  ecrire elle-meme ne touche aucune entree : elle est `heritee`, la jambe passe
  en avertissement. C'est le cas que la mesure d'origine a coute trois
  regressions en une heure (#28362).

Le troisieme test est le plus subtil : la fusion ramene dans l'arbre des
fichiers que la branche n'a **pas ecrits** (`--no-merges`). Compter ces
fichiers rendrait `causee` la PR que le mecanisme existe pour absoudre -- le
test le verifie sur un vrai depot, pas sur une liste fabriquee a la main.

Le quatrieme ferme le sens inverse : « je n'ai pas pu mesurer » n'est jamais
« la PR est innocente ». Une base absente du clone rend `non_attribuable`, qui
**bloque**.
"""
from __future__ import annotations

import os
import subprocess
import sys

import pytest

RACINE = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.join(RACINE, "scripts", "ci"))

from freshness_attribution import (  # noqa: E402
    VERDICTS,
    attribuer,
    base_lisible,
    entrees_touchees,
    fichiers_propres,
    message,
)

MOTIFS = ("*.ipynb", "scripts/generateur.py", "docs/page.md")


def _git(depot, *args):
    resultat = subprocess.run(
        ["git", "-C", str(depot), *args],
        capture_output=True, text=True, encoding="utf-8", errors="replace")
    assert resultat.returncode == 0, resultat.stderr
    return resultat.stdout


def _commit(depot, fichier, contenu, message):
    chemin = depot / fichier
    chemin.parent.mkdir(parents=True, exist_ok=True)
    chemin.write_text(contenu, encoding="utf-8")
    _git(depot, "add", "-A")
    _git(depot, "-c", "user.name=test", "-c", "user.email=test@example.invalid",
         "commit", "-q", "-m", message)


@pytest.fixture()
def depot(tmp_path):
    """Un depot reel, branche `main` avec une entree, puis une branche de PR."""
    racine = tmp_path / "depot"
    racine.mkdir()
    _git(racine, "init", "-q", "-b", "main")
    _commit(racine, "docs/page.md", "v1\n", "base : page")
    _git(racine, "checkout", "-q", "-b", "feature")
    return racine


# --------------------------------------------------------------------------
# Le classifieur, sans git : les quatre verdicts et ce qu'ils bloquent
# --------------------------------------------------------------------------

def test_derive_absente_rend_a_jour_et_ne_bloque_pas():
    verdict = attribuer(False, None, MOTIFS)
    assert verdict["verdict"] == "a_jour"
    assert verdict["bloquant"] is False


def test_derive_sans_entree_touchee_est_heritee_et_ne_bloque_pas():
    verdict = attribuer(True, ["scripts/autre.py", "docs/autre.md"], MOTIFS)
    assert verdict["verdict"] == "heritee"
    assert verdict["bloquant"] is False


def test_derive_avec_entree_touchee_est_causee_et_bloque():
    verdict = attribuer(True, ["MyIA.AI.Notebooks/x/nb.ipynb"], MOTIFS)
    assert verdict["verdict"] == "causee"
    assert verdict["bloquant"] is True
    assert verdict["fichiers_entree"] == ["MyIA.AI.Notebooks/x/nb.ipynb"]


def test_mesure_impossible_est_non_attribuable_et_bloque():
    verdict = attribuer(True, None, MOTIFS)
    assert verdict["verdict"] == "non_attribuable"
    assert verdict["bloquant"] is True


def test_les_quatre_verdicts_sont_couverts():
    rendus = {
        attribuer(False, None, MOTIFS)["verdict"],
        attribuer(True, ["scripts/autre.py"], MOTIFS)["verdict"],
        attribuer(True, ["docs/page.md"], MOTIFS)["verdict"],
        attribuer(True, None, MOTIFS)["verdict"],
    }
    assert rendus == set(VERDICTS)


def test_entrees_touchees_ne_matche_pas_un_suffixe_proche():
    """Un motif ne doit pas attraper un chemin voisin : `*.ipynb` n'est pas `*.ipynb.bak`."""
    fichiers = ["a/b.ipynb", "a/b.ipynb.bak", "scripts/generateur.py", "x/ipynb"]
    assert entrees_touchees(fichiers, MOTIFS) == ["a/b.ipynb", "scripts/generateur.py"]


def test_message_nomme_le_geste_dans_chaque_verdict():
    for verdict in VERDICTS:
        ligne = message(verdict, "python scripts/generateur.py --write")
        assert ligne
        if verdict != "a_jour":
            assert "python scripts/generateur.py --write" in ligne


# --------------------------------------------------------------------------
# La mesure sur un vrai depot : c'est `fichiers_propres` qui porte le mecanisme
# --------------------------------------------------------------------------

def test_base_illisible_rend_none_et_non_une_liste_vide(depot):
    """« je n'ai pas pu lire » ne doit jamais se confondre avec « rien touche »."""
    assert base_lisible(depot, "refs/heads/inexistante") is False
    assert fichiers_propres(depot, "refs/heads/inexistante") is None


def test_controle_negatif_une_pr_qui_ajoute_un_carnet_est_causee(depot):
    _commit(depot, "MyIA.AI.Notebooks/x/nb.ipynb", "{}\n", "ajout carnet")
    fichiers = fichiers_propres(depot, "main")
    verdict = attribuer(True, fichiers, MOTIFS)
    assert verdict["verdict"] == "causee"
    assert verdict["bloquant"] is True


def test_controle_positif_une_fusion_de_base_perimee_est_heritee(depot, tmp_path):
    """La fusion ramene des fichiers que la branche n'ecrit pas : `--no-merges`."""
    # La base avance sur une ENTRÉE (le carnet), sans que la PR l'ecrive.
    _git(depot, "checkout", "-q", "main")
    _commit(depot, "MyIA.AI.Notebooks/x/nb.ipynb", "{}\n", "base : carnet")
    _git(depot, "checkout", "-q", "feature")
    # La PR n'ecrit qu'un fichier hors entrees, puis fusionne la base.
    _commit(depot, "scripts/outil.py", "x = 1\n", "outil de la PR")
    _git(depot, "-c", "user.name=test", "-c", "user.email=test@example.invalid",
         "merge", "-q", "--no-ff", "-m", "fusion main", "main")

    fichiers = fichiers_propres(depot, "main")
    assert "MyIA.AI.Notebooks/x/nb.ipynb" not in fichiers, (
        "la fusion ne doit pas inscrire au credit de la PR un fichier qu'elle "
        "n'a pas ecrit")
    assert attribuer(True, fichiers, MOTIFS)["verdict"] == "heritee"


def test_une_pr_qui_ecrit_elle_meme_l_entree_reste_causee_malgre_la_fusion(depot):
    """L'attribution est conservative : toucher une entree suffit, heriter ne sauve pas."""
    _commit(depot, "docs/page.md", "v2\n", "page regeneree par la PR")
    _git(depot, "checkout", "-q", "main")
    _commit(depot, "MyIA.AI.Notebooks/x/nb.ipynb", "{}\n", "base : carnet")
    _git(depot, "checkout", "-q", "feature")
    _git(depot, "-c", "user.name=test", "-c", "user.email=test@example.invalid",
         "merge", "-q", "--no-ff", "-m", "fusion main", "main")
    verdict = attribuer(True, fichiers_propres(depot, "main"), MOTIFS)
    assert verdict["verdict"] == "causee"
