"""La garde de fraicheur doit couvrir **tout** le chemin du tirage.

`scripts/coordination/main_freshness.py` refuse un tirage dont un module du
chemin differe d'`origin/main` (`ORGANE_DIVERGENT`). Une liste d'organes
incomplete est donc un **trou silencieux** : le module livre hors liste
continue de servir des grains sous un contrat perime, et rien ne le dit.

La prescription est dans `docs/reference/tapis-rapide.md` : « un nouveau
module du tirage entre dans cette liste **avec** sa premiere livraison ».
Ici elle est **verifiee** :

- la fermeture d'import **statique** des points d'entree du tirage doit
  etre incluse dans `ORGANES` ;
- le tableau des modules du document vivant doit y etre inclus aussi.

La verification est **statique** (parseur `ast`) et non un import : importer
le chemin du tirage depuis un test l'executerait, et `main_freshness` est
lui-meme dans la liste -- l'import serait circulaire.

Le test **echoue** la ou il doit : une PR qui livre un module du tirage sans
le declarer porte son propre rouge. C'est la direction utile du defaut.

Organe de reference : `scripts/coordination/main_freshness.py` (liste
`ORGANES`).
"""
from __future__ import annotations

import ast
import re
import sys
from pathlib import Path

import pytest

RACINE = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(RACINE / "scripts"))

from coordination import main_freshness as mf  # noqa: E402

#: Les points d'entree du tirage : ce que la lane execute. Leur fermeture
#: d'import EST le chemin du tirage.
ENTREES = (
    "scripts/coordination/tapis_rapide.py",
    "scripts/coordination/tapis_leger.py",
    "scripts/coordination/tapis_voie_leger.py",
    "scripts/coordination/tapis_prise_en_charge.py",
    "scripts/pick_idle_grain.py",
)

#: Le document vivant qui prescrit la liste.
DOC = "docs/reference/tapis-rapide.md"


def _modules_de(fichier: Path) -> set[str]:
    """Les modules du depot appeles par `fichier` (forme statique)."""
    if not fichier.exists():
        return set()
    arbre = ast.parse(fichier.read_text(encoding="utf-8"), filename=str(fichier))
    out: set[str] = set()
    for noeud in ast.walk(arbre):
        if isinstance(noeud, ast.Import):
            for alias in noeud.names:
                if alias.name.startswith("coordination."):
                    out.add("scripts/coordination/"
                            + alias.name.split(".", 1)[1] + ".py")
        elif isinstance(noeud, ast.ImportFrom):
            if noeud.level:  # import relatif : hors perimetre ici
                continue
            if noeud.module == "coordination":
                for alias in noeud.names:
                    out.add("scripts/coordination/" + alias.name + ".py")
            elif noeud.module and noeud.module.startswith("coordination."):
                out.add("scripts/coordination/"
                        + noeud.module.split(".", 1)[1] + ".py")
    return out


def fermeture(entrees: tuple[str, ...] = ENTREES) -> set[str]:
    """La fermeture d'import des points d'entree (l'arbre, sans cycle)."""
    vus: set[str] = set()
    pile = list(entrees)
    while pile:
        courant = pile.pop()
        if courant in vus:
            continue
        vus.add(courant)
        pile.extend(_modules_de(RACINE / courant))
    return vus


def modules_du_document() -> set[str]:
    """Les modules cites par le tableau « Les modules » du document vivant."""
    texte = (RACINE / DOC).read_text(encoding="utf-8")
    section = texte.split("### Les modules", 1)
    assert len(section) == 2, "le tableau « Les modules » a disparu du document"
    corps = section[1].split("\n## ", 1)[0]
    return set(re.findall(r"`(scripts/coordination/[A-Za-z0-9_]+\.py)`", corps))


def test_la_fermeture_du_tirage_est_dans_la_liste():
    """Aucun module du chemin du tirage ne peut rester hors de `ORGANES`."""
    trous = sorted(fermeture() - set(mf.ORGANES))
    assert not trous, (
        "module(s) du chemin du tirage hors de `ORGANES` : "
        + ", ".join(trous)
        + " -- ajouter le(s) a la liste (la PR qui livre un module du tirage "
          "porte son propre rouge, c'est voulu)")
    # Le controle : la fermeture n'est pas vide, sinon le test ne prouverait
    # rien (une liste vide passerait).
    assert len(fermeture()) >= 20, "la fermeture mesuree est trop petite"


def test_le_tableau_des_modules_du_document_est_dans_la_liste():
    """Le document vivant et la liste disent la meme chose."""
    trous = sorted(modules_du_document() - set(mf.ORGANES))
    assert not trous, (
        "module(s) du tableau « Les modules » hors de `ORGANES` : "
        + ", ".join(trous))
    assert modules_du_document(), "le tableau des modules est vide"


def test_la_liste_na_pas_de_doublon():
    """Un doublon ferait compter un module deux fois dans la lecture."""
    vus: set[str] = set()
    doublons: list[str] = []
    for module in mf.ORGANES:
        if module in vus:
            doublons.append(module)
        vus.add(module)
    assert not doublons, "doublon(s) dans ORGANES : " + ", ".join(doublons)


def test_un_module_hors_liste_est_bien_detecte():
    """CONTROLE NEGATIF : l'oracle sait dire NON.

    Sans ce controle, un test qui ne verrait rien pourrait passer quand meme.
    Un module factice du tirage, absent de la liste, doit etre signale comme
    un trou -- et un module deja declare, non.
    """
    vrai = "scripts/coordination/tapis_inconnu_de_la_liste.py"
    assert vrai not in mf.ORGANES, "le module de controle ne doit pas etre liste"
    trous = sorted(fermeture() | {vrai} - set(mf.ORGANES))
    assert vrai in trous, "un module hors liste doit etre vu comme un trou"
    # Et l'inverse : un module reellement declare n'est pas un trou.
    declare = "scripts/coordination/tapis_leger.py"
    assert declare in mf.ORGANES
    assert declare not in sorted(fermeture() - set(mf.ORGANES))


@pytest.mark.parametrize("rel", ENTREES)
def test_chaque_point_d_entree_existe(rel):
    """Un point d'entree renomme rendrait la fermeture silencieusement vide."""
    assert (RACINE / rel).exists(), f"point d'entree absent : {rel}"
