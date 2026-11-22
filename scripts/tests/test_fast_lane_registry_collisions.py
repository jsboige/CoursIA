"""Le registre de la voie rapide ne doit pas accepter deux gardes homonymes.

**Le defaut, mesure.** Pendant que la PR #27183 (garde des dossiers de premier
niveau) etait ouverte, la PR #27233 a fusionne sur `main` une AUTRE garde sous
le nom `TRANCHE52` (prose<->sorties). Les deux listes s'appelaient donc
`TRANCHE52` dans `scripts/ci/fast_lane_registry.py`, et `scripts/ci/fast_lane.py`
importait `TRANCHE52` DEUX FOIS -- une fois par ligne, la seconde ecrasant la
premiere dans l'espace de noms.

Le resultat etait **silencieusement faux** : aucune erreur d'import, aucun
rouge, aucun avertissement. La garde des dossiers de premier niveau avait
simplement disparu du registre effectif : une garde de CI qui **ne rouge
jamais** est indiscernable d'une garde absente, et l'absence ne se voit que
quand un dossier de premier niveau apparait a la racine sans que rien ne
rougisse.

Ce fichier met sous test les **quatre** collisions de la famille, chacune
detectee par une fonction pure (source en entree, liste en sortie), et chacune
des quatre fonctions est elle-meme mise sous test sur une source SYNTHETIQUE
qui contient la collision : un detecteur qui n'a jamais vu son defaut ne
prouve rien (controle positif).

Les quatre collisions :

1. **deux listes de gardes sous le meme nom** dans le registre ;
2. **deux gardes sous le meme `name=`** -- ce nom est le nom du check-run publie,
   et la deduplication de la voie rapide se fait par nom : deux gardes homonymes
   ne publient qu'un seul verdict ;
3. **un import homonyme** dans `fast_lane.py` (le second ecrase le premier) ;
4. **une liste de gardes definie mais jamais agregée** -- elle ne tournerait
   jamais, pour la meme raison qu'en (1) : une garde absente ne rougit pas.
"""

from __future__ import annotations

import ast
from collections import Counter
from pathlib import Path

import yaml

CI_DIR = Path(__file__).resolve().parents[1] / "ci"
REGISTRE = CI_DIR / "fast_lane_registry.py"
MOTEUR = CI_DIR / "fast_lane.py"
DONNEES = CI_DIR / "fast_lane_registry.d"


# --- les quatre lecturers, purs : source en entree, liste en sortie ---------

def listes_de_gardes(source: str) -> list[str]:
    """Les noms des listes de gardes declarees au niveau module du registre.

    Une liste de gardes est une annotation `NOM: list[Guard] = [...]` : c'est
    la forme employee par le registre pour ses tranches ET par les listes
    nommees (`RISK_KERNEL_GUARDS`).
    """
    noms: list[str] = []
    for noeud in ast.parse(source).body:
        if not isinstance(noeud, ast.AnnAssign):
            continue
        if not isinstance(noeud.target, ast.Name):
            continue
        if not isinstance(noeud.annotation, ast.Subscript):
            continue
        tranche = noeud.annotation.value
        if isinstance(tranche, ast.Name) and tranche.id == "list":
            noms.append(noeud.target.id)
    return noms


def noms_de_garde(docs: list) -> list[str]:
    """Les `name=` des gardes du registre : ce sont les noms des check-runs.

    Depuis #28117 les gardes vivent en donnees (``fast_lane_registry.d/
    <groupe>.yaml``) : le lecteur prend les documents YAML PARSES du
    repertoire de donnees, un par fichier. Un lecteur qui resterait sur le
    source .py ne verrait plus AUCUN ``Guard(`` et serait vert en silence --
    exactement la panne muette que ce fichier existe pour empecher.
    """
    noms: list[str] = []
    for doc in docs:
        for garde in doc.get("guards", []):
            if isinstance(garde, dict) and "name" in garde:
                noms.append(str(garde["name"]))
    return noms


def noms_importes(source: str, module: str) -> list[str]:
    """Les noms importes d'un module donne, forme par forme (simple ou
    parenthesee) : un import homonyme ecrase le precedent sans bruit."""
    noms: list[str] = []
    for noeud in ast.walk(ast.parse(source)):
        if isinstance(noeud, ast.ImportFrom) and noeud.module == module:
            for alias in noeud.names:
                noms.append(alias.asname or alias.name)
    return noms


def noms_agreges(source: str) -> set[str]:
    """Les listes de gardes que le moteur AGREGEE effectivement.

    L'agregation est l'expression `guards = [g for g in A + B + ...]` : une
    liste absente de cette somme ne tourne jamais.
    """
    agreges: set[str] = set()
    for noeud in ast.walk(ast.parse(source)):
        if not isinstance(noeud, ast.Assign):
            continue
        if not any(isinstance(c, ast.Name) and c.id == "guards"
                   for cible in noeud.targets for c in ast.walk(cible)):
            continue
        valeur = noeud.value
        if not isinstance(valeur, ast.ListComp):
            continue
        for generateur in valeur.generators:
            for elt in ast.walk(generateur.iter):
                if isinstance(elt, ast.Name):
                    agreges.add(elt.id)
    return agreges


def doublons(noms: list[str]) -> dict[str, int]:
    """Les noms repetes, avec leur nombre d'apparitions."""
    return {nom: n for nom, n in Counter(noms).items() if n > 1}


# --- les quatre tests, sur les fichiers reels du depot ---------------------

def test_le_registre_ne_declaire_pas_deux_listes_homonymes():
    """Collision (1) : deux listes de gardes sous le meme nom."""
    doubl = doublons(listes_de_gardes(REGISTRE.read_text(encoding="utf-8")))
    assert not doubl, (
        "deux listes de gardes portent le meme nom : la seconde ecrase la "
        f"premiere a l'import, et une garde absente ne rougit jamais -- {doubl}")


def test_le_registre_ne_declaire_pas_deux_gardes_de_meme_nom():
    """Collision (2) : deux gardes de meme `name=` -- un seul check-run publie.

    Depuis #28117 les noms se lisent dans les donnees YAML, pas dans le .py.
    """
    docs = [yaml.safe_load(p.read_text(encoding="utf-8"))
            for p in sorted(DONNEES.glob("*.yaml"))]
    doubl = doublons(noms_de_garde(docs))
    assert not doubl, (
        "deux gardes portent le meme nom de check-run : la deduplication de la "
        f"voie rapide se fait par nom, un seul verdict survive -- {doubl}")


def test_le_moteur_n_importe_pas_deux_fois_le_meme_nom():
    """Collision (3) : un import homonyme ecrase le precedent, sans erreur."""
    doubl = doublons(noms_importes(MOTEUR.read_text(encoding="utf-8"),
                                   "fast_lane_registry"))
    assert not doubl, (
        "le moteur importe deux fois le meme nom du registre : le second "
        f"ecrase le premier, la garde du premier disparait sans bruit -- {doubl}")


def test_chaque_liste_du_registre_est_agregée_par_le_moteur():
    """Collision (4) : une liste definie et jamais agregee ne tourne jamais."""
    registre = REGISTRE.read_text(encoding="utf-8")
    declarees = set(listes_de_gardes(registre))
    agregées = noms_agreges(MOTEUR.read_text(encoding="utf-8"))
    orphelines = sorted(declarees - agregées)
    assert not orphelines, (
        "liste(s) de gardes definie(s) et jamais agregée(s) : elles ne "
        f"tourneront jamais -- {orphelines}")


# --- les controles positifs : les quatre detecteurs savent.fire -----------

REGISTRE_SYNTHETIQUE = '''
from dataclasses import dataclass

@dataclass
class Guard:
    name: str

TRANCHE52: list[Guard] = [
    Guard(name="garde-a"),
]

TRANCHE52: list[Guard] = [
    Guard(name="garde-b"),
]

AUTRE: list[Guard] = [
    Guard(name="garde-a"),
]
'''

MOTEUR_SYNTHETIQUE = '''
from fast_lane_registry import TRANCHE52
from fast_lane_registry import TRANCHE52

def main():
    guards = [g for g in TRANCHE52]
    return guards
'''


def test_le_lecteur_de_listes_detecte_le_doublon():
    """Controle POSITIF du detecteur (1) : sans lui, un detecteur qui ne voit
    rien ne prouverait rien."""
    doubl = doublons(listes_de_gardes(REGISTRE_SYNTHETIQUE))
    assert doubl == {"TRANCHE52": 2}


DONNEES_SYNTHETIQUES = [
    {"group": "TRANCHE52",
     "guards": [{"name": "garde-a", "argv": ["python", "x"],
                 "source": "(x)"}]},
    {"group": "AUTRE",
     "guards": [{"name": "garde-a", "argv": ["python", "y"],
                 "source": "(y)"},
                {"name": "garde-b", "argv": ["python", "z"],
                 "source": "(z)"}]},
]


def test_le_lecteur_de_noms_detecte_le_doublon():
    """Controle POSITIF du detecteur (2) : deux gardes de meme `name=`,
    en donnees YAML depuis #28117."""
    doubl = doublons(noms_de_garde(DONNEES_SYNTHETIQUES))
    assert doubl == {"garde-a": 2}


def test_le_lecteur_d_imports_detecte_le_doublon():
    """Controle POSITIF du detecteur (3) : deux imports du meme nom."""
    doubl = doublons(noms_importes(MOTEUR_SYNTHETIQUE, "fast_lane_registry"))
    assert doubl == {"TRANCHE52": 2}


def test_le_lecteur_d_agregation_detecte_l_orpheline():
    """Controle POSITIF du detecteur (4) : une liste declaree, jamais agregée."""
    declarees = set(listes_de_gardes(REGISTRE_SYNTHETIQUE))
    agregées = noms_agreges(MOTEUR_SYNTHETIQUE)
    assert sorted(declarees - agregées) == ["AUTRE"]
