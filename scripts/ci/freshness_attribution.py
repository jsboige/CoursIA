#!/usr/bin/env python3
"""Attribution d'une derive de page a proprietaire (issue #28841).

**Le probleme.** Les pages a proprietaire -- census Pyodide, pages Lean
derivees -- sont des fichiers generes que la CI compare a leur generateur.
La comparaison rougissait toute PR longue des que `main` bougeait : le retard
venait de `main`, la PR n'y etait pour rien. Mesures citées par les lanes :
`#28362` rougit trois fois en une heure pour un `main` perime, `#28455` et
`#28393` ont chacune regenere deux fois pour la meme cause.

**Le mecanisme.** Une derive n'est imputable a la PR que si la PR a touche une
**entree** de la page. Les entrees sont les fichiers dont le generateur derive
son contenu (les carnets pour le census, l'arbre Lean pour les pages Lean)
plus le generateur, ses artefacts de reference et la page elle-meme -- une
page reecrite a la main est bien un geste de la PR.

**Ce que « la PR a touche » veut dire, exactement.** `git log --no-merges
--name-only base..HEAD` : les fichiers ecrits par les commits **propres** de la
branche. Les fusions sont exclues, et c'est le coeur du mecanisme : une fusion
de `main` ramene dans l'arbre des fichiers que la branche n'a pas ecrits. Les
compter imputerait a la PR ce que la base lui a apporte -- exactement le
defaut que cette attribution corrige.

**Les deux controles de l'issue tiennent** :
  * negatif -- une PR qui ajoute un carnet sans regenerer le census touche un
    `*.ipynb` : elle est `causee`, la jambe reste rouge ;
  * positif -- une PR qui fusionne un `main` perime sans rien ecrire elle-meme
    ne touche aucune entree : elle est `heritee`, la jambe passe en
    avertissement en nommant le geste de regeneration.

**Bornes, dites pour que la lecture ne prete pas a l'attribution plus qu'elle
ne mesure** :
  * une PR qui touche une entree **et** herite d'un retard de `main` reste
    `causee` : l'attribution est conservative, elle ne decompose pas le retard
    en part heritee et part propre ;
  * `git log` illisible (base absente du clone, historique tronque) rend
    `non_attribuable`, qui **bloque** : « je n'ai pas pu mesurer » n'est jamais
    « la PR est innocente ».
"""

from __future__ import annotations

import fnmatch
import subprocess
from pathlib import Path

VERDICTS = ("a_jour", "heritee", "causee", "non_attribuable")


def _git(repo: Path | str, *args: str, timeout: int = 120) -> tuple[int, str]:
    """Lance `git -C <repo> <args>` et rend `(rc, sortie)` sans jamais lever."""
    try:
        proc = subprocess.run(
            ["git", "-C", str(repo), *args],
            capture_output=True, text=True, encoding="utf-8",
            errors="replace", timeout=timeout)
    except (OSError, subprocess.SubprocessError) as exc:
        return 1, str(exc)
    return proc.returncode, proc.stdout or ""


def base_lisible(repo: Path | str, base: str) -> bool:
    """La reference de base est-elle resolvable dans ce clone ?"""
    rc, _ = _git(repo, "rev-parse", "--verify", "--quiet", "%s^{commit}" % base,
                 timeout=60)
    return rc == 0


def fichiers_propres(repo: Path | str, base: str) -> list[str] | None:
    """Fichiers touches par les commits propres de la branche (`base..HEAD`).

    Rend `None` quand la mesure est impossible (base absente, `git log` en
    echec) : l'appelant doit alors traiter la derive comme non attribuable,
    jamais comme heritee.
    """
    if not base_lisible(repo, base):
        return None
    rc, out = _git(repo, "log", "--no-merges", "--name-only", "--format=",
                   "%s..HEAD" % base)
    if rc != 0:
        return None
    vus: set[str] = set()
    resultat: list[str] = []
    for ligne in out.splitlines():
        chemin = ligne.strip()
        if chemin and chemin not in vus:
            vus.add(chemin)
            resultat.append(chemin)
    return resultat


def entrees_touchees(fichiers: list[str], motifs: tuple[str, ...]) -> list[str]:
    """Sous-ensemble de `fichiers` qui releve d'un des motifs d'entree."""
    return sorted(
        f for f in fichiers
        if any(fnmatch.fnmatchcase(f, motif) for motif in motifs))


def attribuer(derive: bool, fichiers: list[str] | None,
              motifs: tuple[str, ...]) -> dict:
    """Classe une derive : a jour, heritee, causee, ou non attribuable.

    `bloquant` est ce que la jambe CI doit lire. Une derive `heritee` ne
    bloque pas : elle appartient a `main`, et le geste de regeneration est
    nomme dans le message au lieu d'etre exige de la PR.
    """
    if not derive:
        return {"verdict": "a_jour", "bloquant": False, "fichiers_entree": []}
    if fichiers is None:
        return {"verdict": "non_attribuable", "bloquant": True,
                "fichiers_entree": []}
    touches = entrees_touchees(fichiers, motifs)
    if touches:
        return {"verdict": "causee", "bloquant": True,
                "fichiers_entree": touches}
    return {"verdict": "heritee", "bloquant": False, "fichiers_entree": []}


def message(verdict: str, geste: str) -> str:
    """Une ligne lisible pour la sortie humaine de l'organe appelant."""
    if verdict == "heritee":
        return ("derive HERITEE de la base : la PR n'ecrit aucune entree de la "
                "page. Geste (sur main) : %s" % geste)
    if verdict == "causee":
        return ("derive CAUSEE par la PR : elle touche une entree de la page. "
                "Geste : %s" % geste)
    if verdict == "non_attribuable":
        return ("derive NON ATTRIBUABLE : la base n'a pas pu etre lue (git log "
                "muet ou reference absente). Geste : %s" % geste)
    return "page a jour"
