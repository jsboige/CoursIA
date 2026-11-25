#!/usr/bin/env python3
"""Le COMMIT qui a ecrit l'etat : l'etat est lie au code qui l'a produit.

Deux etats d'ancre ne sont comparables que s'ils ont ete ecrits par le meme
code : la SEMANTIQUE des etats parkes a change le 19/11 (`tapis_non_tente`
-- le grain propose mais jamais qualifie n'est plus un verdict, c'est un
etat a part). Comparer un etat ecrit hier a un etat ecrit aujourd'hui, sans
dire lequel des deux codes l'a produit, c'est comparer deux langues.

L'estampille est le HEAD du depot qui porte le code. Elle est lue dans les
FICHIERS de git (`.git/HEAD`, la ref, `packed-refs`), sans lancer de
processus : le harnais de tests interdit toute sortie, et un organe qui
tourne dans une tache planifiee n'a pas toujours `git` sous la main. Elle
vaut None si le depot n'est pas lisible : fail-soft, le travail continue et
la mesure signale l'absence d'estampille au lieu d'en inventer une.
"""
from __future__ import annotations

from pathlib import Path


def depot() -> Path:
    """La racine du depot qui porte le code (scripts/coordination/ -> racine)."""
    return Path(__file__).resolve().parents[2]


def _git_dir(root: Path) -> Path | None:
    """Le repertoire git du depot (un worktree y met un FICHIER)."""
    g = root / ".git"
    if g.is_dir():
        return g
    if g.is_file():
        for ligne in g.read_text(encoding="utf-8", errors="ignore").splitlines():
            if ligne.startswith("gitdir:"):
                p = Path(ligne.split(":", 1)[1].strip())
                return p if p.is_absolute() else (root / p)
    return None


def _commondir(git_dir: Path) -> Path | None:
    """Le repertoire des REFS partage (un worktree a son propre HEAD)."""
    f = git_dir / "commondir"
    try:
        p = Path(f.read_text(encoding="utf-8").strip())
    except OSError:
        return None
    return p if p.is_absolute() else (git_dir / p)


def _sha_dans(base: Path, ref: str) -> str | None:
    """La sha d'une ref, loose ou empaquetee dans `packed-refs`."""
    try:
        sha = (base / ref).read_text(encoding="utf-8").strip()
        if sha:
            return sha
    except OSError:
        pass
    try:
        lignes = (base / "packed-refs").read_text(encoding="utf-8").splitlines()
    except OSError:
        return None
    for ligne in lignes:
        if ligne.startswith("#") or not ligne.strip():
            continue
        sha, _, nom = ligne.partition(" ")
        if nom.strip() == ref:
            return sha
    return None


def commit() -> str | None:
    """Le HEAD du depot qui porte le code, ou None s'il n'est pas lisible."""
    git_dir = _git_dir(depot())
    if git_dir is None:
        return None
    try:
        head = (git_dir / "HEAD").read_text(encoding="utf-8").strip()
    except OSError:
        return None
    if not head.startswith("ref:"):
        return head or None
    ref = head.split(":", 1)[1].strip()
    for base in (git_dir, _commondir(git_dir)):
        if base is None:
            continue
        sha = _sha_dans(base, ref)
        if sha:
            return sha
    return None
