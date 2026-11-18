#!/usr/bin/env python3
"""Parsing de la variable ALLOW du gate proof-integrity (#21905).

Extrait de scripts/lean/axiom_check_step.py pour etre unit-testable sans
executer le step (qui lit son environnement au niveau module et sys.exit
s'il est incomplet). Deux formes, dont une nouvelle :

  ALLOW="ax_1,ax_2"                 liste separee par virgules (forme
                                    historique, inchangee)
  ALLOW="@scripts/lean/allow_axioms_conway.txt"
                                    fichier source de verite : un nom par
                                    ligne, lignes vides et commentaires
                                    '#' ignores. Le chemin se resout
                                    contre repo_root (GITHUB_WORKSPACE en
                                    CI, le contrat racine du step) puis
                                    contre le cwd en repli local.

Fail-closed : un fichier '@' absent ou illisible leve SystemExit -- il ne
produit JAMAIS une liste vide silencieuse (une allow-list vide est un
changement de regle du gate, pas un etat par defaut).
"""

from __future__ import annotations

import os
from pathlib import Path


def parse_allow(raw: str, repo_root: Path) -> list[str]:
    """Parse la valeur ALLOW en liste de noms d'axiomes.

    raw       : valeur brute de la variable (jamais None -- l'appelant
                passe os.environ.get("ALLOW", ""))
    repo_root : racine du checkout (GITHUB_WORKSPACE en CI)

    Renvoie la liste des noms, sans doublon preserve d'ordre. Leve
    SystemExit si un '@chemin' ne se resout pas.
    """
    raw = (raw or "").strip()
    if not raw:
        return []
    if not raw.startswith("@"):
        return [a.strip() for a in raw.split(",") if a.strip()]

    ref = raw[1:].strip()
    candidates = [
        (repo_root / ref) if not os.path.isabs(ref) else Path(ref),
        Path(ref),  # repli relatif au cwd (run local hors CI)
    ]
    path = next((p for p in candidates if p.is_file()), None)
    if path is None:
        tried = ", ".join(str(p) for p in candidates)
        raise SystemExit(
            f"ALLOW designe '{ref}' mais aucun fichier ne s'y resout "
            f"(essayes : {tried}) -- une allow-list manquante n'est pas "
            "une allow-list vide, le gate refuse de tourner (#21905)."
        )
    names: list[str] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        line = line.split("#", 1)[0].strip()
        if line:
            names.append(line)
    return names
