#!/usr/bin/env python3
"""Cure canonique des accents francais (registre #2876) — markdown-CELL-SOURCE STRICT.

Pourquoi cet outil existe
-------------------------
Le registre #2876 (restauration des accents francais) a accumule ~60 PRs manuelles,
chacune faite avec un **script ad-hoc non-committe**. Ces scripts ad-hoc sont la
source racine des regressions repetees qui ont mine le registre :

  - #7094/#7143/#7154/#7162/#7167/#7179 : scripts ad-hoc on accentue des
    **identifiants de code** (variables/parametres/proprietes) — HORS scope.
  - #7135/#7145 : scripts ad-hoc accentuent les **cibles de liens markdown**
    `](...ipynb)` -> lien casse (le fichier reel sur disque reste sans accent).
  - #7105/#7124/#7132 : scripts ad-hoc re-executent / regenerent les **outputs**
    et **execution_count** -> diff non-accents-only, re-execute des cellules.

Chaque regression = un script ad-hoc qui n'appliquait PAS les 4 bright-lines du
registre. Cet outil les applique PAR CONSTRUCTION :

  1. **markdown-cell-source ONLY** : `if cell_type != 'markdown': continue`.
     Les cellules code sont integres (ni identifiants, ni commentaires, ni stdout
     touches). C'est le contrat #2876 "markdown-only STRICT" (adjudication ai-01
     17/07).
  2. **skip link targets** : les spans `]( ... )` sont proteges (masques avant la
     cure, restaures apres). Accentuer une cible de lien la decoit du fichier reel
     sur disque (bright-line raffine ai-01 18/07).
  3. **skip code** : consequence de (1) — aucune cellule code n'est touchee.
  4. **skip outputs / execution_count** : seule la cle `source` de chaque cellule
     markdown est re-ecrite ; `outputs`, `execution_count`, `metadata` sont
     intacts. Diff = accents-only, jamais un delta de re-execution.

Comment ca marche
-----------------
Reutilise le dictionnaire CONSERVATEUR `ACCENT_PAIRS` + la regex de
`detect_accent_stripping.py` (source unique de la PAIRE stripped->accentue).
Ce dictionnaire n'inclut QUE les paires ou la forme *stripped* n'est PAS un mot
francais valide (ex. "parametre"->"parametre") : la restauration est donc non-
ambigue ("a"/"ou"/"la"/"tres" exclus car mots FR valides sans accent).

La restauration preserve la casse : le match reutilise `m.group(0)` tel quel pour
remplacer la sous-chaine matchee, et la suggestion est case-ajustee (capitalisee
si le match commence par une majuscule).

Usage
-----
    # dry-run : liste les cures prevues sans ecrire
    python restore_accents_canonical.py NB.ipynb --dry-run
    # applique en place (re-ecrit NB.ipynb)
    python restore_accents_canonical.py NB.ipynb
    # --check : exit 1 si des cures sont disponibles (CI-ready, n'ecrit rien)
    python restore_accents_canonical.py NB.ipynb --check
    # --check --scope : exit 1 aussi si le notebook contient deja des cures dans
    #                   des cellules CODE (signe qu'un script ad-hoc a precede)
    python restore_accents_canonical.py NB.ipynb --check --scope

Exit codes
----------
    0 -- rien a curer (ou mode non --check)
    1 -- cures disponibles (--check seulement)
    2 -- erreur (notebook illisible)

Voir aussi
----------
- detect_accent_stripping.py : la moitie DETECTION (dictionnaire + regex source).
- check_identifier_regression.py : le GATE anti-regression-identifiant (vet les
  PRs accents pour le over-reach code, complementaire de cette cure defensive).
- Memoires : issue-2876-scope-boundary-markdown-vs-code-pending-adjudication
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

# Reutilisation de la source unique de verite : dictionnaire + regex de detection.
sys.path.insert(0, str(Path(__file__).resolve().parent))
import detect_accent_stripping as das  # noqa: E402

ACCENT_PAIRS = das.ACCENT_PAIRS
# La regex matche les formes *stripped* (frontieres de mot, insensible casse).
_CURE_RE = das._build_regex()

# Regex protegeant les spans de cible de lien markdown : ]( ... ). On MASQUE ces
# spans avant la cure (remplace par un placeholder sans lettres accentuables) et
# on les restaure apres, pour ne JAMAIS accentuer une cible de lien/chemin/URL.
# Couvre [display](target), ![alt](src), et les refs de type ](url "title").
# On matche depuis le `](` jusqu'a la parenthese fermante (greedy minimal sur la
# meme ligne ; les liens markdown ne contiennent pas de ")" nu dans la cible).
_LINK_TARGET_RE = re.compile(r"\]\([^)]*\)")


def _preserve_case(match_str: str, suggestion: str) -> str:
    """Ajuste la casse de la suggestion a celle du match.

    Le dictionnaire est en minuscules ; si le match original commence par une
    majuscule (ex. 'Parametre' en debut de phrase), on capitalise la suggestion.
    Le tout-majuscule (rare en prose FR) est aussi preserve.
    """
    if match_str.isupper() and len(match_str) > 1:
        return suggestion.upper()
    if match_str[0].isupper():
        return suggestion[0].upper() + suggestion[1:]
    return suggestion


def _cure_line(line: str) -> tuple[str, int]:
    """Cure une ligne de markdown : accentue les formes stripped dans la PROSE,
    en protegeant les cibles de liens ]( ... ).

    Retourne (ligne_curee, n_cures).
    """
    # 1. extraire + masquer les cibles de liens. On remplace chaque span ]( ... )
    # par un placeholder unique (base64 de l'index) qui ne peut matcher aucun mot
    # du dictionnaire (lettres uniquement). Le contenu original est preserve tel
    # quel dans la liste link_targets, restaure byte-identique a l'etape 3.
    link_targets = []

    def _mask(m):
        link_targets.append(m.group(0))
        return "\x00LT{}\x00".format(len(link_targets) - 1)

    masked = _LINK_TARGET_RE.sub(_mask, line)

    # 2. curer la prose (hors cibles masquees)
    n = [0]

    def _repl(m):
        key = m.group(0).lower()
        suggestion = ACCENT_PAIRS.get(key)
        if suggestion is None:
            return m.group(0)
        n[0] += 1
        return _preserve_case(m.group(0), suggestion)

    cured = _CURE_RE.sub(_repl, masked)

    # 3. restaurer les cibles de liens (byte-identiques a l'original)
    for i, original in enumerate(link_targets):
        cured = cured.replace("\x00LT{}\x00".format(i), original, 1)
    return cured, n[0]


def _cure_source(source) -> tuple[object, int]:
    """Cure le `source` d'une cellule (list[str] nbformat ou str).

    Retourne (nouveau_source, n_cures) en PRESERVANT le type original
    (list reste list, str reste str) et la structure nbformat (chaque element
    de la liste garde son saut de ligne final eventuel).
    """
    if isinstance(source, str):
        lines = source.split("\n")
        cured_lines = []
        total = 0
        for ln in lines:
            cl, n = _cure_line(ln)
            cured_lines.append(cl)
            total += n
        return "\n".join(cured_lines), total
    # list nbformat : chaque chunk peut porter son \n final. On cure CHAQUE CHUNK
    # IN-PLACE (split le chunk en lignes, cure chaque ligne, rejoinde), SANS JAMAIS
    # concatener les chunks entre eux. Pourquoi : un join global -> split -> re-chunk
    # perd l'alignement quand un chunk est un separateur de paragraphe nu ("\n") — le
    # re-decoupage l'absorbe et COLLAPSE les paragraph breaks markdown ("\n\n" -> "\n").
    # Bug firsthand sur Infer-14 (28/33 cellules avec paragraph breaks collapsees,
    # po-2024 c.634) : le chunk standalone "\n" disparait. La cure per-chunk preserve
    # byte-pour-byte la structure de liste (boundaries chunk + trailing \n + blank-line
    # separators) ET applique les accents ligne-par-ligne dans chaque chunk.
    original = list(source)
    new_chunks = []
    total = 0
    for chunk in original:
        lines = chunk.split("\n")
        cured_lines = []
        for ln in lines:
            cl, n = _cure_line(ln)
            cured_lines.append(cl)
            total += n
        new_chunks.append("\n".join(cured_lines))
    if new_chunks == original:
        return original, 0  # rien change -> retourner l'original byte-identique
    return new_chunks, total


def cure_notebook(path: Path, write: bool, check_scope: bool = False):
    """Cure un notebook. Retourne dict {cures, cells_touched, md_cells, code_hits}.

    code_hits > 0 (mode --check --scope) = le notebook contient des formes
    accentuables dans des cellules CODE -> signe qu'un script ad-hoc precedent
    a peut-etre laisse du code a curer (HORS scope #2876) -> flag.
    """
    try:
        with open(path, encoding="utf-8") as f:
            nb = json.load(f)
    except (OSError, json.JSONDecodeError) as exc:
        return {"error": str(exc)}

    total_cures = 0
    cells_touched = 0
    md_cells = 0
    code_hits = 0

    for cell in nb.get("cells", []):
        ctype = cell.get("cell_type", "")
        source = cell.get("source", "")
        if ctype == "markdown":
            md_cells += 1
            new_source, n = _cure_source(source)
            if n > 0:
                total_cures += n
                cells_touched += 1
                if write:
                    cell["source"] = new_source
                    # outputs/execution_count/metadata intacts (jamais touches)
        elif ctype == "code" and check_scope:
            # mode scope : detecter les formes accentuables residuelles en code
            code_text = "".join(source) if isinstance(source, list) else (source or "")
            code_hits += sum(1 for _ in _CURE_RE.finditer(code_text))

    if write and total_cures > 0:
        with open(path, "w", encoding="utf-8", newline="\n") as f:
            json.dump(nb, f, ensure_ascii=False, indent=1)
            f.write("\n")
    return {
        "cures": total_cures,
        "cells_touched": cells_touched,
        "md_cells": md_cells,
        "code_hits": code_hits,
    }


def main(argv=None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    p.add_argument("notebook", help="Chemin du notebook (.ipynb)")
    p.add_argument("--dry-run", action="store_true",
                   help="Liste les cures prevues sans ecrire (defaut)")
    p.add_argument("--apply", action="store_true",
                   help="Applique les cures en place (re-ecrit le notebook)")
    p.add_argument("--check", action="store_true",
                   help="Exit 1 si des cures sont disponibles (CI-ready, n'ecrit rien)")
    p.add_argument("--scope", action="store_true",
                   help="Avec --check : exit 1 aussi si du code contient des formes "
                        "accentuables residuelles (signe de script ad-hoc precedent)")
    p.add_argument("--json", action="store_true", help="Sortie machine JSON")
    args = p.parse_args(argv)

    if args.apply and args.check:
        print("--apply et --check sont mutuellement exclusifs", file=sys.stderr)
        return 2
    write = args.apply

    nb_path = Path(args.notebook)
    if not nb_path.exists():
        print(f"Notebook introuvable: {nb_path}", file=sys.stderr)
        return 2

    res = cure_notebook(nb_path, write=write, check_scope=args.scope)
    if "error" in res:
        msg = f"Notebook illisible: {res['error']}"
        if args.json:
            print(json.dumps({"error": msg}, ensure_ascii=False))
        else:
            print(msg, file=sys.stderr)
        return 2

    if args.json:
        out = {
            "notebook": str(nb_path),
            "mode": "apply" if write else "dry-run",
            **res,
        }
        print(json.dumps(out, ensure_ascii=False, indent=2))
    else:
        verb = "CURED (written)" if write else "would cure"
        print(f"{nb_path}: {verb} {res['cures']} accent(s) in "
              f"{res['cells_touched']}/{res['md_cells']} markdown cells")
        if args.scope and res["code_hits"]:
            print(f"  WARNING: {res['code_hits']} accentable form(s) found in CODE cells "
                  f"(HORS scope #2876 — possible ad-hoc script residue)")

    if args.check:
        if res["cures"] > 0 or (args.scope and res["code_hits"] > 0):
            return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
