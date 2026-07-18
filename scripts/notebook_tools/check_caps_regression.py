#!/usr/bin/env python3
"""Detecte les caps-regressions des cures d'accents markdown (registre #2876).

Pourquoi cet outil existe
-------------------------
Le registre #2876 (restauration des accents francais, markdown-only STRICT) a
produit un nouveau defect-class en juillet 2026 : des scripts de cure ad-hoc
accentuent correctement le mot MAIS en minusculent l'INITIALE capitalisee.

  - `Systeme de Classement` -> `système de Classement` (titre H1 : devait etre `Système`)
  - `| **Equipes** |`          -> `| **équipes** |`        (header table : devait être `**Équipes**`)
  - `Apres chaque match`      -> `après chaque match`     (debut phrase : devait être `Après`)

La cure canonique `restore_accents_canonical.py` (#7186) preserve la casse PAR
CONSTRUCTION (`_preserve_case`), mais les scripts ad-hoc anterieurs non. Le
guard `check_identifier_regression.py` (#7157) detecte les regressions
d'IDENTIFIANTS (code) mais PAS les caps-regressions markdown — ce tool comble
ce gap. Incident fondateur : 3 cycles po-2023/po-2024 ont discrepe firsthand
sur ~10 PRs (alerte -> auto-confirm -> retraction -> retraction elle-meme
fausse) faute d'un detecteur objectif.

Comment ca marche
-----------------
Pour chaque cellule MARKDOWN, on aligne ligne-par-ligne la base (defaut
origin/main) et la HEAD (working tree ou origin/<branch>). Pour chaque mot
aligne qui differe entre base et head :

  1. on verifie que c'est bien une CURE (deaccent(head).lower() == base.lower()
     ET base != head) — sinon on ignore (modification non-accent) ;
  2. on compare la casse de l'initiale : si base[0] est MAJUSCULE et head[0] ne
     l'est pas -> **CAPS-REGRESSION** (la cure a perte la capitale) ;
  3. idem pour le ALL-CAPS : si base est tout-majuscule (len>1) et head ne
     l'est pas -> **CAPS-REGRESSION**.

L'alignement ligne-par-ligne (methode po-2025 c.615, ratifiee sur #7191 = 36
vraies regressions byte-verified) evite le faux-positif massif du scan
non-positionnel : un meme mot FR apparait souvent EN majuscule (titre/header)
ET en minuscule (mi-phrase) dans deux lignes differentes ; curer legitimement
l'occurrence minuscule ne doit PAS etre flaggue. On compare la MEME ligne.

L'outil lit seulement (local git : git show). Il ne touche rien.

Usage
-----
    # un notebook : working tree vs origin/main
    python check_caps_regression.py NB.ipynb
    python check_caps_regression.py NB.ipynb --base origin/main --head origin/fix/ma-branche
    # exit 1 si caps-regression detectee (CI-ready)
    python check_caps_regression.py NB.ipynb --check
    # sortie machine
    python check_caps_regression.py NB.ipynb --json

Exit codes
----------
    0 -- aucune caps-regression detectee (ou mode non --check)
    1 -- un ou plusieurs mots a initiale minusculee (--check seulement)
    2 -- erreur (notebook illisible, ref git introuvable)

Voir aussi
----------
- check_identifier_regression.py (registre #2876, regressions d'IDENTIFIANTS code)
- restore_accents_canonical.py (#7186, cure canonique caps-preserving)
- detect_accent_stripping.py (#2876, moitie DETECTION des accents perdus)
- Memoires : issue-2876-scope-boundary-markdown-vs-code-pending-adjudication
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import unicodedata
from pathlib import Path

# Run de mot : lettres (y compris accentuees). On exclut chiffres et underscore
# pour matcher le vocabulaire francais accentuable (pas les identifiants code,
# meme si on est en markdown — on cible la prose).
_WORD_RE = re.compile(r"[A-Za-zÀ-ÖØ-öø-ÿ]+")

# Caracteres accentues : un mot head qui en contient au moins un est candidat
# cure. Evite de traiter les mots purement ASCII inchanges comme des cures.
_ACCENT_CHARS = set("àâäéèêëïîôöùûüçÀÂÄÉÈÊËÏÎÔÖÙÛÜÇœŒæÆ")


def _deaccent(s: str) -> str:
    return "".join(
        c for c in unicodedata.normalize("NFD", s) if unicodedata.category(c) != "Mn"
    )


def _has_accent(s: str) -> bool:
    return any(ch in _ACCENT_CHARS for ch in s)


def _src_str(cell: dict) -> str:
    s = cell.get("source", "")
    return "".join(s) if isinstance(s, list) else (s or "")


def _git_show_notebook(ref: str, path: str):
    """Lit un notebook a une ref git (None si introuvable)."""
    r = subprocess.run(["git", "show", f"{ref}:{path}"], capture_output=True)
    if r.returncode != 0:
        return None
    try:
        return json.loads(r.stdout.decode("utf-8"))
    except Exception:
        return None


def _md_lines(nb: dict):
    """Retourne [(cell_index, line_index, line)] pour les cellules markdown uniquement."""
    out = []
    for ci, cell in enumerate(nb.get("cells", [])):
        if cell.get("cell_type") != "markdown":
            continue
        for li, line in enumerate(_src_str(cell).split("\n")):
            out.append((ci, li, line))
    return out


def scan(old_nb: dict, new_nb: dict):
    """Compare les cellules markdown old vs new, ligne-par-ligne.

    Retourne (regressions, summary) ou :
      regressions : [(cell_index, line_index, base_word, head_word, context)]
      summary     : dict {cures, struct_changed_lines, caps_regressions}

    Une caps-regression = cure (base non-accentue -> head accentue meme mot)
    dont l'initiale est PASSEE de majuscule a minuscule (ou all-caps -> mixed).
    """
    old_map = {(ci, li): line for ci, li, line in _md_lines(old_nb)}
    new_lines = _md_lines(new_nb)

    regressions = []
    cures = 0
    struct_changed = 0

    for ci, li, nline in new_lines:
        oline = old_map.get((ci, li))
        if oline is None or oline == nline:
            continue  # ligne ajoute ou inchangee
        bwords = _WORD_RE.findall(oline)
        hwords = _WORD_RE.findall(nline)
        if len(bwords) != len(hwords):
            # Le nombre de mots differe = modification structurelle (pas une cure
            # 1:1). On ne peut pas aligner mot-a-mot sans risque de FP ; on
            # compte la ligne comme struct-changed et on ne la scanne PAS (un
            # notebook cure-only n'a JAMAIS de struct-changed — cf test).
            struct_changed += 1
            continue
        for bword, hword in zip(bwords, hwords):
            if bword == hword:
                continue
            # cure candidate : deaccent(head) lower == base lower ?
            if _deaccent(hword).lower() != bword.lower():
                continue
            if not _has_accent(hword):
                continue  # head n'a pas d'accent -> pas une cure
            cures += 1
            # caps check
            bcap = bool(bword) and bword[0].isupper()
            hcap = bool(hword) and hword[0].isupper()
            if bcap and not hcap:
                regressions.append((ci, li, bword, hword, oline.strip()[:90]))
            elif len(bword) > 1 and bword.isupper() and not hword.isupper():
                regressions.append((ci, li, bword, hword, oline.strip()[:90]))

    summary = {
        "cures": cures,
        "struct_changed_lines": struct_changed,
        "caps_regressions": len(regressions),
    }
    return regressions, summary


def main(argv=None) -> int:
    p = argparse.ArgumentParser(
        description="Detecte les caps-regressions des cures d'accents markdown (#2876)."
    )
    p.add_argument("notebook", help="Chemin du notebook (.ipynb)")
    p.add_argument("--base", default="origin/main",
                   help="Ref git de la base (defaut origin/main)")
    p.add_argument("--head", default=None,
                   help="Ref git de la head (defaut: working tree lu depuis le disque)")
    p.add_argument("--check", action="store_true",
                   help="Exit 1 si une caps-regression est detectee (CI-ready, n'ecrit rien)")
    p.add_argument("--json", action="store_true", help="Sortie machine JSON")
    args = p.parse_args(argv)

    nb_path = Path(args.notebook)
    if not nb_path.exists() and args.head is None:
        print(f"error: notebook introuvable: {args.notebook}", file=sys.stderr)
        return 2

    # path relatif au repo pour git show
    git_path = args.notebook.replace("\\", "/")
    if nb_path.exists():
        git_path = str(nb_path.resolve().relative_to(Path.cwd().resolve())).replace("\\", "/") \
            if nb_path.resolve().parent != Path.cwd().resolve() else nb_path.name

    old_nb = _git_show_notebook(args.base, git_path)
    if old_nb is None:
        # fallback : lire git_path tel quel (cas ou l'utilisateur a donne un path repo-root)
        old_nb = _git_show_notebook(args.base, args.notebook.replace("\\", "/"))
    if old_nb is None:
        print(f"error: notebook introuvable a la base {args.base}:{git_path}", file=sys.stderr)
        return 2

    if args.head is None:
        if not nb_path.exists():
            print(f"error: notebook introuvable: {args.notebook}", file=sys.stderr)
            return 2
        with open(nb_path, encoding="utf-8") as f:
            new_nb = json.load(f)
    else:
        new_nb = _git_show_notebook(args.head, git_path)
        if new_nb is None:
            new_nb = _git_show_notebook(args.head, args.notebook.replace("\\", "/"))
        if new_nb is None:
            print(f"error: notebook introuvable a la head {args.head}:{git_path}", file=sys.stderr)
            return 2

    regressions, summary = scan(old_nb, new_nb)

    if args.json:
        out = {
            "notebook": str(nb_path) if nb_path.exists() else args.notebook,
            "base": args.base,
            "head": args.head or "working-tree",
            "caps_regressions": [
                {
                    "cell": ci, "line": li,
                    "base_word": bw, "head_word": hw, "context": ctx,
                }
                for ci, li, bw, hw, ctx in regressions
            ],
            "summary": summary,
        }
        json.dump(out, sys.stdout, ensure_ascii=False, indent=2)
        sys.stdout.write("\n")
    else:
        if summary["caps_regressions"] == 0:
            print(f"OK — aucune caps-regression ({summary['cures']} cures markdown "
                  f"verifiees, {summary['struct_changed_lines']} ligne(s) struct-modifiee(s), "
                  f"{args.notebook})")
        else:
            print(f"FOUND {summary['caps_regressions']} caps-regression(s) markdown "
                  f"sur {summary['cures']} cures ({args.notebook}):\n")
            for ci, li, bw, hw, ctx in regressions:
                print(f"  cell {ci} L{li}: {bw!r} -> {hw!r}")
                print(f"    | {ctx}")
            if summary["struct_changed_lines"]:
                print(f"\n(note: {summary['struct_changed_lines']} ligne(s) avec nb de mots "
                      f"modifie = non scannee(s) pour eviter FP d'alignement)")

    if args.check and summary["caps_regressions"] > 0:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
