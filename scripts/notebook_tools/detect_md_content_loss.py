#!/usr/bin/env python3
"""Detecte la perte de contenu markdown entre la base d'une PR et sa tete (#8655).

Pourquoi cet outil existe
-------------------------
Le rollout #3966 (demotion des titres-H1/H2 en callouts blockquote `> **X :**`)
a un defaut mecanique silencieux : quand le correcteur one-shot opere "a la
granularite ligne" sur une cellule dont le `source` est une **chaine unique
jointe** (et non une liste de lignes), remplacer la "ligne" du titre remplace
la **cellule entiere**. Une cellule de 941 caracteres se reduit a 16 ; un
bloc `**Navigation**` + 5 objectifs + contexte disparait au profit d'un simple
titre H2. Et la CI reste verte : `scan_md_hierarchy`, le verificateur de liens,
le catalogue, la parite des jumeaux -- aucun ne mesure le **volume de prose
markdown**. Une cellule 941c -> 16c compte pour `1-/1+` au `git diff --stat`.

Deux PR reelles ont passe tous les gardes en detruisant du contenu
(issue #8655, verifie firsthand) :

  | PR    | Notebook                              | Cell | Avant | Apres | Contenu perdu                    |
  |-------|---------------------------------------|------|-------|-------|----------------------------------|
  | #8654 | Sudoku/Sudoku-1-...Python.ipynb       | 9    | 941 c | 16 c  | enonce + 4 contraintes + 3 indices|
  | #8630 | GenAI/Texte/11_Quantization.ipynb     | 3    | 998 c | 28 c  | Navigation + duree + prerequis   |
  | #8630 | GenAI/Texte/12_Test_Time_Scaling.ipynb| 2    | 1655c | 61 c  | Navigation + ref Snell 2024      |

Comment ca marche
-----------------
Pour chaque notebook compare entre sa base git (defaut origin/main) et sa tete
(working tree ou ref explicite), cet outil :

  1. NORMALISE le contenu markdown de chaque cellule : retire les marqueurs de
     titre `#{1,6}` et les callouts `> **... :**` (la transformation LEGITIME
     du rollout #3966), plus les espaces. La demotion d'un titre en callout
     laisse alors une empreinte NORMALISEE IDENTIQUE -> invisible. Une perte
     reelle de contenu se traduit par une chute du volume normalise.

  2. COMPARAISON PAR FICHIER (total normalise) puis, **uniquement quand le
     nombre de cellules est inchange**, descente au niveau cellule (design #1
     de l'issue #8655). Une fusion/scission de cellule decale les index et
     produirait des faux positifs position-par-position : on s'en garde en
     restant au niveau fichier quand le compte bouge.

  3. SEUIL DE CHUTE RELATIVE par cellule : signal si le volume normalise
     devient < 75 % du volume d'origine, ET l'original etait substantiel
     (>= MIN_ORIG_CHARS, pour ignorer les cellules triviales). Les 3 cas reels
     chutent a 1-4 %, avec une marge enorme sous le seuil ; une reformulation
     honnete qui resserre de 10-20 % reste au-dessus de 75 %.

  4. MOTIFS STRUCTURANTS PERDUS : signale explicitement la disparition de
     `**Navigation**`, `**Objectif(s)**`, `**Prerequis**`, `### Enonce`, et
     des liens de navigation `[...](*.ipynb)` -- des elements dont la perte
     est un signal fort independamment du seuil de caracteres.

  5. NE BLOQUE PAS LA REFORMULATION LEGITIME : le detecteur SIGNALE, la PR
     justifie en review (design #4). Sortie exploitable : fichier / cellule /
     avant-apres / ratio / motifs perdus.

Usage
-----
    # un notebook, diff vs origin/main (head = working tree)
    python detect_md_content_loss.py NB.ipynb --check
    python detect_md_content_loss.py NB.ipynb --base origin/main --head origin/fix/ma-branche --check
    # sortie machine
    python detect_md_content_loss.py NB.ipynb --json

Exit codes
----------
    0 -- aucune perte de contenu detectee (ou mode non --check)
    1 -- une ou plusieurs pertes detectees (--check)
    2 -- erreur (notebook illisible, ref git introuvable)

Voir aussi
----------
- detect_link_target_regression.py -- modele de detecteur base-vs-head
- detect_caps_regression.py (#7198) -- autre regression markdown base-vs-head
- scan_md_hierarchy / check_notebook_navlinks -- gardes existants (volume-aveugles)
- Issue #8655 -- cahier des charges + 3 cas reels
- Registre #3966 -- le rollout demotion-de-titres dont provient le defaut
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

# Seuil de chute relative : une cellule signale si son volume normalise devient
# strictement inferieur a DROP_THRESHOLD x le volume d'origine (issue #8655 :
# "p. ex. < 75 % du volume d'origine"). Les 3 cas reels chutent a 1-4 %.
DROP_THRESHOLD = 0.75
# Volume normalise minimal d'origine pour qu'une chute soit signalee : evite
# le bruit sur les cellules triviales (un titre seul, un separateur).
MIN_ORIG_CHARS = 100

# Motifs structurants dont la disparition est un signal fort (design #3 #8655).
# Notes : "Navigation" / "Objectif(s)" / "Prerequis" sont matches aussi bien en
# titre (`## Navigation`) qu'en callout (`> **Navigation :**`) car la regex
# cible le mot-cle hors-marqueurs. Les liens de navigation vers un notebook
# sont comptes collectivement (perte = N liens disparus).
MOTIF_PATTERNS = [
    (re.compile(r"\bNavigation\b", re.I), "Navigation"),
    (re.compile(r"\bObjectifs?\b", re.I), "Objectif(s)"),
    (re.compile(r"\bPr[eé]requis\b", re.I), "Prerequis"),
    (re.compile(r"^#{1,6}\s*Enonc[eé]", re.I | re.M), "Enonce"),
]
NAV_LINK_RE = re.compile(r"\[[^\]]+\]\([^)]+\.ipynb\)")


def _normalize(md_text: str) -> str:
    """Normalise le contenu markdown pour la comparaison de volume.

    Retire les transformations LEGITIMES du rollout #3966 (titre H1-H6 ->
    callout blockquote `> **X :**`) afin qu'une demotion honnete laisse une
    empreinte identique (pas de signal), puis retire les espaces. Une perte
    reelle de contenu (cellule tronquee) se traduit par une chute du volume.
    """
    # 1. Marqueurs de titre en debut de ligne : "## Foo" -> "Foo".
    t = re.sub(r"^[ \t]*#{1,6}[ \t]+", "", md_text, flags=re.M)
    # 2. Callouts blockquote de la forme "> **Mot :** ..." (leger data du
    #    rollout #3966) : on retire la LIGNE-entiere de callout quand elle
    #    n'est QU'un marqueur (pas de contenu supplaitre apres). Cela evite
    #    qu'un titre legitiment demote en callout soit compte comme "nouveau"
    #    contenu par rapport au titre original.
    t = re.sub(r"^[ \t]*>\s*\*\*[^*\n]*:\*\*\s*$", "", t, flags=re.M)
    # 3. Espaces : on compare le volume de PROSE, pas la mise en forme.
    t = re.sub(r"\s+", "", t)
    return t


def _norm_len(md_text: str) -> int:
    return len(_normalize(md_text))


def extract_md_cells(nb: dict) -> list[tuple[int, str]]:
    """Retourne [(cell_idx, source_str)] pour les cellules markdown seulement."""
    out = []
    for idx, c in enumerate(nb.get("cells", [])):
        if c.get("cell_type") != "markdown":
            continue
        src = c.get("source", [])
        src = "".join(src) if isinstance(src, list) else (src or "")
        out.append((idx, src))
    return out


def _collect_motifs(nb: dict) -> dict:
    """Compte les occurrences de chaque motif structurant dans le notebook.

    Retourne {motif_label: count} + {'nav_links': count}. La comparaison
    base/head revelera les motifs disparus (count tombe a 0).
    """
    counts: dict = {}
    full_md = "\n".join(src for _, src in extract_md_cells(nb))
    for pat, label in MOTIF_PATTERNS:
        counts[label] = len(pat.findall(full_md))
    counts["nav_links"] = len(NAV_LINK_RE.findall(full_md))
    return counts


def read_notebook_at_ref(nb_path: Path, ref: str) -> dict | None:
    """Lit le contenu d'un notebook a un ref git donne via `git show ref:path`."""
    rel = nb_path.as_posix()
    try:
        out = subprocess.run(
            ["git", "show", f"{ref}:{rel}"],
            capture_output=True, text=True, encoding="utf-8", check=False,
        )
    except (FileNotFoundError, OSError):
        return None
    if out.returncode != 0 or not out.stdout:
        return None
    try:
        return json.loads(out.stdout)
    except json.JSONDecodeError:
        return None


def _compare_cells(base_md: list[tuple[int, str]],
                   head_md: list[tuple[int, str]]) -> list[dict]:
    """Compare cellule-par-cellule (INDEX STABLE requis, design #1 #8655).

    Ne descend au niveau cellule QUE quand le nombre de cellules markdown est
    inchange entre base et head ; sinon une fusion/scission decale les index et
    produirait des faux positifs position-par-position (26 FP observes sur
    10_LocalLlama.ipynb, cite dans l'issue). Retourne les cellules tronquees.
    """
    findings: list[dict] = []
    if len(base_md) != len(head_md):
        return findings  # compte modifie -> la comparaison fichier suffit
    for (b_idx, b_src), (h_idx, h_src) in zip(base_md, head_md):
        b_norm = _norm_len(b_src)
        h_norm = _norm_len(h_src)
        if b_norm < MIN_ORIG_CHARS:
            continue  # cellule d'origine trop courte pour qu'une chute soit du bruit
        if h_norm < DROP_THRESHOLD * b_norm:
            ratio = (h_norm / b_norm) if b_norm else 0.0
            findings.append({
                "kind": "TRUNCATED_CELL",
                "cell_idx": h_idx,
                "before_chars": b_norm,
                "after_chars": h_norm,
                "ratio": round(ratio, 3),
                "before_excerpt": b_src.strip().split("\n", 1)[0][:90],
                "after_excerpt": h_src.strip().split("\n", 1)[0][:90],
            })
    return findings


def _compare_motifs(base_counts: dict, head_counts: dict) -> list[dict]:
    """Signale les motifs structurants disparus (present en base, absent en head)."""
    findings: list[dict] = []
    for key, b_count in base_counts.items():
        h_count = head_counts.get(key, 0)
        if b_count > 0 and h_count == 0:
            findings.append({
                "kind": "LOST_MOTIF",
                "motif": key,
                "before_count": b_count,
            })
        elif key == "nav_links" and h_count < b_count:
            # Perte PARTIELLE de liens de navigation : signalee (secondary).
            findings.append({
                "kind": "LOST_NAV_LINKS",
                "motif": "nav_links",
                "before_count": b_count,
                "after_count": h_count,
                "delta": b_count - h_count,
            })
    return findings


def scan_notebook(nb_path: Path, base_ref: str, head_ref: str | None = None) -> dict:
    """Compare le contenu markdown d'un notebook entre base_ref et head_ref."""
    if head_ref is None:
        try:
            nb_head = json.loads(nb_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as e:
            return {"notebook": str(nb_path), "error": f"head unreadable: {e}"}
        head_label = "working_tree"
    else:
        nb_head = read_notebook_at_ref(nb_path, head_ref)
        if nb_head is None:
            return {"notebook": str(nb_path), "error": f"head_ref {head_ref} unreadable"}
        head_label = head_ref

    nb_base = read_notebook_at_ref(nb_path, base_ref)
    if nb_base is None:
        return {"notebook": str(nb_path), "error": f"base_ref {base_ref} unreadable"}

    base_md = extract_md_cells(nb_base)
    head_md = extract_md_cells(nb_head)

    findings: list[dict] = []
    findings.extend(_compare_cells(base_md, head_md))
    findings.extend(_compare_motifs(_collect_motifs(nb_base), _collect_motifs(nb_head)))

    base_total = sum(_norm_len(s) for _, s in base_md)
    head_total = sum(_norm_len(s) for _, s in head_md)

    return {
        "notebook": str(nb_path),
        "base_ref": base_ref,
        "head_ref": head_label,
        "findings": findings,
        "stats": {
            "base_md_cells": len(base_md),
            "head_md_cells": len(head_md),
            "cell_count_stable": len(base_md) == len(head_md),
            "base_total_normalized_chars": base_total,
            "head_total_normalized_chars": head_total,
            "findings_count": len(findings),
        },
    }


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    p.add_argument("notebook", type=Path, help="Chemin vers le .ipynb")
    p.add_argument("--base", default="origin/main", help="Ref git de la base (defaut origin/main)")
    p.add_argument("--head", default=None, help="Ref git du head (defaut working tree)")
    p.add_argument("--check", action="store_true", help="Exit 1 si perte detectee (CI)")
    p.add_argument("--json", action="store_true", help="Sortie JSON machine")
    args = p.parse_args(argv)

    if not args.notebook.exists():
        print(f"ERROR: notebook introuvable: {args.notebook}", file=sys.stderr)
        return 2

    result = scan_notebook(args.notebook, args.base, args.head)

    if "error" in result:
        print(f"ERROR: {result['error']}", file=sys.stderr)
        return 2

    if args.json:
        print(json.dumps(result, ensure_ascii=False, indent=2))
    else:
        nb = result["notebook"]
        st = result["stats"]
        fins = result["findings"]
        print(f"[NOTEBOOK] {nb}")
        print(f"[BASE]     {result['base_ref']}")
        print(f"[HEAD]     {result['head_ref']}")
        print(f"[STATS]    md_cells base={st['base_md_cells']} head={st['head_md_cells']} "
              f"stable={st['cell_count_stable']} | "
              f"normalized_chars base={st['base_total_normalized_chars']} "
              f"head={st['head_total_normalized_chars']} | findings={st['findings_count']}")
        if fins:
            print("\n[FINDINGS]")
            for f in fins:
                if f["kind"] == "TRUNCATED_CELL":
                    print(f"  - cell {f['cell_idx']} {f['kind']}: "
                          f"{f['before_chars']}c -> {f['after_chars']}c "
                          f"(ratio {f['ratio']}, seuil {DROP_THRESHOLD})")
                    print(f"      before: {f['before_excerpt']!r}")
                    print(f"      after:  {f['after_excerpt']!r}")
                elif f["kind"] == "LOST_MOTIF":
                    print(f"  - {f['kind']}: '{f['motif']}' disparu "
                          f"(base={f['before_count']})")
                elif f["kind"] == "LOST_NAV_LINKS":
                    print(f"  - {f['kind']}: {f['delta']} lien(s) de navigation en moins "
                          f"({f['before_count']} -> {f['after_count']})")

    if args.check and result["findings"]:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
