"""check_end_block_answers.py -- repere les blocs "Verifiez votre comprehension"
sans reponse.

Source : le Concern du mainteneur pose sur la PR #27049 (commentaire
6943057003) -- les sections "verifiez votre comprehension" doivent avoir les
reponses (les *exercices* restant volontairement sans reponse) -- et l'issue de
lot #27611 (Part of #19297) qui en porte le rattrapage par serie.

Ce que l'organe fait
--------------------
Il distingue deux familles de titres de fin de carnet, que l'on-device de la
campagne #19297 melange :

  - "Verifiez votre comprehension" (et ses variantes anglaises / "questions de
    comprehension" / "auto-evaluation") : le controle de comprehension, dont la
    reponse SE TROUVE dans le carnet et doit donc y etre fournie, repliee
    (`<details><summary>... reponse ...</summary>`) ou inline.
  - "Exercices" / "quiz" / "questions" nus : l'exercice volontairement SANS
    reponse (convention C.1).

L'organe ne flaggue que la PREMIERE famille : un carnet qui porte un bloc
"verifiez votre comprehension" canonique dont AUCUNE des questions n'est
accompagnee d'une reponse. C'est precisement le defaut que le mainteneur
rapporte, et le piece qui rend le format de la campagne homogene.

Le faux positif fondateur (mesure en ecrivant l'organe) : un detecteur LARGE
qui compte aussi les blocs "Exercices" signalait de facons erronees des carnets
sains -- ChoixSocial-08-Kemeny-RankedPairs-Dodgson, qui est precisement le
FORMAT DE REFERENCE de la campagne (bloc "verifiez" avec
`<details><summary>Elements de reponse</summary>`), etait listé "sans reponse"
parce qu'il porte AUSSI une section "Exercices" sans reponse. L'organe resserré
sur la famille "comprehension" ci-dessus le blanchit : le controle positif
`--self-test` le porte et doit rester vert.

Deux modes
----------
  --series <nom>   TRIADE / triage : liste, pour une serie (ou sous-serie)
                   donnee, tous les carnets dont un bloc "verifiez votre
                   comprehension" canonique n'a pas de reponse. C'est le mode
                   qui "premache le gros du boulot" du lot : il produit la
                   liste a pourvoir, serie par serie.
  <base>           RATCHET CI : parmi les carnets .ipynb MODIFIES par la PR
                   (vs `base`), flag ceux dont le COMPTE de blocs "verifiez"
                   sans reponse AUGMENTE. L'heritage de base est EXEMPT : un
                   bloc sans reponse deja present a la base ne re-rougit pas
                   (advisory, comme les ratchets check_output_collapse /
                   check_source_collapse, TRANCHE2/11 de fast_lane_registry).

Exit codes
----------
  0 : aucun bloc sans reponse (triage) / aucun bloc sans reponse INTRODUIT (ratchet)
  1 : au moins un bloc sans reponse
  2 : erreur (serie inconnue, base illisible, JSON mal forme, ...)

Usage :
    python check_end_block_answers.py --series GameTheory
    python check_end_block_answers.py --series GameTheory --json
    python check_end_block_answers.py origin/main        # mode CI (advisory)
    python check_end_block_answers.py --self-test
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys

SERIES_ROOT = "MyIA.AI.Notebooks"

# Famille STRICTE "controle de comprehension" -- le bloc qui DOIT avoir des
# reponses. EXCLU de fait : "exercices", "quiz", "questions" nus, "self-test",
# "auto-test", "verifiez vous" -- ce sont les familles volontairement sans
# reponse (ou ambigues) que le detecteur large comptait a tort (faux positif
# ChoixSocial-08, ci-dessus).
VERIF_TITLES = re.compile(
    r"^#{2,3}\s*(vérifiez votre compréhension|verifiez votre comprehension|"
    r"check your understanding|questions? de compr[ée]hension|"
    r"auto-?[ée]valuation|auto-?evaluation)\s*$",
    re.IGNORECASE,
)
# Tout autre titre H2/H3 termine le bloc en cours.
OTHER_HEADING = re.compile(r"^#{2,3}\s")
# Une reponse repliee : `<details>` ... `<summary>` portant un mot de reponse.
DETAILS_OPEN = re.compile(r"<details>", re.IGNORECASE)
SUMMARY_ANSWER = re.compile(
    r"<summary>\s*(?:[ée]l[ée]ments? de r[ée]ponse|r[ée]ponses?|"
    r"solution|corrig[ée]|r[ée]ponse)",
    re.IGNORECASE,
)
# Une reponse inline : une ligne "Reponses :" / "Solution :" au debut du bloc.
INLINE_ANSWER = re.compile(
    r"^\s*(?:\*\*)?(r[ée]ponses?|solution|corrig[ée])(?:\*\*)?\s*[:\-—]",
    re.IGNORECASE,
)


def verif_blocks(nb: dict) -> list[list[str]]:
    """Extraire les blocs "verifiez votre comprehension" d'un carnet.

    Retourne une liste de blocs ; chaque bloc est la liste de lignes du corps
    du bloc (entre son titre et le prochain titre H2/H3). Un carnet peut
    porter plusieurs tels blocs.
    """
    blocks: list[list[str]] = []
    cur: list[str] | None = None
    for cell in nb.get("cells", []):
        if cell.get("cell_type") != "markdown":
            continue
        for line in "".join(cell.get("source", [])).splitlines():
            s = line.strip()
            if VERIF_TITLES.match(s):
                cur = []
                blocks.append(cur)
                continue
            if OTHER_HEADING.match(s):
                cur = None
                continue
            if cur is not None:
                cur.append(line)
    return blocks


def block_has_answer(block: list[str]) -> bool:
    """Un bloc a une reponse s'il porte un `<details>`+`<summary>` de reponse,
    ou une ligne de reponse inline."""
    body = "\n".join(block)
    if DETAILS_OPEN.search(body) and SUMMARY_ANSWER.search(body):
        return True
    return any(INLINE_ANSWER.match(l) for l in block)


def no_answer_blocks(nb: dict) -> list[list[str]]:
    """Les blocs 'verifiez votre comprehension' du carnet SANS reponse."""
    return [b for b in verif_blocks(nb) if not block_has_answer(b)]


def count_no_answer(nb: dict) -> int:
    return len(no_answer_blocks(nb))


# ---------------------------------------------------------------------------
# Mode triage : --series
# ---------------------------------------------------------------------------

def _confined_series(name: str) -> str | None:
    """Confine un nom de serie/sous-serie sous SERIES_ROOT (cf
    check_series_finish.normalize_series_path)."""
    if not name or not isinstance(name, str):
        return None
    cand = name.strip().replace("\\", "/")
    if cand.startswith("/") or ":" in cand:
        return None
    segs = cand.split("/")
    if any(x in ("", ".", "..") for x in segs):
        return None
    if any(x.startswith(".") for x in segs):
        return None
    root = os.path.abspath(SERIES_ROOT)
    target = os.path.abspath(os.path.join(SERIES_ROOT, cand))
    if not (target == root or target.startswith(root + os.sep)):
        return None
    return cand


def _series_notebooks(series: str) -> list[str]:
    root = os.path.join(SERIES_ROOT, series)
    out = []
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [d for d in dirnames
                       if d not in ("_archive", "_output", ".ipynb_checkpoints")]
        for fn in sorted(filenames):
            if fn.endswith(".ipynb") and not fn.endswith("_output.ipynb"):
                out.append(os.path.join(dirpath, fn))
    return sorted(out)


def triage(series: str) -> dict:
    """Mode triage : liste les carnets de la serie dont un bloc 'verifiez'
    canonique n'a pas de reponse."""
    norm = _confined_series(series)
    if norm is None:
        return {"series": series, "error": "invalid_series_name", "rc": 2}
    if not os.path.isdir(os.path.join(SERIES_ROOT, norm)):
        return {"series": series, "error": "series_not_found", "rc": 2}
    with_answer = 0
    flagged = []
    errors = []
    for path in _series_notebooks(norm):
        try:
            with open(path, encoding="utf-8") as fh:
                nb = json.load(fh)
        except Exception as e:  # noqa: BLE001 - un carnet illisible est reporte
            errors.append({"path": path, "error": str(e)})
            continue
        n = count_no_answer(nb)
        if n:
            flagged.append({"path": path.replace(os.sep, "/"), "blocks": n})
        elif verif_blocks(nb):
            with_answer += 1
    total = with_answer + len(flagged)
    return {
        "series": norm,
        "rc": 1 if flagged else 0,
        "verif_total": total,
        "with_answer": with_answer,
        "no_answer": len(flagged),
        "flagged": flagged,
        "errors": errors,
    }


# ---------------------------------------------------------------------------
# Mode ratchet CI : <base>
# ---------------------------------------------------------------------------

def _git(*args: str) -> str:
    return subprocess.run(["git", *args], capture_output=True, text=True,
                          encoding="utf-8", errors="replace").stdout


def _changed_notebooks(base: str) -> list[str]:
    out = _git("diff", "--name-only", "--diff-filter=ACMR",
               f"{base}...HEAD")
    return [p for p in out.splitlines()
            if p.strip().endswith(".ipynb") and not p.strip().endswith("_output.ipynb")]


def _base_blob(base: str, path: str) -> dict | None:
    out = subprocess.run(["git", "show", f"{base}:{path}"],
                         capture_output=True, text=True,
                         encoding="utf-8", errors="replace")
    if out.returncode != 0:
        return None  # nouveau fichier : pas de version a la base
    try:
        return json.loads(out.stdout)
    except Exception:  # noqa: BLE001
        return None


def ratchet(base: str) -> dict:
    """Mode ratchet CI : flag les carnets modifies dont le COMPTE de blocs
    'verifiez' sans reponse AUGMENTE vs la base. L'heritage de base est
    exempt (compte base == compte head -> pas de flag)."""
    try:
        merge_base = _git("merge-base", base, "HEAD").strip()
    except Exception:  # noqa: BLE001
        merge_base = base
    rows = []
    for path in _changed_notebooks(base):
        try:
            with open(path, encoding="utf-8") as fh:
                head_nb = json.load(fh)
        except Exception as e:  # noqa: BLE001
            rows.append({"path": path, "error": str(e)})
            continue
        head_n = count_no_answer(head_nb)
        base_nb = _base_blob(merge_base, path)
        base_n = count_no_answer(base_nb) if base_nb is not None else 0
        introduced = max(0, head_n - base_n)
        rows.append({
            "path": path.replace(os.sep, "/"),
            "base_no_answer": base_n,
            "head_no_answer": head_n,
            "introduced": introduced,
            "flagged": introduced > 0,
        })
    flagged = [r for r in rows if r.get("flagged")]
    return {
        "base_ref": base,
        "merge_base": merge_base,
        "changed": len(rows),
        "flagged": len(flagged),
        "rows": rows,
        "rc": 1 if flagged else 0,
    }


# ---------------------------------------------------------------------------
# Self-test : controles positifs / negatifs + faux positif fondateur
# ---------------------------------------------------------------------------

def _nb(cells: list[tuple[str, str]]) -> dict:
    return {"cells": [{"cell_type": t, "source": s} for t, s in cells]}


def self_test() -> int:
    failures = []

    # Positif : un bloc "verifiez" sans reponse -> detecte.
    pos = _nb([
        ("markdown", "## Vérifiez votre compréhension\n1. Pourquoi ?\n2. Comment ?\n"),
    ])
    if count_no_answer(pos) != 1:
        failures.append("positif : bloc sans reponse non detecte")

    # Negatif : un bloc "verifiez" AVEC reponse repliee -> blanchi.
    neg = _nb([
        ("markdown",
         "## Vérifiez votre compréhension\n1. Pourquoi ?\n"
         "<details>\n<summary>Éléments de réponse</summary>\n"
         "1. Parce que.\n</details>\n"),
    ])
    if count_no_answer(neg) != 0:
        failures.append("negatif : bloc avec reponse repliee faussement flaggue")

    # Faux positif fondateur : "Exercices" (sans reponse) + "verifiez" (avec
    # reponse) -> le carnet est SAIN, l'organe ne doit PAS le flaguer.
    fp = _nb([
        ("markdown", "## Exercices\n1. Resoudre tel probleme (sans reponse).\n"),
        ("markdown",
         "## Vérifiez votre compréhension\n1. Pourquoi ?\n"
         "<details>\n<summary>Éléments de réponse</summary>\n"
         "1. Parce que.\n</details>\n"),
    ])
    if count_no_answer(fp) != 0:
        failures.append("faux positif : section 'Exercices' comptee a tort")

    # 'Exercices' SEUL (sans bloc 'verifiez') -> hors cible, 0.
    exo_only = _nb([("markdown", "## Exercices\n1. Un exercice.\n")])
    if count_no_answer(exo_only) != 0:
        failures.append("exercices seul : hors cible, doit etre 0")

    if failures:
        print("SELF-TEST FAIL")
        for f in failures:
            print("  - " + f)
        return 1
    print("SELF-TEST OK (4 controles : positif, negatif, faux-positif "
          "Exercices, exercices-seul)")
    return 0


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(
        description="Repere les blocs 'Verifiez votre comprehension' sans "
                    "reponse (triage --series, ou ratchet advisory sur les "
                    "carnets modifies d'une PR).")
    ap.add_argument("base", nargs="?",
                    help="Base git ref (mode CI) -- sinon --series")
    ap.add_argument("--series", help="Nom de serie/sous-serie (mode triage)")
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--json", action="store_true", dest="as_json")
    args = ap.parse_args(argv)

    if args.self_test:
        return self_test()

    if args.series:
        verdict = triage(args.series)
    elif args.base:
        verdict = ratchet(args.base)
    else:
        ap.error("--series ou une base ref requis (ou --self-test)")
        return 2

    if args.as_json:
        print(json.dumps(verdict, ensure_ascii=False, indent=2))
    else:
        if "series" in verdict:
            print(f"serie {verdict['series']} : {verdict.get('verif_total', 0)} "
                  f"carnets avec bloc 'verifiez' | {verdict.get('with_answer', 0)} "
                  f"avec reponse | {verdict.get('no_answer', 0)} SANS reponse")
            for f in verdict.get("flagged", []):
                print(f"  SANS REPONSE {f['path']} ({f['blocks']} bloc)")
            for e in verdict.get("errors", []):
                print(f"  ERREUR {e['path']}: {e['error']}")
        else:
            print(f"base {verdict['base_ref']} -> merge-base "
                  f"{verdict['merge_base'][:12]} | {verdict['changed']} "
                  f"carnets modifies | {verdict['flagged']} flaggue(s) (advisory)")
            for r in verdict["rows"]:
                if r.get("flagged"):
                    print(f"  INTRODUIT {r['path']} : blocs sans reponse "
                          f"{r['base_no_answer']} -> {r['head_no_answer']}")
    return verdict["rc"]


if __name__ == "__main__":
    sys.exit(main())
