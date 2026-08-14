#!/usr/bin/env python3
"""Detect markdown cells "interpreting" a code output but placed BEFORE the section
the output belongs to (EPIC #10678, lecon pivot post-enrichissement density #10488).

Pourquoi cet outil existe
-------------------------
L'EPIC #10488 a inonde le corpus de cellules markdown d'interpretation
(`### Lecture du resultat : ...`, `### Interpretation des resultats`) censees
commenter la sortie d'une cellule code. Le bug systematique : ces cellules sont
inserees **apres une cellule code arbitraire** (souvent identifiee par un id
`interp-<codeid>` que l'enrichisseur pose sans verifier), **pas apres la cellule
code dont elles interpretent reellement l'output**. Le contenu pedagogique est
correct, mais la position est semantiquement fausse : un lecteur voit "le
classement final du Click Model" 26 cellules AVANT le Click Model lui-meme.

Exemple fondateur (#10580 PyMC-15-Recommenders, mesure #10678) :
  cell[4]  interp "donnees sparse"           placee apres cell[3] imports numpy/pymc
  cell[9]  interp "163 divergences NUTS"      placee apres cell[8] saisie des donnees
  cell[13] interp "163->5 modele ameliore"    placee apres cell[12] def modele 1
  cell[18] interp "cold-start Item 0"          placee apres cell[17] extraction U/V_mean
  cell[25] interp "classement fusionne §5"     placee apres cell[24] def modele 2 (26 trop tot)

Aucun reviewer (humain ni bot) ne signale : le harnais ne verifie pas l'ordre
pedagogique des cellules (clusterManager-Myia structurel, github-actions
H.1/H.3/C.1, golden-set H.7 reproductibilite seulement).

Regle detectee
--------------
Une cellule d'interpretation est **misplaced** si les 4 conditions sont reunies :
  1. Son `source` commence par un header reconnu (`### Lecture du resultat`,
     `### Lecture des resultats`, `### Interpretation` ou `### Interpretation des
     resultats`) -- le pattern exact est detectable par regex ancree.
  2. La cellule **suivante** est une cellule markdown debutant par `## ` ou
     `### ` (nouvelle section / sous-section).
  3. Le titre de la section suivante n'est PAS un marqueur de fin de
     document (`### Exercices`, `## 7. Exercices`, `### Conclusion`,
     `### Pour aller plus loin`) -- sinon c'est legitime.
  4. **Aucune cellule code ne precede l'interp dans sa propre section** : en
     remontant depuis l'interp, on rencontre un header de section AVANT toute
     cellule code (cf `_is_anchored_to_code`). C'est cette condition qui
     distingue le defaut d'une interp normale.

Pourquoi la condition 4 (correctif c.95)
----------------------------------------
Les conditions 1-3 ne regardent que ce qui SUIT l'interp. Or la forme
CANONIQUE et CORRECTE -- celle que `.claude/rules/cell-interpretation-ordering.md`
prescrit -- est precisement :

    [cellule code produisant l'output]
    ### Lecture du resultat : <commente cet output>     <- placement CORRECT
    ## N. Section suivante                              <- la section suivante s'ouvre

Les conditions 1-3 signalent cette forme. Mesure firsthand sur `origin/main`
(c.95) : **1185 findings, dont 1146 de cette forme** -- soit ~97% de faux
positifs, sur un gate BLOQUANT scope `MyIA.AI.Notebooks/**/*.ipynb`, donc
bloquant toute PR de contenu notebook. La condition 4 ramene le scan a **39
findings, 0 nouveau** : il ne reste que les interps parachutees entre deux
headers, sans code dans leur section -- le defaut reellement decrit ci-dessus.

Ce qui est **hors scope** par design (v1, EPIC #10678 Phase 3) :
- DETECTION SEMANTIQUE du lien interp <-> output (NLP) : trop fragile.
  L'agent enrichisseur declare "insere APRES les outputs" sans verification ;
  on ne peut pas reproduire cette logique sans tomber dans une regex fragile
  sur le body de l'interp.
- CORRECTION AUTOMATIQUE : pas de reordering automatique (le link entre
  l'interp et le code d'origine est implicite ; un script ne peut pas le
  retrouver deterministiquement). Phase 2 = reparation manuelle par humain.
- WORKFLOW DRIFT : ce script ne suit PAS un drift de qualite de l'enrichissement
  (c'est la regle `.claude/rules/notebook-conventions.md` qui s'en charge).

Baseline
--------
`--check` se compare a une baseline commitee
(`scripts/notebook_tools/interp_positioning_baseline.json`) ; seules les
NOUVELLES findings font echouer la gate, pour ne pas bloquer les PRs non
concernees. La baseline v1 portait **1184 hashes** -- des FP a ~97% (cf
"Pourquoi la condition 4"), donc une dette illusoire qu'aucune Phase 4 ne
pouvait bruler. Regeneree a **39** apres le correctif : c'est desormais une
liste de travail reelle, conforme a son propre en-tete ("Burn down, do not
grow").

Usage
-----
    python scripts/notebook_tools/check_interp_positioning.py MyIA.AI.Notebooks/Probas/PyMC/PyMC-15-Recommenders.ipynb    # 1 notebook
    python scripts/notebook_tools/check_interp_positioning.py --family Probas                                                # 1 famille
    python scripts/notebook_tools/check_interp_positioning.py MyIA.AI.Notebooks                                              # tout
    python scripts/notebook_tools/check_interp_positioning.py --check --baseline scripts/notebook_tools/interp_positioning_baseline.json    # CI-ready
    python scripts/notebook_tools/check_interp_positioning.py --update-baseline --baseline scripts/notebook_tools/interp_positioning_baseline.json
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

# ------------------------------------------------------------------ severities
ERROR = "error"
WARN = "warn"

# Les findings `misplaced_before_section` sont ERROR (bloquant -- c'est ce qu'on
# detecte, c'est ce qu'on fixe). Aucun WARN en v1 : le script est jeune, on
# garde la signal au propre plutot que d'inonder le rapport de WARN
# inoperationnels.
RULE_SEVERITY = {
    "misplaced_before_section": ERROR,
}

# ------------------------------------------------------------------ patterns
# Pattern ancree en debut de cellule (apres strip du BOM) :
#   - ### Lecture du resultat
#   - ### Lecture des resultats
#   - ### Interpretation / Interpretation
#   - ### Interpretation des resultats
# Le ":" qui suit le titre (l'interp commence par "Titre : sous-titre") est
# autorise (les enrichisseurs #10488 utilisent ce format).
INTERP_HEADER_RE = re.compile(
    r"^\s*#{2,4}\s+"
    r"(Lecture (du|des) r[ée]sultat[s]?|Interpr[ée]tation|Interpr[ée]tation des r[ée]sultat[s]?)"
    r"\s*[:\.]?",
    re.IGNORECASE,
)

# Pattern pour detecter une cellule de fin de document legitime (la condition 3
# du misplaced). Ces cellules sont des separateurs de section et l'interp qui
# les precede clot la section precedente -- pas un bug.
# Le prefixe numerote (`## 7. Exercices`, `### 4.2 Conclusion`) est la forme
# DOMINANTE dans CoursIA : sans `(?:\d+(?:\.\d+)*\.?\s+)?`, la whitelist ne
# matchait aucun header numerote et un `## 7. Exercices` etait signale comme
# defaut (FP mesure sur GameTheory-16 cell#46, c.95).
LEGIT_FOLLOWING_HEADER_RE = re.compile(
    r"^\s*#{2,4}\s+"
    r"(?:\d+(?:\.\d+)*\.?\s+)?"
    r"(Exercice[s]?|Conclusion[s]?|Pour aller plus loin|R[ée]f[ée]rences?|Annexes?|Ressources|"
    r"Bibliography|Bibliographie|Summary|R[é]sum[ée]|Questions?|Quiz)"
    r"\b",
    re.IGNORECASE,
)

# Pattern ancree pour detecter une cellule de debut de section (la condition 2).
# Note : on accepte uniquement ## et ### (les h2/h3) -- le # (h1) est reserve au
# titre du notebook dans la convention CoursIA, pas aux sections internes.
SECTION_HEADER_RE = re.compile(r"^\s*#{2,3}\s+\S")

# ------------------------------------------------------------------ helpers


def _as_text(source) -> str:
    """Concatene les elements `source` d'une cellule en preservant les '\\n' finaux.

    Convention ipynb : un element `source` se termine par '\\n' s'il y a une
    ligne suivante. `"".join(source)` reproduit fidelement la cellule. Si on
    n'insere pas de '\\n' entre les elements (comme #10397), la cellule se
    collapse en une seule ligne -- on preserve donc le comportement natif.
    """
    if isinstance(source, list):
        return "".join(source)
    return source or ""


def _first_line(text: str) -> str:
    """Premiere ligne non-vide (apres strip)."""
    for line in text.splitlines():
        s = line.strip()
        if s:
            return s
    return ""


def _is_interp_cell(text: str) -> bool:
    """Vrai si la cellule debute par un header d'interpretation (condition 1)."""
    # On teste sur la premiere ligne (le header doit etre la premiere ligne
    # non-vide) -- un bug classique serait de considerer une cellule qui
    # MENTIONNE "Lecture du resultat" au milieu de son body comme une cellule
    # d'interp, ce qui produirait beaucoup de FP.
    first = _first_line(text)
    return bool(INTERP_HEADER_RE.match(first))


def _is_legit_following_header(text: str) -> bool:
    """Vrai si la cellule suivante est un header de fin de document (condition 3).

    Une interp suivie de `### Exercices` ou `### Conclusion` est legitime :
    l'interp clot la section, le nouveau header ouvre un autre registre.
    """
    first = _first_line(text)
    return bool(LEGIT_FOLLOWING_HEADER_RE.match(first))


def _is_section_header(text: str) -> bool:
    """Vrai si la cellule est un header de section `## ` ou `### ` (condition 2)."""
    first = _first_line(text)
    return bool(SECTION_HEADER_RE.match(first))


def _is_anchored_to_code(cells: list, i: int) -> bool:
    """Vrai si l'interp en position `i` suit le code dont elle commente la sortie.

    On remonte depuis `i - 1` : si on atteint une cellule de code AVANT de
    rencontrer un header de section, l'interp est correctement ancree — elle
    clot sa section, et le header qui la SUIT ouvre simplement la suivante.
    C'est la forme normale d'un notebook bien structure, pas un defaut.

    Sans ce test, le detecteur ne regardait que ce qui SUIT l'interp et
    signalait toute interp terminant sa section. FP mesures c.95 sur
    `GenAI/Aspire/01` cell#12 (suit un code a 3 outputs) et cell#17 (7
    outputs), `Z3-Linq2Z3/09` cell#18 (5 outputs) — trois cellules
    correctement placees, qui bloquaient toute PR touchant un notebook.

    Le vrai defaut vise par `misplaced_before_section` (une interp parachutee
    entre deux headers, loin de tout code — incident PyMC-15 #10580) continue
    de rougir : en remontant, on y rencontre un header avant tout code.
    """
    for j in range(i - 1, -1, -1):
        cell = cells[j]
        if cell.get("cell_type") == "code":
            return True
        if _is_section_header(_as_text(cell.get("source", []))):
            return False
    return False


def _stable_finding_hash(rule: str, file: str, cell_index: int, header: str) -> str:
    """Hash STABLE pour comparer findings d'une PR a la baseline.

    Le hash depend de la regle + chemin relatif + index + premiere ligne
    d'interp. Si la cellule est deplacee vers son bon emplacement, l'index
    change -> le hash change -> la baseline se met a jour naturellement.
    Le hash est volontaire COURT (12 char) pour rester lisible dans le
    baseline JSON.

    IMPORTANT : on normalise le chemin en POSIX (separateurs `/`) AVANT de
    hasher, sinon le hash differe entre Windows (`\\`) et Linux/macOS
    (`/`). C'est le bug fondateur de c.8244 v1 (baseline Windows-committed
    inutilisable en CI Linux, toutes les findings flaguees "new").
    Bug decouvert via le GH-Actions run 31649195016 (FAIL 1205/1205).
    """
    posix_file = file.replace("\\", "/") if file else file
    raw = f"{rule}|{posix_file}|{cell_index}|{header}".encode("utf-8")
    return hashlib.sha1(raw).hexdigest()[:12]


def scan_notebook(path: Path) -> list[dict]:
    """Scan un notebook, retourne la liste de findings `misplaced_before_section`.

    Chaque finding est un dict {rule, severity, cell_index, evidence, hash}.
    Aucune distinction par noyau (Python / .NET / QC) -- le bug est structurel
    (placement des cellules markdown), pas lie a l'execution.
    """
    try:
        with open(path, encoding="utf-8") as f:
            nb = json.load(f)
    except (OSError, json.JSONDecodeError) as exc:
        return [{"rule": "scan_error", "severity": ERROR, "error": str(exc),
                 "path": str(path), "hash": "scan-error"}]

    cells = nb.get("cells", [])
    findings: list[dict] = []

    for i, cell in enumerate(cells):
        if cell.get("cell_type") != "markdown":
            continue
        text = _as_text(cell.get("source", []))
        if not _is_interp_cell(text):
            continue

        # Condition 2 : la cellule suivante est-elle un header de section ?
        if i + 1 >= len(cells):
            # L'interp est en fin de notebook -- pas misplaced (rien ne la suit).
            continue
        nxt = cells[i + 1]
        if nxt.get("cell_type") != "markdown":
            # L'interp est suivie d'un code cell -> la position classique OK
            # (code dont on vient d'interpreter la sortie).
            continue
        nxt_text = _as_text(nxt.get("source", []))
        if not _is_section_header(nxt_text):
            # L'interp est suivie d'un markdown mais PAS un header de section
            # (paragraphe, liste, etc.) -- pas un signal fort, on laisse passer.
            continue

        # Condition 3 : le header suivant est-il un separateur legitime ?
        # Si oui, l'interp clot la section avant un nouveau registre.
        if _is_legit_following_header(nxt_text):
            continue

        # Condition 4 : l'interp suit-elle le code dont elle commente la
        # sortie ? Si oui elle est correctement ancree -- le header qui suit
        # ouvre juste la section suivante (cf `_is_anchored_to_code`).
        if _is_anchored_to_code(cells, i):
            continue

        # Les 3 conditions sont reunies -> MISPLACED.
        interp_header = _first_line(text)[:80]
        nxt_header = _first_line(nxt_text)[:80]
        findings.append({
            "rule": "misplaced_before_section",
            "severity": ERROR,
            "cell_index": i,
            "evidence": f"interp '{interp_header}' precedes section header '{nxt_header}'",
            "hash": _stable_finding_hash("misplaced_before_section", str(path),
                                          i, interp_header),
        })

    return findings


# ------------------------------------------------------------------ walk
# Marcheur + SKIP_DIRS canonique centralises dans notebook_walk (#8650).
from notebook_walk import iter_notebooks  # noqa: E402

# ------------------------------------------------------------------ main


def _iter_targets(args_root: Path, family: str | None):
    """Yield des chemins `.ipynb` selon args (un fichier, une famille, ou tout)."""
    if args_root.is_file():
        yield args_root
        return
    if family:
        base = args_root / family
        yield from iter_notebooks(base)
        return
    yield from iter_notebooks(args_root)


def gather(root: Path, family: str | None = None) -> list[dict]:
    """Scan tous les notebooks cibles, retourne la liste plate de findings."""
    out: list[dict] = []
    for nb_path in _iter_targets(root, family):
        rel = nb_path
        for f in scan_notebook(nb_path):
            f["file"] = str(rel)
            f["path"] = str(rel)
            out.append(f)
    return out


def load_baseline(path: Path) -> set[str]:
    if not path.exists():
        return set()
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return set()
    return set(data.get("hashes", []))


def _human_report(findings: list[dict], new_findings: list[dict] | None) -> str:
    lines = [
        f"findings total : {len(findings)}",
    ]
    if new_findings is not None:
        lines.append(f"findings NEW   : {len(new_findings)} (vs baseline)")
    by_rule: dict[str, int] = {}
    for f in findings:
        if "rule" not in f:
            continue
        by_rule[f["rule"]] = by_rule.get(f["rule"], 0) + 1
    for rule, count in sorted(by_rule.items()):
        sev = RULE_SEVERITY.get(rule, "?")
        lines.append(f"  {sev:>5} {rule}: {count}")
    lines.append("")
    shown = new_findings if new_findings is not None else findings
    if not shown:
        lines.append("No misplaced interp cells detected.")
        return "\n".join(lines)
    for f in shown[:100]:
        sev = f.get("severity", "?").upper()
        rule = f.get("rule", "?")
        ci = f.get("cell_index", "?")
        ev = f.get("evidence", "")
        file = f.get("file", f.get("path", "?"))
        lines.append(f"  [{sev}] {file} cell#{ci} [{rule}] {ev}")
    if len(shown) > 100:
        lines.append(f"  ... {len(shown) - 100} more")
    return "\n".join(lines)


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(
        description=__doc__.split("\n\n")[0],
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    ap.add_argument("root", nargs="?", default="MyIA.AI.Notebooks",
                    help="notebook file or directory to scan (default: MyIA.AI.Notebooks)")
    ap.add_argument("--family", help="Top-level family under root/ (e.g. Probas)")
    ap.add_argument("--check", action="store_true",
                    help="exit 1 if any (new) ERROR is found (CI-ready)")
    ap.add_argument("--report", action="store_true", help="human-readable listing")
    ap.add_argument("--json", action="store_true", help="machine-readable JSON output")
    ap.add_argument("--baseline", type=Path, default=None,
                    help="baseline JSON of known violations; --check fails only on NEW ones")
    ap.add_argument("--update-baseline", action="store_true",
                    help="write the current violation set to --baseline and exit")
    args = ap.parse_args(argv)

    root = Path(args.root)
    if not root.exists():
        print(f"error: path not found: {root}", file=sys.stderr)
        return 2

    findings = gather(root, args.family)
    new_findings: list[dict] | None = None

    # ---- update baseline -----------------------------------------------------
    if args.update_baseline:
        if not args.baseline:
            print("error: --update-baseline requires --baseline PATH", file=sys.stderr)
            return 2
        hashes = sorted({f["hash"] for f in findings if f.get("hash") and f.get("rule") != "scan_error"})
        payload = {
            "_comment": "Baseline of known interp-positioning violations. Burn down, "
                        "do not grow. Regenerate with: python scripts/notebook_tools/"
                        "check_interp_positioning.py --update-baseline --baseline <this file>",
            "count": len(hashes),
            "hashes": hashes,
        }
        args.baseline.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
        print(f"baseline written: {len(hashes)} violations -> {args.baseline}")
        return 0

    # ---- baseline compare ----------------------------------------------------
    baseline = load_baseline(args.baseline) if args.baseline else set()
    if baseline:
        new_findings = [f for f in findings
                        if f.get("hash") and f["hash"] not in baseline
                        and f.get("rule") != "scan_error"]

    # ---- output -------------------------------------------------------------
    if args.json:
        print(json.dumps({
            "total": len(findings),
            "new": len(new_findings) if new_findings is not None else None,
            "baseline_size": len(baseline),
            "findings": findings,
        }, indent=2))
    elif args.report or not args.check:
        print(_human_report(findings, new_findings))

    # ---- exit code ----------------------------------------------------------
    if args.check:
        blocking = [f for f in (new_findings if new_findings is not None else findings)
                    if f.get("severity") == ERROR and f.get("rule") != "scan_error"]
        if blocking:
            print(f"\nFAIL: {len(blocking)} new misplaced interp cell(s).",
                  file=sys.stderr)
            for f in blocking[:50]:
                print(f"  {f.get('file', f.get('path'))} cell#{f['cell_index']} "
                      f"[{f['rule']}] {f['evidence']}", file=sys.stderr)
            return 1
        print("OK: no new misplaced interp cells.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())