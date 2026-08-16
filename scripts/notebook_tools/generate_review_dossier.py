#!/usr/bin/env python3
"""Generate the editorial review dossier of a notebook (Epic #11259 task 2).

The Epic's contract: the user's attention is the scarce resource, and it must
NEVER be spent looking for defects -- only judging them. This tool is the
"instruction" half of that split: given ONLY a notebook path, it runs the
existing instruments, collects their verdicts with provenance, drafts the
candidate findings with cited proof, and emits a self-sufficient markdown
dossier following the 4-part structure of the Epic (instruments / constats /
3 questions max / verdict in EDITORIAL_REVIEW_CARD format).

Consumes, never re-implements, the canonical organs:
- validate_pr_notebooks.validate_notebook  -- H.1/H.3/C.1 forensic execution
- pedagogy_density.check_paths             -- #10479 density (chars/code cell)
- count_exercises                          -- #2161 corpus kind + exercise count

Dossiers are EPHEMERAL presentation artifacts (dashboard/hand-off), never repo
files: the durable state is the registry (editorial-review-registry.md) and the
scope (production-scope.md), both read here, neither written.

Usage:
    python generate_review_dossier.py MyIA.AI.Notebooks/Sudoku/Sudoku-12-Z3-Csharp.ipynb
    python generate_review_dossier.py <path> --output dossier.md

Exit codes: 0 always (advisory by design, like pedagogy_density: the signal is
the dossier content, not a green conclusion).
"""

from __future__ import annotations

import argparse
import datetime as dt
import json
import re
import subprocess
import sys
from pathlib import Path

_TOOLS_DIR = Path(__file__).resolve().parent
if str(_TOOLS_DIR) not in sys.path:
    sys.path.insert(0, str(_TOOLS_DIR))

from count_exercises import classify_notebook, count_exercises_in_notebook  # noqa: E402
from pedagogy_density import DENSITY_THRESHOLD, check_paths  # noqa: E402
from validate_pr_notebooks import validate_notebook  # noqa: E402

REPO_ROOT = _TOOLS_DIR.parent.parent
SCOPE_FILE = REPO_ROOT / "docs" / "notebook-metadata" / "production-scope.md"
REGISTRY_FILE = REPO_ROOT / "docs" / "notebook-metadata" / "editorial-review-registry.md"
TWIN_REGISTRY = _TOOLS_DIR / "twin_pairs.d"

# Machine-path leak signature (source of the Stop & Repair rule): a committed
# OUTPUT carrying a host path. Benign in code sources (open('data/...') is
# fine); a leak only when the RUN REPORT echoes an absolute host path.
MACHINE_PATH_RE = re.compile(r"[A-Z]:\\\\Users\\\\|[A-Z]:/Users/|[A-Z]:\\\\Dev\\\\|[A-Z]:/Dev/|/home/[a-z]")


def _title_of(data: dict) -> str:
    for cell in data.get("cells", []):
        if cell.get("cell_type") == "markdown":
            for line in "".join(cell.get("source", [])).split("\n"):
                if line.startswith("# "):
                    return line[2:].strip()
    return ""


def _last_commit(path: Path) -> tuple[str, str, str]:
    """(iso_date, author, short_sha) of the last commit touching the notebook."""
    try:
        out = subprocess.run(
            ["git", "log", "-1", "--format=%ad|%an|%h", "--date=short", "--", str(path)],
            capture_output=True, text=True, cwd=REPO_ROOT, check=True,
        ).stdout.strip()
        date, author, sha = out.split("|")[:3]
        return date, author, sha
    except Exception:
        return "?", "?", "?"


def _scope_of(rel_posix: str) -> str:
    if not SCOPE_FILE.exists():
        return "?"
    text = SCOPE_FILE.read_text(encoding="utf-8")
    if f"`{rel_posix}`" in text:
        section = text[: text.index(f"`{rel_posix}`")]
        if "Strate A" in section.rsplit("## ", 1)[-1] or section.rfind("## Strate A") > section.rfind("## Strate B"):
            return "A (proposé PRODUCTION)"
        return "B (hors proposition v1, BETA)"
    return "C / hors périmètre"


def _registry_entries_for(rel_from_notebooks: str) -> list[dict]:
    """Parse the YAML whitelist block of the registry for this notebook."""
    if not REGISTRY_FILE.exists():
        return []
    text = REGISTRY_FILE.read_text(encoding="utf-8")
    entries = []
    current: dict = {}
    for line in text.split("\n"):
        if line.startswith("- notebook_path:"):
            if current:
                entries.append(current)
            current = {"notebook_path": line.split(":", 1)[1].strip()}
        elif line.startswith("  ") and ":" in line and current:
            key, _, val = line.strip().partition(":")
            current[key.strip()] = val.strip().strip('"')
    if current:
        entries.append(current)
    return [e for e in entries if e.get("notebook_path") == rel_from_notebooks]


def _twin_of(path: Path) -> tuple[str, str]:
    """(twin_relpath_or_empty, parity_note) via filename convention + registry."""
    name = path.name
    stem = name[: -len(".ipynb")]
    candidates = []
    if "-Csharp" in stem:
        candidates.append(stem.replace("-Csharp", "-Python"))
    elif "-Python" in stem:
        for token in ("-CSharp-", "-Csharp"):
            if token in stem:
                candidates.append(stem.replace("-CSharp-", "-").replace("-Csharp-", "-"))
    for twin in candidates:
        tp = path.parent / (twin + ".ipynb")
        if tp.exists():
            note = ""
            if TWIN_REGISTRY.exists():
                for yml in TWIN_REGISTRY.glob("*.yaml"):
                    body = yml.read_text(encoding="utf-8")
                    if str(path.relative_to(REPO_ROOT)).replace("\\", "/") in body or twin in body:
                        m = re.search(r"parity_level:\s*(\S+)", body)
                        if m:
                            note = f" (registre parité: {m.group(1)})"
                        break
            return str(tp.relative_to(REPO_ROOT)).replace("\\", "/"), note
    return "", ""


def _scan_machine_paths(data: dict) -> list[tuple[int, str]]:
    """Cells whose committed OUTPUTS echo an absolute host path."""
    hits = []
    for i, cell in enumerate(data.get("cells", [])):
        for out in cell.get("outputs", []) or []:
            blob = json.dumps(out, ensure_ascii=False)
            if MACHINE_PATH_RE.search(blob):
                hits.append((i, MACHINE_PATH_RE.search(blob).group(0)))
                break
    return hits


def generate(nb_path: Path) -> str:
    rel_posix = str(nb_path.relative_to(REPO_ROOT)).replace("\\", "/")
    rel_from_notebooks = nb_path.relative_to(REPO_ROOT / "MyIA.AI.Notebooks").as_posix() \
        if nb_path.is_relative_to(REPO_ROOT / "MyIA.AI.Notebooks") else rel_posix
    data = json.loads(nb_path.read_text(encoding="utf-8"))

    kind, _num = classify_notebook(nb_path)
    dp = check_paths([nb_path])
    dv = None
    for bucket in (dp.below_threshold, dp.ok, dp.exempt, dp.unmeasured):
        for v in bucket:
            if v.path == str(nb_path):
                dv = v
    forensic = validate_notebook(nb_path)
    excount = count_exercises_in_notebook(nb_path)
    last_date, last_author, last_sha = _last_commit(nb_path)
    scope = _scope_of(rel_posix)
    registry = _registry_entries_for(rel_from_notebooks)
    twin_rel, twin_note = _twin_of(nb_path)
    path_hits = _scan_machine_paths(data)

    today = dt.date.today().isoformat()
    lines: list[str] = []
    A = lines.append

    A(f"# Dossier de revue éditoriale — {nb_path.name}")
    A("")
    A(f"> Généré le {today} par `generate_review_dossier.py` (Epic [#11259](https://github.com/jsboige/CoursIA/issues/11259) T2).")
    A("> Auto-suffisant : instruments relancés à la génération, preuves citées. Vous jugez, vous ne cherchez pas.")
    A("")

    # ---- 1. Identification ----
    A("## 1. Identification")
    A("")
    A(f"- **Chemin** : `{rel_posix}`")
    if _title_of(data):
        A(f"- **Titre** : {_title_of(data)}")
    A(f"- **Corpus** : kind `{kind}` · {len(data.get('cells', []))} cellules ({forensic['total_code']} code exécutables)")
    A(f"- **Dernier commit** : {last_date} · {last_author} · `{last_sha}`")
    A(f"- **Périmètre PRODUCTION** : {scope}")
    if registry:
        e = registry[-1]
        A(f"- **Registre éditorial** : déjà relu par {e.get('reviewer')} le {e.get('review_date')} ({e.get('review_scope')}, PR {e.get('evidence_pr')})")
    else:
        A("- **Registre éditorial** : aucune revue enregistrée (BETA axe éditorial)")
    if twin_rel:
        A(f"- **Jumeau** : `{twin_rel}`{twin_note}")
    A("")

    # ---- 2. Instruments ----
    A("## 2. Ce que les instruments disent")
    A("")
    A("| Instrument | Verdict | Mesure | Provenance |")
    A("|------------|---------|--------|------------|")

    rows = []
    f_err = forensic.get("errors", [])
    if f_err:
        rows.append(("Exécution forensique (H.1/H.3)", "WARN",
                     f"{len(f_err)} anomalie(s) : " + " ; ".join(f_err[:3]), "validate_pr_notebooks.py"))
    else:
        rows.append(("Exécution forensique (H.1/H.3)", "PASS",
                     f"{forensic['total_code']} cellules code, exec_count + outputs cohérents", "validate_pr_notebooks.py"))

    if dv is None:
        rows.append(("Densité pédagogique", "WARN", "non mesurable (0 cellule code ou JSON illisible)", "pedagogy_density.py"))
    elif dv.status == "ok":
        rows.append(("Densité pédagogique", "PASS", f"{dv.density} chars/cellule (seuil {DENSITY_THRESHOLD})", "pedagogy_density.py"))
    elif dv.status == "exempt":
        rows.append(("Densité pédagogique", "PASS", f"exempt (kind {dv.kind})", "pedagogy_density.py"))
    elif dv.status == "unmeasured":
        rows.append(("Densité pédagogique", "WARN", "non mesurée", "pedagogy_density.py"))
    else:
        rows.append(("Densité pédagogique", "WARN", f"{dv.density} chars/cellule < seuil {DENSITY_THRESHOLD}", "pedagogy_density.py"))

    if kind in ("standard",):
        n_ex = getattr(excount, "exercise_count", getattr(excount, "count", None))
        if n_ex is None:
            rows.append(("Exercices (≥3)", "WARN", "comptage indisponible", "count_exercises.py"))
        elif n_ex >= 3:
            rows.append(("Exercices (≥3)", "PASS", f"{n_ex} exercices", "count_exercises.py"))
        else:
            rows.append(("Exercices (≥3)", "WARN", f"{n_ex} exercice(s) seulement", "count_exercises.py"))

    if path_hits:
        rows.append(("Chemins machine dans outputs", "WARN",
                     f"{len(path_hits)} cellule(s) : " + ", ".join(f"cell[{i}]" for i, _ in path_hits[:4]),
                     "regex host-path (Stop & Repair)"))
    else:
        rows.append(("Chemins machine dans outputs", "PASS", "aucun", "regex host-path (Stop & Repair)"))

    for name, verdict, measure, prov in rows:
        A(f"| {name} | {verdict} | {measure} | `{prov}` |")
    A("")

    # ---- 3. Constats ----
    A("## 3. Constats candidats (preuve citée, correctif rédigé)")
    A("")
    constat_n = 0
    if f_err:
        constat_n += 1
        A(f"{constat_n}. **Exécution** — {len(f_err)} anomalie(s) forensique : {' ; '.join(f_err[:3])}. "
          f"*Correctif proposé* : re-exécution complète du notebook (kernel local), commit des outputs réels.")
    if dv is not None and dv.status == "below_threshold":
        constat_n += 1
        A(f"{constat_n}. **Densité** — {dv.density} chars de prose/cellule code < {DENSITY_THRESHOLD}. "
          f"*Correctif proposé* : enrichissement markdown ciblé (interprétations après cellules à output dense), pattern #10488.")
    if path_hits:
        constat_n += 1
        cells = ", ".join(f"cell[{i}]" for i, _ in path_hits[:4])
        constat_n_note = " / ".join(m for _, m in path_hits[:2])
        A(f"{constat_n}. **Chemin machine en sortie** — {cells}.echo `{constat_n_note}`. "
          f"*Correctif proposé* : source → `basename` (jamais scrub d'output), puis re-exécution.")
    if kind == "standard" and (ex := getattr(excount, "exercise_count", None)) is not None and ex < 3:
        constat_n += 1
        A(f"{constat_n}. **Exercices** — {ex} exercice(s) < 3 (convention #2161). "
          f"*Correctif proposé* : ajout d'exercices stub (C.1 : `pass`/`return None`, jamais `raise`).")
    if constat_n == 0:
        A("*Aucun constat instrumenté — les instruments ne signalent rien. Les questions ci-dessous portent le jugement.*")
    A("")

    # ---- 4. Questions ----
    A("## 4. Questions (jugement humain — 3 maximum)")
    A("")
    A("1. Ce notebook **s'enseigne-t-il bien** tel quel (ordre, rythme, exemples) ?")
    A("2. Le ou les **exemples portent-ils** le concept annoncé (pas de cas dégénéré) ?")
    A("3. **Signez-vous** (PROMOTE) — et si oui sous quel scope (`factual`/`substance`/`full`) ?")
    A("")

    # ---- 5. Verdict ----
    A("## 5. Verdict (format EDITORIAL_REVIEW_CARD)")
    A("")
    A("- [ ] **PROMOTE** — `editorial_reviewed_by` renseigné, `BETA → FINAL`")
    A("- [ ] **DO_NOT_PROMOTE** — scope insuffisant ou auto-review")
    A("- [ ] **DEFER** — seconde passe nécessaire (constats substance d'abord)")
    A("")
    A("*Après décision : la lane convertit en entrée de registre (`editorial-review-registry.md` §6) et en issues/PRs pour les constats — vous n'ouvrez rien.*")
    return "\n".join(lines) + "\n"


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("notebook", help="chemin du notebook (relatif au dépôt ou absolu)")
    ap.add_argument("--output", type=Path, default=None,
                    help="écrire le dossier dans ce fichier (défaut : stdout)")
    args = ap.parse_args(argv)

    nb = Path(args.notebook)
    if not nb.is_absolute():
        nb = REPO_ROOT / nb
    if not nb.exists():
        print(f"notebook introuvable : {nb}", file=sys.stderr)
        return 0

    dossier = generate(nb)
    if args.output:
        args.output.write_text(dossier, encoding="utf-8")
        print(f"dossier écrit : {args.output}")
    else:
        sys.stdout.reconfigure(encoding="utf-8")
        print(dossier, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
