"""Audit GenAI notebook corruption - single-line code cells diagnostic.

Detects two classes of GenAI-notebook degradation:
  * **corruption** -- a code cell collapsed onto a single line > 500 chars
    carrying `import` / `def ` / `dotenv` (a tell-tale of a minified/corrupted
    cell that papermill or a botched edit produced).
  * **.env-loading inconsistency** -- which of several competing env-loading
    patterns the notebook uses (env_loaded flag, while-loop walk, GENAI_ROOT,
    find_dotenv, plain load_dotenv, ...), so the fleet can converge.

The detection logic is split into pure functions (no I/O) so it can be unit-
tested hermetically; `main()` does the filesystem walk + reporting. Behaviour
is byte-identical to the original module-level script.
"""
import glob
import json
import os
from collections import defaultdict

GENAI_PREFIX = "MyIA.AI.Notebooks/GenAI/"
SERIES_ORDER = [
    "Audio", "Image", "Video", "Texte",
    "00-GenAI-Environment", "SemanticKernel", "Other",
]
_VALID_SERIES = set(SERIES_ORDER) - {"Other"}


def is_corrupted_line(line):
    """True when a single source line exceeds 500 chars and looks like
    collapsed code (import / def / dotenv). This is the corruption signature."""
    return len(line) > 500 and ("import" in line or "def " in line or "dotenv" in line)


def count_corrupted_cells(nb):
    """Number of code cells in `nb` whose source contains at least one
    corrupted line (one count per offending cell, not per line)."""
    count = 0
    for cell in nb.get("cells", []):
        if cell.get("cell_type") != "code":
            continue
        src = "".join(cell.get("source", []))
        for line in src.strip().split("\n"):
            if is_corrupted_line(line):
                count += 1
                break
    return count


def classify_env_pattern(nb):
    """Env-loading pattern label for the FIRST code cell that carries an env
    marker, or None when no cell uses dotenv/GENAI_ROOT/.env.

    Priority chain (first match wins, mirroring the original elif ladder):
    env_loaded flag > while loop > GENAI_ROOT > find_dotenv > load_dotenv > other.
    """
    for cell in nb.get("cells", []):
        if cell.get("cell_type") != "code":
            continue
        src = "".join(cell.get("source", []))
        if "dotenv" in src or "GENAI_ROOT" in src or ".env" in src:
            if "env_loaded" in src:
                return "env_loaded flag"
            if "while current_path.name" in src:
                return "while loop"
            if "GENAI_ROOT" in src:
                return "GENAI_ROOT"
            if "find_dotenv" in src:
                return "find_dotenv"
            if "load_dotenv" in src:
                return "simple load_dotenv"
            return "other"
    return None


def classify_series(short_path):
    """Top-level GenAI series for a notebook path relative to the GenAI root
    (e.g. ``Audio/04-Applications/foo.ipynb`` -> ``Audio``). Unknown roots
    collapse to ``Other``."""
    parts = short_path.replace("\\", "/").split("/")
    return parts[0] if parts and parts[0] in _VALID_SERIES else "Other"


def status_label(pct):
    """Fleet-health bucket for a corruption percentage."""
    if pct > 50:
        return "CRITIQUE"
    if pct > 20:
        return "MOYEN"
    return "OK"


def shorten_path(nb_path):
    """Strip the GenAI root prefix (forward- and back-slash variants) and
    normalise remaining separators to ``/``."""
    short = nb_path.replace(GENAI_PREFIX, "").replace("MyIA.AI.Notebooks/GenAI\\", "")
    return short.replace("\\", "/")


def audit_notebook(nb):
    """Aggregate per-notebook verdict: (corrupted_cell_count, env_pattern).

    Returns ``(0, None)`` for a clean notebook with no env loading."""
    return count_corrupted_cells(nb), classify_env_pattern(nb)


def main():
    notebooks = glob.glob("MyIA.AI.Notebooks/GenAI/**/*.ipynb", recursive=True)
    # Exclude EPF student notebooks
    notebooks = [n for n in notebooks
                 if os.sep + "EPF" + os.sep not in n and "/EPF/" not in n]

    corrupted = defaultdict(list)
    clean = defaultdict(int)
    pattern_count = defaultdict(int)

    for nb_path in sorted(notebooks):
        try:
            with open(nb_path, "r", encoding="utf-8") as f:
                nb = json.load(f)
            short = shorten_path(nb_path)
            series = classify_series(short)
            corrupt_cells, env_pattern = audit_notebook(nb)
            if env_pattern is not None:
                pattern_count[env_pattern] += 1
            if corrupt_cells:
                corrupted[series].append((short, corrupt_cells))
            else:
                clean[series] += 1
        except Exception:
            pass

    print("=== ETAT DE CORRUPTION DES NOTEBOOKS GENAI (hors EPF) ===\n")
    total_corrupt = 0
    total_clean = 0
    for series in SERIES_ORDER:
        c = len(corrupted.get(series, []))
        cl = clean.get(series, 0)
        total = c + cl
        total_corrupt += c
        total_clean += cl
        if total > 0:
            pct = round(c / total * 100)
            status = status_label(pct)
            print(f"{series}: {c}/{total} corrompus ({pct}%) [{status}]")
            for path, cells in corrupted.get(series, []):
                print(f"  X {path} ({cells} cellules)")

    print(f"\nTOTAL: {total_corrupt} corrompus, {total_clean} sains, "
          f"sur {total_corrupt + total_clean}")
    if total_corrupt + total_clean:
        print(f"Taux de corruption: "
              f"{round(total_corrupt / (total_corrupt + total_clean) * 100)}%")

    print("\n=== PATTERNS .env (inconsistance) ===")
    for p, count in sorted(pattern_count.items(), key=lambda x: -x[1]):
        print(f"  {p}: {count} notebooks")


if __name__ == "__main__":
    main()
