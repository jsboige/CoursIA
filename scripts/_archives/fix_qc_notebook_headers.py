"""Add execution mode headers to all QC Python notebooks.

Categories:
- TEACHING: Pure reference, not executable (QC-Py-01,02,05-07,09-17)
- ML_PARTIAL: ML sections work locally, QCAlgorithm sections are reference (QC-Py-03,08,19-27)
- EXECUTABLE: Fully executable locally (QC-Py-04, QC-Py-18)
"""

import json
import os
import sys

QC_DIR = os.path.join(os.path.dirname(__file__), "..",
                      "MyIA.AI.Notebooks", "QuantConnect", "Python")

TEACHING = {1, 2, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17}
ML_PARTIAL = {3, 8, 19, 20, 21, 22, 23, 24, 25, 26, 27}
EXECUTABLE = {4, 18}

# Already have a header from previous edit
ALREADY_DONE = {1, 19}

HEADER_TEACHING = """\
---

> **Mode d'emploi** : Ce notebook est un **document de reference** (non executable).
> Le code QCAlgorithm presente ici est a **copier dans `main.py`** de votre projet QuantConnect Lab.
> Ne tentez pas de faire "Run All" -- les imports `AlgorithmImports` n'existent pas en Jupyter local.
>
> **Pour demarrer un projet QC** : copiez un `main.py` depuis `projects/` ou `ESGF-2026/templates/`, puis adaptez-le.
> Voir le guide : [ECE-QC-QUICKSTART.md](../ECE-QC-QUICKSTART.md)

---"""

HEADER_ML_PARTIAL = """\
---

> **Mode d'emploi** : Ce notebook a **deux parties** :
> 1. **Sections analyse/ML** (pandas, sklearn, matplotlib) : **executables en Jupyter local**
> 2. **Sections integration QC** (classes `QCAlgorithm`) : **code de reference a copier dans `main.py`** de votre projet QC Lab
>
> Les cellules QCAlgorithm sont marquees `# [REFERENCE QC]` et ne sont pas executables localement.
> Voir le guide : [ECE-QC-QUICKSTART.md](../ECE-QC-QUICKSTART.md)

---"""

HEADER_EXECUTABLE = """\
---

> **Mode d'emploi** : Ce notebook est **entierement executable en Jupyter local**.
> Il utilise pandas, matplotlib et sklearn pour l'analyse de donnees financieres.
> Les resultats peuvent ensuite etre integres dans un projet QuantConnect (voir fin du notebook).

---"""


def get_header(num):
    if num in TEACHING:
        return HEADER_TEACHING
    elif num in ML_PARTIAL:
        return HEADER_ML_PARTIAL
    elif num in EXECUTABLE:
        return HEADER_EXECUTABLE
    return None


def has_mode_emploi(nb):
    """Check if notebook already has a mode d'emploi header."""
    for cell in nb.get("cells", [])[:3]:
        src = "".join(cell.get("source", []))
        if "Mode d'emploi" in src or "mode d'emploi" in src:
            return True
    return False


def add_header_cell(nb, header_text):
    """Insert a markdown cell after the first cell (title)."""
    cell = {
        "cell_type": "markdown",
        "metadata": {},
        "source": [line + "\n" for line in header_text.split("\n")]
    }
    # Remove trailing \n on last line
    if cell["source"]:
        cell["source"][-1] = cell["source"][-1].rstrip("\n")
    nb["cells"].insert(1, cell)


def mark_qcalgorithm_cells(nb):
    """Add # [REFERENCE QC] comment to code cells containing QCAlgorithm classes."""
    for cell in nb.get("cells", []):
        if cell["cell_type"] != "code":
            continue
        src = "".join(cell.get("source", []))
        if "QCAlgorithm" in src and "class " in src:
            lines = cell["source"] if isinstance(cell["source"], list) else [cell["source"]]
            first_line = lines[0] if lines else ""
            if "[REFERENCE QC]" not in first_line:
                marker = "# [REFERENCE QC] Code a copier dans main.py QC Lab (non executable ici)\n"
                cell["source"] = [marker] + lines


def process_notebook(filepath, num):
    with open(filepath, "r", encoding="utf-8") as f:
        nb = json.load(f)

    modified = False

    # Add header if missing
    if not has_mode_emploi(nb):
        header = get_header(num)
        if header:
            add_header_cell(nb, header)
            modified = True
            print(f"  + Added header ({['TEACHING','ML_PARTIAL','EXECUTABLE'][[num in TEACHING, num in ML_PARTIAL, num in EXECUTABLE].index(True)]})")

    # Mark QCAlgorithm cells in ML_PARTIAL and TEACHING notebooks
    if num in TEACHING or num in ML_PARTIAL:
        count = 0
        for cell in nb.get("cells", []):
            if cell["cell_type"] != "code":
                continue
            src = "".join(cell.get("source", []))
            if "QCAlgorithm" in src and "class " in src:
                lines = cell["source"] if isinstance(cell["source"], list) else [cell["source"]]
                first_line = lines[0] if lines else ""
                if "[REFERENCE QC]" not in first_line:
                    marker = "# [REFERENCE QC] Code a copier dans main.py QC Lab (non executable ici)\n"
                    cell["source"] = [marker] + lines
                    count += 1
                    modified = True
        if count > 0:
            print(f"  + Marked {count} QCAlgorithm cell(s) with [REFERENCE QC]")

    if modified:
        with open(filepath, "w", encoding="utf-8", newline="\n") as f:
            json.dump(nb, f, ensure_ascii=False, indent=1)
        return True
    else:
        print(f"  = Already up to date")
        return False


def main():
    modified_count = 0
    for num in range(1, 28):
        pattern = f"QC-Py-{num:02d}-"
        matches = [f for f in os.listdir(QC_DIR) if f.startswith(pattern) and f.endswith(".ipynb")]
        if not matches:
            print(f"QC-Py-{num:02d}: NOT FOUND")
            continue
        filepath = os.path.join(QC_DIR, matches[0])
        print(f"QC-Py-{num:02d}: {matches[0]}")
        if process_notebook(filepath, num):
            modified_count += 1

    print(f"\nDone: {modified_count}/27 notebooks modified")


if __name__ == "__main__":
    main()
