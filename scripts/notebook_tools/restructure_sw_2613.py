"""
Restructure SW-8..SW-13 notebooks for issue #2613.

Convention: Exemples guidés FIRST, Exercices (stubs only) LAST.
Promotes @Sosolalt corrigés to "Exemple guidé", groups stubs at end.

Usage:
    python restructure_sw_2613.py [--dry-run] [notebook_path ...]

    Without paths, processes all 6 SW notebooks.
    --dry-run: print plan without writing.
"""

import json
import sys
import re
import copy
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent.parent
SW_DIR = REPO / "MyIA.AI.Notebooks" / "SymbolicAI" / "SemanticWeb"

DEFAULT_NOTEBOOKS = [
    "SW-8-Python-SHACL.ipynb",
    "SW-9-Python-JSONLD.ipynb",
    "SW-10-Python-RDFStar.ipynb",
    "SW-11-Python-KnowledgeGraphs.ipynb",
    "SW-12-Python-GraphRAG.ipynb",
    "SW-13-Python-Reasoners.ipynb",
]

# Exercise numbering mapping for promoted examples
# Maps corrige cell_id -> (exercise_num, short_topic)
def classify_cell(cell):
    """Classify a cell as corrigé markdown, corrigé code, exercise stub, or other."""
    src = "".join(cell.get("source", []))
    cid = cell.get("id", "")

    # Corrigé markdown: starts with "### Corrigé" or "### Corrige"
    if cell["cell_type"] == "markdown" and re.search(r"^###\s+Corrig[eé]", src, re.IGNORECASE):
        return "corrige_md"

    # Corrigé code: id starts with "corrige-code-"
    if cell["cell_type"] == "code" and cid.startswith("corrige-code-"):
        return "corrige_code"

    # Exercise stub code: has TODO or "Exercice a completer" in source
    if cell["cell_type"] == "code":
        if "Exercice a completer" in src or re.search(r"# TODO etudiant", src, re.IGNORECASE):
            return "exercise_stub"

    # Exercise description markdown: starts with "### Exercice"
    if cell["cell_type"] == "markdown" and re.search(r"^###\s+Exercice\s+\d", src):
        return "exercise_desc"

    return "other"


def extract_exercise_info(md_src):
    """Extract exercise number and topic from a markdown cell."""
    # Try "### Exercice N : Topic" or "### Corrigé : Exercice N : Topic"
    m = re.search(r"Exercice\s+(\d+)\s*[:\-]\s*(.+?)(?:\n|$)", md_src, re.IGNORECASE)
    if m:
        return int(m.group(1)), m.group(2).strip()
    return None, None


def restructure_notebook(path, dry_run=False):
    """Restructure a single notebook."""
    print(f"\n{'='*60}")
    print(f"Processing: {path.name}")
    print(f"{'='*60}")

    with open(path, "r", encoding="utf-8") as f:
        nb = json.load(f)

    cells = nb["cells"]

    # Phase 1: Identify all corrigé pairs and exercise stubs
    corrige_pairs = []  # (desc_idx, code_idx)
    exercise_stubs = []  # (desc_idx, stub_idx)

    i = 0
    while i < len(cells):
        ctype = classify_cell(cells[i])

        if ctype == "exercise_desc":
            # Look ahead for stub + corrigé
            desc_idx = i
            stub_idx = None
            corrige_md_idx = None
            corrige_code_idx = None

            j = i + 1
            # Skip to find stub
            while j < len(cells) and classify_cell(cells[j]) == "other":
                j += 1

            if j < len(cells) and classify_cell(cells[j]) == "exercise_stub":
                stub_idx = j
                k = j + 1
                # Look for corrigé after stub
                while k < len(cells):
                    kt = classify_cell(cells[k])
                    if kt == "corrige_md":
                        corrige_md_idx = k
                    elif kt == "corrige_code":
                        corrige_code_idx = k
                        break
                    elif kt == "exercise_desc":
                        break  # Next exercise, no corrigé for this one
                    k += 1

                if corrige_md_idx is not None and corrige_code_idx is not None:
                    corrige_pairs.append((desc_idx, stub_idx, corrige_md_idx, corrige_code_idx))
                    print(f"  Found corrigé pair: Ex desc@{desc_idx} -> Stub@{stub_idx} -> CorrMD@{corrige_md_idx} -> CorrCode@{corrige_code_idx}")
                else:
                    exercise_stubs.append((desc_idx, stub_idx))
                    print(f"  Found stub (no corrigé): Ex desc@{desc_idx} -> Stub@{stub_idx}")

                i = j + 1
                continue
            elif j < len(cells) and classify_cell(cells[j]) == "corrige_md":
                # stub might be missing, corrigé directly after desc
                corrige_md_idx = j
                k = j + 1
                if k < len(cells) and classify_cell(cells[k]) == "corrige_code":
                    corrige_code_idx = k
                    print(f"  Found corrigé pair (no stub): Ex desc@{desc_idx} -> CorrMD@{corrige_md_idx} -> CorrCode@{corrige_code_idx}")
                    corrige_pairs.append((desc_idx, None, corrige_md_idx, corrige_code_idx))
                    i = k + 1
                    continue

        i += 1

    if not corrige_pairs and not exercise_stubs:
        print("  No corrigés or exercise stubs found. Skipping.")
        return False

    # Phase 2: Build new cell list
    # Strategy: Remove corrigé cells from their positions, collect them.
    # Then find the insertion point (before "## Resume"/"## Conclusion"/last section)
    # Insert "Exemples guidés" section with promoted corrigés
    # Then move all exercise stubs to end (before conclusion)

    indices_to_remove = set()
    promoted_examples = []

    for (desc_idx, stub_idx, corr_md_idx, corr_code_idx) in corrige_pairs:
        indices_to_remove.add(corr_md_idx)
        indices_to_remove.add(corr_code_idx)

        # Create promoted example
        corrige_md = copy.deepcopy(cells[corr_md_idx])
        corrige_code = copy.deepcopy(cells[corr_code_idx])

        # Rename "Corrigé" -> "Exemple guidé"
        src = "".join(corrige_md.get("source", []))
        # Extract exercise topic from the corrigé title
        new_src = re.sub(
            r"^###\s+Corrig[eé]\s*:\s*Exercice\s+(\d+)\s*[:\-]?\s*(.*?)(\n|$)",
            lambda m: f"### Exemple guide : {m.group(2).strip() if m.group(2).strip() else f'Exercice {m.group(1)}'}\n",
            src,
            count=1,
            flags=re.IGNORECASE
        )
        # If the replacement didn't match (no "Exercice N" in title), try simpler pattern
        if new_src == src:
            new_src = re.sub(
                r"^###\s+Corrig[eé]\s*:\s*(.*?)(\n|$)",
                r"### Exemple guide : \1\2",
                src,
                count=1,
                flags=re.IGNORECASE
            )

        corrige_md["source"] = [new_src]
        # Change the id to avoid "corrige" prefix
        old_id = corrige_md.get("id", "")
        corrige_md["id"] = old_id.replace("corrige-", "exemple-").replace("corrige_", "exemple_")

        old_code_id = corrige_code.get("id", "")
        corrige_code["id"] = old_code_id.replace("corrige-code-", "exemple-code-").replace("corrige-code_", "exemple-code_")

        promoted_examples.append((corrige_md, corrige_code))

    # Also collect exercise stubs that need to be moved to end
    # We need: exercise_desc + exercise_stub pairs (including those with corrigés)
    exercise_cells_to_move = []  # (desc_cell, stub_cell)
    indices_to_move = set()

    for (desc_idx, stub_idx, corr_md_idx, corr_code_idx) in corrige_pairs:
        if stub_idx is not None:
            exercise_cells_to_move.append((
                copy.deepcopy(cells[desc_idx]),
                copy.deepcopy(cells[stub_idx])
            ))
            indices_to_move.add(desc_idx)
            indices_to_move.add(stub_idx)
        else:
            # No stub existed, we need to create one
            desc_src = "".join(cells[desc_idx].get("source", []))
            # Create a simple stub
            exercise_cells_to_move.append((
                copy.deepcopy(cells[desc_idx]),
                None  # Will create stub
            ))
            indices_to_move.add(desc_idx)

    for (desc_idx, stub_idx) in exercise_stubs:
        exercise_cells_to_move.append((
            copy.deepcopy(cells[desc_idx]),
            copy.deepcopy(cells[stub_idx])
        ))
        indices_to_move.add(desc_idx)
        indices_to_move.add(stub_idx)

    # Phase 3: Build final cell list
    # Find insertion point: before "## Resume" or "## Conclusion" or last section header
    insert_point = len(cells) - 1  # default: before last cell
    for idx in range(len(cells) - 1, -1, -1):
        src = "".join(cells[idx].get("source", []))
        if re.search(r"^##\s+(Resume|Conclusion|R.sum.|Bilan)", src, re.MULTILINE):
            insert_point = idx
            break

    # Find where the exercises section starts (to know where to insert examples)
    exercises_section_idx = None
    for idx in range(len(cells)):
        src = "".join(cells[idx].get("source", []))
        if re.search(r"^##\s+\d*\.?\s*Ex", src, re.MULTILINE) and "Exemple" not in src:
            exercises_section_idx = idx
            break

    if dry_run:
        print(f"\n  Plan:")
        print(f"    Corrigé pairs found: {len(corrige_pairs)}")
        print(f"    Stub-only exercises: {len(exercise_stubs)}")
        print(f"    Exercises to move to end: {len(exercise_cells_to_move)}")
        print(f"    Insert point (before conclusion): {insert_point}")
        print(f"    Exercises section starts at: {exercises_section_idx}")
        print(f"    Would remove {len(indices_to_remove)} corrigé cells")
        print(f"    Would move {len(indices_to_move)} exercise cells")
        return False

    # Remove corrigé cells (from highest index to lowest)
    for idx in sorted(indices_to_remove | indices_to_move, reverse=True):
        cells.pop(idx)

    # Recalculate insert_point after removals
    # Find the conclusion/resume section again
    new_insert_point = len(cells) - 1
    for idx in range(len(cells) - 1, -1, -1):
        src = "".join(cells[idx].get("source", []))
        if re.search(r"^##\s+(Resume|Conclusion|R.sum.|Bilan)", src, re.MULTILINE):
            new_insert_point = idx
            break

    # Insert "## Exemples guidés" section with promoted corrigés
    exemples_section_md = {
        "cell_type": "markdown",
        "id": "exemples-guides-sosolalt",
        "metadata": {},
        "source": [
            "---\n\n",
            "## Exemples guidés (solutions proposees par @Sosolalt)\n\n",
            "*Les exercices ci-dessous ont ete resolus par @Sosolalt (EPITA-IS, promo 2028).*\n",
            "*Ils servent de modele pour comprendre les concepts abordes dans ce notebook.*\n"
        ]
    }

    # Build the new cells to insert at new_insert_point
    new_cells = [exemples_section_md]
    for (ex_md, ex_code) in promoted_examples:
        new_cells.append(ex_md)
        new_cells.append(ex_code)

    # Add exercise section header
    exercices_section_md = {
        "cell_type": "markdown",
        "id": "exercices-a-completer",
        "metadata": {},
        "source": [
            "---\n\n",
            "## Exercices a completer\n\n",
            "*Ces exercices sont a realiser par l'etudiant. Les stubs utilisent `pass`, `print(\"Exercice a completer\")` ou `return None`.*\n"
        ]
    }
    new_cells.append(exercices_section_md)

    # Add exercise stubs
    for (desc, stub) in exercise_cells_to_move:
        if desc is not None:
            # Remove any "### Corrigé" reference in the description
            desc_src_list = desc.get("source", [])
            new_desc_src = []
            for line in desc_src_list:
                if "Corrigé" not in line and "Corrige" not in line:
                    new_desc_src.append(line)
            desc["source"] = new_desc_src
            new_cells.append(desc)
        if stub is not None:
            # Ensure stub uses safe pattern
            stub_src = "".join(stub.get("source", []))
            if "raise NotImplementedError" in stub_src:
                stub_src = stub_src.replace("raise NotImplementedError", "pass  # TODO etudiant")
                stub["source"] = [stub_src]
            new_cells.append(stub)
        else:
            # Create a minimal stub
            new_cells.append({
                "cell_type": "code",
                "id": f"stub-{desc.get('id', 'unknown')}",
                "metadata": {},
                "source": ["print(\"Exercice a completer\")"],
                "execution_count": None,
                "outputs": []
            })

    # Insert all new cells at new_insert_point
    for offset, cell in enumerate(new_cells):
        cells.insert(new_insert_point + offset, cell)

    print(f"  Restructured: {len(promoted_examples)} exemples guidés, {len(exercise_cells_to_move)} exercices stubs")

    # Write back
    with open(path, "w", encoding="utf-8") as f:
        json.dump(nb, f, ensure_ascii=False, indent=1)
        f.write("\n")

    print(f"  Written to {path}")
    return True


def main():
    dry_run = "--dry-run" in sys.argv

    if dry_run:
        sys.argv.remove("--dry-run")

    paths = sys.argv[1:] if len(sys.argv) > 1 else DEFAULT_NOTEBOOKS

    for name in paths:
        p = Path(name) if "/" in name or "\\" in name else SW_DIR / name
        if p.exists():
            restructure_notebook(p, dry_run=dry_run)
        else:
            print(f"NOT FOUND: {p}")


if __name__ == "__main__":
    main()
