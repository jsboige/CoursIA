"""Audit GenAI notebook corruption - single-line code cells diagnostic."""
import json
import glob
import os
from collections import defaultdict

notebooks = glob.glob("MyIA.AI.Notebooks/GenAI/**/*.ipynb", recursive=True)
# Exclude EPF student notebooks
notebooks = [n for n in notebooks if os.sep + "EPF" + os.sep not in n and "/EPF/" not in n]

corrupted = defaultdict(list)
clean = defaultdict(int)
pattern_count = defaultdict(int)

for nb_path in sorted(notebooks):
    try:
        with open(nb_path, "r", encoding="utf-8") as f:
            nb = json.load(f)

        short = nb_path.replace("MyIA.AI.Notebooks/GenAI/", "").replace("MyIA.AI.Notebooks/GenAI\\", "")
        parts = short.replace("\\", "/").split("/")
        series = parts[0] if parts[0] in ["Audio", "Image", "Video", "Texte", "00-GenAI-Environment", "SemanticKernel"] else "Other"

        has_corruption = False
        corrupt_cells = 0
        for i, cell in enumerate(nb.get("cells", [])):
            if cell.get("cell_type") == "code":
                src = "".join(cell.get("source", []))
                for line in src.strip().split("\n"):
                    if len(line) > 500 and ("import" in line or "def " in line or "dotenv" in line):
                        has_corruption = True
                        corrupt_cells += 1
                        break

        # Check env pattern
        for cell in nb.get("cells", []):
            if cell.get("cell_type") == "code":
                src = "".join(cell.get("source", []))
                if "dotenv" in src or "GENAI_ROOT" in src or ".env" in src:
                    if "env_loaded" in src:
                        pattern_count["env_loaded flag"] += 1
                    elif "while current_path.name" in src:
                        pattern_count["while loop"] += 1
                    elif "GENAI_ROOT" in src:
                        pattern_count["GENAI_ROOT"] += 1
                    elif "find_dotenv" in src:
                        pattern_count["find_dotenv"] += 1
                    elif "load_dotenv" in src:
                        pattern_count["simple load_dotenv"] += 1
                    else:
                        pattern_count["other"] += 1
                    break

        if has_corruption:
            corrupted[series].append((short.replace("\\", "/"), corrupt_cells))
        else:
            clean[series] += 1
    except Exception as e:
        pass

print("=== ETAT DE CORRUPTION DES NOTEBOOKS GENAI (hors EPF) ===\n")
total_corrupt = 0
total_clean = 0
for series in ["Audio", "Image", "Video", "Texte", "00-GenAI-Environment", "SemanticKernel", "Other"]:
    c = len(corrupted.get(series, []))
    cl = clean.get(series, 0)
    total = c + cl
    total_corrupt += c
    total_clean += cl
    if total > 0:
        pct = round(c / total * 100) if total > 0 else 0
        status = "CRITIQUE" if pct > 50 else "MOYEN" if pct > 20 else "OK"
        print(f"{series}: {c}/{total} corrompus ({pct}%) [{status}]")
        for path, cells in corrupted.get(series, []):
            print(f"  X {path} ({cells} cellules)")

print(f"\nTOTAL: {total_corrupt} corrompus, {total_clean} sains, sur {total_corrupt + total_clean}")
print(f"Taux de corruption: {round(total_corrupt / (total_corrupt + total_clean) * 100)}%")

print(f"\n=== PATTERNS .env (inconsistance) ===")
for p, count in sorted(pattern_count.items(), key=lambda x: -x[1]):
    print(f"  {p}: {count} notebooks")
