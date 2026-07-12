"""
Batch extraction of all 12 course slide decks.
Runs the full pipeline: render PNG + extract text + extract images + generate inventory.
"""
import os
import sys
import time

# Add tools directory to path
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from slide_tools import full_extract

SLIDES_ROOT = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

# Mapping: directory name -> PPTX filename in original/
DECKS = {
    "01-introduction": "Intelligence Artificielle - 1 - Introduction.pptx",
    "02-resolution-problemes": "Intelligence Artificielle - 2 - Résolution de problèmes.pptx",
    "03-logique": "Intelligence Artificielle - 3 - Logique.pptx",
    "04-probabilites": "Intelligence Artificielle - 4 - Probabilités.pptx",
    "05-theorie-des-jeux": "Intelligence Artificielle - 5 - Théorie des jeux.pptx",
    "06-apprentissage": "Intelligence Artificielle - 6 - Apprentissage.pptx",
    "07-elargissements": "Intelligence Artificielle - 7 - Elargissements.pptx",
    "08-ia-generative": "Intelligence Artificielle - 8 - IA Générative.pptx",
    "S1-argumentation": "IA et Argumentation.pptx",
    "S2-ia-exploratoire-symbolique": "IA exploratoire et symbolique.pptx",
    "S3-acculturation": "JSBoige - Intelligence Artificielle - Acculturation.pptx",
    "S4-trading-algorithmique": "MyIA - Trading algorithmique.pptx",
}


def main():
    start = time.time()
    results = {}

    for dir_name, pptx_name in DECKS.items():
        pptx_path = os.path.join(SLIDES_ROOT, dir_name, "original", pptx_name)
        output_base = os.path.join(SLIDES_ROOT, dir_name, "extracted")

        if not os.path.exists(pptx_path):
            print(f"SKIP: {pptx_path} not found")
            continue

        print(f"\n{'='*60}")
        print(f"Processing: {dir_name}")
        print(f"{'='*60}")

        try:
            result = full_extract(pptx_path, output_base, render=True)
            results[dir_name] = {
                "slides": result.get("slide_count", 0),
                "renders": result.get("render_count", 0),
                "images": result.get("image_count", 0),
                "status": "OK"
            }
        except Exception as e:
            print(f"ERROR: {dir_name} - {e}")
            results[dir_name] = {"status": f"ERROR: {e}"}

    elapsed = time.time() - start
    print(f"\n{'='*60}")
    print(f"BATCH EXTRACTION COMPLETE in {elapsed:.1f}s")
    print(f"{'='*60}")
    for name, info in results.items():
        if info["status"] == "OK":
            print(f"  {name}: {info['slides']} slides, {info['renders']} renders, {info['images']} images")
        else:
            print(f"  {name}: {info['status']}")


if __name__ == "__main__":
    main()
