#!/usr/bin/env python3
"""
Script de comparaison visuelle Slidev vs PPTX pour le deck S4.
Analyse les slides 3 à 80 et identifie les problèmes.
"""

import os
import subprocess
import json
import re
from pathlib import Path
from typing import Dict, List, Tuple

DECK_PATH = "d:/dev/CoursIA/slides/S4-trading-algorithmique"
SLIDEV_DIR = f"{DECK_PATH}/slidev-export"
PPTX_DIR = f"{DECK_PATH}/pptx-reference"
OUTPUT_FILE = f"{DECK_PATH}/analysis/visual_comparison_s4.md"


def get_slidev_path(slide_num: int) -> str:
    """Retourne le chemin du fichier Slidev pour une slide donnée."""
    return f"{SLIDEV_DIR}/{slide_num}.png"


def get_pptx_path(slide_num: int) -> str:
    """Retourne le chemin du fichier PPTX pour une slide donnée."""
    return f"{PPTX_DIR}/slide-{slide_num:02d}.png"


def file_exists(path: str) -> bool:
    """Vérifie qu'un fichier existe."""
    return os.path.exists(path)


def analyze_slide_pair(slide_num: int) -> Dict:
    """
    Analyse une paire de slides (Slidev vs PPTX) via sk-agent.
    Retourne un dictionnaire avec les résultats.
    """
    slidev_path = get_slidev_path(slide_num)
    pptx_path = get_pptx_path(slide_num)

    # Vérifier que les deux fichiers existent
    if not file_exists(slidev_path):
        return {
            "slide": slide_num,
            "status": "ERROR",
            "reason": f"Fichier Slidev manquant: {slidev_path}"
        }

    if not file_exists(pptx_path):
        return {
            "slide": slide_num,
            "status": "ERROR",
            "reason": f"Fichier PPTX manquant: {pptx_path}"
        }

    # Prompt de comparaison
    prompt = f"""Compare ces deux rendus de la slide {slide_num}:

IMAGE 1 (Slidev - gauche/haut): {slidev_path}
IMAGE 2 (PPTX référence - droite/bas): {pptx_path}

Analyse comparative:
1. **CONTENU**: Texte identique ? Si non, quelle différence ?
2. **LAYOUT**: Structure similaire ? Colonnes, sections, alignement
3. **IMAGES**: Images placées correctement ? Toutes présentes ?
4. **OVERFLOW**: Texte qui dépasse ou est coupé ?
5. **FOOTER**: Footer présent (sauf slide de titre) ?

Classification:
- CRITIQUE: contenu manquant, overflow sévère, texte illisible
- MINEUR: spacing, alignement, couleurs, différences esthétiques
- OK: pas de problème fonctionnel

Format de réponse JSON:
{{
  "status": "OK" | "MINEUR" | "CRITIQUE",
  "differences": "description des différences",
  "missing_content": "contenu manquant (le cas échéant)",
  "overflow": "description overflow (le cas échéant)",
  "layout_issues": "problèmes de layout (le cas échéant)",
  "footer_ok": true | false
}}
"""

    try:
        # Appel à sk-agent via MCP
        result = subprocess.run(
            ["mcp", "call", "sk-agent", "analyze_image"],
            input=json.dumps({
                "image_source": f"{slidev_path}|{pptx_path}",
                "prompt": prompt
            }),
            capture_output=True,
            text=True,
            timeout=30
        )

        if result.returncode != 0:
            return {
                "slide": slide_num,
                "status": "ERROR",
                "reason": f"Erreur MCP: {result.stderr}"
            }

        # Parser la réponse JSON
        response = json.loads(result.stdout)
        response["slide"] = slide_num
        return response

    except subprocess.TimeoutExpired:
        return {
            "slide": slide_num,
            "status": "ERROR",
            "reason": "Timeout MCP"
        }
    except json.JSONDecodeError as e:
        return {
            "slide": slide_num,
            "status": "ERROR",
            "reason": f"Erreur parsing JSON: {e}"
        }
    except Exception as e:
        return {
            "slide": slide_num,
            "status": "ERROR",
            "reason": f"Erreur inattendue: {e}"
        }


def analyze_batch(start: int, end: int) -> List[Dict]:
    """Analyse un lot de slides."""
    results = []
    for slide_num in range(start, end + 1):
        print(f"Analyse slide {slide_num}...")
        result = analyze_slide_pair(slide_num)
        results.append(result)
    return results


def generate_report(all_results: List[Dict]) -> str:
    """Génère le rapport markdown à partir des résultats."""
    ok_slides = []
    minor_slides = []
    critical_slides = []
    error_slides = []

    for r in all_results:
        if r["status"] == "OK":
            ok_slides.append(r["slide"])
        elif r["status"] == "MINEUR":
            minor_slides.append(r)
        elif r["status"] == "CRITIQUE":
            critical_slides.append(r)
        else:
            error_slides.append(r)

    report = f"""# Comparaison Visuelle Slidev vs PPTX - S4 Trading Algorithmique

**Date**: 2026-03-26
**Deck**: {DECK_PATH}
**Slides analysées**: 3 à 80
**Total**: {len(all_results)} slides

---

## Résumé

| Statut | Nombre | Slides |
|--------|--------|--------|
| ✅ OK | {len(ok_slides)} | {format_slide_list(ok_slides)} |
| ⚠️ Mineur | {len(minor_slides)} | {format_slide_list([r["slide"] for r in minor_slides])} |
| 🚨 Critique | {len(critical_slides)} | {format_slide_list([r["slide"] for r in critical_slides])} |
| ❌ Erreur | {len(error_slides)} | {format_slide_list([r["slide"] for r in error_slides])} |

---

## Slides avec Problèmes Critiques 🚨

"""

    # Détails des slides critiques
    for r in critical_slides:
        report += f"""### Slide {r["slide"]}

- **Problème**: {r.get("differences", "Non spécifié")}
- **Contenu manquant**: {r.get("missing_content", "Aucun")}
- **Overflow**: {r.get("overflow", "Aucun")}
- **Layout**: {r.get("layout_issues", "OK")}
- **Footer**: {"✅" if r.get("footer_ok", True) else "❌ Manquant"}

"""

    # Slides avec problèmes mineurs
    report += "\n## Slides avec Problèmes Mineurs ⚠️\n\n"

    for r in minor_slides:
        report += f"""### Slide {r["slide"]}

- **Différences**: {r.get("differences", "Aucune")}
- **Layout**: {r.get("layout_issues", "OK")}

"""

    # Erreurs
    if error_slides:
        report += "\n## Slides avec Erreur d'Analyse ❌\n\n"
        for r in error_slides:
            report += f"### Slide {r["slide"]}\n\n{r.get('reason', 'Erreur inconnue')}\n\n"

    # Conclusion
    report += f"""
---

## Conclusion

**Slides validées**: {len(ok_slides)}/{len(all_results)} ({len(ok_slides)*100//len(all_results)}%)

**Actions requises**:
"""

    if critical_slides:
        report += f"- {len(critical_slides)} slides critiques nécessitent des corrections immédiates\n"
    if minor_slides:
        report += f"- {len(minor_slides)} slides avec problèmes mineurs (améliorations optionnelles)\n"

    if not critical_slides and not minor_slides:
        report += "- ✅ Toutes les slides sont OK !\n"

    return report


def format_slide_list(slides: List[int]) -> str:
    """Formate une liste de numéros de slides en plage compacte."""
    if not slides:
        return "Aucune"

    slides = sorted(set(slides))
    ranges = []
    start = slides[0]
    end = slides[0]

    for i in range(1, len(slides)):
        if slides[i] == end + 1:
            end = slides[i]
        else:
            ranges.append(f"{start}" if start == end else f"{start}-{end}")
            start = slides[i]
            end = slides[i]

    ranges.append(f"{start}" if start == end else f"{start}-{end}")

    # Limiter la longueur
    result = ", ".join(ranges)
    if len(result) > 100:
        return result[:100] + "..."
    return result


def main():
    """Fonction principale."""
    print("Comparaison visuelle Slidev vs PPTX pour S4")
    print("=" * 60)

    # Analyser par lots de 10 slides
    all_results = []
    batch_size = 10

    for start in range(3, 81, batch_size):
        end = min(start + batch_size - 1, 80)
        print(f"\nLot {start}-{end}...")
        batch_results = analyze_batch(start, end)
        all_results.extend(batch_results)

        # Sauvegarde incrémentale
        print(f"Sauvegarde partielle ({len(all_results)} slides analysées)...")
        report = generate_report(all_results)
        Path(OUTPUT_FILE).parent.mkdir(parents=True, exist_ok=True)
        with open(OUTPUT_FILE, "w", encoding="utf-8") as f:
            f.write(report)

    print(f"\n✅ Analyse terminée !")
    print(f"Rapport sauvegardé: {OUTPUT_FILE}")


if __name__ == "__main__":
    main()
