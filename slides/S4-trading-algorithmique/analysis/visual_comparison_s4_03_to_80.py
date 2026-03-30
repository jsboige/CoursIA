#!/usr/bin/env python3
"""
Script de comparaison visuelle Slidev vs PPTX pour les slides S4-03 à S4-80.
Utilise PIL pour comparer les images et identifier les différences significatives.
"""

import os
from pathlib import Path
from PIL import Image, ImageDraw, ImageChops, ImageStat
import json
from typing import Dict, List, Tuple, Optional

DECK_PATH = "d:/dev/CoursIA/slides/S4-trading-algorithmique"
SLIDEV_DIR = f"{DECK_PATH}/slidev-export"
PPTX_DIR = f"{DECK_PATH}/pptx-reference"
OUTPUT_FILE = f"{DECK_PATH}/analysis/visual_comparison_s4_03_to_80.md"

# Dimensions attendues (1920x1080 pour Slidev, PPTX variable)
EXPECTED_WIDTH = 1920
EXPECTED_HEIGHT = 1080


def get_slidev_path(slide_num: int) -> str:
    """Retourne le chemin du fichier Slidev."""
    return f"{SLIDEV_DIR}/{slide_num}.png"


def get_pptx_path(slide_num: int) -> str:
    """Retourne le chemin du fichier PPTX."""
    return f"{PPTX_DIR}/slide-{slide_num:02d}.png"


def file_exists(path: str) -> bool:
    """Vérifie qu'un fichier existe."""
    return os.path.exists(path)


def load_image(path: str) -> Optional[Image.Image]:
    """Charge une image PIL."""
    try:
        return Image.open(path)
    except Exception as e:
        print(f"Erreur chargement {path}: {e}")
        return None


def resize_to_match(img1: Image.Image, img2: Image.Image) -> Tuple[Image.Image, Image.Image]:
    """Redimensionne img2 pour matcher img1 si nécessaire."""
    if img1.size != img2.size:
        print(f"  Redimensionnement {img2.size} -> {img1.size}")
        img2 = img2.resize(img1.size, Image.Resampling.LANCZOS)
    return img1, img2


def compute_difference(img1: Image.Image, img2: Image.Image) -> Image.Image:
    """Calcule la différence entre deux images."""
    img1, img2 = resize_to_match(img1, img2)
    diff = ImageChops.difference(img1, img2)
    return diff


def get_difference_stats(diff: Image.Image) -> Dict:
    """Calcule les statistiques de différence."""
    stat = ImageStat.Stat(diff)
    return {
        "mean": stat.mean[0],  # Moyenne des différences (0-255)
        "stddev": stat.stddev[0],  # Écart-type
        "max": max(stat.extrema)[0]  # Différence maximale
    }


def classify_difference(stats: Dict) -> str:
    """Classifie la différence selon les statistiques."""
    mean_diff = stats["mean"]

    if mean_diff < 5:
        return "OK"  # Différence minimale (bruit, compression)
    elif mean_diff < 15:
        return "MINEUR"  # Différence mineure (spacing, couleurs)
    elif mean_diff < 30:
        return "MODERE"  # Différence modérée (layout, décalage)
    else:
        return "CRITIQUE"  # Différence critique (contenu manquant, overflow)


def detect_overflow(img_slidev: Image.Image) -> Dict:
    """Détecte si le contenu dépasse du cadre."""
    width, height = img_slidev.size

    # Analyser les bords pour détecter du contenu qui dépasse
    # On regarde les pixels sur les bords

    # Bord gauche (5% de la largeur)
    left_region = img_slidev.crop((0, 0, width * 0.05, height))
    left_stat = ImageStat.Stat(left_region)

    # Bord droit (5% de la largeur)
    right_region = img_slidev.crop((width * 0.95, 0, width, height))
    right_stat = ImageStat.Stat(right_region)

    # Bord bas (5% de la hauteur)
    bottom_region = img_slidev.crop((0, height * 0.95, width, height))
    bottom_stat = ImageStat.Stat(bottom_region)

    # Si les bords sont très sombres, pas d'overflow
    # S'ils sont clairs, il y a peut-être du contenu qui dépasse

    overflow_detected = False
    overflow_details = []

    if left_stat.mean[0] > 200:  # Bord gauche clair
        overflow_detected = True
        overflow_details.append("gauche")

    if right_stat.mean[0] > 200:  # Bord droit clair
        overflow_detected = True
        overflow_details.append("droite")

    if bottom_stat.mean[0] > 200:  # Bord bas clair
        overflow_detected = True
        overflow_details.append("bas")

    return {
        "detected": overflow_detected,
        "edges": overflow_details
    }


def analyze_slide_pair(slide_num: int) -> Dict:
    """Analyse une paire de slides (Slidev vs PPTX)."""
    slidev_path = get_slidev_path(slide_num)
    pptx_path = get_pptx_path(slide_num)

    # Vérifier l'existence
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

    # Charger les images
    img_slidev = load_image(slidev_path)
    img_pptx = load_image(pptx_path)

    if img_slidev is None or img_pptx is None:
        return {
            "slide": slide_num,
            "status": "ERROR",
            "reason": "Erreur de chargement des images"
        }

    # Calculer la différence
    diff = compute_difference(img_slidev, img_pptx)
    stats = get_difference_stats(diff)

    # Classifier la différence
    diff_status = classify_difference(stats)

    # Détecter l'overflow
    overflow_info = detect_overflow(img_slidev)

    # Informations dimensionnelles
    result = {
        "slide": slide_num,
        "status": diff_status,
        "slidev_size": img_slidev.size,
        "pptx_size": img_pptx.size,
        "diff_mean": stats["mean"],
        "diff_stddev": stats["stddev"],
        "diff_max": stats["max"],
        "overflow": overflow_info["detected"],
        "overflow_edges": overflow_info["edges"]
    }

    # Analyse qualitative basée sur les métriques
    if diff_status == "CRITIQUE":
        result["analysis"] = "Différence critique entre PPTX et Slidev. Contenu manquant ou layout très différent."
    elif diff_status == "MODERE":
        result["analysis"] = "Différence modérée. Probablement un décalage de layout ou d'espacement."
    elif diff_status == "MINEUR":
        result["analysis"] = "Différence mineure. Probablement des différences de couleur ou de compression."
    else:
        result["analysis"] = "Rendu conforme. Différences minimales."

    # Vérifier si overflow détecté
    if overflow_info["detected"]:
        result["status"] = "CRITIQUE"
        result["analysis"] += f" Overflow détecté sur les bords: {', '.join(overflow_info['edges'])}."

    return result


def analyze_batch(start: int, end: int) -> List[Dict]:
    """Analyse un lot de slides."""
    results = []
    for slide_num in range(start, end + 1):
        print(f"Analyse slide {slide_num}...")
        result = analyze_slide_pair(slide_num)
        results.append(result)
    return results


def generate_report(all_results: List[Dict]) -> str:
    """Génère le rapport markdown."""
    ok_slides = []
    minor_slides = []
    modere_slides = []
    critical_slides = []
    error_slides = []

    for r in all_results:
        if r["status"] == "OK":
            ok_slides.append(r)
        elif r["status"] == "MINEUR":
            minor_slides.append(r)
        elif r["status"] == "MODERE":
            modere_slides.append(r)
        elif r["status"] == "CRITIQUE":
            critical_slides.append(r)
        else:
            error_slides.append(r)

    report = f"""# Comparaison Visuelle Slidev vs PPTX - S4 Trading Algorithmique
## Slides S4-03 à S4-80

**Date**: 2026-03-26
**Deck**: {DECK_PATH}
**Méthode**: Analyse pixel-perfect des images PNG
**Slides analysées**: {len(all_results)}

---

## Résumé Exécutif

| Statut | Nombre | % |
|--------|--------|---|
| ✅ OK (différence minimale) | {len(ok_slides)} | {len(ok_slides)*100//len(all_results)}% |
| ⚠️ Mineur (couleurs, compression) | {len(minor_slides)} | {len(minor_slides)*100//len(all_results)}% |
| 🔶 Modéré (layout, espacement) | {len(modere_slides)} | {len(modere_slides)*100//len(all_results)}% |
| 🚨 Critique (contenu, overflow) | {len(critical_slides)} | {len(critical_slides)*100//len(all_results)}% |
| ❌ Erreur (fichier manquant) | {len(error_slides)} | {len(error_slides)*100//len(all_results)}% |

---

## Slides avec Problèmes Critiques 🚨

"""

    # Slides critiques
    if critical_slides:
        for r in critical_slides:
            report += f"""### Slide S4-{r['slide']:02d}

- **Différence moyenne**: {r['diff_mean']:.1f}/255
- **Différence maximale**: {r['diff_max']:.0f}/255
- **Overflow**: {'Oui - ' + ', '.join(r['overflow_edges']) if r['overflow'] else 'Non'}
- **Taille Slidev**: {r['slidev_size']}
- **Taille PPTX**: {r['pptx_size']}
- **Analyse**: {r['analysis']}

"""
    else:
        report += "*Aucune slide critique détectée !*\n\n"

    # Slides avec problèmes modérés
    report += "## Slides avec Problèmes Modérés 🔶\n\n"

    if modere_slides:
        for r in modere_slides[:20]:  # Limiter à 20 slides
            report += f"""### Slide S4-{r['slide']:02d}

- **Différence moyenne**: {r['diff_mean']:.1f}/255
- **Analyse**: {r['analysis']}

"""
        if len(modere_slides) > 20:
            report += f"*... et {len(modere_slides) - 20} autres slides modérées*\n\n"
    else:
        report += "*Aucune slide modérée détectée !*\n\n"

    # Slides avec problèmes mineurs
    report += "## Slides avec Problèmes Mineurs ⚠️\n\n"

    if minor_slides:
        report += f"*{len(minor_slides)} slides avec différences mineures (couleurs, compression, spacing).\n\n"
        report += "Slides concernées: " + ", ".join([f"S4-{r['slide']:02d}" for r in minor_slides[:20]])
        if len(minor_slides) > 20:
            report += f" ... et {len(minor_slides) - 20} autres"
        report += "\n\n"
    else:
        report += "*Aucune slide mineure détectée !*\n\n"

    # Erreurs
    if error_slides:
        report += "## Slides avec Erreur ❌\n\n"
        for r in error_slides:
            report += f"### Slide S4-{r['slide']:02d}\n\n{r.get('reason', 'Erreur inconnue')}\n\n"

    # Statistiques globales
    report += "---\n\n## Statistiques Globales\n\n"

    if all_results:
        mean_diffs = [r.get("diff_mean", 0) for r in all_results if "diff_mean" in r]
        if mean_diffs:
            report += f"- **Différence moyenne globale**: {sum(mean_diffs)/len(mean_diffs):.1f}/255\n"
            report += f"- **Slides avec overflow**: {sum(1 for r in all_results if r.get('overflow'))}\n"

    # Conclusion
    report += f"""
---

## Conclusion et Recommandations

**Taux de conformité**: {len(ok_slides)}/{len(all_results)} slides ({len(ok_slides)*100//len(all_results)}%)

"""

    if critical_slides:
        report += f"### Actions Requises (Priorité HAUTE)\n\n"
        report += f"- {len(critical_slides)} slides nécessitent une correction immédiate\n"
        report += "- Vérifier le contenu manquant ou l'overflow\n"
        report += "- Ajuster le layout ou la taille du texte\n\n"

    if modere_slides:
        report += f"### Améliorations Recommandées (Priorité MOYENNE)\n\n"
        report += f"- {len(modere_slides)} slides avec problèmes de layout modérés\n"
        report += "- Vérifier l'espacement et l'alignement\n"
        report += "- Ajuster le padding si nécessaire\n\n"

    if not critical_slides and not modere_slides:
        report += "### ✅ Résultat Excellent\n\n"
        report += "Toutes les slides sont conformes aux références PPTX !\n\n"

    return report


def main():
    """Fonction principale."""
    print("Comparaison visuelle Slidev vs PPTX pour S4-03 à S4-80")
    print("=" * 60)

    # Analyser par lots de 20 slides
    all_results = []
    batch_size = 20

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
