#!/usr/bin/env python3
"""
Analyse avancée des différences PPTX vs Slidev
Détecte les zones de contenu et identifie les problèmes de layout
"""

from PIL import Image
import numpy as np
from pathlib import Path

def detect_content_zones(img_path, threshold=240):
    """
    Détecte les zones de contenu non-blances dans une image
    Retourne: (bounding_box, coverage_percentage)
    """
    img = Image.open(img_path)
    arr = np.array(img)

    # Convertir en grayscale si nécessaire
    if len(arr.shape) == 3:
        gray = np.mean(arr[:, :, :3], axis=2)
    else:
        gray = arr

    # Créer un masque des pixels non-blancs
    mask = gray < threshold

    # Trouver les bornes du contenu
    if not np.any(mask):
        return None, 0.0

    rows = np.any(mask, axis=1)
    cols = np.any(mask, axis=0)

    rmin, rmax = np.where(rows)[0][[0, -1]]
    cmin, cmax = np.where(cols)[0][[0, -1]]

    bbox = (cmin, rmin, cmax - cmin, rmax - rmin)  # x, y, width, height
    coverage = np.sum(mask) / (img.width * img.height)

    return bbox, coverage

def compare_layouts(pptx_path, slidev_path):
    """Compare les layouts de deux images"""
    pptx_bbox, pptx_cov = detect_content_zones(pptx_path)
    slidev_bbox, slidev_cov = detect_content_zones(slidev_path)

    if pptx_bbox is None or slidev_bbox is None:
        return {
            'error': 'Impossible de détecter les zones de contenu',
            'pptx_bbox': pptx_bbox,
            'slidev_bbox': slidev_bbox
        }

    pptx_img = Image.open(pptx_path)
    slidev_img = Image.open(slidev_path)

    # Calculer les positions relatives (normalisées par la taille de l'image)
    pptx_rel = {
        'x': pptx_bbox[0] / pptx_img.width,
        'y': pptx_bbox[1] / pptx_img.height,
        'w': pptx_bbox[2] / pptx_img.width,
        'h': pptx_bbox[3] / pptx_img.height
    }

    slidev_rel = {
        'x': slidev_bbox[0] / slidev_img.width,
        'y': slidev_bbox[1] / slidev_img.height,
        'w': slidev_bbox[2] / slidev_img.width,
        'h': slidev_bbox[3] / slidev_img.height
    }

    return {
        'pptx': {
            'bbox': pptx_bbox,
            'relative': pptx_rel,
            'coverage': pptx_cov
        },
        'slidev': {
            'bbox': slidev_bbox,
            'relative': slidev_rel,
            'coverage': slidev_cov
        },
        'differences': {
            'x_shift': slidev_rel['x'] - pptx_rel['x'],
            'y_shift': slidev_rel['y'] - pptx_rel['y'],
            'width_ratio': slidev_rel['w'] / pptx_rel['w'] if pptx_rel['w'] > 0 else 0,
            'height_ratio': slidev_rel['h'] / pptx_rel['h'] if pptx_rel['h'] > 0 else 0
        }
    }

def analyze_horizontal_balance(img_path):
    """
    Analyse l'équilibre horizontal du contenu
    Utile pour détecter les slides avec colonnes
    """
    img = Image.open(img_path)
    arr = np.array(img)

    if len(arr.shape) == 3:
        gray = np.mean(arr[:, :, :3], axis=2)
    else:
        gray = arr

    mask = gray < 240
    if not np.any(mask):
        return {'error': 'Pas de contenu détecté'}

    # Diviser l'image en 3 zones horizontales
    h = img.height
    w = img.width

    left_zone = mask[:, :w//3]
    middle_zone = mask[:, w//3:2*w//3]
    right_zone = mask[:, 2*w//3:]

    left_density = np.sum(left_zone) / left_zone.size
    middle_density = np.sum(middle_zone) / middle_zone.size
    right_density = np.sum(right_zone) / right_zone.size

    return {
        'left': left_density,
        'middle': middle_density,
        'right': right_density,
        'pattern': classify_layout_pattern(left_density, middle_density, right_density)
    }

def classify_layout_pattern(left, middle, right):
    """Classifie le pattern de layout"""
    threshold = 0.05

    if left > threshold and middle > threshold and right > threshold:
        return "full-width"
    elif left > threshold and right > threshold and middle < threshold:
        return "two-columns"
    elif left > threshold and middle < threshold and right < threshold:
        return "left-aligned"
    elif left < threshold and middle > threshold and right < threshold:
        return "centered"
    elif left < threshold and middle < threshold and right > threshold:
        return "right-aligned"
    elif left > threshold and middle > threshold and right < threshold:
        return "left-center"
    elif left < threshold and middle > threshold and right > threshold:
        return "center-right"
    else:
        return "empty-or-minimal"

def main():
    base_path = Path('D:/dev/CoursIA/slides/S4-trading-algorithmique')
    pptx_dir = base_path / 'pptx-reference'
    slidev_dir = base_path / 'slidev-export'

    print("=" * 100)
    print("ANALYSE AVANCÉE PPTX vs SLIDEV - S4 Trading Algorithmique")
    print("=" * 100)

    for i in range(1, 6):
        slide_num = f'{i:02d}'
        pptx_path = pptx_dir / f'slide-{slide_num}.png'
        slidev_path = slidev_dir / f'slide-{slide_num}.png'

        print(f"\n{'=' * 100}")
        print(f"SLIDE {slide_num}")
        print(f"{'=' * 100}")

        # Analyse des zones de contenu
        layout_analysis = compare_layouts(pptx_path, slidev_path)

        if 'error' in layout_analysis:
            print(f"ERREUR: {layout_analysis['error']}")
            continue

        print(f"\n📐 ZONES DE CONTENU:")
        print(f"  PPTX:  x={layout_analysis['pptx']['bbox'][0]:4d}, y={layout_analysis['pptx']['bbox'][1]:4d}, "
              f"w={layout_analysis['pptx']['bbox'][2]:4d}, h={layout_analysis['pptx']['bbox'][3]:4d}")
        print(f"  Slidev: x={layout_analysis['slidev']['bbox'][0]:4d}, y={layout_analysis['slidev']['bbox'][1]:4d}, "
              f"w={layout_analysis['slidev']['bbox'][2]:4d}, h={layout_analysis['slidev']['bbox'][3]:4d}")

        print(f"\n📊 POSITION RELATIVE (normalisée):")
        print(f"  PPTX:  x={layout_analysis['pptx']['relative']['x']:.3f}, y={layout_analysis['pptx']['relative']['y']:.3f}, "
              f"w={layout_analysis['pptx']['relative']['w']:.3f}, h={layout_analysis['pptx']['relative']['h']:.3f}")
        print(f"  Slidev: x={layout_analysis['slidev']['relative']['x']:.3f}, y={layout_analysis['slidev']['relative']['y']:.3f}, "
              f"w={layout_analysis['slidev']['relative']['w']:.3f}, h={layout_analysis['slidev']['relative']['h']:.3f}")

        print(f"\n⚠️  DIFFÉRENCES:")
        diff = layout_analysis['differences']
        print(f"  Décalage X: {diff['x_shift']:+.3f} ({'gauche' if diff['x_shift'] < -0.05 else 'droite' if diff['x_shift'] > 0.05 else 'centré'})")
        print(f"  Décalage Y: {diff['y_shift']:+.3f} ({'haut' if diff['y_shift'] < -0.05 else 'bas' if diff['y_shift'] > 0.05 else 'aligné'})")
        print(f"  Ratio largeur: {diff['width_ratio']:.2f}x")
        print(f"  Ratio hauteur: {diff['height_ratio']:.2f}x")

        # Analyse de l'équilibre horizontal
        pptx_balance = analyze_horizontal_balance(pptx_path)
        slidev_balance = analyze_horizontal_balance(slidev_path)

        if 'error' not in pptx_balance and 'error' not in slidev_balance:
            print(f"\n🔄 ÉQUILIBRE HORIZONTAL:")
            print(f"  PPTX:  gauche={pptx_balance['left']:.3f}, centre={pptx_balance['middle']:.3f}, droite={pptx_balance['right']:.3f}")
            print(f"         Pattern: {pptx_balance['pattern']}")
            print(f"  Slidev: gauche={slidev_balance['left']:.3f}, centre={slidev_balance['middle']:.3f}, droite={slidev_balance['right']:.3f}")
            print(f"         Pattern: {slidev_balance['pattern']}")

            if pptx_balance['pattern'] != slidev_balance['pattern']:
                print(f"  ⚠️  ALERTE: Pattern de layout différent!")
            else:
                print(f"  ✓ Pattern de layout identique")

        # Recommandations
        print(f"\n💡 RECOMMANDATIONS:")
        recommendations = generate_recommendations(layout_analysis, pptx_balance, slidev_balance)
        for rec in recommendations:
            print(f"  - {rec}")

    print(f"\n{'=' * 100}")
    print("ANALYSE TERMINÉE")
    print(f"{'=' * 100}")

def generate_recommendations(layout_analysis, pptx_balance, slidev_balance):
    """Génère des recommandations basées sur l'analyse"""
    recommendations = []

    diff = layout_analysis['differences']

    # Vérifier le décalage horizontal
    if abs(diff['x_shift']) > 0.05:
        recommendations.append(f"Ajuster l'alignement horizontal (décalage de {diff['x_shift']:.1%})")

    # Vérifier le décalage vertical
    if abs(diff['y_shift']) > 0.05:
        recommendations.append(f"Ajuster l'alignement vertical (décalage de {diff['y_shift']:.1%})")

    # Vérifier le ratio de largeur
    if diff['width_ratio'] < 0.9 or diff['width_ratio'] > 1.1:
        recommendations.append(f"Vérifier la largeur du contenu (ratio: {diff['width_ratio']:.2f}x)")

    # Vérifier le ratio de hauteur
    if diff['height_ratio'] < 0.9 or diff['height_ratio'] > 1.1:
        recommendations.append(f"Vérifier la hauteur du contenu (ratio: {diff['height_ratio']:.2f}x)")

    # Vérifier les patterns de layout
    if 'error' not in pptx_balance and 'error' not in slidev_balance:
        if pptx_balance['pattern'] != slidev_balance['pattern']:
            recommendations.append(f"Corriger le pattern de layout (PPTX: {pptx_balance['pattern']}, Slidev: {slidev_balance['pattern']})")

    # Vérifier la couverture
    if layout_analysis['slidev']['coverage'] < layout_analysis['pptx']['coverage'] * 0.8:
        recommendations.append("Slidev a moins de contenu - vérifier les éléments manquants")

    if not recommendations:
        recommendations.append("Aucun problème majeur détecté")

    return recommendations

if __name__ == '__main__':
    main()
