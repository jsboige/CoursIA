#!/usr/bin/env python3
"""
Comparaison visuelle des slides PPTX vs Slidev pour S4-trading-algorithmique
Analyse les slides 01-05 et identifie les problèmes de layout, overflow, etc.
"""

from PIL import Image
import numpy as np
from pathlib import Path

def compare_dimensions(pptx_path, slidev_path):
    """Compare les dimensions des deux images"""
    try:
        pptx = Image.open(pptx_path)
        slidev = Image.open(slidev_path)

        return {
            'pptx_size': pptx.size,
            'slidev_size': slidev.size,
            'ratio_diff': slidev.size[0] / pptx.size[0]
        }
    except Exception as e:
        return {'error': str(e)}

def analyze_image_density(img_path):
    """Analyse la densité de contenu d'une image"""
    try:
        img = Image.open(img_path)
        arr = np.array(img)

        # Calculer la proportion de pixels non-blancs
        if len(arr.shape) == 3:
            # RGB: considérer blanc si R,G,B > 240
            non_white = np.sum(np.all(arr < 240, axis=2))
        else:
            # Grayscale
            non_white = np.sum(arr < 240)

        total = arr.shape[0] * arr.shape[1]
        density = non_white / total

        return {
            'size': img.size,
            'density': density,
            'pixels_non_white': non_white,
            'total_pixels': total
        }
    except Exception as e:
        return {'error': str(e)}

def main():
    base_path = Path('D:/dev/CoursIA/slides/S4-trading-algorithmique')
    pptx_dir = base_path / 'pptx-reference'
    slidev_dir = base_path / 'slidev-export'

    print("=" * 80)
    print("COMPARAISON VISUELLE PPTX vs SLIDEV - S4 Trading Algorithmique")
    print("=" * 80)

    for i in range(1, 6):
        slide_num = f'{i:02d}'
        pptx_path = pptx_dir / f'slide-{slide_num}.png'
        slidev_path = slidev_dir / f'slide-{slide_num}.png'

        print(f"\n{'─' * 80}")
        print(f"SLIDE {slide_num}")
        print(f"{'─' * 80}")

        # Comparaison dimensions
        dims = compare_dimensions(pptx_path, slidev_path)
        if 'error' in dims:
            print(f"  ERREUR: {dims['error']}")
            continue

        print(f"  Dimensions PPTX:  {dims['pptx_size'][0]:4d} x {dims['pptx_size'][1]:4d}")
        print(f"  Dimensions Slidev: {dims['slidev_size'][0]:4d} x {dims['slidev_size'][1]:4d}")
        print(f"  Ratio largeur: {dims['ratio_diff']:.2f}x")

        # Analyse densité
        pptx_density = analyze_image_density(pptx_path)
        slidev_density = analyze_image_density(slidev_path)

        if 'error' not in pptx_density and 'error' not in slidev_density:
            density_diff = slidev_density['density'] - pptx_density['density']
            print(f"  Densité PPTX:  {pptx_density['density']:.3f}")
            print(f"  Densité Slidev: {slidev_density['density']:.3f}")
            print(f"  Différence: {density_diff:+.3f} ({'plus dense' if density_diff > 0 else 'moins dense'})")

            # Détection potentielle d'overflow
            if density_diff > 0.1:
                print(f"  ⚠️  ALERTE: Slidev semble significativement plus dense (overflow possible)")
            elif density_diff < -0.1:
                print(f"  ⚠️  ALERTE: Slidev semble moins dense (contenu manquant possible)")

    print(f"\n{'=' * 80}")
    print("ANALYSE TERMINÉE")
    print(f"{'=' * 80}")

if __name__ == '__main__':
    main()
