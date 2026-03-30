#!/usr/bin/env python3
"""
Comparaison structurée des slides PPTX vs Slidev
Utilise OCR pour extraire et comparer le texte
"""

try:
    import pytesseract
    from PIL import Image
    from pathlib import Path
    OCR_AVAILABLE = True
except ImportError:
    OCR_AVAILABLE = False
    print("OCR non disponible - installation: pip install pytesseract")

def extract_text_from_image(img_path):
    """Extrait le texte d'une image via OCR"""
    if not OCR_AVAILABLE:
        return "OCR non disponible"

    try:
        img = Image.open(img_path)
        # Configuration pour français
        text = pytesseract.image_to_string(img, lang='fra')
        return text.strip()
    except Exception as e:
        return f"Erreur OCR: {e}"

def compare_text_content(pptx_text, slidev_text):
    """Compare deux textes et retourne les différences"""
    pptx_lines = [l.strip() for l in pptx.split('\n') if l.strip()]
    slidev_lines = [l.strip() for l in slidev_text.split('\n') if l.strip()]

    return {
        'pptx_line_count': len(pptx_lines),
        'slidev_line_count': len(slidev_lines),
        'pptx_char_count': len(pptx_text),
        'slidev_char_count': len(slidev_text),
        'missing_in_slidev': len(pptx_lines) - len(slidev_lines)
    }

def main():
    base_path = Path('D:/dev/CoursIA/slides/S4-trading-algorithmique')
    pptx_dir = base_path / 'pptx-reference'
    slidev_dir = base_path / 'slidev-export'

    print("=" * 80)
    print("COMPARAISON DE CONTENU PPTX vs SLIDEV - S4 Trading Algorithmique")
    print("=" * 80)

    if not OCR_AVAILABLE:
        print("\n⚠️  OCR non disponible - veuillez installer: pip install pytesseract")
        print("    Et installer le binaire Tesseract sur votre système")
        return

    for i in range(1, 6):
        slide_num = f'{i:02d}'
        pptx_path = pptx_dir / f'slide-{slide_num}.png'
        slidev_path = slidev_dir / f'slide-{slide_num}.png'

        print(f"\n{'─' * 80}")
        print(f"SLIDE {slide_num}")
        print(f"{'─' * 80}")

        pptx_text = extract_text_from_image(pptx_path)
        slidev_text = extract_text_from_image(slidev_path)

        stats = compare_text_content(pptx_text, slidev_text)

        print(f"  Lignes PPTX:  {stats['pptx_line_count']:3d}")
        print(f"  Lignes Slidev: {stats['slidev_line_count']:3d}")
        print(f"  Caractères PPTX:  {stats['pptx_char_count']:5d}")
        print(f"  Caractères Slidev: {stats['slidev_char_count']:5d}")

        if stats['missing_in_slidev'] > 5:
            print(f"  ⚠️  ALERTE: {stats['missing_in_slidev']} lignes manquantes dans Slidev")
        elif stats['missing_in_slidev'] < -5:
            print(f"  ⚠️  INFO: Slidev a {-stats['missing_in_slidev']} lignes supplémentaires")
        else:
            print(f"  ✓ Contenu textuel similaire")

    print(f"\n{'=' * 80}")

if __name__ == '__main__':
    main()
