#!/usr/bin/env python3
"""
Script de validation du contenu des slides S4-03 à S4-80.
Extrait le texte markdown de chaque slide et identifie les slides potentiellement problématiques.
"""

import re
from pathlib import Path
from typing import Dict, List, Tuple

DECK_PATH = "d:/dev/CoursIA/slides/S4-trading-algorithmique"
SLIDES_MD = f"{DECK_PATH}/slides.md"
OUTPUT_FILE = f"{DECK_PATH}/analysis/content_validation_report.md"


def parse_slides_md(file_path: str) -> List[Dict]:
    """
    Parse le fichier slides.md et extrait le contenu de chaque slide.
    Retourne une liste de dictionnaires avec numéros et contenu.
    """
    with open(file_path, 'r', encoding='utf-8') as f:
        content = f.read()

    # Séparer les slides par les délimiteurs ---
    slides_raw = content.split('---')

    slides = []
    for i, slide_content in enumerate(slides_raw):
        # Ignorer les slides vides ou le frontmatter
        if not slide_content.strip():
            continue

        # Extraire le titre (première ligne #)
        title = "Sans titre"
        title_match = re.search(r'^#\s+(.+)$', slide_content, re.MULTILINE)
        if title_match:
            title = title_match.group(1).strip()

        # Nettoyer le contenu (retirer les balises HTML, v-click, etc.)
        clean_content = slide_content
        clean_content = re.sub(r'<div[^>]*>', '', clean_content)
        clean_content = re.sub(r'</div>', '', clean_content)
        clean_content = re.sub(r'v-click[^>]*', '', clean_content)
        clean_content = re.sub(r'^---$', '', clean_content, flags=re.MULTILINE)
        clean_content = clean_content.strip()

        # Compter les caractères et lignes
        char_count = len(clean_content)
        line_count = len(clean_content.split('\n'))

        slides.append({
            'num': i + 1,  # Numéro de slide (1-based)
            'title': title,
            'content': clean_content,
            'char_count': char_count,
            'line_count': line_count
        })

    return slides


def classify_slide_complexity(slide: Dict) -> str:
    """
    Classifie une slide selon sa complexité.
    """
    if slide['char_count'] < 200:
        return "simple"
    elif slide['char_count'] < 600:
        return "moyenne"
    elif slide['char_count'] < 1200:
        return "complexe"
    else:
        return "très_complexe"


def identify_potential_problems(slide: Dict) -> List[str]:
    """
    Identifie les problèmes potentiels dans une slide.
    """
    problems = []

    # Vérifier si le contenu est très long (risque d'overflow)
    if slide['char_count'] > 1500:
        problems.append("Contenu très long (>1500 caractères) - risque d'overflow")

    # Vérifier s'il y a beaucoup de listes imbriquées
    list_depth = slide['content'].count('  -')
    if list_depth > 10:
        problems.append(f"Beaucoup d'imbrications ({list_depth} niveaux) - risque de layout")

    # Vérifier la présence d'images
    has_image = '![bg' in slide['content'] or '![](' in slide['content'] or '<img' in slide['content']
    if not has_image and slide['char_count'] > 800:
        problems.append("Slide textuel dense sans image - peut être difficile à lire")

    # Vérifier les layouts spéciaux
    if 'layout: image-right' in slide['content'] or 'layout: image-left' in slide['content']:
        problems.append("Layout avec image - vérifier le positionnement")

    if 'layout: two-cols' in slide['content'] or 'layout: two-columns' in slide['content']:
        problems.append("Layout deux colonnes - vérifier l'équilibre")

    return problems


def generate_report(slides: List[Dict]) -> str:
    """Génère le rapport de validation du contenu."""
    # Filtrer les slides 3 à 80
    target_slides = [s for s in slides if 3 <= s['num'] <= 80]

    # Statistiques
    simple = sum(1 for s in target_slides if classify_slide_complexity(s) == "simple")
    moyenne = sum(1 for s in target_slides if classify_slide_complexity(s) == "moyenne")
    complexe = sum(1 for s in target_slides if classify_slide_complexity(s) == "complexe")
    tres_complexe = sum(1 for s in target_slides if classify_slide_complexity(s) == "très_complexe")

    # Identifier les slides avec problèmes potentiels
    slides_with_problems = []
    for slide in target_slides:
        problems = identify_potential_problems(slide)
        if problems:
            slides_with_problems.append({
                'num': slide['num'],
                'title': slide['title'],
                'complexity': classify_slide_complexity(slide),
                'char_count': slide['char_count'],
                'line_count': slide['line_count'],
                'problems': problems
            })

    # Générer le rapport
    report = f"""# Rapport de Validation du Contenu - S4 Trading Algorithmique
## Slides S4-03 à S4-80

**Date**: 2026-03-26
**Méthode**: Analyse du contenu markdown extrait de slides.md
**Slides analysées**: {len(target_slides)}

---

## Résumé Exécutif

| Complexité | Nombre | % |
|------------|--------|---|
| Simple (<200 car.) | {simple} | {simple*100//len(target_slides)}% |
| Moyenne (200-600) | {moyenne} | {moyenne*100//len(target_slides)}% |
| Complexe (600-1200) | {complexe} | {complexe*100//len(target_slides)}% |
| Très complexe (>1200) | {tres_complexe} | {tres_complexe*100//len(target_slides)}% |

**Slides avec problèmes potentiels** : {len(slides_with_problems)}

---

## Slides avec Problèmes Potentiels 🚨

Ces slides méritent une attention particulière lors de la validation visuelle :

"""

    # Slides avec problèmes
    if slides_with_problems:
        for slide in slides_with_problems:
            report += f"""### Slide S4-{slide['num']:02d} : {slide['title']}

- **Complexité** : {slide['complexity']}
- **Caractères** : {slide['char_count']}
- **Lignes** : {slide['line_count']}
- **Problèmes identifiés** :
"""
            for problem in slide['problems']:
                report += f"  - {problem}\n"
            report += "\n"
    else:
        report += "*Aucun problème potentiel identifié !*\n\n"

    # Slides très complexes
    very_complex_slides = [s for s in target_slides if classify_slide_complexity(s) == "très_complexe"]
    if very_complex_slides:
        report += "## Slides Très Complexes (À vérifier en priorité)\n\n"
        for slide in very_complex_slides[:10]:  # Limiter à 10
            report += f"- **S4-{slide['num']:02d}** : {slide['title']} ({slide['char_count']} car.)\n"
        if len(very_complex_slides) > 10:
            report += f"*... et {len(very_complex_slides) - 10} autres slides très complexes*\n"
        report += "\n"

    # Distribution du contenu
    report += "## Distribution du Contenu\n\n"

    char_counts = [s['char_count'] for s in target_slides]
    if char_counts:
        report += f"- **Moyenne** : {sum(char_counts)//len(char_counts)} caractères/slide\n"
        report += f"- **Minimum** : {min(char_counts)} caractères\n"
        report += f"- **Maximum** : {max(char_counts)} caractères\n"
        report += f"- **Médiane** : {sorted(char_counts)[len(char_counts)//2]} caractères\n\n"

    # Recommandations
    report += "---\n\n## Recommandations\n\n"

    if slides_with_problems:
        report += "### Validation Prioritaire\n\n"
        report += f"Les {len(slides_with_problems)} slides avec problèmes potentiels doivent être vérifiées en priorité :\n"
        report += "1. Ouvrir les PNG Slidev et PPTX côte-à-côte\n"
        report += "2. Vérifier que tout le contenu est visible\n"
        report += "3. Confirmer l'absence d'overflow ou de contenu masqué\n\n"

    if very_complex_slides:
        report += "### Slides Complexes\n\n"
        report += f"Les {len(very_complex_slides)} slides très complexes peuvent bénéficier d'un layout compact :\n"
        report += "- Utiliser le layout `compact` si disponible\n"
        report += "- Réduire la quantité de texte par slide\n"
        report += "- Fractionner en plusieurs slides si nécessaire\n\n"

    report += "### Validation Globale\n\n"
    report += "Pour les autres slides, une validation visuelle standard est suffisante :\n"
    report += "- Vérifier l'alignement du texte\n"
    report += "- Confirmer que les images sont présentes\n"
    report += "- Valider la lisibilité (taille de police)\n\n"

    return report


def main():
    """Fonction principale."""
    print("Validation du contenu des slides S4-03 à S4-80")
    print("=" * 60)

    # Parser le fichier slides.md
    print("Parsing de slides.md...")
    slides = parse_slides_md(SLIDES_MD)
    print(f"{len(slides)} slides extraites")

    # Filtrer les slides 3 à 80
    target_slides = [s for s in slides if 3 <= s['num'] <= 80]
    print(f"{len(target_slides)} slides cibles (S4-03 à S4-80)")

    # Générer le rapport
    print("Génération du rapport...")
    report = generate_report(slides)

    # Sauvegarder
    Path(OUTPUT_FILE).parent.mkdir(parents=True, exist_ok=True)
    with open(OUTPUT_FILE, 'w', encoding='utf-8') as f:
        f.write(report)

    print(f"✅ Rapport sauvegardé: {OUTPUT_FILE}")


if __name__ == "__main__":
    main()
