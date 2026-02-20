# Guide de Conversion Marp - Deck 02-resolution-problemes

Ce guide fournit les modèles de code et les configurations nécessaires pour convertir le deck PPTX vers Marp.

---

## Structure des Fichiers

```
02-resolution-problemes/
├── marp/
│   ├── slides.md              # Fichier principal Marp
│   ├── theme/
│   │   └── ia101.css          # Thème personnalisé
│   ├── images/                # Images extraites (symlink vers ../extracted/images/)
│   └── output/                # PDF générés
├── extracted/
│   ├── content.md             # Contenu extrait du PPTX
│   ├── images/                # Images PNG extraites
│   ├── renders/               # Rendus des slides (référence visuelle)
│   └── inventory.json         # Métadonnées
└── analysis/
    ├── pptx_layout_analysis.md     # Analyse des layouts
    ├── problematic_slides_report.md # Slides problématiques
    └── marp_conversion_guide.md    # Ce fichier
```

---

## Thème CSS Personnalisé (ia101.css)

```css
/* @theme ia101 */

/* === Variables === */
@import url('https://fonts.googleapis.com/css2?family=Roboto:wght@300;400;500;700&family=Roboto+Mono:wght@400;500&display=swap');

:root {
  --ia-primary: #1a237e;
  --ia-secondary: #283593;
  --ia-accent: #3f51b5;
  --ia-text: #212121;
  --ia-text-light: #757575;
  --ia-bg: #fafafa;
  --ia-code-bg: #f5f5f5;
}

/* === Base Styles === */
section {
  font-family: 'Roboto', sans-serif;
  color: var(--ia-text);
  background: var(--ia-bg);
  font-size: 24px;
}

h1 {
  color: var(--ia-primary);
  font-size: 48px;
  font-weight: 700;
  margin-bottom: 0.5em;
}

h2 {
  color: var(--ia-secondary);
  font-size: 36px;
  font-weight: 500;
  margin-bottom: 0.4em;
}

h3 {
  color: var(--ia-accent);
  font-size: 28px;
  font-weight: 500;
  margin-bottom: 0.3em;
}

/* === Layout: two-cols (standard) === */
section.two-cols {
  display: grid;
  grid-template-columns: 62% 34%;
  gap: 2%;
  align-items: start;
  padding: 40px;
}

section.two-cols.wide-img {
  grid-template-columns: 55% 43%;
}

section.two-cols .left {
  padding-right: 20px;
}

section.two-cols .right {
  display: flex;
  flex-direction: column;
  gap: 12px;
  align-items: center;
  justify-content: center;
}

section.two-cols .right img {
  max-width: 100%;
  height: auto;
  max-height: 380px;
  object-fit: contain;
  border-radius: 4px;
}

section.two-cols .right p {
  font-size: 0.85em;
  color: var(--ia-text-light);
  text-align: center;
  margin: 0;
}

/* === Layout: centered-img === */
section.centered-img {
  display: flex;
  flex-direction: column;
  align-items: center;
  justify-content: center;
  padding: 30px;
}

section.centered-img h1 {
  align-self: flex-start;
  margin-bottom: 20px;
}

section.centered-img img {
  max-width: 92%;
  max-height: 65vh;
  object-fit: contain;
  border-radius: 6px;
  box-shadow: 0 4px 12px rgba(0,0,0,0.1);
}

section.centered-img p {
  font-size: 0.9em;
  color: var(--ia-text-light);
  margin-top: 16px;
  text-align: center;
}

/* === Layout: wide-table === */
section.wide-table {
  padding: 40px 20px;
}

section.wide-table h1 {
  margin-bottom: 24px;
}

section.wide-table table {
  width: 96%;
  margin: 0 auto;
  border-collapse: collapse;
  font-size: 0.85em;
  background: white;
  border-radius: 6px;
  overflow: hidden;
  box-shadow: 0 2px 8px rgba(0,0,0,0.08);
}

section.wide-table th {
  background: var(--ia-primary);
  color: white;
  font-weight: 500;
  padding: 12px 10px;
  text-align: center;
}

section.wide-table td {
  padding: 10px;
  border-bottom: 1px solid #e0e0e0;
  text-align: center;
}

section.wide-table tr:last-child td {
  border-bottom: none;
}

section.wide-table tr:nth-child(even) {
  background: #f8f9fa;
}

/* === Lists === */
ul, ol {
  margin: 0.5em 0;
  padding-left: 1.5em;
}

li {
  margin: 0.4em 0;
  line-height: 1.5;
}

/* === Code blocks === */
pre {
  background: var(--ia-code-bg);
  border-left: 4px solid var(--ia-accent);
  padding: 16px;
  border-radius: 4px;
  overflow-x: auto;
  font-size: 0.85em;
  line-height: 1.5;
}

code {
  font-family: 'Roboto Mono', monospace;
  background: var(--ia-code-bg);
  padding: 2px 6px;
  border-radius: 3px;
  font-size: 0.9em;
}

pre code {
  background: none;
  padding: 0;
  border: none;
}

/* === Math inline === */
.math {
  font-family: 'Roboto Mono', monospace;
  font-style: italic;
}

/* === Title slide === */
section.title-slide {
  text-align: center;
  display: flex;
  flex-direction: column;
  justify-content: center;
  align-items: center;
  padding: 60px;
}

section.title-slide h1 {
  font-size: 64px;
  margin-bottom: 0.6em;
}

section.title-slide h2 {
  font-size: 32px;
  color: var(--ia-text-light);
  margin-bottom: 1em;
}

section.title-slide .meta {
  font-size: 20px;
  color: var(--ia-text-light);
  margin-top: 2em;
}

/* === Section divider slides === */
section.section-divider {
  text-align: center;
  background: linear-gradient(135deg, var(--ia-primary) 0%, var(--ia-secondary) 100%);
  color: white;
}

section.section-divider h1 {
  color: white;
  font-size: 52px;
}

section.section-divider h2 {
  color: rgba(255,255,255,0.9);
  font-size: 28px;
}

/* === Question slides === */
section.question-slide {
  text-align: center;
  display: flex;
  flex-direction: column;
  justify-content: center;
  align-items: center;
  padding: 100px;
}

section.question-slide h1 {
  font-size: 72px;
  color: var(--ia-accent);
}

/* === Custom elements === */
.highlight {
  color: var(--ia-accent);
  font-weight: 500;
}

strong {
  color: var(--ia-primary);
  font-weight: 500;
}

.warning {
  color: #d32f2f;
  font-weight: 500;
}

.success {
  color: #388e3c;
  font-weight: 500;
}

/* === Print/PDF optimization === */
@page {
  size: 16:9;
}

@media print {
  section {
    page-break-after: always;
  }
}
```

---

## Modèles de Slides Marp

### Modèle 1: Slide de titre

```markdown
---
marp: true
theme: ia101
class: title-slide
<!-- _footer: IA 101 - Intelligence Artificielle -->
<!-- _paginate: false -->

# Résolution de problèmes

## Intelligence Artificielle - II

<br>

<div class="meta">

**Jean-Sylvain Boige**
jsboige@myia.org

</div>
```

### Modèle 2: Slide de section (Sommaire)

```markdown
---
marp: true
theme: ia101
class: section-divider
<!-- _footer: IA 101 -->
<!-- _paginate: true -->

# Sommaire

## Exploration non informée

<br>

- Agents de résolution de problèmes
- Résolution de problèmes par exploration
- Exploration non informée
- Heuristiques et exploration informée
- Exploration en situation d'adversité: les jeux
- Minimax et Alpha-Bêta
- Décisions imparfaites
- Problèmes à satisfaction de contraintes
```

### Modèle 3: Texte + Image (standard - 35 slides)

```markdown
---
marp: true
theme: ia101
class: two-cols
<!-- _footer: IA 101 - Résolution de problèmes -->
<!-- _paginate: true -->

# Arbre d'exploration

**Idée de base**:

- Exploration simulée (hors ligne) de l'espace des états
- Génération des successeurs des états déjà explorés
- Développement des états

**Ensemble des Nœuds feuilles** = Frontière d'exploration

**Choix des nœuds à développer** = Stratégie d'exploration

<div class="right">

![Arbre d'exploration](images/slide_16_img_000.png)

</div>
```

### Modèle 4: Texte + Image large

```markdown
---
marp: true
theme: ia101
class: two-cols wide-img
<!-- _footer: IA 101 - Résolution de problèmes -->
<!-- _paginate: true -->

# Agent fondé sur des buts

Du **Réactif** → **Délibératif**

- Exploration du Futur
- Séquences d'actions
- Recherche, planification

<div class="right">

![Agent délibératif](images/slide_04_img_000.png)

</div>
```

### Modèle 5: Image centrée (7 slides)

```markdown
---
marp: true
theme: ia101
class: centered-img
<!-- _footer: IA 101 - Résolution de problèmes -->
<!-- _paginate: true -->

# Minimax

<br>

![Algorithme Minimax](images/slide_60_img_000.png)

<br>

*Faire "remonter" les valeurs Minimax dans l'arbre de jeu*
```

### Modèle 6: Tableau large (1 slide)

```markdown
---
marp: true
theme: ia101
class: wide-table
<!-- _footer: IA 101 - Résolution de problèmes -->
<!-- _paginate: true -->

# Résumé Exploration non informée

Nécessité d'une abstraction du monde réel
Variété des stratégies non informées

| Critère | BFS | UCS | DFS | DLS | IDS | Bidirectionnelle |
|---------|-----|-----|-----|-----|-----|------------------|
| **Complet** | Oui | Oui* | Non | Si l≥d | Oui | Oui* |
| **Optimal** | Oui | Oui* | Non | Non | Oui | Oui* |
| **Temps** | O(b^d) | O(b^(1+⌈C*/ε⌉)) | O(b^m) | O(b^l) | O(b^d) | O(b^(d/2)) |
| **Espace** | O(b^d) | O(b^(1+⌈C*/ε⌉)) | O(bm) | O(bl) | O(bd) | O(b^(d/2)) |

<small>*si coût d'étape ≥ ε</small>
```

### Modèle 7: Texte + 2 images empilées (5 slides)

```markdown
---
marp: true
theme: ia101
class: two-cols
<!-- _footer: IA 101 - Résolution de problèmes -->
<!-- _paginate: true -->

# Infrastructure: Etats vs Nœuds

**Etats ≠ Nœuds**

Un **Etat** est une représentation de la configuration réelle

Un **Nœud** est une structure de données constitutive d'une exploration:
- Inclut l'état, le nœud parent
- L'action, le coût d'étape g(x), la profondeur

La fonction de développement crée de nouveaux nœuds et utilise la fonction successeur pour déterminer les états enfants.

<div class="right">

![Etat](images/slide_19_img_000.png)
![Nœud](images/slide_19_img_001.png)

</div>
```

### Modèle 8: Texte + 3 images empilées (2 slides)

```markdown
---
marp: true
theme: ia101
class: two-cols
<!-- _footer: IA 101 - Résolution de problèmes -->
<!-- _paginate: true -->

# Classes de Jeux complexes

<div class="right">

![Jeux stochastiques](images/slide_66_img_000.png)

![Jeux partiellement observables](images/slide_66_img_001.png)

![Jeux modernes](images/slide_66_img_002.png)

</div>
```

### Modèle 9: Slide de questions

```markdown
---
marp: true
theme: ia101
class: question-slide
<!-- _footer: IA 101 -->
<!-- _paginate: false -->

# Questions?

<br>

![Questions icon](images/question_icon.png)

<br>

**IA 101 - Résolution de problèmes**
```

### Modèle 10: Slide TP

```markdown
---
marp: true
theme: ia101
class: title-slide
<!-- _footer: IA 101 -->
<!-- _paginate: true -->

# TP

## Exploration non informée et informée

<br>

**Services Web PKP**: Search
**Librairie JavaScript**: PathFinding.js
**Framework**: Aima JavaScript

<br>

<div class="meta">

IA 101 - Intelligence Artificielle

</div>
```

### Modèle 11: Slide Two Content (CSS grid)

```markdown
---
marp: true
theme: ia101
<!-- _footer: IA 101 - CSPs -->
<!-- _paginate: true -->

# Ordre des variables et des valeurs

<div style="display: grid; grid-template-columns: 1fr 1fr; gap: 30px;">

<div>

## Objectif

Détecter les incohérences au plus tôt et éviter les culs-de-sac

## Heuristiques de choix de variables

**MRV** (Minimum Remaining Values):
Variable avec le moins de valeurs légales restantes

**Heuristique des degrés**:
Si égalité MRV → Variable la plus contraignante pour les autres

## Ordonnancement des domaines

**LCV** (Least Constraining Value):
Celle qui exclut le moins de choix par la suite

**Weighted Degree**:
Priorise les variables impliquées dans de nombreux conflits

</div>

<div style="display: flex; flex-direction: column; gap: 15px; align-items: center;">

![MRV](images/slide_82_img_000.png)
![Degré](images/slide_82_img_001.png)
![LCV](images/slide_82_img_002.png)

</div>

</div>
```

---

## Configuration Marp

### marp.config.js

```javascript
module.exports = {
  engine: 'marp3',
  theme: 'ia101',
  themeSet: ['./theme/ia101.css'],
  output: 'output/resolution-problemes.html',
  pdf: {
    outcome: 'output/resolution-problemes.pdf'
  },
  html: {
    allowLocalFiles: true
  },
  options: {
  },
  slides: {
    class: 'default'
  }
};
```

### package.json

```json
{
  "name": "ia101-resolution-problemes",
  "version": "1.0.0",
  "description": "Slides IA 101 - Résolution de problèmes",
  "scripts": {
    "build": "marp marp/slides.md -o output/resolution-problemes.html",
    "pdf": "marp marp/slides.md --pdf -o output/resolution-problemes.pdf",
    "pdfs": "marp marp/slides.md --pdf --pdf-notes --pdf-overrides='--no-sandbox' -o output/resolution-problemes.pdf",
    "serve": "marp -s marp/slides.md",
    "check": "marp --allow-local-files marp/slides.md"
  },
  "devDependencies": {
    "@marp-team/marp-cli": "^3.0.0"
  }
}
```

---

## Script de Migration

### migrate_to_marp.py

```python
#!/usr/bin/env python3
"""
Script de migration PPTX vers Marp pour le deck 02-resolution-problemes
"""

import json
import re
from pathlib import Path
from typing import Dict, List

# Configuration
DECK_PATH = Path("D:/dev/CoursIA/slides/02-resolution-problemes")
EXTRACTED_PATH = DECK_PATH / "extracted"
MARPATH_PATH = DECK_PATH / "marp"
ANALYSIS_PATH = DECK_PATH / "analysis"

# Charger l'inventory
with open(EXTRACTED_PATH / "inventory.json", "r", encoding="utf-8") as f:
    inventory = json.load(f)

# Slides très denses à fractionner
DENSE_SLIDES = {
    9: 2, 25: 2, 38: 2, 42: 3, 63: 3,
    76: 2, 78: 2, 82: 1, 84: 2, 85: 2
}

# Mapping layout PPTX -> class Marp
LAYOUT_MAPPING = {
    "Title Slide": "title-slide",
    "Title and Content": "two-cols",  # par défaut, ajusté manuellement
    "Two Content": "two-cols-grid"
}


def get_slide_class(slide: Dict) -> str:
    """Détermine la classe CSS pour une slide"""
    layout = slide.get("layout_name", "")
    image_count = slide.get("image_count", 0)

    # Slides spéciales
    if slide["number"] in [14, 31, 56, 68, 89]:
        return "question-slide"
    if "Sommaire" in slide["title"]:
        return "section-divider"
    if slide["number"] in [32, 50, 90]:
        return "title-slide"

    # Slides avec image centrée
    centered_slides = [17, 29, 59, 60, 62, 81]
    if slide["number"] in centered_slides:
        return "centered-img"

    # Slides avec tableau large
    if slide["number"] == 29:
        return "wide-table"

    # Layout par défaut
    if image_count == 0:
        return "default"
    else:
        return "two-cols"


def generate_marp_header(slide_num: int, slide: Dict) -> str:
    """Génère le header YAML d'une slide Marp"""
    slide_class = get_slide_class(slide)
    footer = "IA 101"
    if "Résolution de problèmes" in slide.get("title", ""):
        footer += " - Résolution de problèmes"

    header = f"""---
marp: true
theme: ia101
class: {slide_class}
<!-- _footer: {footer} -->
<!-- _paginate: {"true" if slide_num > 1 else "false"} -->
"""
    return header


def convert_content_to_marp(content: str) -> str:
    """Convertit le contenu PPTX en markdown Marp"""
    # Conversion des listes
    lines = content.split("\n")
    result = []
    in_list = False

    for line in lines:
        line = line.strip()
        if not line or line in ["IA 101", "CS 405", "Intelligence(s)"]:
            continue

        # Puces
        if line.startswith("- ") or line.startswith("• "):
            if not in_list:
                result.append("\n")
                in_list = True
            result.append(line + "\n")
        else:
            in_list = False
            result.append(f"{line}\n")

    return "".join(result)


def main():
    """Fonction principale"""
    # Créer le dossier marp si nécessaire
    MARPATH_PATH.mkdir(exist_ok=True)
    (MARPATH_PATH / "theme").mkdir(exist_ok=True)

    # Générer le fichier slides.md
    slides_md = []

    for slide in inventory["slides"]:
        slide_num = slide["number"]
        title = slide["title"]
        content = slide.get("text_content", "")
        image_count = slide["image_count"]

        # Vérifier si la slide doit être fractionnée
        if slide_num in DENSE_SLIDES:
            # TODO: Implémenter le fractionnement
            pass

        # Générer le header
        slides_md.append(generate_marp_header(slide_num, slide))
        slides_md.append(f"\n# {title}\n\n")

        # Convertir le contenu
        marp_content = convert_content_to_marp(content)
        slides_md.append(marp_content)

        # Ajouter les images si présentes
        if image_count > 0:
            if image_count == 1:
                slides_md.append(f"<div class=\"right\">\n\n")
                slides_md.append(f"![{title}](images/slide_{slide_num:02d}_img_000.png)\n\n")
                slides_md.append(f"</div>\n")
            else:
                slides_md.append(f"<div class=\"right\">\n\n")
                for i in range(image_count):
                    slides_md.append(f"![Image {i+1}](images/slide_{slide_num:02d}_img_{i:03d}.png)\n\n")
                slides_md.append(f"</div>\n")

        slides_md.append("\n---\n")

    # Écrire le fichier
    with open(MARPATH_PATH / "slides.md", "w", encoding="utf-8") as f:
        f.writelines(slides_md)

    print(f"✓ Fichier Marp généré: {MARPATH_PATH / 'slides.md'}")
    print(f"✓ {len(inventory['slides'])} slides traitées")


if __name__ == "__main__":
    main()
```

---

## Commandes Utiles

### Installation

```bash
npm install -g @marp-team/marp-cli
```

### Conversion

```bash
# Générer HTML
marp marp/slides.md -o output/resolution-problemes.html

# Générer PDF
marp marp/slides.md --pdf -o output/resolution-problemes.pdf

# Serveur de développement
marp -s marp/slides.md

# Vérifier la syntaxe
marp --allow-local-files marp/slides.md
```

### Script Python

```bash
python scripts/migrate_to_marp.py
```

---

## Checklist de Conversion

- [ ] Créer le dossier `marp/` et `marp/theme/`
- [ ] Copier le fichier `ia101.css` dans `marp/theme/`
- [ ] Créer un symlink vers les images: `marp/images -> ../extracted/images/`
- [ ] Exécuter le script de migration Python
- [ ] Vérifier les 10 slides très denses (fractionnement manuel)
- [ ] Ajuster les layouts des 7 slides à image centrée
- [ ] Vérifier les 7 slides avec images multiples empilées
- [ ] Tester le rendu avec `marp -s`
- [ ] Générer le PDF final
- [ ] Comparer page par page avec les rendus PPTX

---

## Notes Importantes

1. **Les chemins d'images**: Utiliser des chemins relatifs depuis `marp/slides.md`
2. **Les slides très denses**: Nécessitent un fractionnement manuel
3. **Les layouts Two Content**: Utiliser grid CSS au lieu de `two-cols`
4. **Les tableaux**: Vérifier le rendu des tableaux larges (slide 29)
5. **La pagination**: Commencer à la slide 2, pas la slide 1
6. **Les pieds de page**: Adapter selon la section du cours

---

## Ressources

- [Documentation Marp](https://marp.moe/)
- [Marp CLI GitHub](https://github.com/marp-team/marp-cli)
- [Marp Themes](https://github.com/marp-team/marp-core/tree/main/themes)
- [Marp Markdown](https://marp.moe/usage/markdown)
