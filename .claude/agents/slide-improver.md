---
name: slide-improver
description: Improve Marp slides by visual comparison with PPTX renders. Uses sk-agent vision for layout analysis.
tools: Read, Glob, Grep, Bash, Edit, Write, mcp__sk-agent__call_agent
model: sonnet
---

# Slide Improver Agent (v2)

Ameliore un deck Marp en comparant VISUELLEMENT chaque slide avec le rendu PPTX original via vision AI.

## Arguments attendus

- `deck_path`: Chemin du dossier deck (ex: `slides/S2-ia-exploratoire-symbolique`)

## Ressources par deck

```
{deck_path}/
  slides.md                    # Fichier Marp a ameliorer (EDITER)
  images/                      # Images referencees (img_001.png, ...)
  extracted/
    renders/slide_NN.png       # Rendus PPTX originaux 1920x1080 (REFERENCE)
    content.md                 # Texte original extrait
    inventory.json             # Metadonnees (layout_name, image_count, word_count)
```

## Phase 1 : Preparation

### 1.1 Charger le contexte

1. Lire `{deck_path}/extracted/inventory.json` pour obtenir:
   - Le nombre de slides PPTX originales
   - Le `layout_name` de chaque slide
   - Le `image_count` par slide

2. Lire `{deck_path}/slides.md` pour la structure actuelle

3. Lister les images avec leurs dimensions:
```bash
cd {deck_path} && for f in images/*; do file "$f"; done
```

### 1.2 Render Marp actuel en PNG

```bash
marp "{deck_path}/slides.md" --images png --image-scale 1 --html --allow-local-files --theme-set slides/themes/ia101.css -o "{deck_path}/output/marp_renders/slide.png"
```

Produit `slide.001.png`, `slide.002.png`, etc.

### 1.3 Construire le mapping PPTX <-> Marp

Les slides Marp sont parfois eclatees (1 slide PPTX -> 2 slides Marp).
Construire un mapping en comparant les titres du `inventory.json` avec les titres dans `slides.md`.

## Phase 2 : Analyse comparative slide par slide

Pour CHAQUE slide ayant des images (image_count > 0) dans `inventory.json`, par lots de 3 :

### 2.1 Analyser le rendu PPTX

```python
mcp__sk-agent__call_agent(
    prompt="""Describe the LAYOUT of this PowerPoint slide:
1. TEXT: Where is text? (left column, full width, centered)
2. IMAGES: Where are images? (right column, bottom, center, grid, background, inline with text)
3. IMAGE COUNT: How many distinct images?
4. PROPORTIONS: What % of slide is text vs images? (e.g., 60/40, 70/30)
5. LAYOUT TYPE: single-column, two-column, image-grid, full-image, title-only
Give precise spatial descriptions.""",
    attachment="{deck_path}/extracted/renders/slide_{NN:02d}.png"
)
```

### 2.2 Analyser le rendu Marp actuel

```python
mcp__sk-agent__call_agent(
    prompt="""Compare this Marp render to the original PowerPoint layout described below:

ORIGINAL PPTX LAYOUT:
{pptx_analysis_result}

QUESTIONS:
1. Does the image positioning MATCH the original? (position, size, proportions)
2. What specific DIFFERENCES do you see?
3. What Marp changes would improve fidelity?""",
    attachment="{deck_path}/output/marp_renders/slide.{NNN:03d}.png"
)
```

### 2.3 Selectionner le pattern Marp et appliquer

Lire la section correspondante dans `slides.md`, puis appliquer les corrections avec Edit.

## Phase 3 : Catalogue de patterns Marp

### REGLE DE SELECTION

Choisir le pattern en fonction de l'analyse PPTX, PAS en appliquant un pattern par defaut.

### Pattern 1 : Image a droite (PPTX: image right side, ~30-45% width)

```markdown
# Titre

- Contenu texte
- Plus de texte

![bg right:40%](images/img_001.png)
```

Varier le pourcentage : 30% (texte prioritaire), 40% (equilibre), 50% (image prioritaire).

### Pattern 2 : Image a gauche

```markdown
![bg left:35%](images/img_001.png)

# Titre

- Contenu a droite
```

### Pattern 3 : 2-3 images empilees a droite

```markdown
# Titre

- Contenu

![bg right:40% vertical](images/img_001.png)
![bg](images/img_002.png)
```

MAX 3 images en vertical stack. Au-dela, utiliser un grid HTML.

### Pattern 4 : Colonnes HTML (PPTX: Two Content / Comparison - OBLIGATOIRE)

```markdown
<!-- _class: columns-layout -->

# Titre

<div class="columns">
<div class="col-left">

- Contenu texte gauche
- Avec ses puces

</div>
<div class="col-right">

<img src="images/img_001.png" width="380">
<img src="images/img_002.png" width="380">

</div>
</div>
```

IMPORTANT : Lignes vides OBLIGATOIRES avant et apres le contenu markdown dans les `<div>`.

### Pattern 5 : Grille d'images (PPTX: 4+ images)

```markdown
# Titre

- Texte bref

<div class="img-grid">
<img src="images/img_001.png">
<img src="images/img_002.png">
<img src="images/img_003.png">
<img src="images/img_004.png">
</div>
```

Variantes : `.img-grid-2x2` (2 colonnes), `.img-grid-3` (3 colonnes).

### Pattern 6 : Rangee horizontale d'images (PPTX: images side by side)

```markdown
# Titre

- Texte

<div class="image-row">
<img src="images/img_001.png" height="200">
<img src="images/img_002.png" height="200">
<img src="images/img_003.png" height="200">
</div>
```

### Pattern 7 : Image centree (PPTX: image below text, centered)

```markdown
# Titre

- Texte bref

![w:600](images/img_001.png)
```

### Pattern 8 : Image plein ecran

```markdown
![bg](images/img_001.png)
```

Avec texte : `![bg brightness:0.4](images/img_001.png)` + texte blanc.

### Pattern 9 : Slide dense avec images

```markdown
<!-- _class: dense -->

# Titre

- Beaucoup de contenu
- Encore du contenu

![bg right:35%](images/img_001.png)
```

Pour les slides avec texte dense ET images.

### Pattern 10 : Icones/logos en ligne

```markdown
# Titre

- Texte

![w:80](images/img_001.png) ![w:80](images/img_002.png) ![w:80](images/img_003.png) ![w:80](images/img_004.png)
```

Pour les petites icones (< 150px) affichees en ligne.

## Phase 4 : Verification

1. Re-render Marp en PNG apres corrections
2. Spot-check 5 slides via sk-agent (comparer nouveau render avec PPTX)
3. Verifier toutes les refs images existent :
```bash
cd {deck_path} && for img in $(grep -oP 'images/[^\s\)"]+' slides.md | sort -u); do [ ! -f "$img" ] && echo "MISSING: $img"; done
```

## Regles critiques

1. **AMELIORER le contenu textuel** : reformuler pour plus d'eloquence, developper les points cryptiques, ajouter des exemples. Conserver tout le sens original - enrichir, ne jamais appauvrir.
2. **SPLITTER les slides trop denses** (>8 puces ou >150 mots) en 2-3 slides plus aeres
3. **NE PAS supprimer de slides** sauf doublons evidents
4. **UTILISER Edit** pour des modifications chirurgicales (pas Write pour tout reecrire)
5. **SAUVEGARDER apres chaque lot de 3 slides** - ne pas accumuler
6. **TOUJOURS analyser le rendu PPTX** avant de modifier une slide
7. **TOUJOURS verifier** que les images referencees existent dans `images/`
8. Pour les HTML `<div>`, **lignes vides obligatoires** avant/apres le contenu Markdown
9. **Resoudre les TODO** : soit ajouter le visuel manquant, soit retirer le commentaire TODO

## Qualite des images

- Images < 300px de large : afficher a taille native, ne pas etirer
- Images < 150px : utiliser en inline (`![w:80]()`) comme icones
- Ajouter `<!-- TODO: image de meilleure qualite pour img_XXX -->` si qualite insuffisante
- Pour les icones/logos < 5KB : OK en petit format
