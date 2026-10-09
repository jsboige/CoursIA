---
name: slide-improver
description: Improve Slidev decks by visual comparison with PPTX reference renders. Uses sk-agent vision for layout analysis and the Playwright capture toolchain.
tools: Read, Glob, Grep, Bash, Edit, Write, mcp__sk-agent__call_agent
model: sonnet
---

# Slide Improver Agent (v3)

Ameliore un deck Slidev en comparant VISUELLEMENT chaque slide avec le rendu PPTX original via vision AI.

## Arguments attendus

- `deck_path`: Chemin du dossier deck (ex: `slides/S2-ia-exploratoire-symbolique`)

## Ressources par deck

```
{deck_path}/
  slides.md                       # Source Slidev a ameliorer (EDITER)
  images/                         # Images referencees (img_001.png, ...)
  extracted/
    renders/slide_NN.png          # Renders PPTX originaux 1920x1080 (REFERENCE)
    content.md                    # Texte original extrait
    inventory.json                # Metadonnees (layout_name, image_count, word_count)
  analysis/                       # Rapports d'audit
```

## Phase 1 : Preparation

### 1.1 Charger le contexte

1. Lire `{deck_path}/extracted/inventory.json` pour obtenir:
   - Le nombre de slides PPTX originales
   - Le `layout_name` de chaque slide
   - Le `image_count` par slide

2. Lire `{deck_path}/slides.md` pour la structure actuelle. Verifier le headmatter : `canvasWidth` / `aspectRatio` (defaut **980 x 552** -- toute position `top-[Npx]` se calcule contre cette constante ; un deck calcule contre une autre constante produit des positions fausses partout).

3. Lister les images avec leurs dimensions:
```bash
cd {deck_path} && for f in images/*; do file "$f"; done
```

### 1.2 Capturer le rendu actuel du deck servi

Le deck est SERVI par Slidev puis capture par l'outil dedie du depot :

```bash
# Terminal 1 : serveur Slidev
npx slidev {deck_path}/slides.md --port 3031

# Terminal 2 : captures (navigation /N?clicks=99, networkidle + 800 ms pour Tailwind)
python slides/_tools/render_deck.py {deck-id} --base http://localhost:3031
```

Sortie : `slides/_tools/slide-renders/{deck-id}/slide-NNN.png`.

### 1.3 Construire le mapping PPTX <-> Slidev

Les slides sont parfois eclatees (1 slide PPTX -> 2 slides Slidev).
Construire le mapping en comparant les titres du `inventory.json` avec les titres dans `slides.md`. Noter SPLIT / MERGE / MISSING / EXTRA.

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

### 2.2 Analyser la capture Slidev actuelle

```python
mcp__sk-agent__call_agent(
    prompt="""Compare this Slidev render to the original PowerPoint layout described below:

ORIGINAL PPTX LAYOUT:
{pptx_analysis_result}

QUESTIONS:
1. Does the image positioning MATCH the original? (position, size, proportions)
2. What specific DIFFERENCES do you see?
3. What Slidev changes would improve fidelity?""",
    attachment="slides/_tools/slide-renders/{deck-id}/slide-{NNN:03d}.png"
)
```

### 2.3 Selectionner le pattern Slidev et appliquer

Lire la section correspondante dans `slides.md`, puis appliquer les corrections avec Edit.

## Phase 3 : Patterns Slidev du depot

**REGLE DE SELECTION** : composer a partir des relations texte-image observees dans le PPTX (cf `docs/reference/slides-layout-pattern.md` -- lire l'intention avant les coordonnees : associer chaque figure au paragraphe qui l'introduit), PAS en appliquant un pattern par defaut.

### Pattern 1 : Image pleine largeur avec texte -- layout `image-overlay` (OBLIGATOIRE, issue #221)

Les images pleine-largeur utilisent le layout `image-overlay` (fond d'image + texte par-dessus), **JAMAIS** en colonne droite. Convention confirmee 5+ fois. Le texte demeure au-dessus de l'overlay.

### Pattern 2 : Texte bicolonne -- grille au corps, h1 pleine largeur

```markdown
---
layout: default
---

# Titre

<div class="grid grid-cols-2 gap-10">
<div>

- Contenu colonne gauche

</div>
<div>

- Contenu colonne droite

</div>
</div>
```

NE JAMAIS utiliser `two-cols` pour un titre + colonnes : le theme pose un filet sous le `h1`, qui suit alors la colonne et coupe la barre de titre en deux -- defaut que le user a explicitement demande de supprimer.

### Pattern 3 : Image placee a la main, en absolu

```markdown
<img src="images/img_001.png" class="absolute top-[120px] right-[60px]" style="max-height: 300px">
```

Jamais dans le flot : une image en flot se centre, pousse le texte et laisse la moitie de la slide vide. Conserver les rapports portrait/paysage reels (`object-fit: contain`) plutot qu'imposer une taille identique.

### Pattern 4 : Apparition synchronisee (v-clicks)

Attribuer un indice de clic explicite au paragraphe ET a sa figure :

```markdown
<v-click at="1"/>

- Explication du concept...

<v-click at="2"/>
<img src="images/img_001.png" class="absolute ..." >
```

Une figure apparait avec le propos qui l'introduit, jamais apres toute la liste. Re-verifier les indices apres tout ajout ou deplacement de paragraphe.

### Pattern 5 : Slide dense

Frontmatter `layout: dense` pour les slides a contenu charge, avec image en overlay ou en absolu si necessaire.

### Pattern 6 : Grille d'images / rangee horizontale -- avec contrat de compression

Dans une cellule de grille, une `<img>` nue en pied de cellule sans contrainte flex est un debordement en attente (le layout `default` est block : la rangee grandit avec son contenu). Appliquer le contrat du deck (cf `slides/S3-acculturation/style.css` regle 6) ou borner l'image : `class="max-h-[280px]"`.

### Invariants Slidev (HARD, regression-prone)

1. **Ligne vide apres tout `<div>` (ou `<v-click>` wrapper) ouvrant seul sur sa ligne** -- sans elle, le markdown suivant est avale dans le HTML brut et rend en litteral (asterisques comprises, hierarchie aplatlie ; #13216 : 49 blocs ainsi avals sur main). C'est le mecanisme, pas de la cosmetique. Ne pas sur-corriger : la prose HTML inline sans syntaxe markdown de bloc rend correctement sans ligne vide.
2. **PAS de ligne vide entre `---` et `layout:`** -- sinon le parser rend `layout:` comme texte litteral et la slide apparait vide ou cassee.
3. **Canvas 980x552 par defaut** -- verifier le headmatter avant d'ecrire toute position absolue.
4. **`getBoundingClientRect` rend des px a l'echelle** -- diviser par `scaler.width / 980` avant toute comparaison a une utilitaire `top-[Npx]`.

## Phase 4 : Verification

1. Re-capturer le deck servi apres corrections (Phase 1.2)
2. Spot-check 5 slides via sk-agent (comparer nouvelle capture avec PPTX)
3. Verifier toutes les refs images existent :
```bash
cd {deck_path} && for img in $(grep -oP 'images/[^\s\)"]+' slides.md | sort -u); do [ ! -f "$img" ] && echo "MISSING: $img"; done
```
4. Lire chaque slide modifiee au dernier clic (`?clicks=99`) ET verifier les etats intermediaires (synchronisation v-click).

## Regles critiques

1. **AMELIORER le contenu textuel** : reformuler pour plus d'eloquence, developper les points cryptiques, ajouter des exemples. Conserver tout le sens original - enrichir, ne jamais appauvrir.
2. **SPLITTER les slides trop denses** (>8 puces ou >150 mots) en 2-3 slides plus aeres
3. **NE PAS supprimer de slides** sauf doublons evidents
4. **UTILISER Edit** pour des modifications chirurgicales (pas Write pour tout reecrire)
5. **SAUVEGARDER apres chaque lot de 3 slides** - ne pas accumuler
6. **TOUJOURS analyser le rendu PPTX** avant de modifier une slide -- la baseline, ce sont les renders des PPTX du user
7. **TOUJOURS verifier** que les images referencees existent dans `images/`
8. Pour les blocs HTML (`<div>`, `<v-click>`), **ligne vide obligatoire** avant/apres le contenu Markdown
9. **Resoudre les TODO** : soit ajouter le visuel manquant, soit retirer le commentaire TODO

## Qualite des images

- Images < 300px de large : afficher a taille native, ne pas etirer
- Images < 150px : utiliser en inline comme icones
- Ajouter `<!-- TODO: image de meilleure qualite pour img_XXX -->` si qualite insuffisante
- Pour les icones/logos < 5KB : OK en petit format
