# Procédure de refonte des slides Slidev (images + fidélité PPTX)

**Source** : demande de fond du user depuis la transition PPTX→Slidev (janvier 2026), procédure validée le 2026-05-20 sur `slides/03-logique` slide 79 ("Calcul situationnel"). EPIC #1240, issues #1349/#1238/#1241/#1242.

**Principe** : caler **chaque** slide-image individuellement **avec feedback visuel réel**, jamais "au jugé". Une slide = plusieurs cycles d'itération. La qualité prime sur la vitesse.

## Règle de positionnement des images (HARD — refusée 3× par le user si violée)

- Images en **`position:absolute`** avec des valeurs **absolues réglées au cas par cas** (`top`/`right`/`bottom`/`left` + `width`/`height` explicite). Pas de template unique.
- Texte en **pleine largeur**, avec des **retours à la ligne ciblés** (`<br>`) uniquement sur les lignes qui chevaucheraient l'image.
- **INTERDIT** : `<div style="max-width:NN%">` autour du texte, `layout: two-cols`, colonne dédiée à l'image. (Règle issue #221, refusée 3×.)

## Boucle de travail par slide

1. **Servir le deck** (hot-reload) :
   ```bash
   cd slides && ./node_modules/.bin/slidev 03-logique/slides.md --port 3039 --no-open
   ```
2. **Screenshot précis** (playwright MCP) :
   - `browser_resize(1280, 720)`
   - `browser_navigate("http://localhost:3039/<N>?print")`  (N = numéro de slide)
   - `browser_take_screenshot(filename: "checkN.png")` → puis `Read` le PNG (analyse vision)
   - Fallback sans MCP : `./node_modules/.bin/slidev export 03-logique/slides.md --format png --output <dir>` (rend tout le deck en `<dir>/N.png`).
3. **Comparer au PPTX original** : `slides/03-logique/pptx-reference/slide-NN.png` (le mapping Slidev↔PPTX est dans `slides/03-logique/analysis/mapping-*.md`). La numérotation PPTX ≠ Slidev → croiser par **titre/contenu**. Objectif : **ne rien perdre** au passage.
4. **Au SPLIT d'une slide PPTX dense en plusieurs slides Slidev** : répartir les **images** vers la slide **pédagogiquement pertinente**, pas toutes sur la première.
   - Exemple validé : `img_033` (diagramme `Result(Result(S0,Forward),Turn(Right))`) déplacée de "Calcul situationnel" vers "Axiomes du calcul situationnel" (où le concept `Result(p,s)` est traité).
   - **Vérifier la/les slide(s) adjacente(s) AVANT de conclure à une perte de contenu** (le contenu manquant est souvent sur la slide suivante du split).
5. **Mesurer / nettoyer l'image** (Pillow) :
   ```python
   from PIL import Image, ImageChops
   im = Image.open(p).convert("RGB")
   bbox = ImageChops.difference(im, Image.new("RGB", im.size, (255,255,255))).getbbox()
   ```
   - Connaître taille + aspect ratio avant de dimensionner.
   - Autocrop des **bords blancs** uniquement. Le blanc **structurel** (diagramme diagonal laissant un coin vide) n'est pas rognable → le gérer par le positionnement.
6. **Dimensionner pour la lisibilité** : l'image doit être assez grande pour que **les labels soient lisibles** (le vérifier en lisant le screenshot, ne pas supposer). Un diagramme détaillé à ~200px = trop petit = rejeté.
7. **Positionner** :
   - **Centrer verticalement sur le bloc texte** : haut de l'image ≈ haut du texte, bas ≈ bas du texte. **L'image ne doit jamais descendre plus bas que le texte.**
   - Centrer horizontalement dans l'espace libre à droite (ni collée au bord, ni "flottante" au milieu).
8. **Itérer** : screenshot → diagnostic précis → ajuste les px → re-screenshot, jusqu'à un rendu propre (0 chevauchement, 0 overflow, labels lisibles, équilibré).
9. **Validation user** sur l'exemplaire, puis scaler le pattern aux autres slides (en gardant la boucle visuelle sur chacune).

## Réglage de référence (slide 79, validé)

```html
<img src="./images/img_024.png"
     style="position:absolute; top:85px; right:108px; width:345px;"
     alt="Sequence d'etats du Wumpus S0 a S3 (Forward, Turn Right)" />
```
+ texte pleine largeur, 2 formules longues coupées par `<br>` ciblés, aucune `<div max-width>`.

## EXIT criteria (par slide modifiée)

- Vérifiée visuellement (Slidev `?clicks=99` ou screenshot), pas un échantillon.
- 0 chevauchement texte/image, 0 overflow, labels lisibles.
- Contenu complet vs PPTX (rien perdu au split).
- Aucune `max-width:NN%` / `two-cols` résiduelle.

## Anti-patterns (causes de rejet observées)

- Positionner les px sans regarder le rendu ("au jugé").
- Images trop petites (labels illisibles).
- Image plus basse que le texte / mal centrée verticalement.
- Texte en colonne `max-width%` ou image en colonne dédiée.
- Conclure "contenu perdu" sans vérifier la slide adjacente du split.
- Toutes les images du split entassées sur la 1re slide.
