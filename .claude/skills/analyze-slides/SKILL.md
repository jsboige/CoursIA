---
name: analyze-slides
description: Analyze a Slidev deck qualitatively — organ reports (structure, composition) + vision AI on rendered PNGs. Arguments: <deck_id> [--slides 1,5,10]
---

# Analyze Slides (Slidev)

Analyse qualitative d'un deck Slidev : organes du depot d'abord (mesures
objectives), vision AI ensuite sur les rendus PNG (modele vision du MCP
sk-agent). Le mode Marp seul est retire depuis #19578 : 0 fichier `.pptx`
binaire et 0 rendu `marp_renders` dans l'arbre, MAIS la baseline PPTX est
vivante -- 742 renders PNG sous `slides/<deck>/pptx-reference/slide-NN.png`
(12 decks ; `public/pptx-reference/` pour `01-introduction`), d'ou les modes
`pptx` et `compare` de l'agent. Les 12 sources Marp legacy (slides.marp.md)
restent presentes, non servies par les agents.

**Target**: `$ARGUMENTS`

## Arguments

- `deck_id`: Identifiant du deck (ex: `S3-acculturation` pour `slides/S3-acculturation`)
- `--slides`: Liste de slides specifiques (ex: `--slides 1,5,10,15-20`)

## Prerequis

1. **MCP sk-agent** configure (appel `call_agent(prompt, attachment)` -- l'outil
   `analyze_image` n'existe plus, mesure 2026-09-29)
2. Environnement Slidev installe : `cd slides && npm install`
3. Le deck doit pouvoir etre servi : `cd slides/{deck_id} && npx slidev slides.md --port 3031`

## Process

### 1. Organes (objectif, AVANT toute vision)

```bash
python scripts/extract_slidev_titles.py slides/{deck_id}/slides.md
python scripts/check_slidev_structure.py slides/{deck_id}/slides.md
python scripts/notebook_tools/scan_slides_html_block_markdown.py --check slides/{deck_id}/slides.md

# Serveur dev tourne (Terminal 1) :
python scripts/notebook_tools/scan_slidev_composition.py \
  --url http://localhost:3031/ --slides-md slides/{deck_id}/slides.md \
  --out {scratchpad}/composition.json
python scripts/notebook_tools/scan_slidev_gap_report.py --in {scratchpad}/composition.json
```

### 2. Rendus PNG

```bash
python slides/_tools/render_deck.py {deck_id} --base http://localhost:3031
# -> slides/_tools/slide-renders/{deck_id}/slide-NNN.png
```

### 3. Analyse vision (prompt canonique FR, concis)

```
TITRE DE LA SLIDE:
{titre extrait}

---
Analyse UNIQUEMENT la mise en forme et les visuels.
1. VISUELS: Diagrammes, images, icones - lesquels, qualite ?
2. MISE EN FORME: disposition, equilibre texte/visuel
3. LISIBILITE: note /10 pour projection amphitheatre
4. 2 SUGGESTIONS concretes
```

```python
result = mcp__sk-agent__call_agent(
    prompt=prompt_avec_titre,
    attachment=f"slides/_tools/slide-renders/{deck_id}/slide-{num:03d}.png"
)
```

### 4. Parallelisation

Appels par lots de 5 slides en parallele.

### 5. Retry sur erreurs

Si reponse vide ou hallucinee : retry 1 fois avec :
`Decris les visuels de cette slide et note la lisibilite /10.`

### 6. Compilation du rapport (INCREMENTAL OBLIGATOIRE)

Apres CHAQUE lot de 5 slides, Edit pour ajouter les sections -- ne JAMAIS
accumuler plus de 5 slides en memoire avant d'ecrire.

Fichier de sortie : `slides/{deck_id}/analysis/visual_review.md`

### Format du rapport

```markdown
# Revue Visuelle - {deck_id}

**Date**: {date}
**Deck**: slides/{deck_id}/slides.md
**Slides analysees**: {N}/{total}

## Constats d'organes
- STRUCTURE / HTML-BLOCK / COMPOSITION : {constats}

## Slide 01 - {titre}
### Visuels et mise en forme
{reponse MCP}

## Resume
### Tableau recapitulatif
| Slide | Titre | Note | Probleme principal |
### Slides prioritaires (note < 6)
### Bonnes slides (note >= 8)
### Problemes recurrents
```

## Criteres de qualite (amphitheatre)

- **Test des 3 secondes** : message principal compris immediatement
- **Regle 1-6-6** : 1 idee, max 6 points, max 6 mots/point
- **Lisibilite** : police >= 24pt, contraste suffisant
- **Equilibre** : texte et visuels equilibres (regles
  [slides-layout-pattern.md](../../../docs/reference/slides-layout-pattern.md))

## Gestion des erreurs

- Si le MCP echoue 2 fois sur une slide : noter "[ERREUR]" et continuer
- Sauvegarder le rapport partiel apres chaque lot de 5 slides
- Une instance sans capacite vision rend le grain, elle ne valide pas text-only
