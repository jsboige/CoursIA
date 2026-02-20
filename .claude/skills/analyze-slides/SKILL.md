---
name: analyze-slides
description: Analyze PowerPoint slides qualitatively using vision AI. Arguments: <deck_path> [--render] [--slides 1,5,10]
---

# Analyze Slides

Analyse qualitative de slides PowerPoint via le modele vision Qwen3-VL-8B du MCP sk-agent.

**Target**: `$ARGUMENTS`

## Arguments

- `deck_path`: Chemin du dossier deck (ex: `slides/01-introduction`)
- `--render`: Forcer le rendu PNG meme si les fichiers existent
- `--slides`: Liste de slides specifiques (ex: `--slides 1,5,10,15-20`)

## Prerequis

1. **MCP sk-agent** doit etre configure avec le modele `qwen3-vl-8b-thinking`
2. Les PNG doivent exister dans `{deck_path}/extracted/renders/`
3. Le texte extrait doit exister dans `{deck_path}/extracted/content.md`

## Process

### 1. Pre-charger le texte extrait

Lire le fichier `{deck_path}/extracted/content.md` et parser les slides par delimiteur `<!-- Slide number: N -->`.

Stockage dans un dict: `{slide_num: text_content}`

### 2. Verification des renders

```bash
ls {deck_path}/extracted/renders/slide_*.png | wc -l
```

### 3. Analyse via MCP sk-agent (PROMPT REVU)

Pour chaque slide, construire un prompt qui inclut le texte extrait pour que le modele se concentre sur la mise en forme:

**Prompt unique (concis):**
```
TEXTE EXTRAIT DE LA SLIDE:
{texte du slide depuis content.md}

---

Analyse UNIQUEMENT la mise en forme et les visuels (le texte est deja extrait ci-dessus).

1. VISUELS: Diagrammes, images, icones presents ? Lesquels ? Qualite ?
2. MISE EN FORME: Disposition, equilibre texte/visuel, hierarchie
3. LISIBILITE: Note /10 pour projection amphitheatre
4. 2 SUGGESTIONS concretes d'amelioration
```

### 4. Appel MCP

```python
result = mcp__sk-agent__analyze_image(
    image_source=f"{deck_path}/extracted/renders/slide_{num:02d}.png",
    model="qwen3-vl-8b-thinking",
    prompt=prompt_avec_texte
)
```

### 5. Parallelisation

Faire des appels par lots de 5 slides en parallele pour accelerer le traitement.

### 6. Retry sur erreurs

Si reponse vide ou erreur: retry 1 fois avec prompt simplifie:
```
Decris les elements visuels de cette slide et donne une note de lisibilite /10.
```

### 7. Compilation du rapport (INCREMENTAL OBLIGATOIRE)

**IMPORTANT**: Le rapport DOIT etre ecrit de facon incrementale. Apres CHAQUE lot de slides analyse, utiliser Edit pour ajouter les resultats.

**Workflow incrementale**:
1. Creer le fichier avec l'en-tete au debut
2. Apres chaque lot de 5 slides, faire un Edit pour ajouter les sections
3. Ne JAMAIS accumuler plus de 5 slides en memoire avant d'ecrire

Fichier de sortie: `{deck_path}/analysis/visual_review.md`

### Format du rapport

```markdown
# Revue Visuelle - {deck_name}

**Date**: {date}
**Deck**: {deck_path}
**Slides analysees**: {N}/{total}

---

## Slide 01 - {titre extrait du texte}

### Visuels et mise en forme
{reponse MCP}

---

## Slide 02 - {titre}
...

---

## Resume

### Tableau recapitulatif
| Slide | Titre | Note | Probleme principal |
|-------|-------|------|-------------------|
| 01 | ... | X/10 | ... |

### Slides prioritaires (note < 6)
- Slide X: [raison]

### Bonnes slides (note >= 8)
- Slide Y: [raison]

### Problemes recurrents
1. [Probleme] - N slides concernees
2. [Probleme] - N slides concernees
```

## Criteres de qualite (conseils-slides.md)

- **Test des 3 secondes** : message principal compris immediatement
- **Regle 1-6-6** : 1 idee, max 6 points, max 6 mots/point
- **Lisibilite** : police >= 24pt, contraste suffisant
- **Equilibre** : texte et visuels equilibres

## Gestion des erreurs

- Si le MCP echoue 2 fois sur une slide: noter "[ERREUR]" et continuer
- Sauvegarder le rapport partiel apres chaque lot de 5 slides
