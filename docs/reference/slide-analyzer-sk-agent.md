# Slide Analyzer — observabilité sk-agent (Marp vs PPTX + prompts)

> **Origine** : fichier `.claude/agent-memory/slide-analyzer/MEMORY.md` (relocalisé en c.1301+210 dans le cadre de l'EPIC #9535, item 7 — agent-memory relocalisation en doc pérenne). Le contenu est conservé tel quel (anti-régression : cf triage jsboigeEpita, durable vs scratch) ; seul un sommaire FR est ajouté.
>
> **Statut** : durable. Le contenu documente (a) le **comportement observé** de `sk-agent analyze_image` (routage `glm-4.6v`, indépendamment du paramètre `model`) ; (b) deux **prompts canoniques** (primaire FR + retry FR court) qui contournent les hallucinations sur slides logo-heavy ; (c) une **grille de comparaison** Marp vs PPTX (deck `01-introduction`) qui sert de baseline pour les audits futurs de slides. Ce sont des invariants d'environnement, pas du scratch daté.

## Sk-agent analyze_image : comportement observé

### Model Used
- sk-agent routes requests to `glm-4.6v` regardless of the `model` parameter value.
- Specifying `qwen3-vl-8b-thinking` does NOT change the underlying model.

### Hallucination Risk on slide.017
- On the "Qui fait de l'IA" logo-grid slide, the standard English prompt triggered a hallucination:
  the agent returned a fake web URL (`searxng-web_url_read`) instead of analyzing the image.
- Root cause likely: logo-heavy slides with many brand images confuse the model's tool-calling heuristics.
- Fix: use a shorter French prompt — this reliably forces direct image description.

### Prompt Effectiveness (tested 2026-02-21)

| Prompt style | Result | Notes |
|---|---|---|
| Long English (5 questions + rating 1-5) | Works for clean slides, fails on logo-heavy | slide.003 and slide.033 OK, slide.017 hallucinated |
| Short French "Decris les visuels... note /10" | Reliable fallback | Used for retry, succeeded on slide.017 |

### Recommended Primary Prompt (French, concise)
```
TEXTE EXTRAIT:
{texte}

---
Analyse UNIQUEMENT la mise en forme et les visuels.
1. VISUELS: Diagrammes, images, icones - lesquels, qualite ?
2. MISE EN FORME: disposition, equilibre texte/visuel
3. LISIBILITE: note /10 pour projection amphitheatre
4. 2 SUGGESTIONS concretes
```

### Recommended Retry Prompt (on empty/hallucinated response)
```
Decris les visuels de cette slide et note la lisibilite /10.
```

## PPTX vs Marp Rendering Quality (deck 01-introduction)

### General observations
- Marp strips French diacritics inconsistently: "réflexe" -> "reflexe", "académique" -> "academique"
- Marp renders logos as image blocks at bottom (not inline with text as in PPTX)
- Marp loses the PPTX two-column layout: text and diagrams stack vertically instead of side-by-side
- Marp footer "I - Introduction" is visible but truncated on slide.003

### Slide-specific issues
- slide.003 (Sommaire): Marp version cuts the bullet list (content truncated after "Apprentissage"),
  book image is large and fills the right half but text list is incomplete.
- slide.017 (Qui fait de l'IA): Marp version loses inline logos; logos move to a separate bottom row,
  Fujitsu logo partially cut off at bottom edge.
- slide.033 (Agent reflexe): Marp version is the best conversion - two-column layout preserved,
  diagram and pseudocode box visible; book image small but present. Minor: accents stripped.

## File Locations
- PPTX renders: `slides/01-introduction/extracted/renders/slide_NN.png`
- Marp renders: `slides/01-introduction/output/marp_renders/slide.NNN.png`
- Extracted text: `slides/01-introduction/extracted/content.md`
- Analysis output: `slides/01-introduction/analysis/visual_review.md`
