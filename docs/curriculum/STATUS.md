# docs/curriculum/ — STATUS agrégé

> **Périmètre** : `docs/curriculum/` — 10 fichiers markdown de cartographie curriculaire. **Date** : 2026-07-20. **Cycle** : c.694 (po-2025).
> **Epic parente** : #7422 (hygiène docs/ + index.md racine), #5081 (renumérotation narrative).
> **Périmètre cross-famille** : agrège l'état de fraîcheur des curricula GenAI / IA Classique / IA Symbolique / Recherche / Trading + 4 analyses phase-1 docs-only (#5081).

## Inventaire par catégorie

### Cartes curricula (6)

| Fichier | Scope | Last reviewed |
|---------|-------|---------------|
| [genai.md](genai.md) | GenAI Multimodale (Image/Audio/Video/Texte) | non daté |
| [ia-classique.md](ia-classique.md) | IA Classique (Recherche, CSP, résolution) | non daté |
| [ia-symbolique.md](ia-symbolique.md) | IA Symbolique (Preuves formelles, logique, planification) | non daté |
| [recherche.md](recherche.md) | Recherche Avancée (Inférence probabiliste, IIT, RL) | non daté |
| [trading.md](trading.md) | Trading Algorithmique (QC, ML appliqué, probabilités) | non daté |
| [stage5_mamba_ssm.md](stage5_mamba_ssm.md) | Stage 5 — Mamba / State Space Models (Financial Time Series) | **2026-07-19** (récent) |

### Analyses phase-1 docs-only EPIC #5081 (4)

| Fichier | Série auditée | Verdict |
|---------|---------------|---------|
| [infer-renumbering-phase1.md](infer-renumbering-phase1.md) | Probas/Infer | no-defect-found (cf c.432 et #6879) |
| [search-renumbering-phase1.md](search-renumbering-phase1.md) | Search | no-defect-found |
| [pymc-renumbering-phase1.md](pymc-renumbering-phase1.md) | Probas/PyMC | no-defect-found (cf #6885) |
| [planners-renumbering-phase1.md](planners-renumbering-phase1.md) | SymbolicAI/Planners | no-defect-found |

## Diagnostic c.694 (po-2025 worker)

| Constat | État | Action |
|---------|------|--------|
| Cartes curricula (6) | **Sans date de revue** — fraîcheur non traçable hors Mamba SSM | À compléter (5 fichiers à dater) |
| Analyses phase-1 #5081 (4) | Toutes verdict `no-defect-found` = drainé pour ces 4 séries | Aucune action restante sur ces 4 |
| Cohérence cross-famille | Pas de référence morte détectée entre curricula et CATALOG-STATUS | RAS |

## Liens opérationnels

- **#7422** Hygiène docs/ + index.md racine — Epic parente de ce STATUS agrégé
- **#5081** Renumérotation narrative des séries — Epic parente des 4 analyses phase-1
- **#1650** EPIC Traduction multilingue — Phases 0.5 docs primaire FR (cf [readme-french-first.md](../../.claude/rules/readme-french-first.md))
- **#3973** README ascendant — résynchronisation hiérarchie feuilles → principal

## Hors scope (volontairement)

- **Pas de regen catalogue** : R1 catalog-pr-hygiene respectée, ce STATUS n'est PAS un marqueur CATALOG-STATUS.
- **Pas de modification des 10 fichiers existants** : seul ce STATUS est ajouté (1 fichier, agrégat read-only).
- **Pas de relecture exhaustive** : diagnostic = lecture top (header + 5 lignes de contexte par fichier), pas de scan de fond.
- **Pas de datation des 5 curricula non-Mamba** : demanderait un audit fond par agent owner-curriculum — non-trivial.

## Méthodologie G.1 (verify-before-claiming)

- `ls docs/curriculum/` = **10 fichiers** (.md), confirmé.
- Lecture du **header + premiers marqueurs** de chaque fichier (≤ 5 lignes par fichier), pas de scan complet.
- Verdicts `no-defect-found` cités **depuis les analyses elles-mêmes** (cf body `#6885` / `#6879` / c.432), pas depuis un cache mémoriel.
- Date du jour = **2026-07-20** (cf `currentDate` global).
