# README / docs : français d'abord, anglais préservé en `.en.md`

S'applique à **tous les agents** produisant ou éditant de la documentation markdown (README, `docs/**`, prose pédagogique de série/sous-série). Source : mandat user 2026-06-21 (« c'est dommage de continuer à créer du contenu anglais qui aura vocation à être traduit en français »). Consolide CLAUDE.md §E (doc primaire = français) + l'Epic traduction **#1650 Phase 0.5**.

## Règle HARD 1 — nouveau contenu doc = français, JAMAIS « match the surrounding language »

Toute section README/docs **ajoutée ou réécrite** (Conclusion #2651, intro, transition, interprétation, prose pédagogique) est rédigée **en français** — **même si le README environnant est actuellement en anglais**. Le piège récurrent est d'aligner la langue de l'ajout sur celle du fichier : c'est précisément ce qui regénère du contenu anglais voué à re-traduction (gaspillage tokens). Si le fichier est en anglais, voir règle 2 (on le bascule, on ne s'y conforme pas).

Exception : docstrings/commentaires de code = FR ou EN (cf §E). Cette règle vise la **prose de documentation**, pas les commentaires inline.

## Règle HARD 2 — bascule FR d'un doc anglais = préserver l'original en `README.en.md`

Quand on francise un README/doc actuellement en anglais (Epic #1650 Phase 0.5) :

1. `git mv README.md README.en.md` (préserve l'original anglais **tel quel** — futur golden set + livrable que le moteur scripté Phase 3 produirait).
2. Écrire un **nouveau `README.md` en français** : même structure, mêmes liens/ancres, mêmes blocs générés (marqueurs `CATALOG-STATUS` **inchangés**, cf [catalog-pr-hygiene.md](catalog-pr-hygiene.md)).
3. **Séparateur = point** : `README.en.md`, `<nom>.en.md` (décision user 2026-06-21, standard i18n, cohérent avec la Phase 3 de #1650). *Note : les notebooks utilisent l'underscore `xxx_en.ipynb` — l'écart est assumé (point pour markdown, underscore pour notebooks).*

**Ne jamais supprimer** l'original anglais (preuve de préservation, cf CLAUDE.md global « Consolider != Archiver »). Pas de traduction destructive.

## Périmètre Phase 0.5 (backfill manuel, déblocable sans #1271)

- **À traduire** : READMEs **pédagogiques / de série-sous-projet** à nous (ex. `SymbolicAI/Lean/*_lean/README.md`, `GameTheory/*_lean/README.md`, `QuantConnect/partner-course-quant-trading/`, `ML-Training-Pipeline/`).
- **Hors scope (rester EN)** : libs vendored (`foundry-lib/lib/**`, `.lake/packages/**`), data QC LEAN (`ESGF-2026/.../data/**`), `.pytest_cache/`, lakes externes (`_peters`), fork untracked (`Z3.Linq`), stubs QC `projects/*/README.md` auto-générés, README de scripts/build à faible valeur.

## Voir aussi

- CLAUDE.md §E + [code-style.md](code-style.md) — doc primaire = français
- EPIC **#1650** — traduction multilingue (Phase 0.5 = ce backfill ; Phases 1+ = moteur Argumentum scripté, gated par #1271)
- [catalog-pr-hygiene.md](catalog-pr-hygiene.md) — marqueurs `CATALOG-STATUS` inchangés sur la branche
- [readme-pedagogical-prose-mandate](../../docs/reference/procedures-recurrentes.md) — prose pédagogique #2651
