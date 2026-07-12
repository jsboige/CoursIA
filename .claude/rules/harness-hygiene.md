# Harness hygiene — info à 3 tiers, harnais succinct

S'applique à **tous les agents** du cluster CoursIA (workers `po-*` + coordinateur `ai-01`). Source : mandat user 2026-06-01 — « une bonne discipline de consolidation de l'information dans des dispatchs qui n'encombrent pas en permanence le harnais ; le répertoire docs est là pour accueillir la doc pérenne référencée succinctement par les fichiers du harnais ».

## Règle HARD — 3 tiers d'information

| Tier | Support | Contenu | Discipline |
|------|---------|---------|------------|
| **Harnais** (auto-loaded chaque session) | `CLAUDE.md`, `.claude/rules/*.md`, `MEMORY.md` per-machine | Règles durables + **pointeurs succincts** vers `docs/` | **Succinct.** Référence, ne détaille pas. |
| **Doc pérenne** | `docs/<theme>.md` | Détail durable (procédures, état vérifié, leçons consolidées, inventaires de référence) | Référencé **succinctement** depuis le harnais. |
| **Éphémère** | Dashboard RooSync workspace | État de cycle, logs de coordination, rapports de session, dispatches | **Jamais** dans le harnais ni dans un fichier du repo. |

## Anti-patterns interdits

- **Gonfler le harnais** avec des logs de cycle datés, des numéros de PR mergées, des SHA — ça vit sur le **dashboard**, pas dans `MEMORY.md` ni `CLAUDE.md`.
- Créer un fichier `*_REPORT.md` / `*_AUDIT.md` / `*_COORDINATION.md` / `*_STATUS.md` dans le repo (rapport = dashboard).
- Dupliquer dans `MEMORY.md` / `CLAUDE.md` un détail qui a (ou devrait avoir) sa place dans `docs/`.
- Recréer des dizaines de `feedback_*.md` locaux : une leçon cross-machine va dans `CLAUDE.md` / `rules` / `docs`.

## Discipline de consolidation (avant d'ajouter au harnais)

1. **Est-ce durable ?** Non → dashboard. Oui → étape 2.
2. **Est-ce du détail ?** Oui → `docs/<theme>.md` + 1 ligne pointeur dans le harnais. Non (règle / pointeur bref) → harnais directement.
3. **Préserver avant de réduire** (cf CLAUDE.md global « Consolider != Archiver ») : merger le contenu durable dans sa cible AVANT de trimmer la source. Citer la cible comme preuve.

## Voir aussi

- CLAUDE.md global — « Knowledge Preservation » + « Consolider != Archiver »
- [proactive-coordination.md](proactive-coordination.md) — reporting dashboard
- [coordinator-discipline.md](coordinator-discipline.md) — rapports coord = dashboard, pas repo
- [../../docs/reference/procedures-recurrentes.md](../../docs/reference/procedures-recurrentes.md) — procédures + leçons cycle merge consolidées
