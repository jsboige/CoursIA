# Règles globales machine — détail déporté (déplacé)

Ce détail vit désormais dans le dépôt **roo-extensions**, à côté du harnais global dont il porte le détail :

- Détail : `docs/harness/global-rules-detail.md` — matrice action→lecture de « Read Body Before Any Action », incident fondateur 2026-05-17, matrice de scope complète du « Multi-Machine Ping-Pong », verbatim du mandat 2026-05-19.
- Règle : `.claude/configs/user-global-claude.md` — le harnais **machine**, déployé en `~/.claude/CLAUDE.md` dans tous les workspaces.

**Pourquoi là-bas et pas ici.** Le harnais global est machine-level : il s'applique à tous les dépôts, et sa source de vérité est roo-extensions (un trim local est écrasé au prochain déploiement s'il n'y est pas répercuté). Son détail y rejoint les trois autres docs de référence que ce harnais pointait déjà — `roosync-tools-guide.md`, `conversation-browser-detailed.md`, `sddd-conversational-grounding.md`. Garder une seconde copie ici garantissait la dérive entre les deux : rien dans CoursIA ne référençait ce fichier, seul le harnais global le lisait.

Livré par jsboige/roo-extensions#3036 (mergée le 2026-08-05) ; cette copie n'est conservée en pointeur que le temps que les machines aient repris le déploiement.

## Le détail propre à CoursIA

Les règles **projet** et leur détail restent ici :

- [`.claude/rules/harness-hygiene.md`](../../.claude/rules/harness-hygiene.md) — les 3 tiers d'information (harnais succinct / doc pérenne / dashboard éphémère)
- [`.claude/rules/coordinator-discipline.md`](../../.claude/rules/coordinator-discipline.md) — discipline coordinateur
- [`.claude/rules/proactive-coordination.md`](../../.claude/rules/proactive-coordination.md) — L740, re-arm des crons expirés
- [`docs/reference/`](../reference/) — détail déporté des règles projet
