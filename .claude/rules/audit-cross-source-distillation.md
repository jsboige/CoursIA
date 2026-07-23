# Audit cross-source distillation — méthode + sortie dashboard/issue (jamais un rapport commité)

S'applique à **tout agent** auditant une **distillation** : l'écart entre une **source canonique** (MBML, papier SOTA, manuel de référence type Shoham/Leyton-Brown) et son **portage** dans un notebook (Infer.NET, PyMC, Lean, QC…).

## Règle HARD 1 — la SORTIE d'un audit ne se commite JAMAIS dans l'arbre du repo

Un audit produit un **verdict**, pas un fichier. Le compte-rendu va sur le **dashboard RooSync** (éphémère) ; un finding **actionnable** devient une **issue** (le notebook la corrige ensuite en PR). Il ne devient **jamais** un `AUDIT-*.md` / `*_audit_cNNNN.md` commité dans `MyIA.AI.Notebooks/**` (harness-hygiene tier « éphémère » + CLAUDE.md §A « GitHub = code, jamais de rapports d'audit dans le repo »).

Incident fondateur : **18 rapports `audit-distillation` déposés dans l'arbre notebooks** (GameTheory / Probas / DecInfer / PyMC), signalés par le user le 2026-07-23 et retirés par #8168. Un finding d'attribution (« le notebook cite la source 0× ») → **issue** ; le notebook ajoute la citation. Le rapport lui-même n'a aucune valeur commitée.

## Règle HARD 2 — un audit est un grain au cas par cas, jamais un genre reconductible

Un audit se justifie sur **une** cible concrète (ce notebook, cette source), quand un doute réel de fidélité existe. Il ne se déroule **jamais** en **rollout de genre** — « auditer toutes les familles en série », une table « reconductibilité N/N », un décret « audit = contribution, je promeus ma méthode en règle avant de clore ». C'est la monoculture LIGHT scan-générable fermée par [variation-protocol.md](variation-protocol.md) (litmus : « je peux en produire une douzaine en scannant le notebook suivant » → LIGHT). Aucun agent ne s'auto-autorise à promouvoir une règle : tout ajout à `.claude/rules/` passe par une **PR + sign-off user** (CLAUDE.md §A).

## Méthode (quand un audit est réellement justifié)

1. Identifier la **source canonique** + le(s) notebook(s) cible(s).
2. Lire la source **firsthand** — sous-sections + exemples chiffrés, pas seulement l'intro (G.9, cf [verify-before-claiming.md](verify-before-claiming.md)).
3. Comparer **axe par axe** : concepts / dérivation / exemples chiffrés / visualisations / exercices / attribution.
4. Poser un **verdict par axe** :

| Verdict | Critère vérifiable |
|---|---|
| **FIDÈLE** | toutes sous-sections présentes + ≥1 exemple chiffré + ≥1 exercice |
| **PERTE DOCUMENTÉE** | ≥1 axe manquant mais explicite (section « Limites » / renvoi externe) |
| **PERTE PAR COMPLAISANCE** | ≥1 axe manquant sans mention → **finding = issue** |
| **DIVERGENCE POSITIVE** | exercices/exemples originaux ≠ copier-coller (enrichissement, pas régression) |

Le livrable de l'audit est ce tableau de verdicts **sur le dashboard**, plus une **issue par axe « PERTE PAR COMPLAISANCE »** — pas un fichier dans le repo.

## Voir aussi

- [harness-hygiene.md](harness-hygiene.md) — 3 tiers : rapport = dashboard, jamais repo
- [variation-protocol.md](variation-protocol.md) — pas de monoculture de genre (audit inclus)
- [audit-reassessment.md](audit-reassessment.md) — protocole 4 étapes NanoClaw (compatible)
- [verify-before-claiming.md](verify-before-claiming.md) — firsthand, G.1
- [three-exercises-per-notebook.md](three-exercises-per-notebook.md) — richesse pédagogique (axe « exercices »)
