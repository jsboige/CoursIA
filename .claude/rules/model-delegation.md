# Délégation à des sous-agents `sonnet` / `haiku` — read-heavy borné + vérifiable

S'applique à **tout agent qui délègue du travail à un sous-agent**, en priorité au **coordinateur ai-01**. Source : mandat user 2026-06-07 (verbatim) : « N'hésite pas ceci dit à utiliser toi-même des agents sonnet ou haiku, en évaluant la qualité de ce qu'ils peuvent te fournir, en mémoire pour la suite, voire dans claude.md pour tout le monde. » Validé par 7 tests confirmants (HAUTE qualité) — détail des angles morts par classe de tâche : `~/.claude/projects/d--CoursIA/memory/delegation-glm-haiku-quality.md`.

## Règle HARD

1. **Déléguer le READ-HEAVY borné et vérifiable, garder la DÉCISION.** Les tâches à fort volume de lecture mais à critère de sortie objectif — recensement, audit d'issues, vérification de diffs, diagnostic, comptage, extraction format-imposé — vont à un sous-agent **`model: "sonnet"`** (tier intermédiaire) ou **`model: "haiku"`** (tier léger, tâches plus simples). L'agent appelant garde : les **jugements** (labeling exercice/exemple, scope-vs-titre, WIP-acceptable, anti-régression Lean/preuve), les **merges/closes/dispatches**, et le **cross-check G.1** systématique.

2. **JAMAIS de sous-agent `opus` / `default`.** Un sous-agent au tier le plus cher annule l'économie de la délégation. Le tier Opus reste réservé au travail stratégique main-track porté par l'agent appelant lui-même (`model` omis sur l'Agent tool => hérite, ne PAS forcer opus en sous-agent).

3. **Format imposé + evidence-cited dans le prompt.** Le prompt du sous-agent doit exiger un livrable structuré (tableau, schéma JSON, verdict par item) **avec preuve citée** (`file:line`, sha1, sortie de commande), pas une prose libre. Un livrable sans evidence se re-vérifie ; un livrable evidence-cited se spot-checke.

4. **Local-git-only quand l'appelant tient une fenêtre `gh auth`.** Un sous-agent qui appellerait `gh` pendant que l'appelant a basculé `gh auth switch -u jsboige` corromprait l'état d'auth global (race). Donner au sous-agent des ops **`git` locales uniquement** (`git diff origin/main...origin/<branch>`, `git show`, `sha1sum`, `grep`, `Read`), pas de `gh`. L'appelant fait les ops `gh` lui-même, hors fenêtre sous-agent.

5. **Évaluer la qualité et la mémoriser.** Après chaque délégation, noter dans `delegation-glm-haiku-quality.md` : type de tâche, qualité (HAUTE/MOYENNE/FAIBLE), ce qui a été exact, et l'**angle mort** observé. Les angles morts connus par classe de tâche orientent quoi re-vérifier soi-même.

## Angles morts connus (re-vérifier soi-même)

| Classe de tâche déléguée | Angle mort | Ce que l'appelant re-vérifie |
|--------------------------|-----------|------------------------------|
| Triage / framing de PR | Lentilles-incident projet (poison-catalogue, scope-vs-titre, WIP-acceptable) | Appliquer les lentilles soi-même sur le verdict |
| Recensement / comptage | Nombres approximés à l'œil (lignes, fichiers) | Re-`wc -l` / re-grep les chiffres pivots |
| Audit d'issues / déconfliction | Régressions de séquence fines, faux-positifs résiduels | Self-verify la séquence + les FP |
| Labeling exercice/exemple | Ne tranche pas le contenu (et NE DOIT PAS) | Lire la cellule, juger par CONTENU (cf [exercise-example-labeling.md](exercise-example-labeling.md)) |

**Comportement attendu du sous-agent (bon signe)** : déférer explicitement les jugements hors de sa portée (« the coordinator should assess ») plutôt qu'halluciner un verdict. Un sous-agent qui défère sur un blind-spot connu est plus fiable, pas moins.

## Note de mapping (environnement ai-01)

Sur ai-01, les alias résolvent : `sonnet` => GLM-5.1, `haiku` => Qwen 3.6 local. Sur une autre machine le mapping peut différer : raisonner en **tiers** (intermédiaire / léger), pas en nom de modèle. Le principe — déléguer le read-heavy borné, garder la décision, jamais Opus en sous-agent — est invariant.

## Voir aussi

- [coordinator-discipline.md](coordinator-discipline.md) — ai-01 merge actif, no-languishing
- [proactive-coordination.md](proactive-coordination.md) — side-tracks via sous-agents spécialistes async
- [verify-before-claiming.md](verify-before-claiming.md) — cross-check G.1, ne pas propager un claim non vérifié
- [exercise-example-labeling.md](exercise-example-labeling.md) — labeling par contenu (jugement non délégable)
