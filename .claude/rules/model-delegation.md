# Delegation a des sous-agents — modele explicite obligatoire (sonnet/haiku par defaut)

S'applique a **tout agent qui delegue du travail a un sous-agent** (`Agent()` tool), quel que soit le role (coordinateur ai-01 ou worker po-*). Source : mandat user 2026-06-09 (« tout sous-agent doit avoir un modele explicite, sonnet ou haiku typiquement, et uniquement Opus dans des cas exceptionnels qui le justifient »), consolide avec le mandat 2026-06-07 sur la delegation read-heavy. 7 tests confirmants (HAUTE qualite) — detail des angles morts par classe de tache : `~/.claude/projects/d--CoursIA/memory/delegation-glm-haiku-quality.md`.

## Regle HARD — modele explicite obligatoire

1. **Tout appel `Agent()` DOIT specifier un `model` explicite.** L'argument `model` n'est jamais omis — un sous-agent sans modele explicite herite du modele parent (typiquement opus-tier), ce qui annule l'economie de la delegation et contredit la regle.

2. **`sonnet` ou `haiku` par defaut.** Sauf justification ecrite (voir point 3), le model d'un sous-agent est :
   - **`"sonnet"`** : taches intermediaires (audit, recensement, diagnostic, redaction, enrichissement notebook, review structurelle)
   - **`"haiku"`** : taches simples (comptage, extraction format-impose, grep/scan, verification mecanique, listing)

3. **`"opus"` UNIQUEMENT sur justification explicite.** Un sous-agent opus est acceptable **uniquement** si le prompt de l'Agent tool contient une justification en anglais d'une ligne (ex: `// opus justified: needs cross-file architectural judgment beyond sonnet capability`). Les cas typiques justifies :
   - Decision architecturale cross-fichier complexe
   - Synthese multi-sources contradictoires necessitant un jugement nuance
   - Investigation de regression profonde ou un sonnet pourrait manquer des subtilites

   **Non justifies** (opus interdit) : read-heavy borne, comptage, audit d'issues, verification de diffs, labeling, extraction, listing, generation de rapports structures.

4. **Deleguer le READ-HEAVY borne et verifiable, garder la DECISION.** Les taches a fort volume de lecture mais a critere de sortie objectif — recensement, audit d'issues, verification de diffs, diagnostic, comptage, extraction format-impose — vont a un sous-agent `sonnet` ou `haiku`. L'agent appelant garde : les **jugements** (labeling exercice/exemple, scope-vs-titre, WIP-acceptable, anti-regression Lean/preuve), les **merges/closes/dispatches**, et le **cross-check G.1** systematique.

5. **Format impose + evidence-cited dans le prompt.** Le prompt du sous-agent doit exiger un livrable structure (tableau, schema JSON, verdict par item) **avec preuve citee** (`file:line`, sha1, sortie de commande), pas une prose libre. Un livrable sans evidence se re-verifie ; un livrable evidence-cited se spot-checke.

6. **Local-git-only quand l'appelant tient une fenetre `gh auth`.** Un sous-agent qui appellerait `gh` pendant que l'appelant a bascule `gh auth switch -u jsboige` corromprait l'etat d'auth global (race). Donner au sous-agent des ops **`git` locales uniquement** (`git diff origin/main...origin/<branch>`, `git show`, `sha1sum`, `grep`, `Read`), pas de `gh`. L'appelant fait les ops `gh` lui-meme, hors fenetre sous-agent.

7. **Evaluer la qualite et la memoriser.** Apres chaque delegation, noter dans `delegation-glm-haiku-quality.md` : type de tache, qualite (HAUTE/MOYENNE/FAIBLE), ce qui a ete exact, et l'**angle mort** observe. Les angles morts connus par classe de tache orientent quoi re-verifier soi-meme.

## Angles morts connus (re-verifier soi-meme)

| Classe de tache deleguee | Angle mort | Ce que l'appelant re-verifie |
|--------------------------|-----------|------------------------------|
| Triage / framing de PR | Lentilles-incident projet (poison-catalogue, scope-vs-titre, WIP-acceptable) | Appliquer les lentilles soi-meme sur le verdict |
| Recensement / comptage | Nombres approximes a l'oeil (lignes, fichiers) | Re-`wc -l` / re-grep les chiffres pivots |
| Audit d'issues / deconfliction | Regressions de sequence fines, faux-positifs residuels | Self-verify la sequence + les FP |
| Labeling exercice/exemple | Ne tranche pas le contenu (et NE DOIT PAS) | Lire la cellule, juger par CONTENU (cf [exercise-example-labeling.md](exercise-example-labeling.md)) |

**Comportement attendu du sous-agent (bon signe)** : deferer explicitement les jugements hors de sa portee (« the coordinator should assess ») plutot qu'halluciner un verdict. Un sous-agent qui defere sur un blind-spot connu est plus fiable, pas moins.

## Note de mapping (par machine)

Le mapping `model` explicite vers le moteur sous-jacent depend de la machine d'execution. Raisonner en **tiers** (intermediaire / leger), pas en nom de modele. Le principe — deleguer le read-heavy borne, garder la decision, modele explicite obligatoire — est invariant.

| Machine   | `sonnet` (tier intermediaire) | `haiku` (tier leger)     |
|-----------|-------------------------------|--------------------------|
| ai-01     | GLM-5.1                       | Qwen 3.6 local           |
| po-2023   | ZAI GLM-5.1                   | MiniMax M3               |
| autres workers po-* | voir `roosync_inventory`     | voir `roosync_inventory` |

MiniMax M3 (deploie sur `po-2023` depuis 2026-07-02, mandat coordinateur) remplace Qwen 3.6 sur le tier `haiku` pour cette lane. Conséquence operationnelle : les sous-agents `model: "haiku"` invoques depuis `po-2023` (ou routés vers lui) sont executes par MiniMax M3, pas par Qwen. La regle de qualite (deleguer le read-heavy borne, garder la decision) reste identique — seul le moteur change.

## Voir aussi

- [coordinator-discipline.md](coordinator-discipline.md) — ai-01 merge actif, no-languishing
- [proactive-coordination.md](proactive-coordination.md) — side-tracks via sous-agents specialistes async
- [verify-before-claiming.md](verify-before-claiming.md) — cross-check G.1, ne pas propager un claim non verifie
- [exercise-example-labeling.md](exercise-example-labeling.md) — labeling par contenu (jugement non delegable)
