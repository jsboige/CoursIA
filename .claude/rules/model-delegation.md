# Delegation a des sous-agents — modele explicite obligatoire (sonnet/haiku par defaut)

S'applique a **tout agent qui delegue du travail a un sous-agent** (`Agent()` tool), quel que soit le role (coordinateur ai-01 ou worker po-*). Source : mandat user 2026-06-09 (« tout sous-agent doit avoir un modele explicite, sonnet ou haiku typiquement, et uniquement Opus dans des cas exceptionnels qui le justifient »), consolide avec le mandat 2026-06-07 sur la delegation read-heavy, **restreint le 10/10/2026** par le mandat user « Pas du tout » sur les sous-agents Opus des postes po-* (mesure ai-01:claudish : 6 sous-agents Opus partis de po-2027 ce jour, prompts d'agent generaliste avec ligne `opus justified`). Les angles morts observes par classe de tache sont synthetises ci-dessous (section « Angles morts connus »).

## Regle HARD — modele explicite obligatoire

1. **Tout appel `Agent()` DOIT specifier un `model` explicite.** L'argument `model` n'est jamais omis — un sous-agent sans modele explicite herite du modele parent (typiquement opus-tier), ce qui annule l'economie de la delegation et contredit la regle.

2. **`sonnet` ou `haiku` par defaut.** Sauf justification ecrite (voir point 3), le model d'un sous-agent est :
   - **`"sonnet"`** : taches intermediaires (audit, recensement, diagnostic, redaction, enrichissement notebook, review structurelle)
   - **`"haiku"`** : taches simples (comptage, extraction format-impose, grep/scan, verification mecanique, listing)

3. **`"opus"` UNIQUEMENT depuis ai-01 — jamais depuis un poste po-\*, meme justifie (mandat user 10/10/2026).** L'Opus facture Anthropic ne part que d'ai-01 et des lanes que le user a autorisees nommement. Sur les postes po-\*, le parametre `model: "opus"` est **interdit, y compris avec la justification ecrite** que l'ancienne formulation de ce point autorisait : une tache qui semblerait l'exiger **remonte a ai-01** (dispatch ou DM), qui la delegue ou la prend lui-meme. En pratique : `model` explicite `sonnet`/`haiku` sur chaque `Agent()`, et `haiku` si l'on lance l'un des agents globaux du gabarit encore fixes `opus` (`code-explorer`, `git-sync`, `test-runner`, `code-fixer`, `test-investigator`) — le parametre de l'appel passe avant le `model:` du fichier de l'agent (ordre de resolution verifie dans le binaire Claude Code 2.1.296). Les cas autrefois « justifiables » (decision architecturale cross-fichier, synthese multi-sources contradictoire, investigation de regression profonde) restent du travail legitime — ils montent a ai-01 au lieu d'etre factures en Opus depuis un poste po-*.

   **Toujours non justifies** (opus interdit partout) : read-heavy borne, comptage, audit d'issues, verification de diffs, labeling, extraction, listing, generation de rapports structures.

4. **Deleguer le READ-HEAVY borne et verifiable, garder la DECISION.** Les taches a fort volume de lecture mais a critere de sortie objectif — recensement, audit d'issues, verification de diffs, diagnostic, comptage, extraction format-impose — vont a un sous-agent `sonnet` ou `haiku`. L'agent appelant garde : les **jugements** (labeling exercice/exemple, scope-vs-titre, WIP-acceptable, anti-regression Lean/preuve), les **merges/closes/dispatches**, et le **cross-check G.1** systematique.

5. **Format impose + evidence-cited dans le prompt.** Le prompt du sous-agent doit exiger un livrable structure (tableau, schema JSON, verdict par item) **avec preuve citee** (`file:line`, sha1, sortie de commande), pas une prose libre. Un livrable sans evidence se re-verifie ; un livrable evidence-cited se spot-checke.

6. **Local-git-only quand l'appelant tient une fenetre `gh auth`.** Un sous-agent qui appellerait `gh` pendant que l'appelant a bascule `gh auth switch -u jsboige` corromprait l'etat d'auth global (race). Donner au sous-agent des ops **`git` locales uniquement** (`git diff origin/main...origin/<branch>`, `git show`, `sha1sum`, `grep`, `Read`), pas de `gh`. L'appelant fait les ops `gh` lui-meme, hors fenetre sous-agent.

7. **Evaluer la qualite et la memoriser.** Apres chaque delegation, noter dans le journal de delegation local per-machine (`<projet>/.claude/agent-memory-local/delegation-quality.md`, gitignore) : type de tache, qualite (HAUTE/MOYENNE/FAIBLE), ce qui a ete exact, et l'**angle mort** observe. Les angles morts connus par classe de tache orientent quoi re-verifier soi-meme.

## Angles morts connus (re-verifier soi-meme)

| Classe de tache deleguee | Angle mort | Ce que l'appelant re-verifie |
|--------------------------|-----------|------------------------------|
| Triage / framing de PR | Lentilles-incident projet (poison-catalogue, scope-vs-titre, WIP-acceptable) | Appliquer les lentilles soi-meme sur le verdict |
| Recensement / comptage | Nombres approximes a l'oeil (lignes, fichiers) | Re-`wc -l` / re-grep les chiffres pivots |
| Audit d'issues / deconfliction | Regressions de sequence fines, faux-positifs residuels | Self-verify la sequence + les FP |
| Labeling exercice/exemple | Ne tranche pas le contenu (et NE DOIT PAS) | Lire la cellule, juger par CONTENU (cf [exercise-example-labeling.md](exercise-example-labeling.md)) |

**Comportement attendu du sous-agent (bon signe)** : deferer explicitement les jugements hors de sa portee (« the coordinator should assess ») plutot qu'halluciner un verdict. Un sous-agent qui defere sur un blind-spot connu est plus fiable, pas moins.

## Capacite vision — router le QA visuel, jamais le verifier text-only (HARD)

Toute tache dont la valeur depend du **rendu visuel** (galeries de figures README, plots de notebook, sorties d'images GenAI, layout de slides, diagrammes) voit son **QA visuel** confie a un agent **qui voit**. **Jamais** valide text-only : un `test -f` confirme l'**existence**, PAS le **rendu**.

**La capacite appartient au MODELE, pas a la machine (correction user 2026-09-18).** La formulation precedente routait « vers les lanes CoursIA-2 ou ai-01 » : c'est faux, et c'est faux d'une maniere qui coute. Une lane n'est pas un materiel, c'est un modele qui l'anime — et ce modele change. En l'etat mesure :

| Modele animant la lane | Vision |
|---|---|
| GLM (sous Sonnet/CoursIA) | **non** |
| MiniMax (notamment CoursIA-2) | oui |
| Sonnet, y compris les **failovers** | oui |
| les autres du parc | oui |

Consequence operationnelle : **c'est a l'agent de juger s'il peut prendre le grain**, sur ce dont il dispose a cet instant. Ni une table de routage par machine, ni un coordinateur distant ne le savent mieux que lui — et une table par machine se perime silencieusement au premier changement de modele. Un agent qui ne voit pas **le dit et passe la main** ; il ne valide pas text-only, et il n'est pas fautif de rendre le grain.

Routage **capability-driven**, pas token-driven : c'est « meilleur outil pour la tache », pas un fallback degrade.

**`sk-agent` comme vision indirecte : possible, mais on s'y est deja brule.** Ce n'est pas une voie de contournement pour une lane sans vision — au mieux un complement, jamais la preuve qui remplace un regard. Avant de s'en servir, verifier ce qu'il rend reellement sur l'artefact vise ; un verdict de vision indirecte non corrobore ne vaut pas validation.

Le defaut a attraper (cf [sota-not-workaround.md](sota-not-workaround.md) Prong A) : figure reduite a des blocs plats / image blanche / placeholder / render casse **alors que le vrai outil etait invocable** → RECOVERABLE-MACHINE ou -LOCAL, **regenerer**, jamais consacrer.

Mapping `model` → moteur par machine, mecanisme concret (`Read` d'image / screenshot Playwright), couplage sweep-MiniMax ↔ jugement-ai-01, incident fondateur : [cluster-agents.md](../../docs/reference/cluster-agents.md).

## Voir aussi

- [coordinator-discipline.md](coordinator-discipline.md) — ai-01 merge actif, no-languishing
- [proactive-coordination.md](proactive-coordination.md) — side-tracks via sous-agents specialistes async
- [verify-before-claiming.md](verify-before-claiming.md) — cross-check G.1, ne pas propager un claim non verifie
- [exercise-example-labeling.md](exercise-example-labeling.md) — labeling par contenu (jugement non delegable)
