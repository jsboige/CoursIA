# SOTA : vrai outil + probleme non-trivial — install/invoke/re-plug, faire valoir le moteur (HARD)

S'applique a **tous les agents** (workers po-* + coordinateur ai-01) **ET a tous les reviewers (humains ET bots** clusterManager-Myia : Hermes primaire, NanoClaw audit). Source : mandat user 2026-06-21 (3 messages). Registre = **EPIC #3801**. Consolide et durcit : CLAUDE.md section F (reparer, jamais contourner) + [repair-not-consecrate](../../docs/reference/regles-validation-detail.md) + l'audit a 2 axes (committed <-> achievable).

> [msg1] outil SOTA approprie proprement **installe ou invoque** s'il s'agit d'un service ; sinon, **le brancher avec un coup de main user**, ou **le rebrancher** s'il l'a ete dans le passe, typiquement sur une **machine particuliere avec le bon environnement**.
> [msg2] tenir un **registre** et **resserrer le harnais ET le comportement de review des bots** (le leur signaler) — pour l'heure le **reflexe reste de chercher des workarounds degrades** plutot qu'installer et corriger ce qu'il faut.
> [msg3] **qualite des problemes souvent trop basiques** (cf BFS vs A*) — complexifier les pbs actuels ou proposer des pbs additionnels plus complexes pour **faire valoir toutes les capacites des moteurs externes**, la ou des exemples triviaux ne les mettent pas en valeur ; **modulo un temps de traitement raisonnable**.

## Prong A — Vrai outil SOTA, jamais workaround degrade

Un notebook DOIT executer le **vrai outil SOTA dont il parle**. Committer une **sortie de workaround degrade** (ASCII a la place d'une image generee, reimplementation jouet a la place de la lib, stub a la place d'un appel de service, sortie fabriquee a la place d'un backtest) **alors que l'outil reel est installable / invocable / rebranchable** = **regression consacree**, INTERDIT.

Avant de committer une sortie degradee, repondre **par ecrit (body PR)** par 1 des 5 verdicts :

| Verdict | Definition | Action |
|---------|-----------|--------|
| **SOTA-OK** | Le vrai outil est proprement installe/invoque ; la sortie committee EST sa vraie sortie | merge |
| **RECOVERABLE-LOCAL** | Outil installable/invocable sur la machine du worker (regle F) | installer + re-exec, pas de user |
| **RECOVERABLE-MACHINE** | A marche / marche sur une machine SPECIFIQUE avec le bon env (GenAI->po-2023, GPU->po-2024/ai-01, embeddings->po-2026, Lean->WSL, QC->QC-Cloud) | router vers cette machine + re-exec |
| **RECOVERABLE-USER-HAND** | Action user one-time (token, OAuth, creds paper-trading, acces modele gate, hardware) | signaler **EXPLICITEMENT dans vscode** ([user-blocker-signaling](user-blocker-signaling.md)), puis re-exec |
| **INTRINSIC** | Aucun chemin SOTA reel (service externe mort, vraiment intractable) | documenter **HONNETEMENT** le plafond atteignable — explicite, jamais maquille en resultat SOTA |

Le defaut paresseux (« ASCII art / reimplementation jouet / 'Java absent' / 'kernel not available locally' ») committe **sans avoir verifie RECOVERABLE-*** = manquement grave.

### Stop & Repair — JAMAIS hand-editer une sortie de cellule (mandat user 2026-06-22)

Le workaround le plus insidieux = **scrubber / hand-editer la SORTIE de cellule committee** (redacter chemin machine / prefixe de cle / render casse dans `outputs`) au lieu de re-executer = **falsifier la preuve d'execution = malhonnete, BANNI**. On **repare la cause** (env/cwd, outil manquant, source qui imprime) et on **RE-EXECUTE** — jamais maquiller. Seules exceptions : quantbooks QC (non-executables via MCP) + `metadata.papermill.input/output_path` au `basename`. Une PR qui hand-edite une sortie hors ces deux cas = `CHANGES_REQUESTED` (`APPROVED` = complaisance). Regle complete (triage cause A/B/C + incidents) : [secrets-hygiene.md](secrets-hygiene.md) regle 6 + [[feedback-no-cell-output-scrubbing]].

## Prong B — Probleme non-trivial qui met le moteur en valeur

Un notebook qui demontre un **moteur / solveur / modele** (search, CSP, SMT/Z3, planners, metaheuristiques, tactiques Lean, ML, GenAI) DOIT poser un probleme assez riche pour **exercer et faire valoir la capacite distinctive du moteur** — pas un **cas degenere** ou le moteur SOTA equivaut a une baseline triviale.

Cas canonique : **BFS vs A*** sur un graphe a cout uniforme (A* degenere en BFS, l'heuristique ne sert a rien) -> remplacer par un terrain **pondere** ou l'heuristique discrimine (commit `8905f8845`, planners-3). Memes pieges : un Z3 sur une contrainte qu'un `if` resout, un planner sur un plan lineaire sans parallelisme, un metaheuristique sur une fonction convexe a optimum unique.

Action : **complexifier le probleme existant** OU **ajouter un probleme additionnel plus riche**, de sorte que la capacite annoncee soit **visible dans la sortie**. **Modulo un temps de traitement raisonnable** : viser un probleme **discriminant mais borne**, pas un benchmark de plusieurs minutes dans un notebook pedagogique.

### Verification anti-fabrication — mesurer la discrimination AVANT de clamer « heuristique X echoue »

Un enrichissement Prong-B ne se declare pas sur un **pitch plausible** (« les heuristiques gloutonnes rattrapent le nombre chromatique sur les graphes de Mycielski, donc CP-SAT est essentiel ») : on **mesure** d'abord la discrimination firsthand (installer le solveur, regle F, comparer resultat-heuristique vs χ exact sur le graphe candidat). Un pitch non mesure = violation G.9 en attente d'etre livree.

**Anti-exemple verifie firsthand (c.598, ortools 9.15 + networkx 3.4.2)** : sur les graphes de Mycielski standard M_3 (C5), M_4 (Grotzsch), M_5, la coloration gloutonne **et** DSATUR **avec l'ordre networkx par defaut** trouvent **le** χ (3/4/5) — le folklore « greedy rattrape sur Mycielski » **ne reproduit pas** ici (il exige des ordres de sommets adversariaux). S'en servir comme cas Prong-B de coloration = fabriquer un enrichissement faux. Le vrai cas discriminant pour CP-SAT en coloration est le **graphe aleatoire dense Erdos-Renyi G(n, p>=0.3)** (greedy utilise strictement plus de couleurs que χ) — et App-2-GraphColoring le demontre deja (cell benchmark : n=200, greedy=22 / DSATUR=19 / CP-SAT=18).

**Faux signal technique** : un notebook MiniZinc couvre l'optimisation via la syntaxe `solve minimize obj;` (chaine dans le modele), **pas** via `.minimize(` Python — un `grep '.minimize('` renvoie `opt=0` sur des notebooks qui traitent bel et bien l'optimisation. Pour MiniZinc, grepper `solve (min|max)imize` dans les chaines de modele.

## Comportement des bots reviewers (signaler + enforce)

Les bots **DOIVENT** poster `CHANGES_REQUESTED` quand une PR notebook (interne/contributeur) :
- (A) commit une sortie degradee **sans verdict SOTA ecrit**, ou avec un **RECOVERABLE-* non tente** ; ou
- (B) demontre un moteur sur un **cas degenere** qui ne met pas sa capacite en valeur ; ou
- (C) **hand-edite / scrubbe une sortie de cellule** (chemin machine, prefixe de cle, render casse) au lieu de corriger la cause + re-executer — hors quantbook QC et hors `metadata.papermill` (cf Stop & Repair ci-dessus).

`APPROVED` dessus = complaisance. Cf [pr-review-discipline.md](pr-review-discipline.md) §H.

**Exception PR etudiante** (cf [student-pr-reviews.md](student-pr-reviews.md)) : NE PAS appliquer A/B — review bienveillante, pas de CHANGES_REQUESTED sur scaffolding.

## Voir aussi
- CLAUDE.md section F — env/kernel : reparer, jamais contourner
- [pr-review-discipline.md](pr-review-discipline.md) §H — critere bots SOTA + non-trivialite
- [anti-regression.md](anti-regression.md) — ne pas stripper le code reel
- [three-exercises-per-notebook.md](three-exercises-per-notebook.md) — richesse pedagogique (exercices)
- **EPIC #3801** — registre axe-2 SOTA + problem-richness, par famille (GenAI/po-2023 en tete)
