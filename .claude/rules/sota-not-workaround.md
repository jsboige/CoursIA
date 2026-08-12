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

### Procedure d'etablissement INTRINSIC — checklist 6 axes obligatoire (NEW c.8243, #10459)

Un verdict `INTRINSIC` est le plus restrictif des 5 (il declare une impossibilite), et c'est **le plus dangéreux** a laisser passer sans verification : il justifie une substitution durable dans le code, qui devient invisible pour les auditeurs suivants. Pour cette raison, **chaque verdict `INTRINSIC` doit repondre nominativement les 6 axes** suivants, par « non applicable, parce que… » ou « oui, mais testé, résultat : ... » :

| # | Axe | Question a repondre dans le body PR |
|---|---|---|
| 1 | **Binding .NET / NuGet** | Un package officiel existe-t-il pour la cible ? (ex : `OR-Tools`, `Accord.NET`) |
| 2 | **`P/Invoke`** | Une API C stable est-elle exposee par la lib ? (cf `libtesseract`, `libsodium`) |
| 3 | **CLI `Process.Start`** | Un binaire invocable existe-t-il ? (ex : `gambit`, `minizinc`, `clingo`) |
| 4 | **`IKVM`** (pont Java) | La lib est-elle en Java ? Si oui, est-elle deja shadee ? ([`docs/ledgers/`](docs/ledgers/3801-sota-axe2.md)) |
| 5 | **`PythonNet`** (pont CPython) **(NEW c.8243)** | **La lib a-t-elle un binding Python ?** Si oui, le pont `.NET → CPython → pyspiel`-like est disponible via `pythonnet 3.0.5` + `Runtime.PythonDLL` — pas d'`INTRINSIC` sans l'avoir teste. |
| 6 | **Lib differente a role equivalent** | Un autre moteur SOTA .NET tient-il le role ? (cf PyMC ↔ Infer.NET, OR-Tools ↔ choco, mealpy ↔ MetaGeneticSharp) |

**Regle d'enforcement** : un verdict `INTRINSIC` dont le body **ne repond pas nominativement les 6 axes** (y compris « axe 5 N/A parce que la cible n'a pas de binding Python, vérifié sur PyPI/X au commit SHA … ») est **incomplet** → **`CHANGES_REQUESTED`** ([pr-review-discipline.md](pr-review-discipline.md) §H). La liste des 5 verdicts est conservee, c'est **la procedure d'etablissement** d'`INTRINSIC` qui se durcit.

**Origine de la 6ᵉ entree** (incident fondateur #10459) : trois verdicts `INTRINSIC` OpenSpiel convergent dans 3 PRs distinctes (#10390/#10394/#10454) — aucun n'avait examine l'axe PythonNet. Le depot certifiait deja le pont ailleurs (`MyIA.AI.Notebooks/GenAI/SemanticKernel/09-SemanticKernel-Building-CLR.ipynb`, `SOTA-OK` au ledger #3801), et le user l'a rappele verbatim 2026-08-11 (« PythonNet pour bridger est tout a fait acceptable, fonctionne plutot bien … overhead negligeable »). La deuxieme omission d'axe (la premiere etait `IKVM`) demontre qu'une regle non explicite ne se corrige pas par plus de vigilance : elle demande un **organe** (la checklist).

**Preuve d'execution par l'axe 5** : voir #10464/#10470/#10496/#10585/#10598 — 5 PRs MERGED sur `main` posant le pont `.NET → CPython → pyspiel` (CFR expl 0.008226, MCTS action=4, rollout Kuhn, kuhn_poker NashConv 0.0230, axelrod strategie). Plus la precedente SK-09 (PythonNet 3.0.5 + DLL loading SOTA-OK, documente au ledger #3801). La porte etait fermee a tort ; elle est desormais **prouvee**, avec cinq mesures distinctes.

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
- **#10459** — omission d'axe PythonNet dans la taxonomie bucket-3 (3 verdicts INTRINSIC OpenSpiel reclasses, 5 PRs livrees). La checklist 6 axes de ce fichier est l'organe qui ferme la classe d'incidents.
