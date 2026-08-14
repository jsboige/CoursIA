# SOTA : vrai outil + probleme non-trivial — install/invoke/re-plug, faire valoir le moteur (HARD)

S'applique a **tous les agents** (workers po-* + coordinateur ai-01) **ET a tous les reviewers (humains ET bots** clusterManager-Myia : Hermes primaire, NanoClaw audit). Source : mandat user 2026-06-21 (3 messages : outil **installe ou invoque**, sinon **branche/rebranche** — au besoin sur la machine au bon env ; tenir un **registre** + resserrer le harnais ET les bots, le **reflexe workaround degrade** etant le defaut a corriger ; **problemes trop basiques** a complexifier pour faire valoir les moteurs). Registre = **EPIC #3801**. Consolide CLAUDE.md section F (reparer, jamais contourner) + [repair-not-consecrate](../../docs/reference/regles-validation-detail.md) + l'audit a 2 axes (committed <-> achievable).

**Verbatims du mandat, incidents d'axes, mesures anti-fabrication** : [docs/reference/sota-verdicts-detail.md](../../docs/reference/sota-verdicts-detail.md).

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
| 4 | **`IKVM`** (pont Java) | La lib est-elle en Java ? Si oui, est-elle deja shadee ? ([`../../docs/ledgers/3801-sota-axe2.md`](../../docs/ledgers/3801-sota-axe2.md)) |
| 5 | **`PythonNet`** (pont CPython) **(NEW c.8243)** | **La lib a-t-elle un binding Python ?** Si oui, le pont `.NET → CPython → pyspiel`-like est disponible via `pythonnet 3.0.5` + `Runtime.PythonDLL` — pas d'`INTRINSIC` sans l'avoir teste. |
| 6 | **Lib differente a role equivalent** | Un autre moteur SOTA .NET tient-il le role ? (cf PyMC ↔ Infer.NET, OR-Tools ↔ choco, mealpy ↔ MetaGeneticSharp) |

**Regle d'enforcement** : un verdict `INTRINSIC` dont le body **ne repond pas nominativement les 6 axes** (y compris « axe 5 N/A parce que la cible n'a pas de binding Python, vérifié sur PyPI au commit SHA … ») est **incomplet** → **`CHANGES_REQUESTED`** ([pr-review-discipline.md](pr-review-discipline.md) §H). La liste des 5 verdicts est conservee ; c'est **la procedure d'etablissement** d'`INTRINSIC` qui se durcit.

**Origine de la 6ᵉ entree** (#10459) : trois verdicts `INTRINSIC` OpenSpiel convergents dans 3 PRs distinctes, aucun n'ayant examine l'axe PythonNet — alors que le depot certifiait deja le pont (SK-09, `SOTA-OK` au ledger #3801). L'axe est desormais **prouve** par 5 PRs mergees posant le pont `.NET → CPython → pyspiel`. Deuxieme omission d'axe apres `IKVM` : une regle non explicite ne se corrige pas par plus de vigilance, elle demande un **organe** (la checklist). Verbatim user, PRs et mesures : [sota-verdicts-detail.md §2](../../docs/reference/sota-verdicts-detail.md).

### Stop & Repair — JAMAIS hand-editer une sortie de cellule (mandat user 2026-06-22)

Le workaround le plus insidieux = **scrubber / hand-editer la SORTIE de cellule committee** (redacter chemin machine / prefixe de cle / render casse dans `outputs`) au lieu de re-executer = **falsifier la preuve d'execution = malhonnete, BANNI**. On **repare la cause** (env/cwd, outil manquant, source qui imprime) et on **RE-EXECUTE** — jamais maquiller. Seules exceptions : quantbooks QC (non-executables via MCP) + `metadata.papermill.input/output_path` au `basename`. Une PR qui hand-edite une sortie hors ces deux cas = `CHANGES_REQUESTED` (`APPROVED` = complaisance). Regle complete (triage cause A/B/C + incidents) : [secrets-hygiene.md](secrets-hygiene.md) regle 6 + [[feedback-no-cell-output-scrubbing]].

## Prong B — Probleme non-trivial qui met le moteur en valeur

Un notebook qui demontre un **moteur / solveur / modele** (search, CSP, SMT/Z3, planners, metaheuristiques, tactiques Lean, ML, GenAI) DOIT poser un probleme assez riche pour **exercer et faire valoir la capacite distinctive du moteur** — pas un **cas degenere** ou le moteur SOTA equivaut a une baseline triviale.

Cas canonique : **BFS vs A*** sur un graphe a cout uniforme (A* degenere en BFS, l'heuristique ne sert a rien) -> remplacer par un terrain **pondere** ou l'heuristique discrimine (commit `8905f8845`, planners-3). Memes pieges : un Z3 sur une contrainte qu'un `if` resout, un planner sur un plan lineaire sans parallelisme, un metaheuristique sur une fonction convexe a optimum unique.

Action : **complexifier le probleme existant** OU **ajouter un probleme additionnel plus riche**, de sorte que la capacite annoncee soit **visible dans la sortie**. **Modulo un temps de traitement raisonnable** : viser un probleme **discriminant mais borne**, pas un benchmark de plusieurs minutes dans un notebook pedagogique.

### Verification anti-fabrication — mesurer la discrimination AVANT de clamer « heuristique X echoue »

Un enrichissement Prong-B ne se declare pas sur un **pitch plausible** : on **mesure** d'abord la discrimination firsthand (installer le solveur — regle F — et comparer resultat-heuristique vs optimum exact sur le graphe candidat). Un pitch non mesure = violation G.9 en attente d'etre livree.

Anti-exemple mesure (Mycielski : greedy ET DSATUR trouvent χ, le folklore ne reproduit PAS — le vrai cas discriminant est Erdos-Renyi dense) + faux signal de grep MiniZinc (`solve minimize` dans la chaine de modele, pas `.minimize(`) : [sota-verdicts-detail.md §3](../../docs/reference/sota-verdicts-detail.md).

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
