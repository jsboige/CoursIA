# Slow lane (voie asynchrone) — tranches 1-2 #12856

## Strategie

Sortir les controles **lourds et idempotents** du `pull_request` et les payer
**une fois par fournee** sur `main` (schedule). Strategie user 2026-08-23 :
« les jobs lourds ne devraient etre payes qu'une fois par fournee, les
legers tournent a chaque fois, et pourquoi pas les moyens peuvent etre
declanches sur des batchs controles ».

Le pilote tranche 1 (#11835 volet 1) demontre la **voie rapide** (1 checkout
pour 9 gardes, gain 5,1x) en ombre. Le present document decrit la **voie
lente** (slow-lane), complement asynchrone de la voie rapide.

## Tranche 1 — pilote ICT-Series

Cette PR ajoute `slow-lane.yml` avec **un seul job** :
`ict-tests-pilot`. Aucun workflow d'origine n'est modifie. C'est la preuve
d'infrastructure : schedule declenche, verdict publie, mesure reproductible.

### Acceptance tranche 1 (cf. #12856)

| # | Critere | Etat tranche 1 |
|---|---|---|
| 1 | `slow-lane.yml` existe, sur `schedule`, publie un verdict | ✅ job `ict-tests-pilot` |
| 2 | Chaque workflow deplace perd son trigger `pull_request` dans le meme commit | N/A (aucun mouvement) |
| 3 | Mesure avant/apres documentee | ✅ baseline = ce document ; apres = tranche 2 |
| 4 | Controle positif obligatoire (au moins une PR rouge deliberee) | A mesurer en tranche 2 |
| 5 | `git revert` d'un seul commit restaure le regime actuel | ✅ aucun fichier d'origine modifie |

### Frequence

Mardi 02:30 UTC (apres le pic push europeen, avant le pic US). Une seule
execution par fournee.

### Verdict

Le verdict est publie via `::notice` (PASS) ou `::error` (rouge delibere) sur
le run GitHub Actions. La convention reprend celle de `fast-lane-shadow.yml`
(un lot entierement vert est indiscernable d'un moteur debranche ; la
publication explicite du verdict distingue les deux).

### Faux vert du pilote — le verdict ne pouvait pas rougir (mesuré le 2026-10-26)

La tranche 1 est censée être la preuve que la voie lente tient un verdict sur
la suite ICT. Mesure firsthand sur les runs du pilote : **ce n'était pas le
cas**, et le défaut n'était pas visible depuis le tableau des runs.

**1. La suite n'exécutait rien.** La commande du job était
`python -m pytest tests ict/tests -q --no-header`, qui collecte **deux arbres
de tests dans une seule session**. Les deux arbres partagent **16 basenames
de modules** (`test_time_arrow.py`, `test_workspace.py`,
`test_catastrophe.py`, `test_sensitivity.py`, …) et **aucun des deux ne porte
de `__init__.py`** : pytest les importe alors par nom de fichier et refuse
(`import file mismatch`). Reproduction sur `origin/main` (mesure locale,
Python 3.14 ; **le fait décisif — les 16 erreurs — est lui mesuré dans le log
du job CI**, pas seulement en local) :

| Invocation | Collected | Erreurs |
|---|---|---|
| `pytest tests ict/tests` (session unique) | 2 335 | **16** |
| `pytest tests` | 1 324 | 0 |
| `pytest ict/tests` | 1 295 | 0 |

Les 16 paires sont des **fichiers différents** (16 md5 distincts sur 16 —
aucun doublon périmé). Dans les logs du job, la collecte s'interrompt :

```text
1 skipped, 2 warnings, 16 errors in 1.63s
!!!!!!!!!!!!!!!!!!! Interrupted: 16 errors during collection !!!!!!!!!!!!!!!!!!!
```

**2. Le job ne pouvait pas rougir.** L'étape `Run ict-tests suite` fait
`set +e`, écrit `${PIPESTATUS[0]}` dans un output, et se termine sur un
`echo` — son code de sortie est donc **0**. L'étape suivante publie une
annotation `::error`, et **une annotation GitHub n'échoue pas une étape**.
Mesure sur le run `39389459201` (2026-10-20) :

| Élément | Valeur |
|---|---|
| Étape 5 `Run ict-tests suite` | `success` |
| Étape 6 `Publish verdict` | `success` |
| Conclusion du job ICT | `success` |
| Log de l'étape 6 | `##[error]La suite ICT-Series a echoue en mode slow-lane (exit=2)` |
| Conclusion du **run** | `failure` — sur les 4 jambes CodeQL, pas sur ICT |

Les **4 jambes `Analyze:failure`** de ce run sont **hors périmètre de cette
PR** : le job `codeql-scheduled` n'est pas touché par ce correctif, et leur
cause n'est pas établie par lui (la seule cause documentée dans ce document
est le conflit SARIF / *default setup*, constaté au contrôle positif du
2026-09-05). Le point d'observation est le **prochain run `schedule`**
(mardi 02:30 UTC). Ne pas confondre ce rouge-là avec le faux vert ICT.

Les sept runs `schedule` consécutifs du **2026-09-08** au **2026-10-20** sont
donc en `failure` **au niveau du run** alors que la jambe ICT est verte à
chaque fois, et elle est verte parce qu'elle n'exécute rien et qu'elle ne
peut pas échouer.

**3. Ce que le correctif change.** Trois volets, tous dans
`.github/workflows/slow-lane.yml` :

- **deux invocations au lieu d'une** (`pytest tests` puis `pytest ict/tests`),
  chacune avec son rootdir donc son mode d'import — exactement ce que fait la
  voie rapide `ict-tests.yml`, qui en fait **deux jobs** (`ICT tests/ (58)` et
  `ICT ict/tests/ (69 package)`). Cette répartition est **mesurée verte en
  CI** : run `40328940542` (2026-10-26), les deux jobs `success` ;
- **le code de sortie de l'étape vaut celui de la suite** (`exit 1`), pour que
  le critère d'acceptance #12856-4 (« la voie lente rougit sur un vrai
  défaut ») soit atteignable ;
- **`timeout-minutes` de 15 à 60**, comme `ict-tests.yml` : durées mesurées
  le 2026-10-26 (runs `40333089185` et `40328940542`), **jusqu'à 7 min 54 s**
  pour la jambe `tests/` et **jusqu'à 10 min 26 s** pour la jambe
  `ict/tests/`, plus ~2 min d'installation. À 15 min, le correctif de collecte
  aurait seulement transformé le faux vert en timeout rouge.

**Le correctif de mode d'import aurait été un faux vert.** `--import-mode=importlib`
sur la session unique rendrait la collecte propre, mais le `pytest.ini` central
du dépôt force déjà `--import-mode importlib` (`addopts`, racine) et ce mode
**ignore les `sys.path.insert` de niveau module** — or `ict/tests/` en dépend
pour son `from ict import ...`. C'est précisément pourquoi `ict/tests/pytest.ini`
existe, et son en-tête dit que sans lui `test_reversibility_budget.py` et
`test_time_arrow.py` **n'ont jamais pu être exécutés**. Séparer les deux
jambes est donc le seul correctif qui n'échange pas un faux vert contre un
faux rouge.

**Ce que ce constat implique pour la suite du dossier.** La condition 1 de la
tranche 2 (ci-dessous) n'est pas « presque remplie » : elle n'a **jamais** été
mesurée sur un verdict réel. Le premier run `schedule` après ce correctif est
le **premier verdict vrai** du pilote — et s'il est rouge, ce sera un rouge
ICT à traiter, non un faux rouge.

## Tranche 2 — premier mouvement reel (a venir)

Conditions a remplir AVANT de deplacer un workflow dans la voie lente :

1. La tranche 1 a ete observee en production **>= 1 semaine**, sans faux
   vert ni faux rouge, avec verdict publie.
   > **Ré-ancré le 2026-10-26 : la condition n'avait jamais été mesurée sur un
   > verdict réel.** Le pilote a publié sept fois `##[error]` sur un job
   > `success` (section « faux vert du pilote » ci-dessus) : il n'y a pas eu
   > de « faux rouge » — il n'y a pas eu de verdict. La condition ne sera
   > remplie qu'après le correctif et **une semaine d'observation** d'un
   > verdict publié, rouge ou vert. Le contrôle positif du 2026-09-05 reste
   > valide pour la jambe CodeQL (la jambe ICT était verte ce jour-là, avant
   > l'apparition de la collision de collecte) : c'est la **durée
   > d'observation** qui est à re-compter, pas le contrôle positif.
2. Le workflow candidat a ete instrumente au niveau **ETAPE**
   (`steps[].started_at → steps[].completed_at`, fenetre 24 h). **Trois**
   instruments ont ete essayes le 2026-08-24 (commentaire ai-01 #12856) :
   run-level (`run_started_at → updated_at`) et job-level
   (`started_at → completed_at`) sont **tous deux contamines par l'attente
   en file** (des detecteurs aux travaux differents y convergent a six
   secondes pres — signature d'attente partagee, pas de cout) ; seul le
   niveau etape ne court que pendant le travail. Ne citer aucun chiffre
   run- ou job-level.
3. Le mouvement retire le trigger `pull_request` **dans le meme commit** que
   l'ajout a la voie lente (cf. acceptance #12856-2).
4. La mesure apres-mouvement compare la meme PR temoin avant/apres.

### Candidats a instruire (liste de depart, a confirmer par mesure etape-level)

- **`ict-tests.yml`** : ~3-5 min runner, 746 + 42 items, dejà instrumente.
- **CodeQL `Analyze` x4** : 4 jobs lourds sur PR notebook sans ligne C#/JS.
  Geres par GitHub Security tab, pas par un workflow du repo — mouvement
  indirect (desactiver au niveau repo + ajouter un slow-lane custom).
- **Quarto** (`quarto-pages-deploy.yml`) : ~3-8 min, dejà instrumente.
- **`lean-build.yml`** et les ~30 lakes Lean : tres lourds quand ils tirent,
  filtres par `paths:`. A instruire sans regresser la couverture.

## Tranche 2 — premier mouvement reel : CodeQL (PR livrante)

> **Constat d'epoque — re-ancré le 2026-10-26** (voir « Faux vert du pilote »
> ci-dessus). La commande de collecte unique (`python -m pytest tests
> ict/tests`) etait **deja** celle du commit d'origine du workflow
> (`15e899de87`, 2026-08-27, PR #13189) : le run du 2026-09-01 a donc
> collecte **un item**, comme les six suivants. La mention « ~1 semaine en
> production sans faux vert ni faux rouge » **ne vaut pas** — il n'y a pas eu
> de faux rouge, il n'y a pas eu de verdict. Ce qui reste a recompter apres
> le correctif, c'est la **duree d'observation** d'un verdict publie.

Sortie de tranche 1 constatee : run schedule 33463688662 (2026-09-01 02:44
UTC) `success`, step « Publish verdict » `success`, ~1 semaine en production
sans faux vert ni faux rouge.

**Tri etape-level 24 h (2026-09-05)** : le default setup CodeQL a tire
**78 runs `pull_request` en 24 h** (matrice x4 = ~312 jobs, ~14 min/run
github-hosted), y compris sur des PR 100 % docs — ~18 h runner/jour pour
une detection qui n'est pas un check requis (seul `PR gate` l'est). Tout le
reste du top etape-level est paths-filtre sur la surface touchee (Scripts
Tests 9,2 min/run, Notebook Validation 5,4, ML Tests 5,2), scoped
(Quarto 3,7 min/run post-#14429), protege par regime (golden-set H.7,
3,1), mutualise (Always-on guards) ou hors scope (PR gate 8,0). Les
deplacer serait une regression de couverture, pas une economie.

> **Etat mesure au 2026-10-25 — la jambe `codeql-scheduled` n'existe plus.**
> CodeQL est passe en *advanced setup* par un workflow du depot
> (`.github/workflows/codeql.yml`, issue #22548, decision mainteneur
> Q142 = c) : `pull_request` filtre par `paths` sur le code reellement
> analyse, matrice derivee des langages touches, plus `push: main` et un
> `schedule` hebdomadaire comme filet. Le job `codeql-scheduled` de
> `slow-lane.yml` a donc ete retire dans la meme PR : deux analyses de la
> meme tete de `main` sous la meme categorie SARIF se recouvriraient. Tout ce
> qui suit reste l'historique de la tranche 2 — le raisonnement, la mesure
> 24 h et le controle positif gardent leur valeur ; seule l'adresse du
> mouvement a change. Le job `ict-tests-pilot` de la tranche 1 est intact.

**Mouvement** : job `codeql-scheduled` dans `slow-lane.yml` (matrice x4,
`ubuntu-latest`, verdict publie par job). Le trigger per-PR vit dans le
**default setup** (settings repo, `dynamic/github-code-scanning/codeql`),
pas dans un fichier : la suppression = **toggle admin au merge** (Settings →
Code scanning → Default setup → Disable). Ne merger la jambe schedule qu'avec
le toggle — sans lui, double cout (per-PR + hebdo).

**Controle positif (acceptance #12856-4)** : dispatch slow-lane sur une
branche temoin portant un defaut deliber (C# non compilable dans un projet
du sln) — [run 33970230585](https://github.com/jsboige/CoursIA/actions/runs/33970230585)
(2026-09-05) :

- `Slow-lane CodeQL (csharp)` : **ROUGE pour la bonne raison** — Autobuild
  failure sur le code casse, Analyze skipped, verdict `::error` publie ;
- `Slow-lane ICT-Series pilot` : **success** (pas de faux rouge sur la jambe
  saine) ;
- langues interpretees : **ROUGE SARIF** — « Code Scanning could not process
  the submitted SARIF file: CodeQL analyses from advanced configurations
  cannot be processed when the default setup is enabled ». Découverte
  structurante : **la jambe schedule ne peut pas verdir tant que le default
  setup est actif** — le rejet SARIF est le verrou fail-closed qui force la
  coordination. Merger la jambe et basculer le toggle **le meme jour** ;
  d'ici là chaque run hebdo publie ces rouges nommés (honnête, visible,
  auto-résorbant au toggle).

**Reversibilite** : `git revert` du commit tranche 2 + reactivation du
default setup restaurent le regime per-PR.

## Mesure baseline (fenetre 24 h, mesuree 2026-08-27)

A capturer via `scripts/ci/measure_runner_demand.py` une fois la tranche 1
deployee sur main. Cible : etablir le **runner_minutes** par workflow
`pull_request` sur 24 h glissantes pour :

- `ict-tests.yml` (cible tranche 2)
- `quarto-pages-deploy.yml`
- `lean-build.yml`

La mesure tranche 2 comparera la meme fenetre 24 h apres mouvement. Le delta
est le gain attendu de la voie lente.

## Mesure du nombre de checks — critère d'acceptation #12856-3

Le critère demande « une mesure avant/après du nombre de checks sur une PR
témoin de surface étroite », avec un point de départ **écrit** : « 60 checks
sur #12840 (surface de 8 éléments) ». C'est un **nombre de checks**, pas une durée de
runner : il se mesure sur les **check-runs de la tête de la PR**, lus avec
`--paginate` et pliés par **nom exact**. (`runs?head_sha=` rend 0 sur une tête
qui a des check-runs : l'adresse par tête n'est pas la bonne.)

**Avant — la baseline, re-mesurée sur sa propre population.** Le point de
départ écrit vaut **60**. La population *settled* de #12840 (tête
`fb82de75db842f59f5866462562d9b2ba784930e`) en porte **73 check-runs, tous
de noms distincts**. Les 60 de l'issue sont un **décompte à mi-vol** : les
jobs lents (CodeQL, ombres, always-on) n'étaient pas tous atterris quand la
mesure a été prise. La baseline **réglée** est donc **73**, pas 60 — et c'est
73 qu'il faut comparer.

**Après — la même classe de PR, mesurée sur des PR de carnet mergées après le
mouvement de tranche 2** (même méthode, sur la tête de chaque PR) :

| PR | Surface | Mergée le | check-runs bruts | noms distincts |
|---|---|---|---|---|
| #12840 (témoin d'origine) | 7 carnets + 1 json | 2026-08-24 | 73 | **73** |
| #22196 | 4 carnets | 2026-10-26 | 97 | **97** |
| #22365 | 6 carnets | 2026-10-25 | 112 | **93** |
| #22364 | 10 carnets | 2026-10-25 | 96 | **94** |

**Le compte a augmenté, il n'a pas diminué** : de 73 à 93-97 (+27 % à +33 %)
sur la même classe de PR, et il est insensible à la surface (4, 6 ou 10
carnets donnent le même ordre de grandeur). La décomposition des noms, entre
les PR #12840 et #22196 : **54 ajoutés, 30 retirés**.

**Pourquoi la tranche 2 n'a rien réduit, et pourquoi ce n'était pas un
accident.** Le déclencheur `pull_request` de CodeQL **ne vit dans aucun
fichier du dépôt** : il est dans le *default setup* de GitHub (settings du
dépôt), et sa suppression est un **bascule admin** — c'est dit dans
l'en-tête du workflow `codeql.yml` de #22553, et le contrôle positif du
2026-09-05 publie déjà ce verrou (« le rejet SARIF est le verrou fail-closed
qui force la coordination »). Tant que la bascule n'est pas faite, **les
analyses per-PR continuent de tirer** et le compte ne baisse pas.

Une part de la hausse est en outre une **granularité**, pas du travail
supplémentaire : la voie rapide est passée d'un check agrégé
(`Fast lane (ombre) -- 21 gardes, 1 checkout`) à un check **par garde**
(`fast-lane (ombre): perimeter-review-guard`,
`… : Solution-leak HIGH delta (advisory, WARN phase, #8053)`,
`… : notebook-navlink-check`, …). Le même travail se compte sous plus de
noms. Le reste — les ratchets `Output-collapse`, `Source-collapse`,
`Split-reading`, `Output-flood`, les advisories de markdown, le bundle
`Always-on guards -- 16 organes, 1 checkout` — ce sont des gardes **nouvelles
qui ont atterri sur `main`** entre le 2026-08-24 et le 2026-10-26.

**Le brut et le distinct divergent** (112 bruts pour 93 distincts sur #22365) :
ce sont les **rejeux** d'un même nom de check. Un décompte brut compte donc
des reprises de job, pas des checks déclenchés — d'où la règle de plier par
nom exact.

**Ce qui reste à mesurer** : le gain réel du mouvement n'est mesurable
qu'après le bascule admin du *default setup*. C'est là — et seulement là —
que le compte de checks par PR doit **descendre**. La mesure à re-faire après
bascule, sur un témoin de même surface, avec la même méthode.

## Tranche 3 — lot quotidien en ombre (P3 du plan « CI à deux étages »)

Le lot quotidien est un **job de plus** dans ce workflow, pas un workflow de
plus. La voie lente est un organe unique : lui ajouter une cadence, un
budget et une politique de runner dans un second fichier aurait dupliqué
trois choses et aurait rendu « la voie lente » une notion diffuse.

### Ce que le lot fait — et ce qu'il ne fait pas

Il **mesure**. Depuis la tranche 2, le lot **émet un check-run *advisory* par
tête du lot** : le verdict devient lisible sur la PR, mais il **ne bloque
rien** — son nom porte le marqueur `advisory` que le `PR gate` route hors
porte. Le `PR gate` reste le seul juge. Le job est une mesure du coût de
l'étage 2, et la phase d'ombre d'avant bascule.

Il mesure deux choses :

- la **durée** d'un lot vert et d'un lot rouge ;
- la **fin de lot avant l'échéance** de son créneau (10:00Z / 13:00Z /
  21:30Z / 00:00Z). Un lot qui déborde retarde le suivant — la cadence
  tient, ou elle ne tient pas, et c'est cette mesure qui le dira.

### La tranche livrée, et ce qui reste

La **tranche 1** livre **ce qu'on mesure** :

- l'**arbre d'intégration** — `main` plus les PRs du lot ;
- la **suite complète** de la jambe `Scripts Tests`, jouée sur cet arbre.

La **tranche 2** livre le **check-run sur chaque tête du lot** : le verdict
du lot devient lisible sur la PR, et il porte aussi la **remarque de
troncature** du pool.

Ce qui reste pour la phase suivante : la **bascule** — le `PR gate` accepte
« étage 2 vert sur le lot du jour » à la place du vert par tête, et
`merge_ready` merge le lot. C'est **P4**, qui ne s'exécute qu'après une
semaine d'ombre qui tient le critère des 24 h.

### Le check-run du lot (tranche 2)

Un check-run par tête du lot, nommé `Heavy batch lot (advisory, non
bloquant)`. Trois règles le structurent.

**1. Il ne bloque aucun merge.** Le `PR gate` ne traite en *advisory* que
les check-runs dont le **nom** contient `advisory`
(`scripts/pr_gate.py::is_advisory`) : c'est le même prédicat que celui de la
voie rapide, et la mesure qui l'a établi est dans son code — un check d'ombre
dont le nom ne portait pas le marqueur entrait dans les rouges du gate et
rendait le gate **requis** rouge (mesure du 2026-08-25, 2 PR bloquées sur
125 portant un check d'ombre). Le test de cette tranche applique le
prédicat du gate lui-même, pas une copie.

**2. Le verdict porte sur l'arbre, pas sur l'isolement.** Le lot mesure
`main` plus les PRs du lot ; le résumé du check-run le dit, et nomme la PR
coupable quand la bissection en a isolé une. Un check-run qui prétendrait
juger la PR seule serait un mensonge : une PR peut être verte en isolement
et rouge dans l'arbre.

**3. Ce qui n'a pas été mesuré ne se présente pas comme rouge.** Seul le
statut `rouge` — la suite rejouée **et** en échec — donne `failure`. Une
dépendance manquante, une sélection vide, un sélecteur en échec, une PR de
fork : `neutral`, `skipped`, ou **pas de check-run du tout** avec le motif
nommé. Une PR de fork n'a pas de tête dans le dépôt de base : l'API Checks
ne peut pas y porter de check-run, et le motif le dit.

**La troncature du pool est portée dans le résumé.** Quand la population
inspectée atteint le plafond de lecture (`pool_inspecte == limit`), la
sélection peut être **partielle**, et un lot « vert » ne dit rien des PRs
non inspectées. Le plan du lot emporte donc son plafond et son droit de
troncature, et le check-run le dit sur la PR — pas seulement dans le rapport
du run.

L'**écriture** passe par l'organe natif `scripts/ci/fast_lane.py`
(`emit_check_run`) : le dépôt avait déjà la fonction qui poste un check-run
sur une tête de PR, avec le même `gh api --input -`. Ce module ne fait que
décrire le verdict du lot.

**Un check-run par tête, et un seul.** Deux publications de même nom sur la
**même** tête ne s'empilent pas : la seconde **remplace** la première
(mesuré au témoin : deux publications sur une même tête → un seul check-run
survivant, celui de la dernière). Deux têtes distinctes portent chacune leur
check-run (mesuré : un `success` sur la tête du témoin et un `neutral` sur
la tête précédente coexistent). Un lot rejoué sur la même tête met donc son
verdict à jour, au lieu d'empiler des verdicts contradictoires sur la PR.

### La porte du lot : l'APPROVE du coordinateur à la tête exacte

Une PR n'occupe un créneau que si elle porte l'**APPROVE du coordinateur**
(`myia-ai-01`) **à sa tête exacte**. C'est la porte que le merge franchit :
le lot mesure ainsi la durée du lot **réel**, celui qui mergera.

Un `LGTM` dans le corps d'une review Hermes n'est **pas** une approbation —
c'est un avis, pas la porte. Le verdict de revue est toujours lu et affiché
dans le rapport (il informe sur l'état de la file), mais il ne sélectionne
plus.

L'approbation vaut pour la tête qu'elle couvre : une APPROVE posée sur une
tête qui a bougé depuis ne couvre plus le contenu qui mergera. Et sur une
même tête, c'est la **dernière** review du coordinateur qui fait foi — une
APPROVE suivie d'une `CHANGES_REQUESTED` referme la porte.

### La population du lot, et l'absence de plafond

La population candidates est celle que le **merge** touche : les PRs
ouvertes que le coordinateur a **relues** (`--search "reviewed-by:myia-ai-01
sort:created-asc"`), les plus anciennes d'abord.

Le lot n'a **pas de plafond par défaut**. Un plafond appliqué *après* la
porte ne fait que retrancher des PRs que le merge mergera : la liste
courte des 15 PRs les plus anciennes decidait du lot, alors que la
population utile était plus large — mesure du 2026-11-09 sur le pool réel :
**16 PRs inspectées, 5 sélectionnées**, 11 exclusions nommées. Sous la
liste tronquée et le plafond de 4, la même mesure donnait 1 PR
sélectionnée sur 15 : c'était la troncature et le plafond qui décidaient,
pas la porte.

Le détail (verdict, approbation) est lu **par PR** — une requête GraphQL
par PR — donc élargir la population ne coûte pas une requête unique, elle
coûte une requête de plus par PR.

`--max-prs` reste disponible pour un lot volontairement restreint ; `0`
signifie « pas de plafond ».

### L'environnement : celui de la suite, pas une liste recopiée

Le lot installe son environnement avec le **même script** que la jambe
`Scripts Tests` : `scripts/ci/install_scripts_tests_deps.sh`. Le bloc
d'installation a été extrait **verbatim** de `scripts-tests.yml` le
2026-11-09, et les deux jambes l'appellent.

C'est ce qui rend les durées comparables. Une liste de dépendances minimale
donne des durées qu'on ne peut comparer à rien : une dépendance manquante
rend la PR « non mesurable » au lieu de la faire échouer.

De même, les **cibles** de la suite ne sont pas recopiées dans l'organe :
elles sont **lues** dans le bloc pytest de `scripts-tests.yml`
(`heavy_batch.py::suite_lourde_cible`). Le lot joue donc exactement les
chemins de la jambe, avec les mêmes options pytest (`-n 4 --dist loadscope
--tb=short -q`). Un bloc de cible introuvable rend la mesure
**non mesurable** — jamais un lot vide présenté comme un lot vert.

### La cadence — quatre créneaux par jour

| Créneau (UTC) | Secours (UTC) | Échéance de fin |
|---|---|---|
| 04:17 | 04:47 | 10:00 |
| 10:17 | 10:47 | 13:00 |
| 16:17 | 16:47 | 21:30 |
| 21:17 | 21:47 | 00:00 (le lendemain) |

Les créneaux sont placés **hors des deux pics mesurés** de la file CI
(13:00-15:00Z et 00:00-02:00Z) : le lot occupe le parc quand celui-ci
respire. Le créneau du mardi 02:30 reste celui du pilote — les deux
n'empruntent pas la même nuit.

**Pourquoi un cron de secours.** Sous la charge de la flotte, GitHub retarde
ou abandonne des événements `schedule`. Sur les anciens crons (minute :30),
le lot a démarré à 10:16, 12:49, 21:51, 01:19, 11:58, 22:51, 02:20 et 12:59
entre le 10/11 et le 12/11 : deux lots par jour au lieu de quatre, avec 1,5 à
5 h de retard, et aucun lot parti des créneaux 04:30 et 16:30. Chaque créneau
est donc doublé d'un cron trente minutes plus tard. Le job `lot-gate` saute ce
secours quand un lot planifié a déjà été servi depuis moins de 150 min : son
job `lot` a réussi, ou tourne encore. Un `workflow_dispatch`, l'avance du
coordinateur, n'est jamais dédoublonné. Si l'API ne répond pas, la garde
laisse passer : un lot en double coûte un runner hébergé, un lot perdu coûte
une journée.

### Un seul lot à la fois

Le groupe de concurrence `slow-lane-lot` est partagé par les quatre
créneaux, et `cancel-in-progress` est **faux** : un créneau qui déborde
**attend** le lot en cours au lieu de l'annuler. Une annulation automatique
produirait un rapport partiel présenté comme un rapport complet. Le pilote
habite un groupe distinct (`slow-lane-pilot`) : il ne retarde pas un lot, et
un lot ne retarde pas le pilote.

### L'arbre d'intégration

Le lot joue deux temps. D'abord, chaque PR du lot est mesurée **isolément**
sur sa ref de fusion, avec les tests **sélectionnés par chemin** (la mesure
fine de l'étage 1). Ensuite — c'est la mesure qui compte — il construit
l'arbre **qui va réellement atterrir** — `main` plus les PRs du lot, dans
l'ordre du lot — et joue **la suite complète** dessus.

C'est la seule forme qui supprime **par construction** la classe de #24821
(`main` rouge après le merge de PRs vertes à leur propre tête, sur un `main`
qui avait bougé) : on ne la rattrape plus après coup, on ne la crée plus.

Un conflit d'intégration est **nommé** (le numéro de la PR) et la PR sort de
l'arbre — elle n'est pas testée du tout, et elle n'est pas réputée verte
pour autant.

### La bissection

Quand l'arbre est rouge, la PR fautive est isolée par **`git bisect run`** —
l'organe natif, pas une recherche maison. Chaque fusion de l'arbre porte le
sujet `lot: PR #N` : le commit que la bissection isole est donc rattaché à
sa PR, et le coupable est **nommé** dans le rapport.

Le rattachement se fait par deux lectures, dans cet ordre : le sujet du
commit s'il porte la marque, sinon **l'ascendance** (la première fusion du
lot dont le commit contient le coupable). La seconde lecture est celle de
confiance : elle ne dépend d'aucun nom, et elle reste juste quand la
référence de fusion d'une PR est elle-même un commit de fusion — ce que
GitHub produit.

Un `ModuleNotFoundError` rend la mesure **indéterminée** (code 125), jamais
rouge : une dépendance absente n'est pas une régression.

### Avancer un test

Le coordinateur déclenche l'étage 2 sur **une seule** PR, tout de suite, par
`workflow_dispatch` avec l'entrée `pr`. Cette PR prend la place du lot.

La **garde fork n'est pas levée** par cette désignation : une PR de fork
n'entre dans le lot qu'après l'APPROVE du coordinateur, parce que le job
exécute du code de PR. Le refus est explicite et le lot ne peut pas se
présenter comme vert.

### Permissions et runner

`contents: read` et `pull-requests: read`, et rien d'autre — sauf le job du
lot, qui demande en plus `checks: write` depuis la tranche 2 : il publie
un check-run par tête du lot. Les permissions d'un job **remplacent** celles
du workflow, donc les deux lectures sont rédéclarées au niveau du job.
Aucun `secrets.*` n'est lu : le job exécute du code de PR, sur un runner
**hébergé** par GitHub — hors du parc de la flotte, et sans rien pouvoir
lire de sensible. Une jambe self-hosted exigerait une entrée dans
`SELF_HOSTED_WORKFLOW_ALLOWLIST`, qui est une politique d'owner : le
coordinateur, pas la lane.

## Hors scope

- Ne pas toucher `PR gate` lui-meme.
- Ne pas toucher la protection de branche (injoignable sans droit admin).
- Ne pas basculer la voie rapide hors ombre (c'est #11835 volet 1, tranche
  distincte et adjugee separement).

## Voir aussi

- #11835 — voie rapide (pilote ombre)
- #12856 — slow-lane (tranche 1 : pilote ; tranche 2 : CodeQL)
- `scripts/ci/measure_runner_demand.py` — instrument de mesure (run/job-level ;
  pour le tri des candidats, lui préférer l'instrument etape-level du
  commentaire ai-01 2026-08-24 sur #12856)
