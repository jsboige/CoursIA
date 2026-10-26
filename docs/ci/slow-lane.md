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

```
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
  CI** : run `40328940542` (2026-10-25), les deux jobs `success` ;
- **le code de sortie de l'étape vaut celui de la suite** (`exit 1`), pour que
  le critère d'acceptance #12856-4 (« la voie lente rougit sur un vrai
  défaut ») soit atteignable ;
- **`timeout-minutes` de 15 à 60**, comme `ict-tests.yml` : durées mesurées
  le 2026-10-26 (runs `40333089185` et `40328940542`), **7 min 54 s** pour la
  jambe `tests/` et **10 min 26 s** pour la jambe `ict/tests/`, plus ~2 min
  d'installation. À 15 min, le correctif de collecte aurait seulement
  transformé le faux vert en timeout rouge.

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
#12840 et #22196 : **54 ajoutés, 30 retirés**.

**Pourquoi la tranche 2 n'a rien réduit, et pourquoi ce n'était pas un
accident.** Le déclencheur `pull_request` de CodeQL **ne vit dans aucun
fichier du dépôt** : il est dans le *default setup* de GitHub (settings du
dépôt), et sa suppression est un **bascule admin** — c'est dit dans
l'en-tête du workflow `codeql.yml` de #22553, et le contrôle positif du
2026-09-05 publie déjà ce verrou (« le rejet SARIF est le verrou fail-closed
qui force la coordination »). Tant que la bascule n'est pas faite, **les
analyses per-PR continuent de tirer** et le compte ne baisse pas.

Une part de la hausse est en outre une ** granularité**, pas du travail
supplémentaire : la voie rapide est passée d'un check agrégé
(`Fast lane (ombre) -- 21 gardes, 1 checkout`) à un check **par garde**
(`fast-lane (ombre): perimeter-review-guard`, `… : solution-leak-guard`,
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
