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

## Tranche 2 — premier mouvement reel (a venir)

Conditions a remplir AVANT de deplacer un workflow dans la voie lente :

1. La tranche 1 a ete observee en production **>= 1 semaine**, sans faux
   vert ni faux rouge, avec verdict publie.
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
