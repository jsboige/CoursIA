# Slow lane (voie asynchrone) — tranche 1 #12856

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
2. Le workflow candidat a ete instrumente au niveau JOB
   (`scripts/ci/measure_runner_demand.py` avec fenetre 24 h, mesure
   `started_at → completed_at`, **pas** `run_started_at → updated_at` qui
   inclut l'attente en file — cf. piege consigne dans le body de #12856).
3. Le mouvement retire le trigger `pull_request` **dans le meme commit** que
   l'ajout a la voie lente (cf. acceptance #12856-2).
4. La mesure apres-mouvement compare la meme PR temoin avant/apres.

### Candidats a instruire (liste de depart, a confirmer par mesure job-level)

- **`ict-tests.yml`** : ~3-5 min runner, 746 + 42 items, dejà instrumente.
- **CodeQL `Analyze` x4** : 4 jobs lourds sur PR notebook sans ligne C#/JS.
  Geres par GitHub Security tab, pas par un workflow du repo — mouvement
  indirect (desactiver au niveau repo + ajouter un slow-lane custom).
- **Quarto** (`quarto-pages-deploy.yml`) : ~3-8 min, dejà instrumente.
- **`lean-build.yml`** et les ~30 lakes Lean : tres lourds quand ils tirent,
  filtres par `paths:`. A instruire sans regresser la couverture.

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
- #12856 — slow-lane (cette PR, tranche 1)
- `scripts/ci/measure_runner_demand.py` — instrument de mesure
