# Actuariat — la sous-série assurance de la théorie de la décision (T1-T5)

[← Série DecPyMC](../DecPyMC/README.md) · [Arc DecisionTheory](../README.md) · [Index Probas](../../README.md)

L'assurance est le **métier** de la décision bayésienne : un posterior n'y est pas une fin, c'est une **prime**, un **capital**, une **décision de souscription**. Cette sous-série descend l'ancienne jambe actuarielle de la série [`DecPyMC/`](../DecPyMC/README.md) (ex-notebooks 8 à 12) en un dossier dédié, régraduée **T1 → T5** (EPIC [#12904](https://github.com/jsboige/CoursIA/issues/12904), descente arbitrée [#14873](https://github.com/jsboige/CoursIA/issues/14873)). Le capstone [DecPyMC-08 — Actuariat Capstone](../DecPyMC/DecPyMC-08-Actuariat-Capstone.ipynb) en est l'**escalier** : il présente la sous-série, mesure sa surface, et laisse le lecteur décider s'il entre.

## Pourquoi une sous-série

Trois raisons, celles de la doctrine de gradation ([#5081](https://github.com/jsboige/CoursIA/issues/5081)) :

1. **L'objet change.** DecPyMC 1-7 traite de la décision *en général* (utilité, information, séquence). T1-T5 traite d'un **métier** : chaque notebook y répond à une question d'assureur — tarifer, provisionner, mutualiser, capitaliser, souscrire.
2. **La profondeur change.** Les modèles deviennent hiérarchiques (fréquence × sévérité, crédibilité), les distributions calculées (ruine), les décisions commerciales (chargement, valeur d'information en souscription).
3. **Le public change.** Un lecteur venu du métier peut entrer par T1 et remonter vers DecPyMC-2 (utilité) ou DecPyMC-5 (EVPI) au besoin — la série mère garde son escalier au slot 08.

## L'escalier T1-T5

| # | Notebook | Durée | Ce qu'il apporte | Suppose |
|---|----------|-------|------------------|---------|
| T1 | [Actuariat-01-Prime-Pure-Chargement](Actuariat-01-Prime-Pure-Chargement.ipynb) | 45 min | Du risque à la prime : prime pure, chargement, prime commerciale — trois régimes (fréquentiste, bayésien, commercial) que la théorie mélange | [DecPyMC-2](../DecPyMC/DecPyMC-2-Utility-Money.ipynb) |
| T2 | [Actuariat-02-Freq-Sev-Hierarchique](Actuariat-02-Freq-Sev-Hierarchique.ipynb) | ~50 min | Fréquence × sévérité hiérarchique : le partial pooling en assurance, la structure de crédibilité avant la crédibilité | T1 |
| T3 | [Actuariat-03-Actuarial-Credibility](Actuariat-03-Actuarial-Credibility.ipynb) | 20-30 min | Crédibilité actuarielle de Bühlmann–Straub : pondérer l'expérience individuelle contre celle du portefeuille | T2 |
| T4 | [Actuariat-04-Ruine-Lundberg](Actuariat-04-Ruine-Lundberg.ipynb) | 45 min | Ruine et capital : processus de Cramér–Lundberg, inégalité de Lundberg, la prime comme garde-fou | T1 |
| T5 | [Actuariat-05-Valeur-Info-Souscription](Actuariat-05-Valeur-Info-Souscription.ipynb) | ~45 min | Valeur de l'information en souscription : quand un test vaut son prix (EVPI/EVSI appliqués au métier) | [DecPyMC-5](../DecPyMC/DecPyMC-5-Value-Information.ipynb), T1 |

**Durée totale** : ≈ 3 h 30 – 4 h (durées déclarées dans les carnets ; T2 et T5 reprises de la série mère).

**Pourquoi cet ordre.** La régraduation T1→T5 réordonne l'ancienne jambe (8→12) en un **arc de métier** : on apprend d'abord à **tarifer** (T1 : la prime), puis à **modéliser le portefeuille** (T2 : la structure fréquence × sévérité qui rend le tarif estimable), puis à **mélanger l'individuel et le collectif** (T3 : la crédibilité, consommée par T2), puis à **capitaliser** (T4 : la ruine, qui juge le tarif), et enfin à **décider d'acquérir de l'information** (T5 : la souscription, qui boucle sur la théorie de l'information de la série mère). La crédibilité (T3) suit T2 parce que la hiérarchie fréquence × sévérité en est le cadre naturel — l'ordre 8→12 d'origine plaçait la crédibilité avant la structure qui la motive.

## Correspondance avec l'ancienne numérotation

| Ex- (série mère) | Nouveau | 
|---|---|
| DecPyMC-9-Prime-Pure-Chargement | **T1** — Actuariat-01 |
| DecPyMC-12-Freq-Sev-Hierarchique | **T2** — Actuariat-02 |
| DecPyMC-8-Actuarial-Credibility | **T3** — Actuariat-03 |
| DecPyMC-10-Ruine-Lundberg | **T4** — Actuariat-04 |
| DecPyMC-11-Valeur-Info-Souscription | **T5** — Actuariat-05 |

## Ce que cette sous-série suppose

- **Côté théorie** : l'utilité espérée et l'aversion au risque ([DecPyMC-2](../DecPyMC/DecPyMC-2-Utility-Money.ipynb)), la valeur de l'information ([DecPyMC-5](../DecPyMC/DecPyMC-5-Value-Information.ipynb)) pour T5. Le capstone [DecPyMC-08](../DecPyMC/DecPyMC-08-Actuariat-Capstone.ipynb) suffit pour entrer à T1.
- **Côté outillage** : PyMC + ArviZ (kernel `python3`), mêmes exigences que la série mère — chaque carnet s'exécute de bout en bout, exercices non complétés compris (règle C.1 du dépôt).
- **Côté miroir** : la Théorie des Jeux regarde le même métier du côté **marché** (GT-17a/17b : antisélection, screening) quand T1-T5 le regarde du côté **assureur** — la filiation est citée dans chaque carnet.

## Miroir GameTheory — la même assurance, deux côtés du marché

| Question | Côté assureur (cette sous-série) | Côté marché ([GameTheory](../../../GameTheory/README.md)) |
|---|---|---|
| Antisélection | La souscription et la valeur d'information (T5) | Rothschild–Stiglitz, screening (GT-17a/17b) |
| Tarif | Prime pure et chargement (T1) | Équilibre de marché, contrats concurrents |
| Mutualisation | Hiérarchie et crédibilité (T2, T3) | Jeux coopératifs, Shapley (GT-15) |

## Pour aller plus loin

- [Capstone DecPyMC-08](../DecPyMC/DecPyMC-08-Actuariat-Capstone.ipynb) — l'escalier, depuis la série mère
- [Lake `decision_theory_lean`](../decision_theory_lean/) — la couche de certification Lean de l'arc décision
- [Corpus bayésien PyMC](../../PyMC/README.md) — les fondations d'inférence
