# Actuariat — tarifer, mutualiser, capitaliser, souscrire

[↑ Théorie de la décision](../README.md)

En assurance, une loi a posteriori n'est pas un aboutissement : elle devient une prime, un capital immobilisé, une décision d'accepter ou de refuser un candidat. Cette sous-série applique la théorie de la décision bayésienne à ce métier. Elle suit les questions d'un assureur dans l'ordre où elles se posent : à quel prix couvrir un risque, comment tarifer des segments dont les historiques sont inégaux, quel poids donner à l'expérience propre d'un groupe, combien de capital immobiliser pour traverser les mauvaises années, et quand payer pour mieux connaître un candidat.

Les données sont simulées, à vérité connue : c'est ce qui permet de mesurer l'erreur d'un tarif. Deux portefeuilles reviennent d'un carnet à l'autre, une assurance automobile aux sinistres fréquents et légers et une responsabilité civile médicale aux sinistres rares et lourds, avec un jeune cabinet dont l'historique tient en trois années. La sous-série s'adresse à des étudiants de master à l'aise avec l'inférence bayésienne. Aucune connaissance actuarielle n'est supposée : chaque terme du métier est défini à sa première apparition. Elle prolonge la progression [DecPyMC](../DecPyMC/README.md), dont le dernier carnet, [DecPyMC-08](../DecPyMC/DecPyMC-08-Actuariat-Capstone.ipynb), sert de porte d'entrée.

## Comment lire ce README — Découverte

Le principe [« Choisir sa vitesse de lecture »](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture) distingue le parcours principal, les approfondissements et les prolongements de recherche.

- **Vous découvrez** : suivez le parcours principal dans l'ordre des numéros. Actuariat-01 pose le vocabulaire et les deux portefeuilles que les carnets suivants réutilisent.
- **Vous creusez un palier** : la section « Approfondissements » explique l'ordre des carnets, relie chaque question à son pendant en théorie des jeux et liste les exercices.
- **Vous cherchez la recherche en cours** : « Pour aller plus loin » dit ce que les modèles laissent de côté et où se trouve la formalisation Lean de la prime.

## Parcours principal — Master

| # | Notebook | Ce qu'on y apprend | Public | Pour approfondir |
|---|---|---|---|---|
| 01 | [Actuariat-01 — Du risque à la prime](Actuariat-01-Prime-Pure-Chargement.ipynb) · [C#](Actuariat-01-Prime-Pure-Chargement-CSharp.ipynb) | Trois primes que le vocabulaire confond : la prime de risque d'un décideur averse, la prime pure $\pi = \lambda\,\mathbb{E}[S]$ et la prime commerciale $P = \pi/(1-c)$. Les deux portefeuilles donnent des primes pures de `1439` et `8241` euros par an, avec des formes de risque opposées. Le régime bayésien montre que la prime est elle-même incertaine, et bien plus dispersée avec trois ans d'historique qu'avec trente. Le chargement de sécurité se calibre alors sur un quantile de la prime. Une simulation d'antisélection montre un portefeuille tarifé au prix moyen perdre ses bons risques : leur part tombe de `0.500` à `0.025` pendant que la prime moyenne monte. | Master : utilité espérée, inférence bayésienne. Mesures du carnet Python. Le C# rejoue le protocole avec son propre générateur. Outils C# : Infer.NET, MathNet et PyMC via Python.NET. | Exercices : portefeuille habitation, chargement au quantile 80, décision sur trois profils. |
| 02 | [Actuariat-02 — Fréquence × sévérité hiérarchique](Actuariat-02-Freq-Sev-Hierarchique.ipynb) · [C#](Actuariat-02-Freq-Sev-Hierarchique-CSharp.ipynb) | Un portefeuille automobile découpé en segments d'expositions très inégales, et trois façons de les tarifer : chaque segment seul, tout le monde au tarif moyen, ou un modèle hiérarchique qui mutualise partiellement. L'erreur quadratique relative sur la prime pure vaut `0.3058`, `0.5276` puis `0.2493`. Le lissage suit la taille : la part de signal propre va de `0.493` pour un petit segment à `0.839` pour un grand, corrélée à `0.903` avec l'exposition. Le tarif unique sous-tarife précisément les segments les plus chers. Quand l'hétérogénéité réelle grandit, il se dégrade vite alors que le modèle hiérarchique apprend lui-même combien lisser. | Master : modèles hiérarchiques, MCMC. Mesures du carnet Python. Le C# conserve les budgets et utilise son propre générateur. Outils C# : MathNet, PyMC et ArviZ via Python.NET. | Exercices : le petit segment, coût d'une mutualisation aveugle, hausse de la fréquence collective. |
| 03 | [Actuariat-03 — Crédibilité de Bühlmann–Straub](Actuariat-03-Actuarial-Credibility.ipynb) | La réponse classique au même problème, sur la fréquence seule. Le facteur de crédibilité $Z_i = w_i/(w_i + K)$ pondère l'expérience du groupe par celle du portefeuille. Sur cinq groupes d'exposition 50 à 5000, la constante vaut `250.69` et $Z_i$ va de `0.166` à `0.952`. Le carnet compare quatre estimateurs : par groupe, collectif, crédibilité classique et modèle hiérarchique PyMC. Les deux derniers divergent sur le plus petit groupe (`0.098701` contre `0.083332`) et se rejoignent sur les grands. Le modèle bayésien apporte en plus un intervalle. | Master : estimation bayésienne. Outils : PyMC, ArviZ, numpy, pandas. | Exercices : calcul direct de $Z$ et de la prime, sensibilité à l'exposition, groupe tenu à part. |
| 04 | [Actuariat-04 — Ruine et capital](Actuariat-04-Ruine-Lundberg.ipynb) | Le processus de surplus de Cramér–Lundberg, simulé sur dix ans. À chargement et capital relatif égaux, la probabilité de ruine vaut `0.0000` pour l'automobile et `0.0442` pour la responsabilité civile : la forme du risque décide, pas son espérance. L'inégalité de Lundberg est confrontée à la simulation. Sur une sévérité exponentielle elle tient ; sur une sévérité lognormale son hypothèse manque et la borne ne s'applique plus. Enfin l'incertitude sur la fréquence est propagée vers la ruine : pour le jeune cabinet, la probabilité de ruine à cinq ans devient une loi, de quantiles `0.255`, `0.500` et `0.833`. Le carnet compare alors capital immobilisé et réassurance en quote-part. | Master : processus de Poisson composé, simulation Monte Carlo. Outils : PyMC, ArviZ, numpy, scipy. | Exercices : capital doublé, capital au quantile 95, choix du levier pour un objectif de ruine. |
| 05 | [Actuariat-05 — Valeur de l'information en souscription](Actuariat-05-Valeur-Info-Souscription.ipynb) | Faut-il payer pour mieux connaître un candidat ? L'information parfaite vaudrait `558` euros par candidat : c'est le plafond de toute dépense. Trois signaux imparfaits sont évalués contre leur coût. Le questionnaire, pourtant corrélé au risque, vaut `0.0` parce qu'il ne change aucune décision. L'examen médical vaut `310.8` pour un coût de `90.0`. La télématique vaut `478.3` pour un coût de `500.0`. La calibration des signaux est ensuite propagée avec PyMC : la valeur d'un signal devient une loi, et l'achat une décision robuste ou incertaine. Le carnet retourne enfin la situation : quand l'assuré paie lui-même le signal, les types se séparent sans que l'assureur décide. | Master : valeur de l'information, règle de Bayes. Outils : PyMC, ArviZ, numpy, pandas. | Exercices : plafond selon la part de mauvais risques, nouveau signal, coût séparateur maximal. |

## Approfondissements — Master

### Pourquoi cet ordre

L'ordre des carnets est celui du métier, et chaque palier répond à une limite du précédent.

- **Tarifer (01).** La prime pure est une espérance. Elle ne dit rien de la dispersion, que le chargement doit couvrir.
- **Modéliser le portefeuille (02).** Une prime par portefeuille ne suffit pas quand les segments diffèrent. Le modèle hiérarchique rend le tarif estimable segment par segment.
- **Mélanger l'individuel et le collectif (03).** La crédibilité donne la version déterministe du même compromis : un poids fixé par l'exposition, là où le modèle hiérarchique l'apprend.
- **Capitaliser (04).** Un chargement calibré sur un quantile laisse des années en perte. Le capital les absorbe, et la probabilité de ruine dit combien en immobiliser.
- **Acquérir de l'information (05).** Provisionner pour une incertitude que l'on pourrait acheter coûte deux fois. La valeur de l'information dit quand le test vaut son prix.

Les carnets 01, 02 et 03 se lisent à la suite. Le carnet 04 ne demande que le 01. Le carnet 05 reprend l'antisélection du 01 et l'incertitude d'estimation du 04, avec le cadre de [DecPyMC-05](../DecPyMC/DecPyMC-05-Value-Information.ipynb).

### La même assurance vue des deux côtés du marché

La sous-série regarde l'assurance du côté de l'assureur. La série [Théorie des jeux](../../../GameTheory/README.md) regarde le même marché du côté de l'équilibre entre assurés et assureurs.

| Question | Côté assureur, dans cette sous-série | Côté marché, en théorie des jeux |
|---|---|---|
| Antisélection | La spirale du carnet 01, puis la valeur d'un signal de souscription (05) | Les modèles d'information asymétrique, dont le screening de Rothschild–Stiglitz : [GameTheory-17b](../../../GameTheory/GameTheory-17b-Asymmetric-Information-Python.ipynb) |
| Tarif | Prime pure et chargement (01) | L'équilibre de marché lu comme un bilan d'espérances : [GameTheory-17f](../../../GameTheory/GameTheory-17f-Market-to-Balance-Sheet-Python.ipynb) |
| Mutualisation | Modèle hiérarchique et crédibilité (02, 03) | Les jeux coopératifs et la valeur de Shapley : [GameTheory-15](../../../GameTheory/GameTheory-15-CooperativeGames-Python.ipynb) |

### Exercices des carnets

- **Actuariat-01** : tarifer un portefeuille habitation, calibrer le chargement sur le quantile 80, décider pour trois profils de risque.
- **Actuariat-02** : mesurer l'effet du modèle hiérarchique sur le plus petit segment, trouver l'hétérogénéité à partir de laquelle le tarif unique devient le pire choix, étudier une hausse de la fréquence collective.
- **Actuariat-03** : calculer à la main le facteur de crédibilité d'un nouveau segment, tracer $Z$ en fonction de l'exposition, réestimer le modèle en tenant un groupe à part.
- **Actuariat-04** : estimer la ruine quand le capital double, dimensionner le capital du jeune cabinet sur le quantile 95, choisir entre capital et réassurance pour un objectif de ruine donné.
- **Actuariat-05** : tracer le plafond de valeur selon la part de mauvais risques, évaluer un score fondé sur des données ouvertes, comparer trois formules de boîtier télématique.

Les cellules d'exercice s'exécutent sans erreur tant qu'elles ne sont pas complétées.

## Installation — pratique, tous niveaux

Les carnets tournent sur le noyau `python3`, sans GPU. Ils utilisent PyMC et ArviZ, avec numpy, scipy, pandas et matplotlib.

```bash
python -m pip install -r MyIA.AI.Notebooks/Probas/requirements.txt
python -m pip install jupyterlab ipykernel
jupyter lab MyIA.AI.Notebooks/Probas/DecisionTheory/Actuariat/Actuariat-01-Prime-Pure-Chargement.ipynb
```

PyMC 6 et ArviZ 1 demandent Python 3.12 ou plus récent : le fichier [requirements.txt](../../requirements.txt) explique pourquoi. Les tirages sont semés et l'échantillonnage reste court, de quelques secondes à quelques dizaines de secondes par modèle.

## Pour aller plus loin — Recherche

**Ce que les modèles laissent de côté.** Les carnets le disent eux-mêmes. La crédibilité du carnet 03 ignore les covariables et n'est pas validée hors échantillon. Le carnet 02 signale un paramètre de sévérité mal mélangé par l'échantillonneur. Le carnet 04 rappelle qu'une borne dont l'hypothèse échoue n'est pas fausse mais inapplicable, et que la simulation reste l'outil qui dimensionne le capital.

**De la décision ponctuelle à la décision répétée.** Le choix entre capital et réassurance du carnet 04 et l'achat d'un signal du carnet 05 se révisent à mesure que l'expérience s'accumule. La structure de ces politiques est traitée dans [DecPyMC-07](../DecPyMC/DecPyMC-07-Sequential.ipynb).

**Formalisations Lean.** Le lake [`decision_theory_lean/`](../decision_theory_lean/) contient un module `Coherence/Premium` qui relie la cohérence des croyances à la prime. Le carnet [DecInfer-01c](../DecInfer/DecInfer-01c-Lean-Coherence.ipynb) en lit les énoncés et les rattache à cette sous-série.

## Ressources — tous niveaux

- [DecPyMC-02](../DecPyMC/DecPyMC-02-Utility-Money.ipynb) pour l'aversion au risque et la prime de risque, [DecPyMC-05](../DecPyMC/DecPyMC-05-Value-Information.ipynb) pour la valeur de l'information : les deux prérequis de théorie.
- [La série PyMC](../../PyMC/README.md) pour les fondations d'inférence bayésienne.
- Chaque carnet se termine par sa bibliographie : théorie du risque et de la ruine, théorie de la crédibilité, modèles de sinistres, économie de l'information.

[↑ Théorie de la décision](../README.md) · [Série Probas](../../README.md) · [Catalogue du dépôt](../../../../COURSE_CATALOG.generated.md)
