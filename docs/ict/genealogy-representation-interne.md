# ICT — 4e fil de lecture : le problème de la représentation interne (généalogie de `p̂`, ICT-10 → ICT-17)

> **Statut.** Document de synthèse transversal, grade **C-documentaire** (consolidation, pas de nouveau dispatch). Consolide un **quatrième fil de lecture** de la série ICT, à côté des trois déjà documentés dans [`synthese-invariants-dissociations-obstructions.md`](synthese-invariants-dissociations-obstructions.md) : Grothendieck (invariants), Schmidhuber (dissociations), Thom + Grothendieck (obstructions). Le **quatrième fil** est celui du **problème de la représentation interne** : la généalogie successive de `p̂` à travers les notebooks ICT-10 → ICT-17.
> **Objet.** Documenter la **famille successive** des objets représentationnels mesurés dans la série — chacun répondant à une insuffisance du précédent — et la distinguer explicitement (a) de la *prégnance thomienne* (cf. rectification A1 de [#7733](https://github.com/jsboige/CoursIA/issues/7733), propagée par PR #7889) et (b) du *global workspace* (Dehaene/Baars, ICT-24). Le document **ne propose pas de théorie unifiée** : il décrit une généalogie, marque les ponts qui *résistent* à un transport formel, et se tient à distance des unifications prématurées (cf. l'avertissement méthodologique de [`synthese-invariants-dissociations-obstructions.md`](synthese-invariants-dissociations-obstructions.md#ce-que-ce-document-nest-pas)).
> **Discipline.** Consolidation grade C. Aucune nouvelle dépendance expérimentale n'est créée. Les livrables existants — notebooks ICT-10/12/14/15/16/17 et leurs sorties mesurées — sont ré-organisés selon un axe chronologique-conceptuel (le passage d'un représentant ponctuel à un état causal prédictif complet) ; aucun claim n'est ajouté, aucune mesure n'est revisitée. Issue-source : [#7735](https://github.com/jsboige/CoursIA/issues/7735). See [#4588](https://github.com/jsboige/CoursIA/issues/4588). Part of [#7396](https://github.com/jsboige/CoursIA/issues/7396).

## Pourquoi un quatrième fil

La grille 3-régimes ([`synthese-invariants-dissociations-obstructions.md`](synthese-invariants-dissociations-obstructions.md)) est **transversale** : elle dit, pour une même trajectoire, *quelle question on est en train de poser*. Elle ne dit pas *ce qui se transforme à l'intérieur du système* quand celui-ci devient capable d'anticiper. Or la série ICT a, à partir de ICT-10, fait entrer dans son instrumentation une **grandeur nouvelle** — un *représentant interne* — qui n'existait pas dans les strates 1 et 2. Cette grandeur n'est pas un nombre parmi d'autres : c'est un **objet d'une espèce différente**, qui se transforme qualitativement au fil des notebooks, et dont la transformation est *elle-même* un objet d'étude.

Le quatrième fil est donc **diachronique** (au contraire de la grille 3-régimes qui est synchronique) : il raconte comment un système qui extrapole ponctuellement un signal devient un système qui *possède un état causal résumant son passé prédictif*. Cette transformation est l'arrière-plan silencieux des régimes 1, 2 et 3 : sans représentant interne, point de dissociation entre `p̂` et persistance (régime 2, ICT-10) ; sans précision adaptative, point de *free energy* (régime 1 ICT-14) ; sans compression du substrat, point d'ε-machine (ICT-17). Le quatrième fil **alimente** la grille 3-régimes sans s'y réduire.

## La généalogie : six maillons

Chaque maillon répond à une **insuffisance du précédent**, repérée empiriquement dans la série. La généalogie est **chronologique** (ordre des notebooks dans la série) et **conceptuelle** (chaque maillon subsume ou généralise le précédent). Elle ne suppose aucun transport formel d'un objet à l'autre — elle marque les **ruptures** autant que les continuités (cf. garde-fou 1 ci-dessous).

### Maillon 1 — ICT-10 : `p̂` comme représentation ponctuelle

[`ICT-10-CatastropheGrammar`](../../MyIA.AI.Notebooks/IIT/ICT-Series/ICT-10-CatastropheGrammar.ipynb) (charnière strate 2→3, lacet de prédation) mesure pour la première fois un **représentant interne** `p̂` : extrapolation à vitesse constante à partir du signal observé, vitesse lissée par moyenne mobile exponentielle (EMA). Le proxy est **scalaire et instantané** — `p̂` à l'instant `t` est un point, pas une distribution. Évaluation : erreur de prédiction + corrélation au futur de la proie, contre trois baselines adverses (persistance, AR(1), moyenne mobile in-sample). Verdict honnête déjà documenté (ICT-0-Framing.md ligne 454-457 et [matrice dissociations](../../MyIA.AI.Notebooks/IIT/ICT-Series/assets/readme/MANIFEST.md)) : `p̂` *gagne* en anticipation sur trajectoire lisse, *perd* sur dérive/créneau. **Régime-dépendance**, pas avantage universel.

**Note de rigueur (audit #4, [#7733](https://github.com/jsboige/CoursIA/issues/7733) A1).** `p̂` est un **anticipateur représentationnel** (sortie d'un algorithme d'extrapolation). Ce n'est **pas** la prégnance thomienne — « fluide invasif qui se propage de forme saillante en forme saillante » (`docs/grothendieckian-lens.md` §3, rectification A1 propagée par PR #7889), *section locale* au sens de Grothendieck, grandeur biologique et transférable. L'identification `p̂ ≡ prégnance` relèverait d'une lecture spéculative des deux côtés. La correspondance **`p̂ ↔ anticipation`** du Ch.2 « Le Langage » de Thom est **nommée** dans la série, pas démontrée.

### Maillon 2 — ICT-12 : `p̂` au service de l'action

[`ICT-12-ValenceFieldsAndAnimats`](../../MyIA.AI.Notebooks/IIT/ICT-Series/ICT-12-ValenceFieldsAndAnimats.ipynb) (strate 3, animats dans un champ de valence) promeut `p̂` de **prédiction** à **contrôle** : l'animat anticipateur vise *où la source sera*, et le verdict compare le gain en capture/fuite au coût en erreurs sur trajectoire erratique. Le maillon 2 ne change pas la *forme* de `p̂` (toujours scalaire instantané) mais change son **rôle** dans la boucle perception-action : `p̂` n'est plus seulement mesuré pour sa qualité prédictive, il est *consommé* par une politique. ICT-12 inaugure aussi l'**opérateur `W`** (workspace, cf. [`docs/ict/dissociations-matrix.md`](dissociations-matrix.md#pourquoi-cette-ossature-4-objets)) au sens où la prédiction devient disponible à la décision — sans être un *workspace* au sens Dehaene/Baars (cf. garde-fou 2).

### Maillon 3 — ICT-14 : la *free energy* attachée à `p̂`

[`ICT-14-FreeEnergySurprise`](../../MyIA.AI.Notebooks/IIT/ICT-Series/ICT-14-FreeEnergySurprise.ipynb) (strate 4) articule `p̂` au formalisme de l'énergie libre : à précision fixe, la *free energy* est une transformée monotone de l'erreur quadratique de `p̂` ; à **précision adaptative**, elle ajoute le **coût d'être surpris** — un terme de précision qui pondère l'erreur par l'inverse de la variance prédite. Le représentant interne cesse d'être un point dans un espace de signaux pour devenir un point dans un espace *(moyenne, précision)* : sa qualité n'est plus seulement *où* il pointe, mais *à quel point il sait qu'il sait*. Le maillon 3 n'est pas un raffinement du maillon 1 : il ajoute une dimension (la précision), même si la dimension n'est pas *encore* mesurée comme telle.

### Maillon 4 — ICT-15 : la surprise transitionnelle

[`ICT-15-IntegratedComplexity`](../../MyIA.AI.Notebooks/IIT/ICT-Series/ICT-15-IntegratedComplexity.ipynb) (strate 4/charnière 5) mesure la surprise transitionnelle sur la TPM hors-échantillon : `p̂` n'est plus seulement jugé *en un point*, mais sur la **distribution** de ses erreurs au cours du temps — un juge qui exige la **régularité statistique** du représentant, pas seulement sa justesse ponctuelle. Le maillon 4 ajoute la dimension *temporelle-collective* : ce qui compte n'est plus l'erreur moyenne, c'est la queue de distribution, le moment où le représentant *se trompe de façon persistante*. ICT-15 fait entrer la convergence Φ/F/K comme *gate* sur trois substrats — c'est l'amorce de la mesure *du représentant par son substrat*, pas seulement *par son signal*.

### Maillon 5 — ICT-16 : la compression K du représentant

[`ICT-16-MDLTwoPartCode`](../../MyIA.AI.Notebooks/IIT/ICT-Series/ICT-16-MDLTwoPartCode.ipynb) (strate 5) fait le pont MDL : la *free energy* est la partie résiduelle du code K (Kolmogorov) + la bosse complexité-entropie. Identité formelle MDL ↔ énergie libre. Le représentant interne gagne ici une **lecture information-théorique** : il est ce qui peut être *décrit* par un code, et le coût de cette description est précisément la *free energy*. Le maillon 5 ne mesure pas K directement (intractable) mais fixe la **borne inférieure** mesurable : la longueur de la description MDL du représentant sur les données observées.

### Maillon 6 — ICT-17 : l'ε-machine de Crutchfield

[`ICT-17-EpsilonMachine`](../../MyIA.AI.Notebooks/IIT/ICT-Series/ICT-17-EpsilonMachine.ipynb) (strate 5, gate Crutchfield vs Hoel) parachève la généalogie : l'**état causal** (au sens de Crutchfield) est l'état qui *résume tout ce que le passé permet de prédire du futur* — c'est l'**estimateur prédictif suffisant**. Le **descendant formel le plus naturel de `p̂` n'est ni le SAE, ni la J-lens, c'est l'état causal prédictif**. Une ε-machine a une propriété que `p̂` n'a pas : son entropie d'excès `E` est **la limite de ce qu'un estimateur de type `p̂` peut capturer** — c'est-à-dire la quantité d'information *structurelle* du signal qui *fuit* un représentant ponctuel, aussi bon soit-il. ICT-17 est le point où le représentant interne cesse d'être un *proxy* (qui approxime le signal) pour devenir un *résumé* (qui capture la structure causale du signal).

### Synthèse de la généalogie

| Maillon | Notebooks | Opération | Grandeur | Limitation mise au jour |
|---|---|---|---|---|
| 1 | ICT-10 | `p̂` scalaire instantané | Point | Pas de distribution, pas d'action |
| 2 | ICT-12 | `p̂` consommé par politique | Point + rôle | Pas de coût d'erreur |
| 3 | ICT-14 | Précision adaptative | Point + variance | Pas de juge temporel |
| 4 | ICT-15 | Surprise transitionnelle | Distribution des erreurs | Pas de borne information-théorique |
| 5 | ICT-16 | MDL ↔ énergie libre | Code du représentant | Pas d'état causal |
| 6 | ICT-17 | ε-machine (Crutchfield) | État causal prédictif | (Plafond atteint : `E` = ce qui *fuit* `p̂`) |

Le mouvement est net : d'un **point dans un espace de signaux** vers un **état dans un espace de causalité**. Le représentant interne *se complexifie* au fil de la série, non pas en accumulant des paramètres mais en changeant de **nature mathématique** (scalaire → scalaire-plus-rôle → scalaire-plus-variance → distribution → code → état causal).

## Deux garde-fous d'honnêteté (audit #4)

### Garde-fou 1 — Continuité conceptuelle, pas expérimentale

L'audit GitHub cross-notebooks **ne trouve aucun transport formel** de `p̂` vers les features SAE (ICT-21) ou la J-lens (ICT-SAE-JLens-TeteATete). Ce qu'on a, c'est une **continuité conceptuelle** (chaque maillon répond à une insuffisance du précédent) et une **continuité numérique** (les grandeurs mesurées ICT-10/12/14 sont les mêmes). Mais le passage `p̂` → état causal (ICT-17) ne se fait pas par démonstration formelle : il se fait par **monstration successive**, chaque maillon fermant une objection locale sans nier les objections globales. **À présenter comme généalogie, pas comme théorie unifiée.**

### Garde-fou 2 — Le global workspace n'est PAS une version structurée de `p̂`

[`ICT-24-WorkspaceIgnition`](../../MyIA.AI.Notebooks/IIT/ICT-Series/ICT-24-WorkspaceIgnition.ipynb) (strate 5, axe Global Workspace Dehaene/Baars) mesure l'**opérateur `W_t`** — ce qui rend des composantes disponibles à d'autres mécanismes (décision, raisonnement, rapport, contrôle). `W_t` n'est **pas** `p̂` *structuré*. `p̂` = un *contenu* (représentation de la proie future) ; `W_t` = une *organisation de l'accès* (qui rend quoi disponible à quel mécanisme). Un contenu entre dans un workspace ; le workspace n'est pas ce contenu. La distinction est soulignée par la matrice de dissociations ([`docs/ict/dissociations-matrix.md`](dissociations-matrix.md)) : la dissociation `q_t` bon / `W_t` sélectif (pattern « bien représenté non globalement accessible », ICT-24) **est exactement le contraire** d'un workspace qui serait `p̂` structuré — c'est la preuve par dissociation que les deux grandeurs ne se réduisent pas l'une à l'autre.

## Lien avec les chantiers actifs

- **[#7396](https://github.com/jsboige/CoursIA/issues/7396)** (N2 — invariants et dissociations sur les trajectoires de *représentations*). Le pivot états → représentations est **le parapluie** de la généalogie. #7735 ne *fait* pas le pivot : il **raccroche** la généalogie ICT-10 → ICT-17 à ce parapluie, et identifie ICT-17 (état causal) comme le candidat naturel pour l'objet *représentation* que N2 cherche à suivre.

- **[#7399](https://github.com/jsboige/CoursIA/issues/7399)** (synthèse 3-régimes). La grille 3-régimes est **transversale** ; le quatrième fil est **diachronique**. Les deux se complètent sans se chevaucher : la grille dit *quelle question poser*, le quatrième fil dit *ce qui se transforme dans le système entre deux questions*.

- **[#7734](https://github.com/jsboige/CoursIA/issues/7734)** (matrice de dissociations). Le quatrième fil alimente la colonne `q_t` (représentation prédictive) : chaque maillon y ajoute une lecture (scalaire → scalaire+précision → distribution → code → état causal). L'**objet `q_t` n'est pas une grandeur figée** — c'est une *suite* de grandeurs, chacune indexée par le maillon de la généalogie qui la mesure.

- **[#7739](https://github.com/jsboige/CoursIA/issues/7739)** (distillation Thom 1991). Le quatrième fil est **orthogonal** à la distillation : Thom nomme les *catastrophes* du mode de représentation (bifurcation), le quatrième fil raconte l'*évolution* du représentant à l'intérieur d'un mode. Les deux se rencontrent en ICT-10 (la charnière où `p̂` est introduit) mais ne se confondent pas.

- **[#7733](https://github.com/jsboige/CoursIA/issues/7733)** (dette de rigueur audit #4). Rectification A1 (`p̂` ≠ prégnance thomienne) est **le prérequis** de ce document : sans cette rectification, le quatrième fil pourrait être lu comme une reconstruction de la prégnance, alors qu'il raconte l'évolution d'un objet *distinct*.

## Ce que ce document n'est pas

- **Pas une théorie unifiée.** Le quatrième fil est une *généalogie*, pas une théorie. Les six maillons sont des *lectures successives* d'un objet qui se transforme ; aucune d'elles ne subsume les autres.

- **Pas une démonstration de convergence.** ICT-17 *croit* à l'état causal comme descendant formel de `p̂`, mais ne le *démontre* pas : la genèse numérique est là, le transport formel (`p̂` → ε-machine) reste à faire (cf. garde-fou 1).

- **Pas une inclusion du SAE ou de la J-lens dans la généalogie.** ICT-21 (SAE Qwen-Scope) et la J-lens mesurent le représentant *à l'échelle d'un substrat LLM*, pas à l'échelle des signaux jouets ICT-10/12/14. Le passage de l'un à l'autre est précisément le chantier #5105 / #7396 (panneau cross-échelle 700M → 120B), ouvert par la rectification A4 (PR #7889).

- **Pas un nouveau dispatch.** Aucune nouvelle dépendance expérimentale n'est créée. Les notebooks ICT-10/12/14/15/16/17 sont livrés et mesurés ; ce document les ré-organise selon un axe (la généalogie) qu'ils sous-tendaient sans l'expliciter.

## Repères vérifiables

- Série ICT : [`MyIA.AI.Notebooks/IIT/ICT-Series/`](../../MyIA.AI.Notebooks/IIT/ICT-Series/) ([Epic #4588](https://github.com/jsboige/CoursIA/issues/4588)).
- Notebooks-ancrage du quatrième fil : [ICT-10](../../MyIA.AI.Notebooks/IIT/ICT-Series/ICT-10-CatastropheGrammar.ipynb), [ICT-12](../../MyIA.AI.Notebooks/IIT/ICT-Series/ICT-12-ValenceFieldsAndAnimats.ipynb), [ICT-14](../../MyIA.AI.Notebooks/IIT/ICT-Series/ICT-14-FreeEnergySurprise.ipynb), [ICT-15](../../MyIA.AI.Notebooks/IIT/ICT-Series/ICT-15-IntegratedComplexity.ipynb), [ICT-16](../../MyIA.AI.Notebooks/IIT/ICT-Series/ICT-16-MDLTwoPartCode.ipynb), [ICT-17](../../MyIA.AI.Notebooks/IIT/ICT-Series/ICT-17-EpsilonMachine.ipynb).
- Doc companion obstruction/recollement : [`docs/grothendieckian-lens.md`](../grothendieckian-lens.md) (§3 — cadrage `p̂`/`q_t` vs prégnance, post-A1 PR #7889).
- Grille 3-régimes : [`docs/ict/synthese-invariants-dissociations-obstructions.md`](synthese-invariants-dissociations-obstructions.md) (le quatrième fil est orthogonal à cette grille).
- Matrice de dissociations : [`docs/ict/dissociations-matrix.md`](dissociations-matrix.md) (la colonne `q_t` est indexée par le quatrième fil).
- Distillation Thom 1991 : [`MyIA.AI.Notebooks/IIT/ICT-Series/thom-synthese-distillation.md`](../../MyIA.AI.Notebooks/IIT/ICT-Series/thom-synthese-distillation.md) (orthogonale : catastrophes vs évolution du représentant).
- Issue-source : [#7735](https://github.com/jsboige/CoursIA/issues/7735) · Epic umbrella [#4588](https://github.com/jsboige/CoursIA/issues/4588) · Parapluie représentations [#7396](https://github.com/jsboige/CoursIA/issues/7396).
