# Chantier 1 — tranche A12 : statuation de l'opération `réviser une croyance` au format d'admission (deux témoins + condition de rétrogradation)

**EPIC** : [#12204](https://github.com/jsboige/CoursIA/issues/12204) · **lane** `myia-po-2024:CoursIA` · **date de mesure** 2026-11-09
**Base** : `9eba187419dd` (`origin/main`)
**Tranches sœurs** : [A2](12204-ict-chantier-1-a2.md) (op 1) · [A3](12204-ict-chantier-1-a3.md) (ops 3, 9) · [A4](12204-ict-chantier-1-a4.md) (op 4) · [A5](12204-ict-chantier-1-a5.md) (ops 2, 6, 10) · [A6](12204-ict-chantier-1-a6.md) (statuation 11-13 + file d'attente) · [A7](12204-ict-chantier-1-a7.md) (Correctif du 2026-10-21) · [A8](12204-ict-chantier-1-a8.md) (conditions de rétrogradation) · [A9](12204-ict-chantier-1-a9.md) (seconde attestation op 2) · [A10](12204-ict-chantier-1-a10.md) (statuation op 2) · [A11](12204-ict-chantier-1-a11.md) (statuation ops 3 et 5, dossier `réviser une croyance`)

## Ce que cette tranche fait

L'[A11](12204-ict-chantier-1-a11.md), corrigée le 04/11 après signalement du dossier d'adjoint (c.6618976519), a établi **l'existence** des deux témoins de `réviser une croyance`, mesuré chacun firsthand, écrit une condition de rétrogradation, puis **renvoyé l'acte d'admission à ai-01** avec ce motif : « l'évaluation contre le contrat est faite ci-dessus, la promotion reste un acte ai-01 ».

Or la pièce que le contrat d'admission exige — la **pesée de l'origine sur les trois axes du Correctif A7** — n'était pas dans la section d'A11 : elle portait les deux témoins et leur condition de sortie, mais pas le tableau d'origine que les ops 3 et 5 avaient reçu dans le même ledger. C'est cette pièce que la présente tranche produit, et c'est elle qui permet de statuer.

Elle apporte en outre deux mesures que les tranches précédentes n'avaient pas faites :

1. un **troisième usage** de l'opération existe dans l'arbre de travail partagé (`Argumentation-06c-Revision-Croyances-Python.ipynb`, organe `argumentation_lib._belief_revision_handler`) — il est **mesuré et NON COMPTÉ**, parce qu'il n'est pas committé : ni le carnet ni l'organe qu'il appelle n'existent sur `main`. Il est rapporté au coordinateur comme **collision vivante** et comme témoin futur ;
2. le **jumeau C#** du premier témoin est un usage de la **même bibliothèque** (IKVM sur Tweety, 27 occurrences d'`IKVM`, 0 de `CrMas`) : c'est une **variante de substrat**, pas une attestation supplémentaire. Le compter reviendrait à compter deux fois le même algorithme dans deux langages hôtes.

## Départage préalable — trois usages repérés, deux comptés

| Usage | Où | Sur `main` ? | Compté ? | Motif |
|---|---|---|---|---|
| **Tweety-04-Belief-Revision-Python.ipynb** | `MyIA.AI.Notebooks/SymbolicAI/Tweety/` | **oui** | **oui — attestation 1** | opérateurs CrMas de Tweety réellement exécutés sur la JVM, révision produite |
| **GameTheory-13e-Revision-Croyances-Adversaire-Python.ipynb** | `MyIA.AI.Notebooks/GameTheory/` | **oui** (PR #20215, `500473d8132`) | **oui — attestation 2** | AGM implémenté à la main sur un modèle d'adversaire, noyaux + incision, Z3 |
| `Tweety-04-Belief-Revision-CSharp.ipynb` | `MyIA.AI.Notebooks/SymbolicAI/Tweety/` | oui | **non** | **même bibliothèque** via IKVM : variante de substrat, pas un algorithme distinct (axe ii du Correctif A7) |
| `Argumentation-06c-Revision-Croyances-Python.ipynb` + `argumentation_lib/_belief_revision_handler.py` | `MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/` | **NON** — indexé `A` (staged) dans l'arbre partagé ; l'organe est **absent** de `main` (`git ls-tree origin/main` sur `argumentation_lib/` ne rend aucun fichier `belief`) | **non** | un témoin doit exister **dans le dépôt** ; ce qui vit dans un index local n'est attestable par personne d'autre. À re-mesurer au merge |

L'usage `Argumentation-06c` a tout de même été lu, parce qu'un candidat se mesure avant de se compter ou de s'écarter : cellules code toutes exécutées, aucune erreur, JVM opérationnelle (42 JARs), organe `BeliefRevisionHandler` avec `REVISION_METHODS = ['dalal', 'levi']`, contraction de noyau mesurée (`['p&&q','r'] − p → ['r']`), révision remplaçant une croyance par sa négation (`['p','q'] * !p → ['!p','q']`), stabilité sur 10 appels (1 sortie distincte), et **un défaut de l'organe mesuré** (`method='inconnu'` acceptée silencieusement, la clé `method` rapportée recopiant l'entrée). Quand il atterrira, ce sera un **troisième** témoin — d'une troisième lignée d'implémentation. Il ne pèse ni pour ni contre la statuation ci-dessous.

## Re-mesures firsthand de ce cycle

Une statuation ne s'appuie pas sur la mesure d'un autre sans relire (G.1). Toutes les mesures ci-dessous sont exécutées le **2026-11-09** sur `origin/main` (`9eba187419dd`), lecture JSON des carnets committés.

**État d'exécution** :

| Témoin | Cellules code | `execution_count` null | Erreurs |
|---|---|---|---|
| `SymbolicAI/Tweety/Tweety-04-Belief-Revision-Python.ipynb` | 13 | 0 | 0 |
| `GameTheory/GameTheory-13e-Revision-Croyances-Adversaire-Python.ipynb` | 13 | 0 | 0 |
| `SymbolicAI/Tweety/Tweety-04-Belief-Revision-CSharp.ipynb` (non compté) | 11 | 0 | 0 |
| `SymbolicAI/Argument_Analysis/Argumentation-06c-Revision-Croyances-Python.ipynb` (non compté) | 11 | 0 | 0 |

Les empreintes ont été lues **dans les sorties committées**, pas seulement dans la source :

- **Tweety-04 §3.1a** — les huit classes CrMas sont présentes et nommées une à une : `InformationObject`, `CrMasBeliefSet`, `CrMasRevisionWrapper`, `CrMasSimpleRevisionOperator`, `CrMasArgumentativeRevisionOperator`, `LeviMultipleBaseRevisionOperator`, `DefaultMultipleBaseExpansionOperator`, `KernelContractionOperator`. La sonde nomme la classe manquante : une rupture d'API se verrait.
- **Tweety-04 §3.1b** — ordre de crédibilité `A1 > A2 > A3` ; base initiale `{A2:q, A3:!q, A1:p, A3:!r, A2:(p=>r)}` ; nouvelles informations `{!p (A2), s (A3)}`.
- **Tweety-04 §3.1c** — les trois opérateurs rendent **trois résultats distincts** sur la même entrée : Levi → `[A2:!p, A3:s, A2:q, A1:p, A3:!r]` (les deux nouvelles informations entrent, `p=>r` et `!q` sont écartés) ; Simple → `[A2:q, A3:!q, A1:p, A3:!r, A2:(p=>r)]` (base inchangée : `!p` et `s` viennent d'agents moins crédibles que le détenteur de `p`) ; Argumentatif → `[A3:s, A2:q, A1:p, A3:!r]` (intègre `s`, refuse `!p`, retire `p=>r` et `!q`). C'est ce **contraste** qui fait le témoin : trois sémantiques de révision différentes, appliquées à la même base, produisant trois états de croyance différents.
- **Tweety-04 §3.2-3.4** — Contension `3.0` sur une base de 9 formules ; **5 MUS** énumérés nommément (`{!c,c}`, `{!a||!c,a,c}`, `{!a&&!b,a}`, `{!a&&!b,b}`, `{!a,a}`) ; MaxSAT RC2 `OPTIMUM FOUND`, coût `25`, assignation `a=False, b=True, c=False, d=True, f=True, g=False`. Ces sections **mesurent** l'incohérence, elles ne révisent pas — le carnet le dit lui-même ; elles ne sont pas comptées dans le témoin, elles documentent l'environnement de l'opération.
- **GT-13e** — noyaux de `B` pour l'évidence φ : `[['b4'], ['b1','b3']]`, contrôle croisé Z3 `assert_and_track` → `unsat`, core = noyau ; enracinement **mesuré** sur l'histoire tenue à part `h2` (`b4 = 0.500`, les quatre autres atomes `1.000`) ; incision gloutonne sous cet ordre → atomes sacrifiés `['b1','b4']`, survivants `['b2','b3','b5']` ; `B` admet le type `t2`, `B * φ` admet `t8`, et le vrai type (`t8`) est admis après révision (`True`) ; contrôle négatif : évidence cohérente → `noyaux = []`, la révision **dégénère en expansion**, zéro perte ; **témoin exploitable** sur 200 tours contre le vrai type `t8` : `revise : +450.0`, `reset : −15.0`, `refus : −765.0` (changement d'avis minimal `+465`, coût du refus d'évidence `+1215`) ; **batterie** : 20 bases aléatoires (3 à 6 atomes), 7 postulats AGM **20/20 chacun** (succès, inclusion, vacuité, cohérence, extensionnalité, sous-expansion, super-expansion).

## Pesée de l'origine sur les trois axes du Correctif A7

Le Correctif du 2026-10-21 demande, pour la seconde attestation, une **origine documentairement établie** sur trois axes — et non un simple constat de coexistence. Voici la pesée, témoin par témoin.

| Axe | Attestation 1 — Tweety-04 (CrMas) | Attestation 2 — GT-13e (AGM à la main) | Verdict |
|---|---|---|---|
| **(i) Littérature propre citée** | AGM 1985 (Alchourrón, Gärdenfors & Makinson) ×16 mentions ; Gärdenfors & Makinson 1988 sur l'enracinement ×2 ; identités de **Levi** et **Harper** ; lignée **CrMas** (révision multi-agents de la bibliothèque Tweety, `org.tweetyproject.beliefdynamics.mas`) ×60 ; la distinction **crédibilité des sources contre enracinement des croyances** y est explicitement construite comme deux ordres orthogonaux | AGM 1985 ; **contraction par noyaux** (Alchourrón & Makinson) ; **Darwiche-Pearl** cité comme limite assumée (révision itérée hors de ce carnet) ; pas de lignée CrMas | **partagé sur le canon, distinct sur les branches.** Le noyau AGM est commun — c'est structurel : l'opération *est* une théorie, contrairement aux ops 3 et 5 où deux champs étrangers se sont trouvés partager un mécanisme. Ce qui est propre à chaque côté : crédibilité multi-agents + révision argumentative d'un côté, enracinement mesuré sur un modèle de jeu de l'autre. **Non disqualifiant** : le Correctif A7 n'érige pas un recouvrement bibliographique en disqualification (précédent A11 sur GT-19 citant Kroer-Sandholm), et son test — *la seconde attestation est-elle la première renommée ?* — se tranche sur l'axe (ii) |
| **(ii) Algorithme identifiable et distinct du cadre de la première attestation** | Les opérateurs de la **bibliothèque tierce** : `LeviMultipleBaseRevisionOperator(kernel_contraction, DefaultMultipleBaseExpansionOperator())` avec `KernelContractionOperator` + `RandomIncisionFunction`, `CrMasSimpleRevisionOperator`, `CrMasArgumentativeRevisionOperator`, sur `CrMasBeliefSet` ordonnée par `Order<Agent>` | AGM **implémenté à la main** : énumération exhaustive des noyaux par taille croissante avec minimalité par inclusion, contrôle croisé Z3 (`assert_and_track`, le core de l'`unsat` *est* le noyau), incision gloutonne sous un ordre d'enracinement **mesuré empiriquement** (valeur prédictive des atomes sur une histoire tenue à part) | **réuni** — bibliothèque tierce contre implémentation propre ; espace de formules propositionnelles multi-agents contre modèle fini de types comportementaux ; crédibilité (qui croire) contre enracinement (à quoi renoncer), que Tweety-04 qualifie lui-même d'orthogonaux |
| **(iii) Témoin mesuré** | Trois opérateurs, trois états de croyance distincts sur la **même** base contradictoire (sorties committées) ; + 5 MUS et un MaxSAT optimal documentés | Noyaux et incision imprimés ; `t2 → t8` (le vrai type est admis après révision) ; contrôle négatif ; 7 postulats 20/20 sur 20 bases ; coût mesuré des attitudes rivales (`+465` / `+1215`) | **réuni** — deux formes de témoin non interchangeables : un **contraste d'opérateurs** d'un côté, une **batterie de postulats + un gain exploitable** de l'autre |

**Lecture honnête de l'axe (i).** La paire ne démontre pas l'opération sur deux **théories** indépendantes ; elle la démontre sur deux **substrats indépendants** — une bibliothèque tierce et une implémentation propre — et deux **problèmes distincts** — fusion multi-agents sous crédibilité et révision mono-agent sous enracinement. C'est ce que le critère §1 de l'EPIC demande (« attestée au moins deux fois dans des endroits indépendants du dépôt »), et cela satisfait l'axe (ii) du Correctif ; l'axe (i) est **partagé** et consigné comme tel plutôt que maquillé en indépendance théorique.

## Statuation — Opération `réviser une croyance` : PROMUE TABLE

**Attestation 1** — `MyIA.AI.Notebooks/SymbolicAI/Tweety/Tweety-04-Belief-Revision-Python.ipynb` (série SymbolicAI/Tweety ; présent sur `main` ; cellules code toutes à `execution_count` renseigné, aucune erreur — mesuré le 2026-11-09) : révision de croyances **multi-agents** par les opérateurs CrMas de Tweety sur JVM (42 JARs, cinq outils externes détectés) — ordre de crédibilité `A1 > A2 > A3`, base contradictoire de cinq formules, trois nouvelles informations injectées, et **trois opérateurs rendant trois états de croyance distincts** sur la même entrée (Levi, Simple, Argumentatif). L'enracinement y est présenté comme un ordre **orthogonal** à la crédibilité, ce qui est exactement la jonction que l'attestation 2 exploite.

**Attestation 2** — `MyIA.AI.Notebooks/GameTheory/GameTheory-13e-Revision-Croyances-Adversaire-Python.ipynb` (PR #20215, mergée le 10/10, commit `500473d8132` ; cellules code toutes à `execution_count` renseigné, aucune erreur — mesuré le 2026-11-09) : AGM **implémenté à la main** sur un modèle d'adversaire en jeu répété — noyaux énumérés et contrôlés par Z3, enracinement **mesuré** (valeur prédictive sur histoire tenue à part), incision, révision `B * φ`, contrôles négatifs, batterie de 7 postulats **20/20** sur 20 bases aléatoires, et **témoin exploitable** sur 200 tours (`revise +450.0` contre `reset −15.0` et `refus −765.0`). **Origine documentairement établie** sur les axes (ii) et (iii) du Correctif A7, partagée sur le canon AGM de l'axe (i) — mesuré ci-dessus.

**Condition de rétrogradation** (exécutable, falsifiable, sans critère d'omission) :

- **(a) Violation mesurée du témoin** : une re-exécution où l'un des deux témoins cesse de porter son témoin — soit Tweety-04, dont les **trois opérateurs ne produisent plus trois résultats distincts** sur la base `{A2:q, A3:!q, A1:p, A3:!r, A2:(p=>r)}` avec `{!p (A2), s (A3)}` (imports CrMas cassés, la sonde 3.1a nommant la classe manquante, ou Levi cessant d'intégrer les nouvelles informations pendant que Simple cesse de les refuser) ; soit GT-13e, dont la **batterie tombe sous 20/20** sur l'un des 7 postulats, ou dont la révision cesse d'admettre le vrai type (`B * φ` rendant `t2` au lieu de `t8`), ou dont le contrôle négatif cesse de dégénérer en expansion pure sur évidence cohérente. *Exécutable : re-exécuter chaque carnet et comparer aux empreintes ci-dessus ; pour GT-13e, faire varier la graine (`RNG` figée à `20261010`) et vérifier que la batterie reste à 20/20.*
- **(b) Perte d'un témoin** : retrait du dépôt, effondrement de sortie (ratchet collapse) ou `execution_count` null sur Tweety-04 ou GT-13e — l'admission retombe à une attestation et l'opération repart en file d'attente, au mécanisme §1 du body.

**Ni l'apparition ni la disparition d'une citation bibliographique** dans l'un des carnets n'est une condition (Correctif A7).

**Limite consignée, non maquillée.** Les deux témoins partagent le canon AGM : la paire établit l'opération sur deux **substrats** et deux **problèmes**, pas sur deux théories étrangères l'une à l'autre. Un troisième témoin d'une lignée différente lèverait cette limite — `Argumentation-06c` en est un candidat mesuré, non committé, à re-mesurer au merge.

## Ce que cette tranche ne fait pas

- Elle ne modifie **ni** le ledger A11 ni les ledgers A2-A10 : la correction du 04/11 d'A11 reste la référence de la découverte des deux témoins ; la présente tranche ajoute la pièce d'origine qui manquait à son renvoi.
- Elle ne compte **pas** l'usage `Argumentation-06c` : non committé, il n'est pas attestable. Elle ne le déclare pas non plus inexistant — elle le mesure et le nomme.
- Elle ne compte **pas** le jumeau C# comme troisième attestation : même bibliothèque via IKVM.
- Elle ne statue pas sur `institutionnaliser` ni `inhiber`, qui restent sans attestation nouvelle.
- Elle ne touche à aucun carnet : aucune ré-exécution n'est due (C.2 ne s'applique pas), aucune sortie n'est modifiée.

## Effet demandé sur le body de l'EPIC

1. Case **A12** dans la liste des grains §4 (format des cases A2-A11).
2. File d'attente §2 : `réviser une croyance` **sort de la file** et rejoint la TABLE ; liste finale des entrées TABLE portée à 16 (ops 1-14 + `point fixe` + `réviser une croyance`).
3. Annotation de la file remplacée par le renvoi au présent ledger pour la pesée d'origine et la condition de rétrogradation.

## Références

- Correctif du 2026-10-21 (preuve d'indépendance requalifiée, trois axes) : [A7](12204-ict-chantier-1-a7.md#correctif-du-2026-10-21--la-preuve-dindépendance-requalifiée-revue-externe-dispatch-ai-01)
- Format d'admission à trois champs (arbitrage coordinateur) : [issuecomment-6179879158](https://github.com/jsboige/CoursIA/issues/12204#issuecomment-6179879158)
- Découverte des deux témoins et correction de l'annotation « Tweety, non branché » : [A11 §Dossier](12204-ict-chantier-1-a11.md) · dossier d'adjoint c.6618976519 (`myia-po-2025:CoursIA-2`, 04/11)
- Conditions de rétrogradation (référence de forme pour les entrées antérieures) : [A8](12204-ict-chantier-1-a8.md) · précédent de statuation d'une op 2 : [A10](12204-ict-chantier-1-a10.md)
- Attestation 1 : `SymbolicAI/Tweety/Tweety-04-Belief-Revision-Python.ipynb` · Attestation 2 : `GameTheory/GameTheory-13e-Revision-Croyances-Adversaire-Python.ipynb` (PR #20215, `500473d8132`)
- EPIC : [#12204](https://github.com/jsboige/CoursIA/issues/12204) · claim de tranche : c.6736334042 (09/11)
