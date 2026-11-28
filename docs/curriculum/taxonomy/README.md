# Taxonomie pédagogique

Cette taxonomie matérialise le nœud de série et les carnets de Compression, jumeaux C# compris (le carnet compagnon Lean reste dans sa sous-série distincte). Les carnets Python et leurs jumeaux C# n'ont pas de sous-série dans le catalogue. Elle part des concepts nommés dans les cellules de titre et d'exposé ; chaque rattachement pointe vers le chemin du carnet et son identifiant de cellule. Les UUID des concepts sont opaques et ne changent pas lorsque leurs chemins taxonomiques évoluent. La tranche pilote en déclarait sept ; la couverture de la série entière est décrite dans « Série Compression — tranche 4 ».

Le format conserve les trois colonnes de repérage d'Argumentum : `path`, `decimal_path` et `depth`. La hiérarchie pédagogique réserve aussi les niveaux `example` et `exercise` sous le carnet ; ils ne sont pas peuplés à ce jour. Les prérequis relient chaque concept aux notions qu'il suppose, dans la série. Le validateur vérifie les références, les cellules, la couverture de chaque carnet déclaré, les prérequis inconnus et les cycles.

`compression.json` contient les données éditoriales, et `schema.json` décrit leur structure. Pour régénérer les exports SKOS/Turtle et OWL/RDF/XML dans un répertoire temporaire :

```bash
python scripts/notebook_tools/curriculum_taxonomy.py \
  --skos-output /tmp/compression.ttl \
  --owl-output /tmp/compression.owl
```

Les sources des concepts sont exportées en liens GitHub vers les vrais carnets. Chaque relation `cursus:hasCellCitation` regroupe le lien du carnet et son `cursus:cellId`, contrôlé contre le notebook local.

L'export des concepts reste un graphe à part de l'export catalogue afin que chaque forme garde sa validation dédiée. Un consommateur peut les unir dans un même graphe RDF en chargeant les deux Turtle, par exemple `graph.parse("catalogue.ttl", format="turtle")` puis `graph.parse("compression.ttl", format="turtle")`.

## Série Compression — tranche 4 (la série entière : 13 carnets Python, 7 jumeaux C#, 1 carnet Lean)

`compression.json` couvre les **21 carnets** de la série : les treize carnets Python, leurs sept **jumeaux C#** et le carnet Lean `Compression-01b`, sous la sous-série `Compression_lean` — **136 concepts** et **216 citations de cellule**, contre 18 concepts sur 7 carnets pour le pilote. Le même `schema.json` et le même validateur `curriculum_taxonomy.py` s'appliquent. Les **prérequis** relient les carnets entre eux : l'inégalité de Kraft après les codes préfixes, le codage de Huffman avant sa forme canonique puis sa table de décodage, les codes préfixes avant la fenêtre glissante de LZ77, l'état ANS avant ses variantes rANS et tANS.

Mesurée par `curriculum_taxonomy.py --density`, la densité va de **7 à 12 concepts par carnet, médiane 10**, et aucun carnet déclaré n'est sans concept. Six groupes nouveaux complètent l'arbre du pilote : **Banc de compression** (7), **Taux d'entropie** (8), **Recette de reconstruction** (9), **Triage par le LLM** (10), **Assemblage de documents** (11) et son enfant **Assemblage par le LLM** (11.1). Les 66 concepts créés qui en relèvent citent onze carnets que le pilote ne citait pas et deux qu'il citait déjà : `Compression-02-HuffmanCanonique-Python` (de 2 à 8 concepts) et `Compression-04b-CodecsSOTA-Pareto-Python` (de 1 à 11). Les 46 autres concepts créés rejoignent des nœuds existants, sous-groupes compris : `codes-prefixes` en reçoit 14, `lz77` 9, `ans` 8, `modeles-neuronaux` 7, `mdl` 6 et `huffman-canonique` 2.

Trois règles ont guidé la densification. **Les 18 concepts du pilote sont intacts** : identifiant, `decimal_path`, libellés, définitions et profondeur inchangés ; la tranche ne fait que leur ajouter des citations, 23 sur 10 d'entre eux. **Une notion enseignée dans deux carnets reste un seul concept, porteur de deux citations** : 58 concepts sont cités par au moins deux carnets, et `query_curriculum.py concepts --notebook` les rend carnet par carnet. **Une citation d'un carnet Python n'est mise en miroir vers son jumeau C# que si les deux cellules, Python et C#, sont des cellules markdown d'au moins 80 caractères dont la prose atteint la similarité 0,85** (mesure `difflib` sur le texte débarrassé de ses blancs superflus, les couples dont la longueur diffère de plus de 35 % étant écartés d'office) : 35 citations sont mises en miroir sur les jumeaux `01`, `06`, `07` et `08` ; aucune cellule des jumeaux `02`, `03` et `04` n'atteint ce seuil avec la prose de son jumeau Python (une cellule Python de `02` et deux de `03` y trouvent un voisin entre 0,5 et 0,85, aucune de `04` ne dépasse 0,5), leurs concepts sont donc extraits de leurs propres cellules.

```bash
python scripts/notebook_tools/curriculum_taxonomy.py --density --json
python scripts/notebook_tools/query_curriculum.py --graph /tmp/taxonomies.ttl \
  concepts --notebook MyIA.AI.Notebooks/InformationCalcul/Compression/Compression-03-LZ77-CSharp.ipynb
```

Les notions qu'un carnet nomme sans les définir ni les démontrer restent hors taxonomie : la description de la PR de la tranche en tient la liste. Les ponts **inter-séries** relèvent de la tranche 3 de #26646 : à ce jour `--bridges` ne relève aucune paire candidate impliquant Compression.

## Série Probas — tranche 1 (sous-série Infer)

`probas.json` étend le même format à la série **Probas**, sur la sous-série **Infer** fondation : six carnets (`Infer-01` à `Infer-05`, dont `Infer-01b`) et 22 concepts. Le même `schema.json` et le même validateur `curriculum_taxonomy.py` s'appliquent ; les **prérequis** relient les carnets entre eux (par ex. les réseaux bayésiens et la d-séparation avant l'inférence causale). Chaque concept cite les cellules de carnet où il est enseigné ; ceux qui s'y rattachent (réseaux bayésiens, d-séparation, inférence causale) nomment en outre le chapitre **AIMA 3e/4e** correspondant dans leur définition, les concepts propres à Infer.NET (moteur, graphes de facteurs, VMP/EP, mélanges gaussiens) n'ayant pas d'équivalent AIMA.

```bash
python scripts/notebook_tools/curriculum_taxonomy.py \
  --data docs/curriculum/taxonomy/probas.json \
  --skos-output /tmp/probas.ttl \
  --owl-output /tmp/probas.owl
```

La tranche 2 ajoutera la sous-série **PyMC** au même fichier, puis les carnets Infer avancés (IRT, TrueSkill, processus de Kalman, etc.).

## Série GameTheory — tranche 1 (cœur : forme normale → Nash → minimax → forme extensive → SPE)

`gametheory.json` étend le même format à la série **GameTheory**, sur le **cœur** de la série : neuf carnets (`GameTheory-01` à `GameTheory-10`, hors `08`) et 28 concepts. Le même `schema.json` et le même validateur `curriculum_taxonomy.py` s'appliquent ; les **prérequis** relient les carnets entre eux (par ex. la forme normale et la meilleure réponse avant l'équilibre de Nash, l'induction arrière avant les raffinements de perfection). Chaque concept cite les cellules de carnet où il est enseigné ; ceux qui s'y rattachent (jeu en forme normale, équilibre de Nash, jeu à somme nulle, forme extensive, induction arrière, dilemme du prisonnier) nomment en outre le chapitre **AIMA 3e/4e** correspondant dans leur définition, les concepts sans équivalent AIMA (topologie des jeux 2x2, théorie évolutionnaire, perfection en sous-jeux, induction avant, perfection en mains tremblantes) n'en citant aucun.

```bash
python scripts/notebook_tools/curriculum_taxonomy.py \
  --data docs/curriculum/taxonomy/gametheory.json \
  --skos-output /tmp/gametheory.ttl \
  --owl-output /tmp/gametheory.owl
```

Les tranches suivantes étendront la série aux sous-séries **SocialChoice**, **Coalitions**, **Dynamics**, aux jeux bayésiens et aux jeux globaux — ajoutées au même `gametheory.json`, une PR par tranche, sur ce même modèle.

## Série Search — tranche 1 (sous-série Part1-Foundations : espaces d'états → non informée → informée → locale → adversariale → MCTS)

`search.json` étend le même format à la série **Search**, sur la sous-série **Part1-Foundations** : six carnets (`Search-01-StateSpace`, `02-Uninformed`, `03-Informed`, `04-LocalSearch`, `06-AdversarialSearch`, `07-MCTS-And-Beyond`) et 24 concepts. Le même `schema.json` et le même validateur `curriculum_taxonomy.py` s'appliquent ; l'arbre de carnets porte ici le niveau **sous-série** (`Search/Part1-Foundations`). Les **prérequis** relient les carnets entre eux (par ex. la formulation du problème avant la recherche non informée, le minimax avant l'élagage alpha-bêta, l'adversarial avant le MCTS). Chaque concept cite les cellules de carnet où il est enseigné ; ceux qui s'y rattachent (espaces d'états, recherche non informée, recherche informée et A*, recherche locale, recherche adversariale, minimax) nomment en outre le chapitre **AIMA 3e/4e** correspondant dans leur définition, les concepts sans équivalent AIMA (MCTS, sélection UCB1, AlphaZero) n'en citant aucun.

```bash
python scripts/notebook_tools/curriculum_taxonomy.py \
  --data docs/curriculum/taxonomy/search.json \
  --skos-output /tmp/search.ttl \
  --owl-output /tmp/search.owl
```

Les tranches suivantes étendront la série aux sous-séries de `Search/` (autres parties du catalogue) et aux carnets de `Part1-Foundations` non couverts ici — ajoutées au même `search.json`, une PR par tranche, sur ce même modèle.

## Série Planners — tranche 1 (cœur classique : formulation → PDDL → espace d'états → Fast Downward → heuristiques → domaines)

`planners.json` étend le même format à la série **Planners**, sur le **cœur classique** de la série : six carnets (`01-Foundation` : `Planners-01-Introduction`, `02-PDDL-Basics`, `03-State-Space` ; `02-Classical` : `04-Fast-Downward`, `05-Heuristics`, `06-Domains`, versions `-Python`) et 26 concepts. Le même `schema.json` et le même validateur `curriculum_taxonomy.py` s'appliquent ; l'arbre de carnets porte ici le niveau **sous-série** (`Planners/01-Foundation` et `Planners/02-Classical`). Les **prérequis** relient les carnets entre eux (par ex. la formulation du problème avant PDDL et la recherche d'états, la recherche d'états avant Fast Downward, PDDL avant les domaines). Chaque concept cite les cellules de carnet où il est enseigné ; ceux qui s'y rattachent (formulation, PDDL, planification comme recherche d'états, heuristiques de planification) nomment en outre le chapitre **AIMA ch. 10** correspondant dans leur définition, les concepts sans équivalent AIMA (Fast Downward, graphe de planification, LM-cut, satisficing, les heuristiques h^max/h^add/FF/landmarks, les domaines de référence) n'en citant aucun.

```bash
python scripts/notebook_tools/curriculum_taxonomy.py \
  --data docs/curriculum/taxonomy/planners.json \
  --skos-output /tmp/planners.ttl \
  --owl-output /tmp/planners.owl
```

Les tranches suivantes étendront la série aux sous-séries avancées de `SymbolicAI/Planners/` (planification sous incertitude, planification temporelle, SAT-based) et aux autres carnets de `01-Foundation` / `02-Classical` non couverts ici — ajoutées au même `planners.json`, une PR par tranche, sur ce même modèle.

## Série IIT — tranches 1+2 (cœur : réseau causal → Φ → CES → complexe majeur → coarse-graining → frontière → lentilles → objection Aaronson → formalisation Lean → partitionnement MIP)

`iit.json` étend le même format à la série **IIT** (Integrated Information Theory), sur le **cœur** de la série : dix carnets (`IIT-01` à `IIT-09`, dont `IIT-08b` — 6 carnets Python PyPhi/Φ et 4 carnets Lean du lake `iit_lean`) et 28 concepts. Le même `schema.json` et le même validateur `curriculum_taxonomy.py` s'appliquent ; les **prérequis** relient les carnets entre eux (par ex. le réseau causal avant Φ et la CES, Φ avant le complexe majeur, le problème de frontière, l'objection d'Aaronson et la formalisation Lean). Chaque concept cite les cellules de carnet où il est enseigné. IIT étant une théorie de la conscience spécifique, **aucun concept ne nomme de chapitre AIMA** (hors du périmètre d'AIMA) — les citations pointent les cellules des carnets uniquement.

> **Tranche 2 — IIT-02 ajouté.** Le carnet `IIT-02-AdvancedTopics` (MIP, répertoires cause-effet, MICE, big Φ vs small φ) portait cinq cellules **sans identifiant stable** (métadonnée Jupyter `id`), ce qui l'avait écarté de la tranche 1 (le validateur exige un `id` stable par cellule). Les cinq `id` sont désormais stabilisés, le carnet est déclaré, et ses quatre concepts cœur sont rattachés : **partition minimale d'information (MIP)**, **répertoires cause et effet**, **MICE** et **small φ** — la MIP étant rattachée au **big Φ** (elle est la coupe qui le définit).

```bash
python scripts/notebook_tools/curriculum_taxonomy.py \
  --data docs/curriculum/taxonomy/iit.json \
  --skos-output /tmp/iit.ttl \
  --owl-output /tmp/iit.owl
```

Les tranches suivantes étendront la série à la série **ICT** (`ICT-Series/`, 102 carnets, Epic #4588) — extension distincte documentée dans son propre README, ajoutée au même `iit.json` ou dans un `ict.json` dédié, une PR par tranche, sur ce même modèle.

## Série Z3-Linq2Z3 — tranche 1 (la série entière : DSL déclaratif → théorie des tableaux → capstone du planificateur → applications SMT)

`z3-linq2z3.json` étend le même format à la série **Z3-Linq2Z3** (`SymbolicAI/SMT/Z3-Linq2Z3/`), sur ses vingt carnets (`01_Linq2Z3_Intro` à `20_Theorem_Rewriters`) et 21 concepts. Le même `schema.json` et le même validateur `curriculum_taxonomy.py` s'appliquent. Les **prérequis** dessinent un tronc et un éventail : la programmation déclarative avant le DSL `Theorem` de Z3.Linq ; le DSL avant la théorie des tableaux, puis les grilles 2D, la modélisation du planificateur de repas, la jointure de données réelles, le capstone patient et l'encodage à l'échelle ; le DSL, encore, avant chacune des applications indépendantes (ordonnancement, coloration, cryptarithmes, MaxSAT, bit-vectors, arithmétique réelle, cores UNSAT, énigme d'Einstein, tactiques, réécritures). Chaque concept cite les cellules de carnet où il est enseigné ; **aucun ne nomme de chapitre AIMA**, la série enseignant un outil SMT et son DSL C# plutôt qu'un chapitre du livre.

```bash
python scripts/notebook_tools/curriculum_taxonomy.py   --data docs/curriculum/taxonomy/z3-linq2z3.json   --skos-output /tmp/z3-linq2z3.ttl   --owl-output /tmp/z3-linq2z3.owl
```

## Série Tweety — tranche 1 (logiques → révision de croyances → argumentation)

[`tweety.json`](tweety.json) décrit le cœur Python de la sous-série **SymbolicAI/Tweety** : `Tweety-02-Basic-Logics`, `Tweety-03-Advanced-Logics`, `Tweety-04-Belief-Revision`, `Tweety-05-Abstract-Argumentation` et `Tweety-06-Structured-Argumentation`. Le même `schema.json` et le validateur `curriculum_taxonomy.py` s'appliquent. Les prérequis relient notamment la satisfiabilité à MaxSAT et aux sous-ensembles inconsistants minimaux, puis le cadre de Dung à l'admissibilité et aux sémantiques d'argumentation. Cette tranche ne prétend pas couvrir toute la série Tweety.

Les définitions françaises et anglaises citent les **cellules sources des carnets** par chemin et identifiant stable. Aucun chapitre AIMA n'est indiqué dans cette tranche : le choix est de sourcer les formulations effectivement enseignées avec Tweety, notamment AGM, CF2, ASPIC+, DeLP et ABA, plutôt que de leur attribuer un chapitre généraliste sans correspondance établie. Cela ne signifie pas que les fondements de logique propositionnelle ou du premier ordre sont absents d'AIMA ; un rattachement bibliographique supplémentaire demanderait une vérification explicite, distincte des citations de cellules présentes ici.

```bash
python scripts/notebook_tools/curriculum_taxonomy.py \
  --data docs/curriculum/taxonomy/tweety.json \
  --skos-output /tmp/tweety.ttl \
  --owl-output /tmp/tweety.owl
```

## Série BioMédecine — tranche 1 (sous-série Dynamiques : trois modèles, trois contrôles indépendants)

[`biomedecine.json`](biomedecine.json) ouvre la série **BioMedecine** (`MyIA.AI.Notebooks/BioMedecine/`), sous la sous-série `Dynamiques`. Elle ne compte aujourd'hui **qu'un carnet**, `Dynamiques-01-Populations-et-Epidemies-Python` : la tranche déclare donc un arbre à trois nœuds (série, sous-série, carnet) et **17 concepts**, porteurs de **40 citations de cellule**. Le même `schema.json` et le même validateur `curriculum_taxonomy.py` s'appliquent.

Le carnet applique aux trois dynamiques le contrat de méthode de la série — modèle, calcul, contrôle indépendant, contre-témoin, statut — et la taxonomie suit ce contrat plutôt que l'ordre des sections. Le concept racine `controle-independant` reçoit ses deux enfants `contre-temoin` et `statut-du-resultat` : un contrôle ne vaut que s'il sait échouer, et ce qu'il établit se déclare. Les trois modèles portent chacun leur chaîne : `croissance-logistique` avant `capacite-de-charge` et `solution-analytique` (la forme fermée est le juge) ; `schema-euler-explicite` avant `ordre-de-convergence` (l'erreur doit décroître comme $h^p$, ce qui rattache l'écart à la discrétisation et non à une faute de calcul) ; `lotka-volterra` avant son `point-fixe` puis son `integrale-premiere`, qui est précisément le contrôle de la section ; `modele-sir` avant `nombre-de-reproduction-base`, puis `taille-finale` (l'équation transcendante résolue par dichotomie, sans intégrer le système), `immunite-de-groupe` (le seuil $S/N < 1/R_0$ est la condition d'arrêt réelle) et `approximation-de-branchement` (valable sous le seuil seulement). `integrateur-adaptatif` reste un concept racine : il est la voie de calcul de référence, pas un modèle.

**Aucun chapitre AIMA n'est indiqué** : le carnet enseigne trois modèles classiques et la manière de les contrôler, sans rattacher son propos à un chapitre du livre. **Aucun champ `matches` n'est non plus déclaré** : la recherche d'une correspondance réelle avec les neuf autres taxonomies du dossier (sur `euler`, `runge`, `integration`, `logistique`, `epidemie`, `SIR`, `volterra`, `population`) ne rend que des faux positifs — « codes préfixes » pour Compression, « modèle STRIPS » pour Planners — et une correspondance inventée vaudrait moins que son absence. Un pont vers la série Physique, qui pratique le même contrat de méthode, reste à établir sur ses propres concepts quand cette taxonomie existera.

Deux trous sont assumés et documentés plutôt que comblés par des concepts adossés à rien. Les **notions réservées aux exercices** — l'ordre 2 du schéma du point milieu, l'ordre auquel Euler conserve l'invariant, la position du pic infectieux — ne sont pas des concepts : le niveau `exercise` de la hiérarchie est réservé et non peuplé à ce jour. Le **réseau de contacts**, modèle à agents annoncé en fin de carnet comme objet des feuilles suivantes, est du travail à venir : il n'apparaît pas ici tant qu'aucune cellule ne l'enseigne.

Mesurée par `curriculum_taxonomy.py --density`, la densité vaut **17 concepts pour le seul carnet déclaré**, et aucun carnet n'est sans concept. Deux concepts ne sont cités qu'une fois ; les quinze autres le sont au moins deux fois, chaque modèle portant ses propres cellules de lecture.

```bash
python scripts/notebook_tools/curriculum_taxonomy.py \
  --data docs/curriculum/taxonomy/biomedecine.json \
  --skos-output /tmp/biomedecine.ttl \
  --owl-output /tmp/biomedecine.owl
```

## Valider toutes les taxonomies d'un coup

`--all` valide chaque `*.json` du dossier (hors `schema.json`), nomme le fichier fautif, puis contrôle la cohérence d'ensemble du dossier (voir « Ce que le validateur contrôle »). Seul, il n'écrit aucun export :

```bash
python scripts/notebook_tools/curriculum_taxonomy.py --all
```

Avec `--skos-output` et `--owl-output`, `--all` écrit **un seul graphe** qui réunit toutes les taxonomies du dossier. C'est dans ce graphe réuni qu'un prérequis ou un alignement vers une autre taxonomie retrouve le concept visé, avec ses libellés et ses citations :

```bash
python scripts/notebook_tools/curriculum_taxonomy.py --all \
  --skos-output /tmp/taxonomies.ttl \
  --owl-output /tmp/taxonomies.owl
```

## Ponts entre taxonomies

Chaque fichier du dossier est une **taxonomie** : le vocabulaire d'une série ou d'une sous-série. L'unité est le fichier, pas le champ `series` : deux fichiers peuvent déclarer la même série (`semanticweb.json` et `tweety.json` déclarent toutes deux `SymbolicAI`), ils restent deux taxonomies, nommées d'après leur fichier.

Les identifiants de concept sont des UUID, uniques dans tout le dossier. Trois écritures permettent à deux taxonomies de se parler ; aucune ne demande de réécrire un fichier existant.

| Pont | Écriture | Quand l'employer |
|---|---|---|
| Concept partagé | une entrée de `citations` qui vise le carnet d'une autre taxonomie | la notion est enseignée dans deux séries et un seul identifiant suffit : on cite le second carnet plutôt que de créer un doublon |
| Prérequis | l'UUID d'un concept d'une autre taxonomie dans `prerequisites` | la notion s'appuie sur une notion définie dans une autre série |
| Alignement | le champ optionnel `matches` | chaque série garde son propre concept, avec son cadrage, et les deux désignent la même notion (`exact`) ou des notions voisines (`close`) |

### Le champ `matches`

```json
{
  "id": "b0000000-0000-4000-8000-000000000001",
  "label_fr": "Fonction d'utilité",
  "prerequisites": [],
  "matches": [
    {"concept": "a0000000-0000-4000-8000-000000000002", "kind": "exact"}
  ]
}
```

L'extrait vient de [`beta.json`](../../../scripts/tests/fixtures/curriculum_taxonomy/beta.json), l'une des taxonomies figées des tests, réduit aux champs utiles à la lecture ; un concept garde tous ses champs obligatoires. `concept` est l'UUID d'un concept d'une **autre** taxonomie du dossier. `kind` vaut `exact` quand les deux concepts sont interchangeables (`skos:exactMatch`), `close` quand ils se recouvrent sans se confondre (`skos:closeMatch`) : même objet vu sous deux formalismes, cas particulier et cas général. Dans le doute, `close`.

Un alignement est symétrique : il se déclare d'un seul côté, dans la taxonomie qui l'affirme, et compte une fois. Le déclarer des deux côtés est permis à condition de donner le même `kind`.

Cette forme est la moins invasive. Le champ est optionnel, donc un fichier qui ne l'emploie pas reste valide tel quel. L'alignement vit à côté du concept qu'il qualifie, dans le fichier de la série qui l'affirme : il se relit, se valide et se corrige avec lui, sans fichier central de vocabulaire à arbitrer entre séries. Les prérequis ne demandent aucun champ nouveau : les UUID étant uniques dans le dossier, la liste `prerequisites` accepte l'identifiant d'un concept d'une autre taxonomie.

### Ce que le validateur contrôle

Pour chaque taxonomie :

- un concept ne porte aucun champ inconnu, si bien qu'une faute de frappe sur `matches` est refusée au lieu de passer pour une absence d'alignement ;
- chaque alignement a exactement les champs `concept` et `kind`, un `kind` parmi `exact` et `close`, une cible qui existe dans une autre taxonomie du dossier ; un concept ne s'aligne ni sur lui-même, ni sur un concept de sa propre taxonomie, ni deux fois sur la même cible ;
- chaque prérequis existe, dans la taxonomie ou dans une autre du dossier, et les cycles sont cherchés à travers les taxonomies ;
- chaque citation vise un carnet déclaré par la taxonomie ou par une autre du dossier, et une cellule qui existe dans ce carnet ;
- chaque carnet déclaré reste cité par au moins un concept de sa propre taxonomie.

Pour le dossier entier, avec `--all` :

- un identifiant de concept n'est déclaré que par un fichier ;
- un carnet n'est déclaré que par une taxonomie (une autre taxonomie le cite, elle ne le redéclare pas) ;
- deux alignements réciproques ne se contredisent pas (`exact` d'un côté, `close` de l'autre) ;
- une chaîne d'alignements `exact` ne rend pas identiques deux concepts d'une même taxonomie.

### Mesurer la densité et les ponts

```bash
python scripts/notebook_tools/curriculum_taxonomy.py --density
python scripts/notebook_tools/curriculum_taxonomy.py --bridges
python scripts/notebook_tools/curriculum_taxonomy.py --density --bridges --json
```

`--density` donne, par taxonomie, le nombre de carnets déclarés, de concepts et de citations, la distribution du nombre de concepts par carnet (minimum, médiane, maximum), les carnets qu'aucun concept ne cite, et les concepts cités une seule fois ou dans un seul carnet. Le nombre de concepts d'un carnet compte tous les concepts qui le citent, y compris ceux d'une autre taxonomie.

`--bridges` liste les trois familles de ponts déclarés, puis les **ponts candidats** : deux identifiants de taxonomies différentes qui portent le même libellé ou la même définition, à la casse, aux accents et à la ponctuation près, et qu'aucun alignement ne relie encore. Un candidat est une question posée au rédacteur, pas une erreur : soit les deux concepts s'alignent, soit leurs libellés méritent d'être distingués. La même coïncidence à l'intérieur d'une taxonomie est listée à part, comme doublon. Le relevé se termine par un décompte par paire de taxonomies.

Les deux relevés lisent tout le dossier et mesurent ce qui est écrit, sans valider : ils fonctionnent sur un fichier en cours de rédaction. Ajouter `--all` valide d'abord. Avec `--json`, la sortie standard ne porte que le relevé.

### Dans l'export, et pour l'interroger

L'export porte chaque pont :

- `skos:exactMatch` et `skos:closeMatch` pour les alignements ;
- `cursus:requiresConcept` pour les prérequis, y compris vers le concept d'une autre taxonomie ;
- `cursus:concept`, du carnet vers chaque concept qui le cite, sur le même nœud de carnet que l'export du catalogue ; un concept cité par plusieurs carnets porte autant de liens et autant de `cursus:hasCellCitation` ;
- `rdfs:isDefinedBy`, du concept et du carnet vers le nœud `cursus:Taxonomy` de leur fichier.

`query_curriculum.py` lit ces liens dans l'export réuni :

```bash
python scripts/notebook_tools/query_curriculum.py --graph /tmp/taxonomies.ttl bridges
python scripts/notebook_tools/query_curriculum.py --graph /tmp/taxonomies.ttl \
  concepts --notebook MyIA.AI.Notebooks/Search/Part1-Foundations/Search-01-StateSpace.ipynb
```

`bridges` écrit une ligne par pont, triée par paire de taxonomies : la paire, la famille (`concept partagé`, `prérequis`, `alignement exact`, `alignement close`), les libellés et les identifiants. `concepts --notebook` écrit, pour un carnet, chaque concept qui le cite avec son identifiant, sa taxonomie et les cellules citées ; le chemin s'accepte avec ou sans `MyIA.AI.Notebooks/`. Sur l'export d'une seule taxonomie, ce qui mène à un concept ou à un carnet d'une autre est rangé sous « hors des graphes chargés ».

Ces règles sont rejouées sur trois taxonomies figées par [`test_curriculum_taxonomy_bridges.py`](../../../scripts/tests/test_curriculum_taxonomy_bridges.py).
