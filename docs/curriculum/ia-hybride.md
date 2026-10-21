<!--
  FICHIER MANUEL — parcours narratif écrit à la main, PAS un artefact du
  catalogue. scripts/notebook_tools/generate_parcours.py n'écrit que les
  5 pages catalogue (genai.md, ia-classique.md, ia-symbolique.md,
  trading.md, recherche.md) ; ce fichier suit la convention des pages
  manuelles (comme genai-rush.md, hors de la liste du générateur et du cron
  catalog-cron.yml) et n'est jamais régénéré. Cf EPIC #13844, front vivant
  §3 (tri du 26/09, item 1 : le triptyque « IA sans LLM / IA générative /
  IA hybride » — le troisième n'était suivi par aucun parcours).
-->

# IA hybride : LLM + solveurs + vérificateurs (~5-7 h)

Quatrième parcours narratif de l'EPIC #13844, première tranche du front vivant (tri du 26/09) :
composer **un LLM qui propose et un moteur formel qui vérifie** — la thèse du dépôt — n'était
suivi par aucun itinéraire de bout en bout. Les trois parcours pilotes couvrent l'IA générative
([genai-rush.md](genai-rush.md)), le symbolique et sa formalisation
([symbolic-formalization.md](symbolic-formalization.md)) et l'IA classique par manuel de
référence ([aima-walk.md](aima-walk.md)) ; celui-ci traverse la **couture** entre eux.

**Public visé** — le développeur ou la développeuse qui sait déjà prompter un LLM (quelques
appels API) et veut apprendre à le **fiabiliser** : où s'arrête le modèle, où commence le
solveur, comment la boucle informel/formel converge vers un verdict — et ce que ça change
quand le vérificateur est un SAT-solveur, une théorie du choix social encodée, ou une
conjonction statistique.

## Prérequis vérifiables (~15 minutes)

| À vérifier | Comment | Succès attendu |
|---|---|---|
| Python 3.10+ | `python --version` | `Python 3.1x` ou plus |
| Jupyter | `jupyter --version` (ou l'extension Jupyter de VS Code) | une version s'affiche, sans erreur |
| Java (JVM) pour Tweety | `java -version` | une version 11+ s'affiche ; sinon l'étape 1 installe et configure le pont JPype |
| Clé API LLM | fichier `.env` de la série (étape 1) ou variable d'environnement | requise pour la section 5 de l'étape 2 et le bras LLM de l'étape 8 ; **toutes les autres étapes tournent sans clé** |

Clause de prérequis — ce qui est supposé, et ce qui ne l'est pas :

> Ce parcours suppose une pratique intermédiaire de Python (boucles, dictionnaires, `pandas`
> de base), des **notions de logique propositionnelle** (variables booléennes, conjonction,
> implication — utilisées aux étapes 3 et 7) et de savoir ce qu'est un prompt LLM. Il ne
> suppose **rien d'autre** : ni Tweety ni Java maîtrisés (l'étape 1 installe le pont), ni z3
> (installé en route), ni Lean, ni GPU, ni Docker. Chaque série embarque ses dépendances ;
> les packages (`semantic_kernel`, `jpype1`, `z3-solver`, `deap`) s'installent au fil des
> premières cellules de leurs carnets respectifs.

## Durée estimée — et pourquoi elle est défendable

Chaque étape porte ci-dessous la `duree_estimee` du catalogue
(`COURSE_CATALOG.generated.json`). Somme sur les 8 étapes :

| Bloc | Étapes | Durée catalogue |
|---|---|---|
| Le pont LLM → solveur | 1-5 | 2 h 30 |
| Un théorème par SAT | 6-7 | 1 h 30 |
| Le LLM comme moteur de recherche | 8 | 45 min |
| **Total** | | **4 h 45** |

La fenêtre **~5-7 h** du titre couvre la somme catalogue plus les relectures et les reprises
d'appels API inévitables (l'étape 2 section 5 et l'étape 8 bras LLM appellent un vrai modèle).

## Sortie concrète

À la fin du parcours, vous avez **exécuté** :

- un pipeline d'analyse argumentative complet : extraction LLM du tissu argumentatif d'un
  texte, formalisation propositionnelle, vérification de cohérence par solveur (Tweety),
  détection de sophismes, orchestration Semantic Kernel (étapes 1-5) ;
- une preuve automatique d'un théorème d'impossibilité du choix social par encodage
  SAT résolu par Z3 — le vérificateur **sans** LLM, pour mesurer ce qu'il apporte seul
  (étapes 6-7) ;
- une boucle de génération où un LLM propose des expressions alpha dans une grammaire et
  où une conjonction statistique (edge ≥ 2σ, Diebold-Mariano directionnel) arbitre contre
  un facteur fixe et contre l'évolution génétique au même budget (étape 8).

Et vous pouvez nommer la division du travail que chaque bloc incarne : **le LLM propose,
le moteur formel dispose** — extraction vs vérification (bloc 1), théorème vs encodage
(bloc 2), génération vs validation (bloc 3).

## Le parcours (8 étapes, dans l'ordre)

Pour chaque étape : ce qu'elle **apporte**, ce qu'elle **suppose acquis** — lu sur la section
Prérequis réelle du notebook quand elle existe (marqué « déclaré »), sinon déduit de son
contenu — et sa durée catalogue.

### Bloc 1 — Le pont LLM → solveur (série Argument_Analysis)

1. **[Argumentation 00 — Setup Tweety](../../MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argumentation-00-Setup-Tweety-Python.ipynb)**
   (`Argumentation-00-Setup`, 15 min)
   - **Apporte** : l'environnement de la série — JVM, pont JPype vers TweetyProject,
     Semantic Kernel, `.env` de clés — installé et vérifié une fois pour toutes.
   - **Suppose** : rien. C'est le point d'entrée.

2. **[Argumentation 02 — Détection de sophismes](../../MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argumentation-02-Fallacies-Detection-Python.ipynb)**
   (`Argumentation-02`, 30 min)
   - **Apporte** : la détection d'homme de paille, faux dilemmes, appels à l'autorité —
     d'abord déterministe (sections 1-4, sans clé), puis par entonnoir agentique LLM
     (section 5).
   - **Suppose** : l'étape 1 ; `pandas`, `semantic_kernel` installés ; lecture de CSV
     (déclarés) ; la clé API pour la seule section 5 (déclaré).

3. **[Argumentation 05 — Vérification formelle](../../MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argumentation-05-Formal-Verification-Python.ipynb)**
   (`Argumentation-05`, 30 min)
   - **Apporte** : la moitié vérificatrice du pont — formalisation propositionnelle des
     arguments extraits, contrôle de cohérence par le solveur, matrices de richesse formelle.
   - **Suppose** : l'étape 1 (déclaré) ; des bases de logique formelle (déclaré) ;
     `jpype` installé.

4. **[Argumentation 07 — Orchestration](../../MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argumentation-07-Orchestration-Python.ipynb)**
   (`Argumentation-07`, 30 min)
   - **Apporte** : l'assemblage — comment les briques informelles (02) et formelles (05)
     deviennent un pipeline orchestré ; stdlib uniquement, zéro appel LLM (déclaré).
   - **Suppose** : les notebooks 02 et 05 (déclaré) ; des bases d'algorithmique de graphe.

5. **[Argumentation 08 — Capstone](../../MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argumentation-08-Capstone-Python.ipynb)**
   (`Argumentation-08`, 45 min)
   - **Apporte** : le pipeline complet sur un vrai texte — extraction, formalisation,
     vérification, verdict — et la comparaison LLM-only vs hybride.
   - **Suppose** : les rungs 02 et 07 (déclaré) ; Python intermédiaire (déclaré).

### Bloc 2 — Un théorème par SAT (série GameTheory/SocialChoice)

6. **[SocialChoice 03 — Méthodes de vote et paradoxes](../../MyIA.AI.Notebooks/GameTheory/SocialChoice/03-Voting-Methods.ipynb)**
   (`03-Voting-Methods`, 45 min)
   - **Apporte** : le vocabulaire du choix social — paradoxe de Condorcet, règles de vote
     (pluralité, Borda, Copeland) — implémenté from scratch ; c'est l'entrée qu'exige
     l'étape suivante.
   - **Suppose** : rien au-delà du Python de base (compagnon Python autonome de la série).

7. **[SocialChoice 04 — Agrégation computationnelle par SAT-Z3](../../MyIA.AI.Notebooks/GameTheory/SocialChoice/04-Computational-Aggregation-SAT-Z3.ipynb)**
   (`04-Computational-Aggregation-SAT-Z3`, 45 min)
   - **Apporte** : un théorème d'impossibilité (Gibbard-Satterthwaite) **prouvé par la
     machine** — l'encodage booléen des conditions du théorème, Z3 cherche le
     contre-exemple, il n'existe pas. Le vérificateur sans LLM, à l'état pur.
   - **Suppose** : l'étape 6 (déclaré) ; des notions de logique propositionnelle —
     variables, clauses, CNF (déclaré).

### Bloc 3 — Le LLM comme moteur de recherche (série QuantConnect/Python)

8. **[QC-Py-42 — Alpha mining par évolution et LLM](../../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-42-Alpha-Mining-Evolution.ipynb)**
   (`QC-Py-42`, 45 min)
   - **Apporte** : l'hybride par la génération — un LLM propose des expressions alpha dans
     une grammaire contrainte, au même budget d'évaluations qu'une évolution `deap`, et la
     conjonction §C (edge ≥ 2σ ET Diebold-Mariano directionnel, Sharpe nets de coûts de
     transaction) rend son verdict trois bras. Données locales du dépôt.
   - **Suppose** : Python 3.10+, `pandas`/`numpy` de base ; la clé API pour le bras LLM
     (le carnet lève une erreur explicite sans clé) ; aucune connaissance financière
     supposée — le carnet est *from scratch*.

## Pourquoi cet itinéraire, et pas un autre

- La thèse « LLM + solveurs + vérificateurs » se prétend de plusieurs familles du dépôt ;
  l'itinéraire en traverse **trois** et les prend au moment précis où chacune fait tenir la
  couture. Argument_Analysis est le pont le plus court et le plus complet (extraction LLM →
  SAT → orchestration SK) ; SocialChoice montre le vérificateur **sans** LLM — il faut avoir
  vu ce que la machine prouve seule pour mesurer ce que le LLM ajoute et ce qu'il ne peut
  pas ; QC-Py-42 retourne le sens du pont (le LLM devient le *générateur*, la conjonction
  statistique le vérificateur).
- Le critère de succès de l'EPIC — « un apprenant qui suit le parcours dans l'ordre peut
  compléter chacun des notebooks référencés avec ses prérequis satisfaits » — a été vérifié
  étape par étape sur les sections Prérequis **réelles** des carnets, pas déduit des
  numérotations. C'est ce critère qui a **exclu** des candidats naturels : `SL-9`
  (boucle LLM-vérification) suppose SL-1 à SL-4 complets, `SL-11` (capstone neuro-symbolique)
  suppose SL-1 à SL-10, `Lean-07`/`Lean-08` (preuve à l'ère des LLMs) supposent Lean-1 à
  Lean-6 — les inclure aurait exigé d'embarquer 4 à 7 h de fondations et cassé la promesse
  d'un parcours d'une journée. Ils sont en prolongements, avec leur prérequis annoncé.
- Les trois blocs sont **détachables** : un apprenant qui n'a pas de clé API fait les
  étapes 3-7 en entier (toutes déterministes) et revient sur 2 et 8 quand il en a une.

## Prolongements (ce que ce parcours débloque)

- **SymbolicLearning** — `SL-9` (boucle LLM-vérification symbolique, ~40 min, suppose
  SL-1 à SL-4 ≈ 3 h), puis `SL-7` (T-norms différentiables, Logic Tensor Networks) et
  `SL-11` (capstone : du texte brut aux faits découverts, LLM réel aux deux extrémités,
  suppose SL-1 à SL-10). Cf [README SymbolicLearning](../../MyIA.AI.Notebooks/SymbolicAI/SymbolicLearning/README.md).
- **Lean 7-10, la preuve à l'ère des LLMs** — intégration LLM, preuve agentique,
  orchestration multi-agents, LeanDojo (suppose les fondations Lean-1 à Lean-6 ≈ 4 h 30).
  Cf [README Lean](../../MyIA.AI.Notebooks/SymbolicAI/Lean/README.md).
- **Argument_Analysis, les approfondissements** — schémas de Walton (01b), cartes
  Argumentum (02b), sémantiques de Dung (03), JTMS (06), gouvernance multi-agents et
  règles de sophismes symboliques.
- **GameTheory/SocialChoice** — Arrow par preuve Lean (01b), manipulation et pouvoir
  (05-06), comités et noyau (07-09). Cf [README SocialChoice](../../MyIA.AI.Notebooks/GameTheory/SocialChoice/README.md).
- **QuantConnect/Python** — les carnets de validation financière qui prolongent QC-Py-42
  (ML, paper trading), cf [README de la série](../../MyIA.AI.Notebooks/QuantConnect/Python/README.md).

## Sources

- [EPIC #13844](https://github.com/jsboige/CoursIA/issues/13844), front vivant §3 (tri du
  26/09) : « le triptyque IA sans LLM / IA générative / IA hybride — le troisième (composer
  LLM + solveurs + vérificateurs, la thèse du dépôt) n'est suivi par aucun parcours de bout
  en bout ».
- [Carte de la famille SymbolicAI](../../MyIA.AI.Notebooks/SymbolicAI/README.md) — les ponts
  neuro-symboliques (ambre) : Argumentation et SymbolicLearning ; « On peut lire la carte
  comme un parcours : … puis les ponts avec les LLMs. »
- [genai-rush.md](genai-rush.md) — le moule : durée annoncée, liste numérotée, clause de
  prérequis, critère de prérequis vérifié étape par étape.
- READMEs des séries traversées : [Argument_Analysis](../../MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/README.md)
  (~4-5 h pour la série complète, orchestration LLM + Tweety + SK),
  [SocialChoice](../../MyIA.AI.Notebooks/GameTheory/SocialChoice/README.md) (DAG : cinq
  angles du même résultat — simulation, vote, preuve Lean, SAT-Z3, manipulation),
  [QuantConnect/Python](../../MyIA.AI.Notebooks/QuantConnect/Python/README.md) (§ Recherche
  — alpha mining par évolution et LLM).
- `COURSE_CATALOG.generated.json` — champ `duree_estimee` par notebook, sommé étape par
  étape ci-dessus.
