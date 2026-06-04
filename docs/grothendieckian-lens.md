# La mer qui monte — une grille de lecture grothendieckienne du depot CoursIA

> **Cle de lecture transversale.** Ce document lit le depot CoursIA comme un projet intellectuel coherent, sans rien reecrire au code. Distinct de [#1646](https://github.com/jsboige/CoursIA/issues/1646) (formaliser le *langage* de Grothendieck dans Mathlib) — ici, on lit le depot a travers le *geste*.

---

## 1. La mer qui monte

Grothendieck opposait deux facons d'ouvrir une noix : le marteau et le burin, ou bien laisser monter la mer jusqu'a ce que la coque cede sans effort. Le depot, lu transversalement, choisit regulierement la seconde. Trois mouvements reviennent, d'une serie a l'autre :

- **Local -> global (recollement).** Une donnee locale engendre une structure globale : la regle de voisinage de Conway fait emerger des motifs Turing-complets ; la sensibilite ponctuelle d'une fonction booleenne se hisse au theoreme de Huang ; les preferences individuelles se heurtent a l'impossibilite d'Arrow ; une action PDDL se compose en un plan ; une transition de contrat devient une obligation immuable ; une distribution locale se resout en politique de decision. C'est, litteralement chez Grothendieck (topologie, faisceaux), et par analogie partout ailleurs, le passage du local au global par recollement.

- **Changement de representation.** Le meme objet traverse plusieurs representations entre lesquelles on traduit : grille <-> quadtree <-> inductif Lean ; fonction booleenne <-> coloration de l'hypercube <-> algebre lineaire ; graphe de facteurs Infer.NET <-> PyMC ; PDDL <-> graphe d'etats <-> CP-SAT ; langage naturel <-> semantiques formelles d'argumentation. Le *resultat* est invariant ; ce qui change, c'est le **cout** et la **prouvabilite**. Trouver la representation ou le probleme devient facile — ou demontrable — *est* le travail.

- **Monter d'un cran.** Quand un axe sature, on ne s'acharne pas : on change la question. C'est le ressort le plus grothendieckien, et celui qui donne au depot sa signature propre.

## 2. La signature du depot : la certification

Une lecture « local -> global » seule resterait une belle observation un peu generale. Le depot ajoute une **seconde dimension**, moins evidente et plus originale : il ne se contente pas d'assembler, il demande *avec quelle garantie ?* Toute transformation calculee se mesure alors sur **deux axes orthogonaux** :

- **Axe quantitatif** — *combien*, *a quelle echelle*. C'est l'axe que maximisent les outils communautaires (Golly et HashLife sautent `2^k` generations, OTCA et Gemini se comptent en millions de pas).
- **Axe de certification** — *avec quelle garantie* la transformation est-elle atteste. C'est l'axe que le depot ouvre des qu'il porte une construction en Lean, en Z3, en verification formelle.

Les deux ne sont pas en competition : ils sont independants. L'intuition s'est d'abord cristallisee sur Conway/HashLife (#1647, #2062) — un portage Lean ne battra jamais Golly sur l'axe quantitatif, mais il ouvre une garantie que Golly, qui *calcule* sans *certifier*, ne touche jamais. Mais le constat deborde tres largement ce cas : c'est la grille qui distingue, dans *toute* la table du §3, ce qui est prouve de ce qui est mesure.

Pour que « qualite de certification » soit mesurable plutot qu'incantatoire, on la gradue :

| Grade | Mecanisme | Confiance | Portee |
|-------|-----------|-----------|--------|
| **A — noyau** | `rfl` / `decide` verifies par le noyau Lean | maximale | plafonne en taille |
| **B — compilateur de confiance** | `native_decide` (code compile + axiome `ofReduceBool`) | elevee — fait confiance au compilateur Lean | passe a l'echelle ; deja plus fort que tout outil qui ne certifie rien |
| **C — ouvert** | test, backtest, evaluation, `#eval`, preuve empirique | aucune garantie machine | c'est une donnee, declaree comme telle |

L'echelle vaut **partout**, pas qu'en Lean : un backtest QuantConnect, une eval ML, une inference PyMC sont des certificats de **grade C** parfaitement legitimes. Le seul defaut possible n'est jamais « etre en grade C » — c'est « presenter un grade C comme un grade A ». La grille rend cette question uniforme et la pose sans agressivite.

Cette signature est aussi **d'actualite** : a mesure que l'IA bascule vers le LLM, plusieurs series (SL-7, Planners, Argumentum) montrent le meme reflexe — reprendre la sortie d'un modele de langage et la *re-representer* dans un cadre verifiable. Le changement de representation vers la prouvabilite y devient un garde-fou, pas une coquetterie formelle.

## 3. Le geste, serie par serie (verifie contre le depot)

Chaque ligne est grounded sur les fichiers reels (chemins / Epics cites). Grade = certificat *dominant* aujourd'hui ; entre parentheses, le grade *vise* quand il differe.

| Serie | Objet local | Structure globale | Changement de representation | Grade |
|-------|-------------|-------------------|------------------------------|-------|
| **Grothendieck** (`Lean/grothendieck_lean`, [Lean-13](../MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-13-Grothendieck-Tribute.ipynb) ; [#1646](https://github.com/jsboige/CoursIA/issues/1646)) | objet local d'un site | structure globale recollee (faisceau, schema) | proprietes locales <-> globales via topologie de Grothendieck (Mathlib) | **A vise** — formalisation *en cours*, ~6 sorry residuels, [#1646](https://github.com/jsboige/CoursIA/issues/1646) ouverte |
| **Sensitivity** (`Lean/sensitivity_lean`, [Lean-12](../MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-12-Sensitivity-Theorem.ipynb)) | sensibilite ponctuelle d'une fonction booleenne | theoreme de Huang (degre dans l'hypercube) | fonction booleenne <-> coloration de l'hypercube <-> algebre lineaire | **A** (0 sorry, dust-off `mathlib/Archive/Sensitivity`) |
| **Social Choice** (`GameTheory/social_choice_lean`) | preference individuelle | impossibilites d'Arrow / Sen, mecanismes | profils <-> fonctions de bien-etre <-> theoreme Lean | **A** (0 sorry sur Arrow/Sen/Voting.lean) |
| **Coop. games / Stable marriage** (`GameTheory/*_lean`) | coalition / paire | coeur, stabilite | combinatoire <-> Lean | **A** (residus sorry honnetes, ex. Bondareva-Shapley) |
| **Conway / Life** (`Lean/conway_lean`, [Lean-14](../MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-14b-Conway-Game-of-Life-Lean.ipynb)) | regle B3/S23 sur une cellule | motifs emergents, Turing-completude | grille <-> quadtree (MacroCell/HashLife) <-> inductif Lean | **B** par-pattern ; A vise sur motifs periodiques bornes ; *honnnete : pas de theoreme general `evolveHashlife = evolve`* ([#2062](https://github.com/jsboige/CoursIA/issues/2062)) |
| **GameTheory** (pratique) | gains d'un joueur | equilibres | tables de gains <-> Nashpy / OpenSpiel / CFR | **C** (calcul/simulation) |
| **SmartContracts** (`SymbolicAI/SmartContracts`, 27 notebooks) | une transition d'etat | obligation immuable, ecosysteme (DeFi/DAO) | intention <-> Solidity <-> bytecode EVM <-> invariants Foundry / ZKP | **C -> B**, verif. formelle = A vise |
| **Planners** (`SymbolicAI/Planners`, 27 notebooks) | une action (preconditions/effets) | un plan atteignant le but | monde <-> PDDL/STRIPS <-> graphe d'etats <-> CP-SAT / heuristiques | **C** (plan verifiable ; optimalite parfois prouvee) |
| **SymbolicLearning** (`SymbolicAI/SymbolicLearning`, SL-1 a SL-7) | exemple + connaissance du domaine | hypothese / regle generale | version space <-> clauses Horn (ILP) <-> tenseurs logiques (LTN/DeepProbLog) <-> LLM+verif | **C** ; SL-7 = boucle LLM + verification symbolique = montee vers le certificat |
| **Probas — Decision** (`Probas/Infer` + `Probas/PyMC`, 20+20 notebooks) | distribution / utilite locale | reseau de decision, valeur de l'information | **graphe de facteurs Infer.NET <-> PyMC** : le *meme* contenu en deux representations | **C** — *le double port EST le changement de representation incarne* |
| **Argumentum** (`SymbolicAI/Argument_Analysis` ; [#2137](https://github.com/jsboige/CoursIA/issues/2137), [#1650](https://github.com/jsboige/CoursIA/issues/1650)) | un argument / une assertion | graphe d'argumentation, depot multilingue | langage naturel <-> Tweety (semantiques formelles) <-> CSV traduisibles | **C** (pipeline LLM + Tweety + SK) |
| **RL** (`RL`, 8 notebooks) | transition `(s,a,r,s')` | politique optimale | MDP <-> Bellman <-> reseau (DQN/PPO) | **C** (empirique) |
| **IIT** (`IIT`, 3 notebooks) | mecanisme local (TPM) | Phi integre | TPM <-> cause-effet <-> macro / coarse-graining / blackboxing | **C** + discussion critique assumee |
| **Search / Sudoku** (`Search`, `Sudoku`) | une contrainte / un coup | solution globale | backtracking <-> CSP/SAT/SMT/DLX <-> metaheuristiques <-> LLM | **C** ; SMT (insatisfiabilite prouvee) = vers A. Sudoku = banc d'essai multi-representation |
| **ML / GenAI** (`ML`, `GenAI`) | echantillon / prompt | modele, pipeline orchestre | features <-> ONNX <-> SemanticKernel / agents | **C** (eval, tests) |
| **QuantConnect** (`QuantConnect`, 190+ notebooks) | une barre de marche | strategie / portefeuille | donnees <-> signal <-> backtest OOS | **C** (walk-forward + couts ; honnetete = pas de same-period leak) |

*Les noix historiques externalisees — MetaGeneticSharp ([#1203](https://github.com/jsboige/CoursIA/issues/1203)), Z3.Linq ([#1206](https://github.com/jsboige/CoursIA/issues/1206)), semantic-fleet ([#1210](https://github.com/jsboige/CoursIA/issues/1210)) — se lisent par la meme cle (primitives composables -> bestiaire d'algorithmes ; contraintes locales -> solveur global ; connecteurs -> routeur multi-fournisseurs).*

Lue ainsi, la table raconte une progression : du **A** (certitude formelle, plafonnee en taille) vers le **C** (echelle statistique, sans garantie machine), et le depot construit explicitement les ponts — c'est tout le sens de SMT en Search, de la verification formelle en SmartContracts, de SL-7 en SymbolicLearning. La montee vers le certificat *est* le fil rouge.

## 4. Honnetete du certificat

Le constat de fond est positif : les series sont serieuses et correctement sourcees. La grille ne sert pas a instruire un proces — elle pose partout la meme question utile, « ce resultat, a quel grade est-il certifie, et le depot le dit-il honnetement ? », et le depot y repond bien dans l'immense majorite des cas. Quand la lecture fait remonter une coquille (un grade C habille en A, une trace perimee, une parenthese qui surclasse un theoreme), on la corrige au passage, sans en faire le sujet.

### Coquilles reperees pendant le grounding

1. **Sensitivity — README ligne 25 (CORRIGE, PR #2064).** Le README disait « *Formalization of the Sensitivity Theorem (sensitivity <= block sensitivity)* », alors que le theoreme formalise est `huang_degree_theorem` (`sensitivity_lean/Sensitivity/MainTheorem.lean:84`, Huang 2019). « sensitivity <= block sensitivity » est trivial et n'est pas le resultat de Huang. Parenthese reformulee dans **PR #2064**. `NOTICE.md` et `Sensitivity.lean:9` etaient deja corrects.
2. **KochenSpecker — numero (CORRIGE).** Le notebook est **Lean-15-Kochen-Specker**, pas Lean-14 (= Conway-Tribute). La coherence trace `sorry` vs README 0-sorry reste a verifier sur le bon fichier avant toute action.
3. **HashLife — statut (DEJA TRACE [#2062](https://github.com/jsboige/CoursIA/issues/2062)).** Vocabulaire honnete : `#eval` + `native_decide` par-pattern, pas de theoreme general. Rien a corriger, ne pas surclasser.

---

## Reconciliation avec les Epics existantes

| Epic | Rapport |
|------|---------|
| **[#1646](https://github.com/jsboige/CoursIA/issues/1646)** Hommage Grothendieck (formaliser le langage dans Mathlib) | **Socle conceptuel.** [#1646](https://github.com/jsboige/CoursIA/issues/1646) montre le langage *dans* le depot ; ce document lit le depot *avec* le geste. La conclusion Lean-13 fait la jointure. |
| **[#1647](https://github.com/jsboige/CoursIA/issues/1647) / [#1651](https://github.com/jsboige/CoursIA/issues/1651) / [#2062](https://github.com/jsboige/CoursIA/issues/2062)** Conway (Phases 2-3, HashLife) | Exemple-source des deux axes et cas d'ecole d'honnetete du certificat. |
| **[#1468](https://github.com/jsboige/CoursIA/issues/1468)** SOTA Lean (harnais + lib + notebooks) | La grille des 3 grades fournit un vocabulaire commun reutilisable ; reste distincte (concret vs. meta). |
| **[#1203](https://github.com/jsboige/CoursIA/issues/1203) / [#1206](https://github.com/jsboige/CoursIA/issues/1206) / [#1210](https://github.com/jsboige/CoursIA/issues/1210)** trilogie externalisee | Lues par la cle, mentionnees seulement. |
| **[#1271](https://github.com/jsboige/CoursIA/issues/1271) / [#1650](https://github.com/jsboige/CoursIA/issues/1650)** Argumentum | Une ligne de la table ; [#1650](https://github.com/jsboige/CoursIA/issues/1650) = vecteur d'une eventuelle traduction du document. |

---

*Document de lecture — aucun nouveau code de serie, aucun dossier encyclopedique. Voir [#2065](https://github.com/jsboige/CoursIA/issues/2065) pour l'Epic originale.*
