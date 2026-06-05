# La mer qui monte — lire le depot CoursIA d'un seul geste

Grothendieck decrivait deux facons de venir a bout d'un probleme dur, comme on ouvre une noix. On peut la frapper au marteau et au burin, jusqu'a ce que la coque cede sous le coup. Ou bien on peut la plonger dans l'eau et laisser la mer monter — lentement, sans bruit — jusqu'a ce qu'un jour la coque, ramollie, s'ouvre d'elle-meme. Sa preference allait a la seconde : non pas forcer le probleme, mais faire monter autour de lui le cadre qui le rend soluble.

Le depot CoursIA, parcouru d'une serie a l'autre, ressemble d'abord a un catalogue : automates cellulaires, preuves formelles, programmation probabiliste, theorie des jeux, planification, contrats intelligents, apprentissage par renforcement, trading, GenAI. Une vingtaine de sujets sans rapport evident. Mais lu avec une seule question en tete, il se met a raconter une histoire continue. La question n'est pas « comment resoudre ce probleme ? » — elle est grothendieckienne : *dans quel cadre ce probleme cesse-t-il d'etre dur ?* Suivons-la.

---

## Changer de representation jusqu'a ce que la difficulte se dissolve

Le premier mouvement est partout le meme : prendre un objet et le reecrire dans une autre langue, ou il devient maniable. La regle de voisinage de Conway, posee cellule par cellule, n'apprend rien sur les motifs qui en emergent ; transformee en quadtree puis en type inductif ([`conway_lean`](../MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean/)), elle laisse sauter `2^k` generations d'un coup — et pose enfin la question de la preuve de ces sauts. La sensibilite d'une fonction booleenne parait combinatoire ; devenue coloration de l'hypercube puis affaire d'algebre lineaire, elle tombe sous le theoreme de Huang ([`sensitivity_lean/Sensitivity/MainTheorem.lean`](../MyIA.AI.Notebooks/SymbolicAI/Lean/sensitivity_lean/Sensitivity/MainTheorem.lean), `huang_degree_theorem`, 0 `sorry`). Le meme Sudoku se laisse attaquer comme probleme de contraintes, comme formule SAT, ou par recherche pure — trois representations, trois couts, une seule grille a remplir. Et un meme modele probabiliste vit deux fois dans le depot : une fois comme graphe de facteurs Infer.NET, une fois comme programme PyMC — [`Probas/Infer`](../MyIA.AI.Notebooks/Probas/Infer/) et [`Probas/PyMC`](../MyIA.AI.Notebooks/Probas/PyMC/) se repondent notebook pour notebook, des graphes de facteurs jusqu'a la theorie de la decision (valeur d'une information, action optimale sous utilite). Contenu identique, seules changent la langue, et avec elle le cout et la lisibilite.

La theorie des jeux pousse ce geste a la limite, presque en clair : l'existence d'un equilibre de Nash, la valeur d'une coalition, un jeu combinatoire a la Conway s'y ecrivent chaque fois *trois fois* — en prose conceptuelle, en preuve Lean, en code Python ([`GameTheory-4/4b/4c`](../MyIA.AI.Notebooks/GameTheory/GameTheory-4-Nash-Equilibria.ipynb), [`-15/15b/15c`](../MyIA.AI.Notebooks/GameTheory/GameTheory-15-CooperativeGames.ipynb), [`-8/8b/8c`](../MyIA.AI.Notebooks/GameTheory/GameTheory-8-Combinatorial-Games.ipynb)). Le theoreme ne bouge pas d'une version a l'autre. Ce qui bouge, c'est ce qu'on peut en faire : le calculer vite, ou le demontrer. Trouver la representation ou le probleme devient facile — ou prouvable — n'est pas le preliminaire du travail. C'est le travail. Et, on va le voir, c'est aussi ce qui decide de la garantie qu'on en retire.

## Du local au global

Le deuxieme mouvement est celui que Grothendieck a place au coeur des mathematiques, et qu'on retrouve ici par analogie d'une serie a l'autre : une donnee purement locale engendre une structure globale. La regle B3/S23 d'une seule cellule suffit a la Turing-complete. Des strategies individuelles se recollent en un equilibre dont aucun joueur n'a interet a devier — et dont l'existence se *prouve*, en Lean ([`GameTheory-4b`](../MyIA.AI.Notebooks/GameTheory/GameTheory-4b-Lean-NashExistence.ipynb)). Des preferences individuelles, recollees, se heurtent au contraire a l'impossibilite d'Arrow ([`social_choice_lean`](../MyIA.AI.Notebooks/GameTheory/social_choice_lean/), 0 `sorry`). Une fonction caracteristique — ce que vaut chaque coalition prise a part — se resout en une allocation equitable unique, la valeur de Shapley ([`cooperative_games_lean`](../MyIA.AI.Notebooks/GameTheory/GameTheory-15b-Lean-CooperativeGames.ipynb)). Une action PDDL, composee avec ses semblables, devient un plan ([`Planners`](../MyIA.AI.Notebooks/SymbolicAI/Planners/)). Une transition d'etat de contrat devient une obligation que plus personne ne peut defaire — et qu'on cherche meme a verifier formellement ([`SmartContracts`](../MyIA.AI.Notebooks/SymbolicAI/SmartContracts/), [SC-14 Formal-Verification](../MyIA.AI.Notebooks/SymbolicAI/SmartContracts/03-Foundry-Testing/SC-14-Formal-Verification.ipynb), [SC-17 Verifiable-Voting](../MyIA.AI.Notebooks/SymbolicAI/SmartContracts/04-Privacy-Cryptography/SC-17-E2E-Verifiable-Voting.ipynb)). C'est le geste du recollement — litteral chez Grothendieck, a travers faisceaux et topologies ([`grothendieck_lean`](../MyIA.AI.Notebooks/SymbolicAI/Lean/grothendieck_lean/), et l'hommage du notebook [Lean-13](../MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-13-Grothendieck-Tribute.ipynb)), metaphorique partout ailleurs.

## Monter d'un cran : deux axes, et la question de la garantie

Jusqu'ici, un seul mouvement : changer de langue jusqu'a ce que le probleme s'allege. Mais le depot en superpose un second, plus discret — *monter d'un cran* des qu'un axe de progres sature. Car il n'y a pas un axe, il y en a deux, et ils sont independants. Le premier est celui de l'echelle : calculer plus grand, plus vite, plus loin. C'est l'axe que maximisent les outils de la communaute — HashLife saute `2^k` generations d'un coup, Golly fait tourner des motifs sur des millions de pas, les grands modeles avalent des corpus entiers. Le second est celui de la garantie : non pas *jusqu'ou* va le resultat, mais *a quel point on peut s'y fier*.

Ces deux axes ne se confondent pas, et c'est tout l'interet de les separer. On peut filer tres loin sur le premier sans avancer d'un pouce sur le second — HashLife calcule des sauts gigantesques sans demontrer le theoreme qui les justifierait. Et l'on peut tenir le sommet du second en restant tout petit sur le premier — une preuve que le noyau de Lean verifie ligne a ligne est d'une certitude maximale, mais plafonne vite en taille. C'est sur ce second axe que le depot met le plus volontiers son energie, des qu'une serie porte un resultat vers Lean ou Z3.

Et la, la garantie n'est pas binaire : c'est un continuum. A une extremite, la preuve verifiee ligne a ligne par le noyau : le theoreme de Huang est la, sans aucun `sorry`, aussi sur qu'un enonce mathematique peut l'etre. Un cran en deca, `native_decide` : on fait confiance au compilateur Lean plutot qu'au seul noyau, on cede un peu de certitude mais on gagne l'echelle — deja sans commune mesure avec un outil qui calcule sans rien attester. A l'autre extremite, le certificat ouvert, et c'est la que vit la plus grande part du depot : un backtest QuantConnect sur periode hors-echantillon, ses Sharpe, CAGR et drawdown reportes sans fard ; une politique d'apprentissage par renforcement, dont la seule caution est le rendement mesure sur des episodes ([`GameTheory-17`](../MyIA.AI.Notebooks/GameTheory/GameTheory-17-MultiAgent-RL.ipynb)) ; le Phi de la theorie de l'information integree, quantite que PyPhi *calcule* sur de petits systemes sans pretendre la *demontrer*, et qui plafonne en taille aussi vite qu'elle gagne en sens ; un modele entraine ou une image generee, juges par une evaluation. Aucun de ces certificats ne garantit rien mecaniquement, et c'est tres bien — a condition de le dire.

La theorie des jeux donne d'ailleurs a voir le continuum sans detour : l'existence de Nash *prouvee* en Lean ([`GameTheory-4b`](../MyIA.AI.Notebooks/GameTheory/GameTheory-4b-Lean-NashExistence.ipynb)) et la meme existence *constatee* numeriquement en Python ([`GameTheory-4c`](../MyIA.AI.Notebooks/GameTheory/GameTheory-4-Nash-Equilibria.ipynb)) ne sont pas au meme cran, bien que ce soit le meme theoreme. Changer de representation, ce n'est pas seulement changer de cout : c'est changer de garantie.

Car le seul vrai defaut, dans tout le depot, n'est jamais d'etre a l'extremite ouverte du continuum, ni d'etre reste petit sur l'axe de l'echelle. C'est d'etre a l'extremite ouverte tout en portant le costume de l'autre : un resultat empirique presente comme une preuve, une reussite d'echelle maquillee en garantie. Le portage HashLife en est le garde-fou exemplaire — il pousse loin l'axe de l'echelle et valide ses sauts motif par motif (`#eval`, `native_decide`), sans jamais pretendre au theoreme general `evolveHashlife = evolve`, qui reste a etablir ([#2062](https://github.com/jsboige/CoursIA/issues/2062)). L'hommage a Grothendieck est honnete de la meme maniere : sa formalisation est en chemin — les micro-preuves et smoke tests Lean sont arrives a maturite (0 `sorry` de production, 7 fichiers), mais la cartographie mathematique et l'interpretation restent au stade documentaire — une montee commencee, pas achevee, et nommee comme telle ([#1646](https://github.com/jsboige/CoursIA/issues/1646)). Rester franc sur la marche ou chaque resultat se tient : voila le seul imperatif, et il vaut pour les deux axes.

## Pourquoi ce geste, maintenant

On pourrait croire l'affaire purement formelle. Elle est, au contraire, d'une actualite immediate. A mesure que l'IA bascule vers les grands modeles de langage, plusieurs series refont spontanement le meme geste : prendre la sortie fluide mais incertaine d'un modele, et la re-representer dans un cadre qui, lui, se verifie. L'apprentissage symbolique reboucle un LLM sur une verification logique ([`SL-7`](../MyIA.AI.Notebooks/SymbolicAI/SymbolicLearning/SL-7-LLM-SymbolicLearning.ipynb)) ; l'analyse d'argumentation traduit le langage naturel en semantiques formelles que l'on peut interroger ([`Tweety`](../MyIA.AI.Notebooks/SymbolicAI/Tweety/), [`Argument_Analysis`](../MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/)) ; le planificateur confronte une intention dite en mots a un solveur qui tranche ([`Planners-10`](../MyIA.AI.Notebooks/SymbolicAI/Planners/04-NeuroSymbolic/Planners-10-LLM-Planning.ipynb)) ; le contrat assiste par LLM se relit a l'aune de sa verification formelle ([`SC-11`](../MyIA.AI.Notebooks/SymbolicAI/SmartContracts/02-Solidity-Advanced/SC-11-LLM-Assisted.ipynb)). Le changement de representation vers le verifiable cesse alors d'etre une elegance : il devient le garde-fou. Lu d'un bout a l'autre, le depot soutient a voix basse une these simple — l'IA digne de confiance sera grothendieckienne par necessite : elle consistera a trouver le cadre ou l'affirmation devient controlable.

Cette lecture ne remplace aucun des chantiers de formalisation en cours : l'hommage au *langage* de Grothendieck dans Mathlib ([#1646](https://github.com/jsboige/CoursIA/issues/1646)), le portage Conway/HashLife ([#1647](https://github.com/jsboige/CoursIA/issues/1647)), le theoreme HashLife qui reste a etablir ([#2062](https://github.com/jsboige/CoursIA/issues/2062)) avancent pour leur propre compte. Elle passe au-dessus d'eux, et les relie.

## Une cle, pas une cathedrale

Ce que cette lecture demande est volontairement petit, et a l'image de son sujet. Un document — celui-ci. Une conclusion ajoutee au notebook [Lean-13-Grothendieck-Tribute](../MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-13-Grothendieck-Tribute.ipynb), qui referme l'hommage au langage de Grothendieck sur ce *geste*-ci. Quelques liens depuis les series citees. Rien de plus : pas de nouvelle serie, pas d'encyclopedie. Une cle n'a pas a etre plus grande que la porte.

D'ailleurs, la cle a deja servi. En relisant le depot de cette facon, une coquille a saute aux yeux : le README de `sensitivity_lean` annoncait une formalisation de « sensitivity <= block sensitivity » — la direction triviale — la ou le code prouve le vrai theoreme de degre de Huang, celui qui resout la conjecture de sensibilite (PR [#2064](https://github.com/jsboige/CoursIA/pull/2064) l'a corrige). Une grille n'aurait pas attrape cela ; une lecture suivie, si.

Et s'il faut une derniere note meta : une cle de lecture qui parle de trouver la bonne representation se devait de trouver la sienne. Ce texte aurait pu etre un tableau — une ligne par serie, une colonne pour la garantie, tout range en boites. Mais un tableau decoupe en fragments isoles ce qui n'est qu'un seul geste, et remplace une idee par un bareme. La bonne representation d'un fil continu, c'est une prose continue. La mer, pas le burin.

---

### Annexe — Grades de certification (pour qui veut creuser, sans rompre le fil)

Cette echelle vaut partout, pas qu'en Lean. Le seul defaut possible n'est jamais d'etre en grade C — c'est de presenter un grade C comme un grade A.

| Grade | Mecanisme | Confiance | Portee |
|-------|-----------|-----------|--------|
| **A — noyau** | `rfl` / `decide` verifies par le noyau Lean | maximale | plafonne en taille |
| **B — compilateur de confiance** | `native_decide` (code compile + axiome `ofReduceBool`) | elevee | passe a l'echelle |
| **C — ouvert** | test, backtest, evaluation, `#eval` | aucune garantie machine | declaree comme telle |

Exemples par serie :

| Serie | Mecanisme dominant | Portee certifiee |
|-------|--------------------|-------------------|
| **Sensitivity** (Lean-12) | A (0 sorry, `huang_degree_theorem`) | Theoreme de Huang complet |
| **Social Choice** | A (0 sorry sur Arrow/Sen/Voting) | Theoremes d'impossibilite |
| **Grothendieck** (Lean-13) | A sur les micro-preuves ; C-documentaire | Faisceaux, schemas : cartographie Mathlib, pas formalisation EGA/SGA |
| **Conway / HashLife** (Lean-14) | B par-pattern (`native_decide`) | Motifs bornes ; theoreme general en chantier ([#2062](https://github.com/jsboige/CoursIA/issues/2062)) |
| **SmartContracts** | C → B (Foundry fuzz/invariants), A vise (SC-14 verif formelle) | Transitions d'etat et invariants |
| **GameTheory** | A sur les portages Lean ; C sur simulations Python | Existence Nash, Shapley (Lean) ; equilibres numeriques (Python) |
| **Planners** | C | Plans verifiables, optimalite parfois prouvee |
| **SymbolicLearning** | C ; SL-7 = montee vers B via LLM+verif | Hypotheses symboliques |
| **Probas** | C | Infer.NET exact (petit) / PyMC MCMC (echelle) |
| **RL / ML / GenAI** | C | Rendement empirique |
| **QuantConnect** | C (walk-forward + couts) | Performance hors-echantillon |
| **IIT** | C | Calcul Phi sur petits systemes |

### Reconciliation avec les Epics existantes

| Epic | Rapport |
|------|---------|
| [#1646](https://github.com/jsboige/CoursIA/issues/1646) Hommage Grothendieck | **Socle conceptuel.** #1646 montre le langage *dans* le depot ; ce document lit le depot *avec* le geste. La conclusion Lean-13 fait la jointure. |
| [#1647](https://github.com/jsboige/CoursIA/issues/1647) / [#2062](https://github.com/jsboige/CoursIA/issues/2062) Conway/HashLife | Exemple-source des deux axes et cas d'ecole d'honnetete du certificat. |
| [#1468](https://github.com/jsboige/CoursIA/issues/1468) SOTA Lean | La grille des 3 grades fournit un vocabulaire commun ; reste distincte (concret vs. meta). |
| [#1203](https://github.com/jsboige/CoursIA/issues/1203) / [#1206](https://github.com/jsboige/CoursIA/issues/1206) / [#1210](https://github.com/jsboige/CoursIA/issues/1210) | Lues par la cle, mentionnees seulement. |
| [#2137](https://github.com/jsboige/CoursIA/issues/2137) Argumentum | Une ligne de la table ; pipeline LLM + Tweety = changement de representation vers le verifiable. |

---

*Reperes verifiables : `conway_lean` et le statut HashLife [#2062](https://github.com/jsboige/CoursIA/issues/2062) ; `sensitivity_lean/Sensitivity/MainTheorem.lean` (`huang_degree_theorem`, 0 `sorry`) ; `social_choice_lean/SocialChoice/Arrow.lean` (0 `sorry`) ; `cooperative_games_lean` + [`GameTheory-15b`](../MyIA.AI.Notebooks/GameTheory/GameTheory-15b-Lean-CooperativeGames.ipynb) (Shapley) ; [`GameTheory-4/4b/4c`](../MyIA.AI.Notebooks/GameTheory/GameTheory-4-Nash-Equilibria.ipynb) (Nash : concept/Lean/Python) ; `grothendieck_lean` + notebook [Lean-13](../MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-13-Grothendieck-Tribute.ipynb) ([#1646](https://github.com/jsboige/CoursIA/issues/1646)) ; `Probas/Infer` <-> `Probas/PyMC` (miroir 1-a-1) ; `Sudoku` / `Search` ; `SymbolicAI/{SmartContracts, Planners, SymbolicLearning, Argument_Analysis, Tweety}` ; `IIT` ; `QuantConnect`.*
