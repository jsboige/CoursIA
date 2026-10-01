# Activités — IA Vulgarisation

Activités de vulgarisation utilisées en cours (EPF, MSMIN5IN52 « IA Générative et Chatbots » 2025-2026). Importées du gisement Drive (`G:\Mon Drive\MyIA\Formation\EPF\2026\MSMIN5IN52 IA Générative et Chatbots\Activités - IA Vulgarisation.txt` + version PDF) — issue #18223. Le texte est fidèle à la source ; chaque activité indique la série du dépôt qui enseigne la notion.

Les activités GenAI proprement dites vivent dans [Activités-GenAI.md](Activités-GenAI.md) (corrigé : [Correction-Activites-GenAI.md](Correction-Activites-GenAI.md)).

---

## 1. Exploration : cannibales et missionnaires

Dans ce défi, 3 missionnaires et 3 cannibales doivent franchir une rivière en barque. Pour assurer leur sécurité, il faut respecter ces règles :

- La barque ne peut transporter qu'1 ou 2 personnes à la fois.
- Les missionnaires ne doivent pas être en infériorité numérique par rapport aux cannibales de chaque côté de la rivière, sinon ils seront en danger.
- À chaque traversée, tout le monde doit descendre de la barque.

**Question** : Pour commencer sans risque, quelle est la première action à effectuer ?

**Indices** :

- Il s'agit d'un problème simple d'exploration.
- Il est important de bien modéliser les états du problème.
- La construction d'un arbre d'exploration peut être utile pour visualiser les différentes étapes possibles.

**Références** :

- Librairie simple illustrant les principaux algorithmes de recherche de chemin en JavaScript : <https://qiao.github.io/PathFinding.js/visual/>
- Librairie Java associée au livre de cours qui a inspiré la présentation : <https://github.com/aimacode/aima-java>

**Série du dépôt** : [`Search/`](../../Search/) (exploration non informée).

## 2. Heuristiques de la satisfaction de contraintes

Dans les problèmes à satisfaction de contraintes, où des variables doivent être assignées à des valeurs spécifiques tout en respectant certaines contraintes, certaines stratégies, appelées heuristiques, peuvent faciliter la recherche de solutions.

**Question** : Parmi les heuristiques suivantes, lesquelles facilitent l'exploration des solutions dans les problèmes à satisfaction de contraintes ?

**Indice** :

- Vous partez au ski, comment remplissez-vous votre coffre ?
- Traduisez cela en termes généraux : les bagages sont des variables, les emplacements les valeurs.

**Références** (librairies de programmation par contraintes / solveurs SMT / prouveurs de théorèmes / raisonneurs) :

- <https://developers.google.com/optimization>
- <https://www.minizinc.org/>
- <https://choco-solver.org/>
- <https://github.com/Z3Prover/z3>
- <https://leanprover.github.io/>
- <http://tweetyproject.org/>

**Série du dépôt** : [`SymbolicAI/SMT/`](../../SymbolicAI/SMT/) (Z3, Choco), [`SymbolicAI/Lean/`](../../SymbolicAI/Lean/) (Lean), [`SymbolicAI/Tweety/`](../../SymbolicAI/Tweety/) (Tweety).

## 3. Raisonnement : arguments fallacieux

Visualisez la taxonomie des arguments fallacieux disponible à ces adresses :

- <https://www.argumentum.games/Fallacies_fr.html>
- <https://www.argumentum.games/Fallacies_en.html>

**Question** : De quelle famille sont les arguments fallacieux consistant à attaquer la personne plutôt que de répondre à l'argument ?

**Indice** :

- Identifiez les branches principales des familles de couleur.

**Série du dépôt** : [`GenAI/FallacyDetection/`](../FallacyDetection/), jeu [Argumentum](../../SymbolicAI/Argument_Analysis/Argumentum/) (sous-module).

## 4. Argumentum

On constitue des tables avec un membre de chaque équipe pour jouer à [Argumentum](https://www.argumentum.games).

La partie se joue en 4 points gagnant. Chaque vainqueur remporte 5 points à son équipe.

**Série du dépôt** : sous-module [`Argumentum`](../../SymbolicAI/Argument_Analysis/Argumentum/).

## 5. Heuristiques de la planification

La planification a été présentée comme une redéfinition des problèmes d'exploration en utilisant la syntaxe de la logique du premier ordre pour définir les conditions initiales et le schéma des actions du modèle de transition, avec pour chacune des actions :

- son nom ;
- ses préconditions ;
- ses effets.

Ce formalisme permet de créer de nouvelles heuristiques utiles à l'exploration de problèmes complexes de façon systématique.

**Question** : Comment s'y prendre pour les découvrir ?

**Indice** :

- Vous ne connaissez rien au Rubik's cube ou au Taquin. On vous demande de résoudre l'un de ces puzzles. Comment procédez-vous mentalement pour avancer dans la bonne direction à tâtons ?

**Série du dépôt** : [`SymbolicAI/Planners/`](../../SymbolicAI/Planners/).

## 6. Probabilités : chaîne de Markov de la météo

Nous utilisons une chaîne de Markov simple pour modéliser la météo locale, décrivant la transition entre des journées de soleil et de pluie. Selon le modèle :

- Une journée ensoleillée est suivie d'une autre journée de soleil avec une probabilité de 8 sur 10, d'une journée de pluie avec une probabilité de 2 sur 10.
- Une journée pluvieuse est suivie d'une autre journée de pluie avec une probabilité de 9 sur 10, d'une journée de soleil avec une probabilité de 1 sur 10.

**Question** : Si on ne connaît pas le temps qu'il fait aujourd'hui, quelle est la probabilité estimée P_soleil d'avoir une journée ensoleillée selon ce modèle ?

**Indices** :

- On cherche la distribution stationnaire permettant de passer de la prévision météo à court terme au climat.
- La probabilité stationnaire reflète le rapport à long terme entre les jours ensoleillés et pluvieux, indépendamment des conditions initiales.
- La somme de la probabilité de soleil et de pluie fait 1.
- La probabilité stationnaire doit être constante par application du modèle de transition : P_soleil(t+1) = P_soleil(t).

**Références** (programmation probabiliste) :

- Infer.NET : <https://dotnet.github.io/infer/>
- Pyro : <https://pyro.ai/>
- TensorFlow Probability : <https://www.tensorflow.org/probability>
- PyMC : <https://www.pymc.io/welcome.html>

**Série du dépôt** : [`Probas/`](../../Probas/) (Infer.NET, PyMC).

## 7. Axiomes de préférences rationnelles et irrationalité humaine

Un agent rationnel exprime ses préférences entre les loteries : L = [p1, S1; p2, S2; … pn, Sn].

On utilise la notation suivante :

- A ≻ B : l'agent préfère A à B ;
- A ∼ B : l'agent est indifférent entre A et B ;
- A ≳ B : l'agent préfère A à B ou est indifférent.

**Questions** :

1. Quels sont les 6 axiomes que des préférences raisonnables doivent respecter pour pouvoir définir une fonction d'utilité ?
2. Quelle est la définition des 5 effets suivants, qui caractérisent l'irrationalité des humains, incompatibles avec une utilité rationnelle ?
   - Effet de certitude ;
   - Régression fallacieuse ;
   - Évitement d'ambiguïté ;
   - Effet de cadrage ;
   - Effet d'ancrage.

**Série du dépôt** : [`Probas/`](../../Probas/) (théorie de l'utilité, systèmes probabilistes).

## 8. Processus de décision de Markov de l'aspirateur autonome

Considérez un aspirateur autonome évoluant dans un environnement simplifié représenté par une grille. Dans cette grille, l'aspirateur a pour objectif de rejoindre son socle de rechargement (+1) tout en évitant une chaussette qui traîne (-1) et en gérant son niveau de batterie restant (avec un niveau de charge restant confortable, soit une pénalité légèrement négative, R, pour chaque déplacement).

**Conditions** :

- En tentant d'avancer vers une case vide, l'aspirateur a 80 % de chances de réussir, 10 % de chances de dévier à gauche, et 10 % de chances de dévier à droite.
- Le « grid world » inclut une case mur, une case obstacle (-1), et la case objectif (+1).

**Question** : Parmi les politiques de déplacement suivantes, laquelle représente la stratégie optimale pour l'aspirateur, lui permettant de maximiser sa chance de rejoindre le socle de rechargement tout en minimisant la pénalité due au déplacement ?

**Indices** :

- Les flèches dans les images indiquent les directions de déplacement préférées dans chaque case de la grille.
- Chaque image correspond à une politique différente adaptée à un niveau de pénalité R spécifique.
- Pour un niveau de batterie confortable, notre aspirateur choisira de ne pas prendre de risque.

*(Les 4 images de politiques sont dans la version PDF du gisement Drive.)*

**Série du dépôt** : [`RL/`](../../RL/) (processus de décision de Markov).

## 9. Théorie des jeux : bataille des Sexes

Dans le jeu de la Bataille des Sexes, un couple doit choisir entre deux activités : assister à un match de boxe ou aller voir un ballet. L'homme préfère le match de boxe, tandis que la femme préfère le ballet. Leurs préférences sont représentées par la matrice de gains suivante :

- Si les deux choisissent le match de boxe, l'homme reçoit une utilité de 2 et la femme de 1.
- Si les deux choisissent le ballet, l'homme reçoit une utilité de 1 et la femme de 2.
- Si leurs choix divergent, ils reçoivent tous les deux une utilité de 0.

Ce jeu a trois équilibres de Nash : 2 équilibres en stratégie pure, dits de domination (« j'impose toujours mon choix ») et de soumission (« je concède toujours la décision »), ainsi qu'un équilibre en stratégie mixte, dit de négociation, où chacun des joueurs randomise sa stratégie.

**Question** : Quelle est l'utilité espérée pour l'homme et la femme dans l'équilibre de Nash mixte de ce jeu ?

**Indices** :

- Pour trouver l'équilibre mixte, chaque joueur doit être indifférent entre ses deux stratégies. Cela conduit à deux équations d'indifférence : 2q = 1−q pour l'homme et p = 2−2p pour la femme.
- On retrouve les probabilités du mix stratégique en résolvant ces équations.
- L'utilité espérée dans cet équilibre est calculée en pondérant les gains de la matrice par les probabilités du mix calculées.

**Référence** :

- Librairie très complète d'apprentissage par renforcement et minimisation de regret : <https://github.com/deepmind/open_spiel>

**Série du dépôt** : [`GameTheory/`](../../GameTheory/) (OpenSpiel, équilibres de Nash).

## 10. Évolution de la confiance

Séquence de questions sur l'animation suivante : <https://ayowel.github.io/trust/>

*(Simulation interactive « The Evolution of Trust » — confiance, trahison et jeux répétés.)*

**Série du dépôt** : [`GameTheory/`](../../GameTheory/) (jeux répétés).

## 11. Théorie du choix social : le scrutin de Condorcet et l'élection présidentielle française

Dans le cadre des élections présidentielles françaises, le système de vote utilisé est le scrutin uninominal à deux tours. Ce système, cependant, ne garantit pas toujours que le candidat élu soit un « vainqueur de Condorcet », c'est-à-dire un candidat qui aurait battu tous les autres candidats dans des duels hypothétiques un contre un.

**Définition** : Un mode de scrutin est dit de Condorcet s'il garantit l'élection du candidat qui serait préféré à chacun des autres candidats dans des élections par paires. Si un tel candidat existe, il est considéré comme le vainqueur de Condorcet. Le mode de scrutin de l'élection présidentielle française, contrairement à celui d'autres pays, n'est pas un scrutin de Condorcet, il est hautement stratégique (importance du vote utile).

**Question** : Au cours d'une des dernières élections présidentielles françaises, quel candidat a été identifié comme un vainqueur de Condorcet, c'est-à-dire préféré à tous les autres dans des sondages de duel hypothétique, mais n'a pas été élu à cause du système de scrutin en place ?

**Indices** :

- Des sondages d'opinion réalisés avant l'élection ont montré ce résultat, bien que le système de vote n'ait pas permis de refléter cette préférence globale.
- Pour identifier le vainqueur de Condorcet malheureux, il est utile de considérer la loi de Hotelling en théorie politique, qui postule que dans un système bipolaire, les candidats tendent à se positionner proche de l'électeur médian pour maximiser leurs chances de victoire, garantie dans un scrutin de Condorcet. Ce phénomène peut aider à comprendre pourquoi certains candidats peuvent être favorisés dans un scrutin de Condorcet mais désavantagés dans le scrutin uninominal à deux tours.

**Série du dépôt** : [`GameTheory/SocialChoice/`](../../GameTheory/SocialChoice/) (choix social, Condorcet).

## 12. Oobabooga — Personae

Pour cet exercice, un LLM hébergé localement est choisi comme modèle conversationnel pour chaque équipe participante.

Il s'agit pour chaque équipe de proposer :

- une nouvelle personnalité associée à ce modèle, comprenant un prompt système composé d'une attribution de rôle, d'une conversation de présentation avec didascalies et d'une amorce de conversation ;
- un jeu de paramètres de génération associé à cette personnalité (température, taille maximale des réponses, pénalité de répétition, etc.).

Une fois chaque personnalité créée et partagée, l'évaluation est effectuée par la menée d'une conversation pour chaque personnalité par chacune des autres équipes participantes. Chaque conversation comprend au plus 10 messages.

Chaque proposition fait l'objet d'une évaluation par les autres groupes sous forme d'une note sur 20. La meilleure proposition pour chacune des interfaces remporte à son équipe 5 points.

**Série du dépôt** : [`GenAI/Texte/`](../Texte/) (paramètres de génération), [`GenAI/Plateformes-Conversationnelles/`](../Plateformes-Conversationnelles/).

## 13. Oobabooga — Dataset

Pour cet exercice, proposer des données de personnalisation du LLM hébergé sous oobabooga en vue de la création d'un fine-tune de type LoRA.

Chaque proposition fait l'objet d'une évaluation par les autres groupes sous forme d'une note sur 20. La meilleure proposition remporte à son équipe 5 points.

**Série du dépôt** : [`GenAI/FineTuning/`](../FineTuning/) (LoRA).

## 14. Semantic Kernel

Pour cet exercice, proposer une idée de fonction sémantique, native ou hybride sur le modèle des fonctions présentées en exemple.

Chaque proposition fait l'objet d'une évaluation par les autres groupes sous forme d'une note sur 20.

**Série du dépôt** : [`GenAI/SemanticKernel/`](../SemanticKernel/).
