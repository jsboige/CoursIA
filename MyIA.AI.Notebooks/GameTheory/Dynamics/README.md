# Dynamics — coopération, programmes et institutions

[↑ GameTheory](../README.md) · [Entrée : évolution de la confiance](../GameTheory-06-EvolutionTrust-Python.ipynb)

Pourquoi répéter une interaction peut-il rendre la coopération soutenable ? Que change la possibilité de lire le programme de son partenaire, et que reste-t-il de cette transparence lorsque calculer ou raisonner coûte quelque chose ? Cette sous-série de [GameTheory](../README.md) aborde ces questions par des simulations Python, des expériences comparatives et des compagnons formels en Lean.

Elle s'adresse aux étudiants et enseignants connaissant la forme normale d'un jeu et l'équilibre de Nash. Le point d'entrée est [GameTheory-06 — Évolution de la confiance](../GameTheory-06-EvolutionTrust-Python.ipynb), qui introduit les tournois de stratégies et la dynamique des populations. Pour les biens publics et les joueurs inspirés des modèles de langage, lire aussi [GameTheory-03 — Topologie des jeux 2×2](../GameTheory-03-Topology2x2-Python.ipynb). Les simulations supposent les bases de Python ; les preuves demandent une familiarité supplémentaire avec Lean et les hypothèses des énoncés.

## Comment lire ce README — découverte

Le parcours suit le principe [« Choisir sa vitesse de lecture »](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture) : les numéros nus donnent la progression, les lettres approfondissent un palier.

- **Vous découvrez** : suivez le parcours principal et ses prérequis. Les variantes Python, C# et Lean d'un même numéro partagent une ligne.
- **Vous creusez un palier** : ouvrez l'approfondissement correspondant ; ses prérequis précisent le changement de niveau.
- **Vous cherchez des prolongements** : consultez « Pour aller plus loin », où figurent les formalisations et les limites des expériences.

Le début du parcours explique la coopération par l'histoire des interactions. À partir de 04, l'information disponible porte aussi sur le programme adverse : ses réponses possibles deviennent examinables. Le budget de calcul, le coût du raisonnement, la simulation mutuelle et les certificats publics donnent ensuite des modèles distincts de cette coopération. Les biens publics et les joueurs simulés prolongent ce parcours en revenant aux jeux introduits dans GameTheory-03.

## Parcours principal — lecture guidée et prérequis

| # | Notebook | Ce qu'on y apprend | Public et prérequis | Pour approfondir |
|---|---|---|---|---|
| 01 | [Jeux répétés et théorème Folk — Python](Dynamics-01-Jeux-Repetes-Folk-Theorem-Python.ipynb) · [C#](Dynamics-01-Jeux-Repetes-Folk-Theorem-CSharp.ipynb) | Relier horizon, actualisation et crédibilité d'une punition ; calculer le seuil de coopération de *grim trigger*, puis explorer les paiements soutenables. | Après GameTheory-06 ; séries géométriques. C# pour le jumeau .NET. | Lecture formelle en 02 ; sympathie et engagement en 03. |
| 02 | [Jeux répétés en Lean, depuis Python](Dynamics-02-Jeux-Repetes-Lean-Python.ipynb) | Lire les définitions et garanties formelles de l'actualisation et de *grim trigger*, puis repérer ce qui reste à démontrer dans le théorème Folk complet. | Après 01 ; lecture d'énoncés Lean. Le noyau du carnet est Python. | [Formalisations Lean](#formalisations-lean). |
| 03 | [Sympathie contre engagement](Dynamics-03-Sympathie-vs-Engagement-Python.ipynb) | Faire varier les gains d'autrui à gains propres constants pour distinguer des modèles de préférence et de règle de conduite. | Après la statique comparative de 01 ; NumPy et notion de vraisemblance. | Contrôles négatifs et exercices sur les mélanges et l'identifiabilité. |
| 04 | [Jeux à programmes publics](Dynamics-04-Open-Source-Game-Theory-Python.ipynb) | Construire une matrice de confrontations entre programmes inspectables et comparer le moteur à un vérificateur indépendant. | Jeux répétés et fonctions Python ; inspection de code. | [04b — FairBot et Löb](#autour-de-04--fairbot-et-logique-de-prouvabilité). |
| 05 | [Agents bornés — Python](Dynamics-05-Agents-Bornes-Python.ipynb) · [Lean](Dynamics-05-Agents-Bornes-Lean.ipynb) | Donner un budget à l'agent et à son interprète ; comparer les issues calculées aux garanties formelles sur une famille d'agents. | Après 04 ; Lean pour la variante formelle. | Faire varier le budget et étendre la famille d'agents dans les exercices. |
| 06 | [Preuves bornées et coût du raisonnement](Dynamics-06-Preuves-Bornees-Cout-du-Raisonnement-Python.ipynb) | Instrumenter profondeur, états explorés et coût ; observer les conséquences d'une limite de calcul. | Après 04 et 05 ; lecture du moteur de simulation. | Distinguer coût mesuré, longueur de preuve et comportement de repli. |
| 07 | [Équilibres par simulation](Dynamics-07-Equilibres-par-Simulation-Python.ipynb) | Étudier des programmes qui simulent leurs partenaires, leur terminaison et l'effet d'un aléa partagé sur les issues. | Après 06 ; probabilités élémentaires et NumPy. | Déviations stochastiques et validité hors de la famille testée. |
| 08 | [Institutions transparentes](Dynamics-08-Institutions-Transparentes-Python.ipynb) | Comparer des règles de coopération fondées sur des certificats publics ; isoler l'effet de la représentation du partenaire. | Après les jeux à programmes publics ; lecture de règles d'inférence. | Séparer observations finies et théorèmes de prouvabilité cités. |
| 09 | [Biens publics N-personnes](Dynamics-09-Biens-Publics-N-Personnes-Python.ipynb) | Explorer des bénéfices non linéaires, la coexistence, la bistabilité et l'hystérésis dans le plan `(k, s, c/b)`, en examinant la dépendance des trajectoires à leur histoire. | GameTheory-03 ; NumPy, graphiques et dynamique des populations. | Limites du banc biologique et synthèse sur les ensembles limites. |
| 10 | [Joueur LLM dans les jeux répétés](Dynamics-10-Joueur-LLM-Python.ipynb) | Comparer des règles de joueur simulé, séparer prédiction et action et mesurer l'effet d'un changement du jeu pendant l'interaction. | GameTheory-03 et jeux répétés ; Python. | Exercice de connexion à un modèle de langage, avec configuration et contrôle des appels. |

## Approfondissements — Recherche

### Autour de 04 — FairBot et logique de prouvabilité

[04b — FairBot par le théorème de Löb](Dynamics-04b-FairBot-Loeb-Lean.ipynb) prolonge les heuristiques du carnet 04 par la lecture et l'exécution du module `ProgramGames.FairBot`. Il demande un noyau Lean, la lecture des implications logiques et une attention aux hypothèses de chaque théorème.

Le carnet expose la coopération de FairBot sous l'interface `ModalProvability`. **Le schéma de Löb est un champ de cette interface** : le carnet ne le dérive pas. Son instance pédagogique `toyBox`, où toute proposition est prouvable, sert à montrer le rôle de la cohérence ; elle ne représente pas une prouvabilité effective. Le [pont GL de Lean-34b](../../SymbolicAI/Lean/Lean-34b-FairBot-Loeb.ipynb) fournit un prolongement vers la logique de la prouvabilité.

## Installation — pratique, tous niveaux

Ouvrir les carnets depuis un clone du dépôt : certains lisent des modules ou appellent des vérificateurs voisins. La procédure générale figure dans le [README GameTheory](../README.md).

- **Python** : noyau Python 3 avec NumPy, SciPy, Matplotlib et Pandas selon le carnet. Le carnet 02 lit également les sources Lean présentes dans le dépôt.
- **C#** : noyau .NET Interactive ; le carnet 01 charge MathNet.Numerics par sa directive NuGet.
- **Lean** : les carnets natifs 04b et 05 utilisent le noyau `lean4-wsl` et les modules du projet [game_theory_lean](../game_theory_lean/README.md). Suivre sa procédure de construction et sa toolchain.
- **Modèle de langage** : le parcours central de 10 simule des règles locales. Son exercice de connexion utilise une passerelle configurée par `CLAUDISH_BASE_URL`, `CLAUDISH_PROXY_KEY` et `CLAUDISH_MODEL`. La sortie enregistrée de cet exercice dépend d'un service externe ; sa cassette en mémoire n'est pas un jeu de données committé permettant un rejeu autonome.

## Pour aller plus loin — recherche

### Du comportement observé au programme inspectable

Dans le dilemme du prisonnier de 01, la stratégie *grim trigger* coopère jusqu'à une défection, puis punit durablement. Avec les gains de l'exemple, le seuil d'actualisation est `δ = 0,5` : l'importance accordée aux interactions futures détermine si la déviation immédiate est avantageuse. On peut modifier les gains pour comprendre de quoi dépend ce seuil.

Le palier 04 change l'information accessible : un historique montre des coups déjà joués, tandis qu'un programme public permet aussi d'examiner des réponses à des situations non rencontrées. Dans 08, deux programmes qui coopèrent peuvent ainsi susciter des réponses différentes selon que cette coopération est certifiable ou opaque pour leur partenaire. Les budgets et règles d'inférence délimitent ce que l'agent peut effectivement vérifier.

Le carnet 09 revient aux populations et aux biens publics. À paramètres identiques, une trajectoire peut dépendre de son état initial et de l'histoire des paramètres : c'est le sens de la bistabilité et de l'hystérésis étudiées. Ces expériences donnent une raison de regarder les trajectoires, au-delà d'un seul équilibre calculé.

### Garanties et domaine des résultats

Chaque méthode répond à une question précise :

- **Jeux répétés** : le seuil de *grim trigger* est calculé et relié à des énoncés formels. Le théorème Folk complet conserve un `sorry` dans `RepeatedGames/Folk.lean` ; sa sémantique générale d'équilibre n'est pas établie par le carnet 02.
- **Sympathie et engagement** : une réponse plate peut aussi venir d'un protocole peu informatif. Le carnet 03 compare des modèles sur un banc synthétique ; il ne diagnostique pas les motivations d'une personne.
- **Programmes et budgets** : les agents de 04 sont des heuristiques déclarées. Les expériences de 06 et 07 portent sur des moteurs et des familles finis ; leurs résultats ne démontrent pas un théorème général sur tous les programmes.
- **Institutions** : le paramètre de 08 compte des tours d'inférence dans une clôture finie. Les théorèmes dépendant de Löb borné sont cités séparément ; `PrudentBot_borne` reste un candidat et les questions ouvertes de la source restent ouvertes.
- **Biens publics** : sur les paramètres biologiques du banc 09, aucun modèle ne franchit le seuil de validation déclaré. Le modèle non linéaire donne l'erreur la plus faible ; cette proximité ne suffit pas à confirmer le modèle.
- **Joueurs LLM** : les résultats principaux de 10 caractérisent des règles simulées. L'effet de l'anticipation sociale y diffère de celui rapporté pour les modèles de langage de la publication étudiée.

### Synthèse : où peut finir une trajectoire ?

[GameTheory-06i — Ensembles limites et Poincaré–Bendixson](../GameTheory-06i-Ensembles-Limites-Poincare-Bendixson-Python.ipynb) apporte une lecture des points fixes, orbites et connexions hétérocliniques des dynamiques planaires. Il se lit après la dynamique des populations de GameTheory-06 et permet de discuter les trajectoires rencontrées ici. Les conclusions de Poincaré–Bendixson dépendent de ses hypothèses, notamment de la dimension ; elles ne s'étendent pas automatiquement à tous les modèles du parcours.

### Formalisations Lean

Les projets Lean outillent les carnets. Leurs toolchains et leur état détaillé sont centralisés dans [LEAN_INVENTORY.md](../LEAN_INVENTORY.md).

| Compagnon | Lecture associée |
|---|---|
| [RepeatedGames/Discounting](../game_theory_lean/RepeatedGames/Discounting.lean), [RepeatedGames/GrimTrigger](../game_theory_lean/RepeatedGames/GrimTrigger.lean) et [RepeatedGames/Folk](../game_theory_lean/RepeatedGames/Folk.lean) | Actualisation et *grim trigger* en 01–02 ; frontière entre résultats démontrés et théorème Folk complet. |
| [ProgramGames/Bounded](../game_theory_lean/ProgramGames/Bounded.lean) | Budget, interprète et garanties des agents du palier 05 ; prolongement expérimental en 06. |
| [ProgramGames/FairBot](../game_theory_lean/ProgramGames/FairBot.lean) | Hypothèses modales et coopération dans l'approfondissement 04b. |
| [Abstraction/Basic](../game_theory_lean/Abstraction/Basic.lean) | Prolongement dans la série mère sur le raffinement et sa dette ; voir le [parcours GameTheory](../README.md). |

## Ressources — tous niveaux

Les références et discussions des carnets donnent les sources et le contexte de chaque expérience : théorie des jeux répétés en [01](Dynamics-01-Jeux-Repetes-Folk-Theorem-Python.ipynb), coopération par prouvabilité en [04b](Dynamics-04b-FairBot-Loeb-Lean.ipynb), institutions transparentes en [08](Dynamics-08-Institutions-Transparentes-Python.ipynb), biens publics d'Archetti et Scheuring en [09](Dynamics-09-Biens-Publics-N-Personnes-Python.ipynb), jeux répétés et modèles de langage étudiés par Mei et ses coauteurs en [10](Dynamics-10-Joueur-LLM-Python.ipynb).

[Retour à GameTheory](../README.md) · [Catalogue du dépôt](../../../COURSE_CATALOG.generated.md)
