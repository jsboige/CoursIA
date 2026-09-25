# Théorie des Jeux - Game Theory

[← Notebooks](../README.md) | [↑ ..](../README.md) | [→ RL](../RL/README.md)

<!-- CATALOG-STATUS
series: GameTheory
pedagogical_count: 108
breakdown: root=98, SocialChoice=10
maturity: BETA=99, DRAFT=5, ALPHA=4
-->

La théorie des jeux est le langage mathématique de la stratégie. Elle modélise les situations où des agents rationnels prennent des décisions dont le résultat dépend des choix des autres : enchères, négociations, élections, poker, allocation de ressources. Cette tension entre coopération et compétition traverse l'économie, les sciences politiques et l'informatique (mécanismes de vote, contrats, réseaux), et le prix Nobel d'économie a récompensé des théoriciens des jeux à sept reprises entre 1994 et 2020.

La série se lit sur deux axes complémentaires. Le premier est **pratique** : simuler des jeux avec Nashpy et OpenSpiel, calculer des équilibres, organiser des tournois itérés, explorer les algorithmes modernes (CFR). Le second est **formel** : prouver des résultats en Lean 4, de l'existence d'équilibres au théorème d'Arrow et à la valeur de Shapley. Le parcours principal couvre les jeux non coopératifs (Nash, minimax, équilibre parfait en sous-jeux) comme les jeux coopératifs (Shapley, Core).

**À qui s'adresse cette série** : étudiants en économie, informatique et mathématiques appliquées. Aucun prérequis en théorie des jeux : les concepts sont introduits depuis les matrices de gains. Une familiarité avec l'algèbre linéaire et les probabilités de base est utile. Le parcours principal s'exécute en Python natif, à l'exception des notebooks 13 et 17 qui demandent l'environnement OpenSpiel sous WSL.

## Comment lire ce README

Ce README suit le principe des parcours à plusieurs vitesses du dépôt ([choisir sa vitesse de lecture](../../README.md#choisir-sa-vitesse-de-lecture)).

- **Vous découvrez le sujet** : lisez le [Parcours principal](#parcours-principal), les notebooks à numéro nu de 01 à 17, dans l'ordre. Il se suffit à lui-même.
- **Vous voulez creuser un palier** : ouvrez la section de ce palier dans [Approfondissements](#approfondissements). Une lettre (`04b`, `04c`…) creuse le palier dont elle porte le numéro : formalisation Lean, variante, résultat plus récent. Elle ne fait pas avancer dans la série.
- **Vous cherchez la matière de recherche** : la [sous-série SocialChoice](#sous-série-socialchoice), les [extensions](#extensions-au-delà-du-parcours) numérotées au-delà de 17, et [Pour aller plus loin](#pour-aller-plus-loin), qui regroupe les notes techniques et les formalisations Lean.

Chaque ligne des tables annonce son public : **Découverte**, **Licence** ou **Recherche**. Pour exécuter les notebooks, voir [Installation](#installation).

### Lire un nom de fichier

Un nom de notebook porte toute l'information utile, toujours dans le même ordre :

```
GameTheory-<NN><lettre?>-<Titre>[-Part<N>]-<Noyau>.ipynb
```

| Élément | Exemple | Ce qu'il dit |
|---|---|---|
| `<NN>` | `04` | le palier, sur deux chiffres |
| `<lettre>` | `04b` | un approfondissement de ce palier ; absente sur le parcours principal |
| `-Part<N>` | `-Part2` | la suite d'un notebook découpé en tranches |
| `<Noyau>` | `-Python`, `-CSharp`, `-Lean`, `-Lean-Python` | le noyau d'exécution ; `-Lean-Python` désigne un notebook Python qui pilote réellement Lean (lecture d'un lake, appel à `lake`) |

Les jumeaux Python, C# et Lean d'un même notebook partagent son numéro : on choisit l'implémentation, pas le contenu. La série n'applique pas encore partout le suffixe de noyau. La passe de renommage de la série mettra chaque nom en conformité ; d'ici là, la colonne **Noyau** des tables fait foi.

## Pourquoi cette série

La théorie des jeux est le **point de rencontre** entre l'optimisation (maximiser son gain), la logique (raisonner sur les croyances d'autrui) et l'informatique (algorithmes de résolution, formalisation en assistant de preuve).

La série est construite sur une **dualité délibérée simulation/preuve** :

- **Simulation (Python)** : calculer des équilibres, simuler des tournois itérés, entraîner des agents CFR. On *voit* la théorie en action : les équilibres émergent des interactions répétées, la coopération émerge de l'égoïsme même.
- **Preuve formelle (Lean 4)** : prouver l'existence d'équilibres, l'impossibilité d'Arrow, les axiomes de Shapley. On *certifie* les résultats : la machine vérifie ce que l'intuition avait suggéré.

Le notebook Python montre *pourquoi* l'équilibre de Nash est plausible ; le notebook Lean montre *pourquoi il existe forcément*. Le notebook Arrow de la sous-série SocialChoice montre que le théorème est *contre-intuitif* ; `Arrow.lean` prouve qu'il est *inévitable*.

**Parité .NET** : chaque notebook du parcours principal, à partir de 02, a un **jumeau C#** (.NET Interactive) qui réimplémente ses algorithmes sans librairie dédiée, en BCL .NET seule : élimination de Gauss pour Nash mixte, simplexe de Dantzig pour le minimax, CFR sur le poker de Kuhn, Shapley et Banzhaf, Vickrey, VCG et Gale-Shapley. La théorie se code sans boîte noire (marathon de parité #4956).

### Où la théorie des jeux sert

- **Enchères** (notebooks 11 et 16) : les mécanismes VCG et leurs dérivés fondent les enchères publicitaires en ligne et les ventes de fréquences télécom orchestrées par les États.
- **Marchés d'appariement** (notebooks 15 et 16) : l'algorithme de Gale-Shapley affecte des élèves aux écoles, des internes aux hôpitaux, et organise les dons d'organes par échanges croisés (prix Nobel d'économie 2012).
- **Poker et bluff optimal** (notebook 13) : Counterfactual Regret Minimization a permis à des programmes de battre les meilleurs joueurs humains au Texas Hold'em, première résolution d'un jeu majeur à information imparfaite.
- **Vote et gouvernance** (sous-série SocialChoice) : le théorème d'Arrow et les méthodes de Condorcet ou de Borda éclairent le choix d'un mode de scrutin, du vote citoyen à la gouvernance on-chain.
- **Coopération et évolution** (notebook 06) : le tournoi d'Axelrod et les dynamiques de réplication modélisent l'émergence de la coopération en biologie, en relations internationales et dans les protocoles pair-à-pair.
- **Crédibilité et dissuasion** (notebooks 10 à 12) : induction arrière, réputation et signaling formalisent la crédibilité des menaces, de la politique monétaire à la stratégie concurrentielle.
- **Assurance et information asymétrique** (approfondissement 17b) : Akerlof, Spence et Rothschild-Stiglitz formalisent la tarification quand l'assuré connaît son risque mieux que l'assureur, et pourquoi un marché peut s'effondrer en « marché des citrons ».

## Objectifs d'apprentissage

À l'issue du parcours principal, vous serez capable de :

1. **Modéliser** une interaction stratégique sous forme normale ou extensive, et y lire dominance, meilleure réponse, ensembles d'information et menaces crédibles.
2. **Calculer** des équilibres : Nash pur et mixte (Lemke-Howson), minimax et dualité LP en jeux à somme nulle, équilibre parfait en sous-jeux par induction arrière et avant.
3. **Simuler** des dynamiques d'apprentissage et d'évolution : tournois itérés à la Axelrod, dynamique du réplicateur, processus de Moran en population finie, apprentissage multi-agent (CFR, NFSP, PSRO).
4. **Analyser** la coopération : valeur de Shapley, Core, condition de Bondareva-Shapley ; concevoir un mécanisme incitatif (principe de révélation, VCG).

Les approfondissements et la sous-série SocialChoice ajoutent deux compétences :

5. **Raisonner** sur l'agrégation collective : impossibilité d'Arrow, théorème de Sen, méthodes de Condorcet, Borda et Copeland, et leur encodage SAT résolu par Z3.
6. **Formaliser** ces résultats en Lean 4 et saisir ce que « prouver » veut dire dans un assistant de preuve.

Chaque notebook suit la même trame : introduction motivée, plan ancré, exemples exécutés, exercices corrigés, pensée pour un travail en autonomie.

## Parcours principal

Les notebooks à numéro nu forment le parcours principal. Chacun porte un concept et ne suppose que ce qui le précède. La colonne **Pour approfondir** renvoie aux lettres du palier, décrites dans [Approfondissements](#approfondissements) ; on peut toutes les ignorer au premier passage.

Les figures qui ponctuent le parcours sont extraites des sorties réelles des notebooks ; leur provenance exacte (notebook et cellule) est documentée dans [`assets/readme/MANIFEST.md`](assets/readme/MANIFEST.md).

### Phase 1 : jeux statiques et équilibres (01 à 06)

On apprend à représenter un jeu sous forme normale, puis à le résoudre : dominance, meilleure réponse, équilibre de Nash pur et mixte, théorème minimax. La phase se termine sur l'évolution : comment la coopération émerge d'un tournoi itéré. À l'issue, les trois piliers sont en place : Nash, minimax et évolution.

| # | Notebook | Ce qu'on y apprend | Durée | Public | Pour approfondir |
|---|----------|--------------------|-------|--------|------------------|
| 01 | Mise en route — [Python](GameTheory-01-Setup.ipynb) | Installation de Nashpy et OpenSpiel, premier dilemme du prisonnier | 20 min | Découverte | — |
| 02 | Forme normale — [Python](GameTheory-02-NormalForm.ipynb) ([suite](GameTheory-02-NormalForm-Part2-Python.ipynb)) · [C#](GameTheory-02-NormalForm-Csharp.ipynb) ([suite](GameTheory-02-NormalForm-Csharp-Part2.ipynb)) | Matrices de gains, dominance, meilleure réponse ; la suite énumère les supports mixtes d'un jeu N×N | 45 min | Découverte | [02b](GameTheory-02b-Lean-Definitions.ipynb) · [02c](GameTheory-02c-Travelers-Dilemma.ipynb) |
| 03 | Topologie des jeux 2×2 — [Python](GameTheory-03-Topology2x2.ipynb) · [C#](GameTheory-03-Topology2x2-Csharp.ipynb) | La table périodique de Robinson-Goforth : classer tous les jeux 2×2 ordinaux et dériver leur quotient | 80 min | Licence | [03a](GameTheory-03a-Chemins-de-Swaps.ipynb) · [03b](GameTheory-03b-Chambres-et-Murs.ipynb) · [03c](GameTheory-03c-Le-Joueur-LLM.ipynb) · [03d](GameTheory-03d-Plan-de-deformation.ipynb) · [03e](GameTheory-03e-Meta-Actions-Tarifees.ipynb) · [03h](GameTheory-03h-Deux-Especes-de-Fleches.ipynb) |
| 04 | Équilibre de Nash — [Python](GameTheory-04-NashEquilibrium.ipynb) · [C#](GameTheory-04-NashEquilibrium-Csharp.ipynb) | Nash pur et mixte, Lemke-Howson, analyse paramétrique | 60 min | Découverte | [04b](GameTheory-04b-Lean-NashExistence.ipynb) · [04c](GameTheory-04c-NashExistence-Python.ipynb) · [04d](GameTheory-04d-Marchandage-Asymetrique.ipynb) · [04e](GameTheory-04e-Reflective-Oracles.ipynb) · [04f](GameTheory-04f-Theories-Decision-Predicteur.ipynb) |
| 05 | Jeux à somme nulle — [Python](GameTheory-05-ZeroSum-Minimax.ipynb) · [C#](GameTheory-05-ZeroSum-Minimax-Csharp.ipynb) | Théorème minimax de von Neumann, programmation linéaire primal/dual | 40 min | Découverte | [05b](GameTheory-05b-Lean-Minimax.ipynb) |
| 06 | Évolution de la confiance — [Python](GameTheory-06-EvolutionTrust.ipynb) · [C#](GameTheory-06-EvolutionTrust-Csharp.ipynb) | Tournoi d'Axelrod, tit-for-tat, dynamique du réplicateur, processus de Moran en population finie | 65 min | Découverte | [06b](GameTheory-06b-Lean-RepeatedGames.ipynb) · [06c](GameTheory-06c-RepeatedGames-FolkTheorem.ipynb) · [06d](GameTheory-06d-Sympathie-vs-Engagement.ipynb) · [06e](GameTheory-06e-Open-Source-Game-Theory.ipynb) · [06f](GameTheory-06f-Bounded-Agents-Python.ipynb) · [06f bis](GameTheory-06f-Bounded-Proofs-Reasoning-Costs.ipynb) · [06g](GameTheory-06g-Bounded-Agents-Lean.ipynb) · [06g bis](GameTheory-06g-Simulation-Based-Program-Equilibria.ipynb) · [06h](GameTheory-06h-Transparent-Institutions.ipynb) |

Les deux figures suivantes, bâties sur le Dilemme du Prisonnier, illustrent les deux gestes fondateurs de cette phase : **représenter** un jeu, puis le **résoudre**.

![Matrice de gains 2×2 du Dilemme du Prisonnier ; la case (Défaire, Défaire) = (1, 1) est encadrée en bleu comme unique équilibre de Nash.](assets/readme/gt1-setup.png)

*`GameTheory-01-Setup` — représenter un jeu sous forme normale : la matrice des gains du Dilemme du Prisonnier. Chaque case porte le couple (gain Ligne, gain Colonne) ; la case (Défaire, Défaire) = (1, 1), encadrée en bleu, est l'unique équilibre de Nash, bien que (Coopérer, Coopérer) = (3, 3) soit collectivement supérieur.*

![Le même jeu résolu par la méthode des meilleures réponses : soulignements bleus (joueur Ligne), rouges (joueur Colonne), case verte à leur intersection.](assets/readme/gt2-normalform.png)

*`GameTheory-02-NormalForm` — résoudre un jeu : on souligne la meilleure réponse de chaque joueur (bleu = joueur Ligne, rouge = joueur Colonne). La seule case où les deux soulignements coïncident (en vert) est l'équilibre de Nash.*

### Phase 2 : jeux dynamiques et information incomplète (07 à 12)

Le modèle s'enrichit du temps et de l'incertitude : arbres de jeu et ensembles d'information, jeux combinatoires, induction arrière puis avant, jeux bayésiens et jeux de réputation. Cette phase présuppose la phase 1.

| # | Notebook | Ce qu'on y apprend | Durée | Public | Pour approfondir |
|---|----------|--------------------|-------|--------|------------------|
| 07 | Forme extensive — [Python](GameTheory-07-ExtensiveForm.ipynb) · [C#](GameTheory-07-ExtensiveForm-Csharp.ipynb) | Arbres de jeu, ensembles d'information, stratégies comportementales | 50 min | Licence | — |
| 08 | Jeux combinatoires — [Python](GameTheory-08-CombinatorialGames.ipynb) · [C#](GameTheory-08-CombinatorialGames-Csharp.ipynb) | Positions P/N, Nim, valeurs de Grundy, théorème de Sprague-Grundy | 55 min | Licence | [08b](GameTheory-08b-Lean-CombinatorialGames.ipynb) · [08c](GameTheory-08c-CombinatorialGames-Python.ipynb) · [08d](GameTheory-08d-Lean-CGT-Native.ipynb) |
| 09 | Induction arrière — [Python](GameTheory-09-BackwardInduction.ipynb) · [C#](GameTheory-09-BackwardInduction-Csharp.ipynb) | Induction arrière, mille-pattes, escalade, engagement | 55 min | Licence | [09b](GameTheory-09b-Commitment-Stackelberg.ipynb) · [09c](GameTheory-09c-Stackelberg-SecurityGame.ipynb) |
| 10 | Induction avant et SPE — [Python](GameTheory-10-ForwardInduction-SPE.ipynb) · [C#](GameTheory-10-ForwardInduction-SPE-Csharp.ipynb) | Équilibre parfait en sous-jeux, menaces crédibles, induction avant | 60 min | Licence | — |
| 11 | Jeux bayésiens — [Python](GameTheory-11-BayesianGames.ipynb) · [C#](GameTheory-11-BayesianGames-Csharp.ipynb) | Types privés, croyances, équilibre bayésien | 55 min | Licence | [11b](GameTheory-11b-Lean-BayesianGamesExt.ipynb) |
| 12 | Jeux de réputation — [Python](GameTheory-12-ReputationGames.ipynb) · [C#](GameTheory-12-ReputationGames-Csharp.ipynb) | Signaling, cheap talk, réputation (Kreps-Wilson) | 50 min | Licence | — |

![Arbre d'un jeu séquentiel (choix Out/In puis Stag/Hare) et raisonnement d'induction avant menant au SPE (In, Stag, Stag) → (4, 4).](assets/readme/gt10-spe.png)

*`GameTheory-10-ForwardInduction-SPE` — l'induction avant sur la forme extensive. L'ensemble d'information de J2 (ellipse pointillée) l'empêche de distinguer les deux nœuds ; mais en jouant « In » plutôt que l'option extérieure « Out » (garantie de 2), J1 révèle son intention de jouer Stag. Ce raisonnement « brûle » l'équilibre (Hare, Hare) et sélectionne le sous-jeu parfait (In, Stag, Stag) de valeur (4, 4).*

### Phase 3 : algorithmes, coopération, mécanismes, apprentissage (13 à 17)

La dernière phase ouvre les frontières de la discipline : CFR pour les jeux à information imparfaite, jeux différentiels, théorie coopérative, conception de mécanismes, apprentissage multi-agent. Le palier 16 sert aussi d'escalier vers la [sous-série SocialChoice](#sous-série-socialchoice), consacrée à l'agrégation des préférences.

| # | Notebook | Ce qu'on y apprend | Durée | Public | Pour approfondir |
|---|----------|--------------------|-------|--------|------------------|
| 13 | Information imparfaite et CFR — [Python (WSL)](GameTheory-13-ImperfectInfo-CFR.ipynb) · [C#](GameTheory-13-ImperfectInfo-CFR-Csharp.ipynb) | Counterfactual Regret Minimization, MCCFR, Deep CFR sur le poker | 70 min | Licence | [13b](GameTheory-13b-Safe-Subgame-Solving.ipynb) · [13c](GameTheory-13c-Safe-Subgame-Solving-Csharp.ipynb) · [13d](GameTheory-13d-Optimistic-CFR.ipynb) |
| 14 | Jeux différentiels — [Python](GameTheory-14-DifferentialGames.ipynb) · [C#](GameTheory-14-DifferentialGames-Csharp.ipynb) | Jeux en temps continu, boucle ouverte et fermée, Stackelberg, poursuite-évasion | 60 min | Licence | — |
| 15 | Jeux coopératifs — [Python](GameTheory-15-CooperativeGames.ipynb) · [C#](GameTheory-15-CooperativeGames-Csharp.ipynb) | Valeur de Shapley, Core, condition de Bondareva-Shapley | 65 min | Licence | [15b](GameTheory-15b-Lean-CooperativeGames.ipynb) · [15c](GameTheory-15c-CooperativeGames-Python.ipynb) · [15d](GameTheory-15d-Mobius-Coalitions.ipynb) · [15e](GameTheory-15e-Coalition-Power-SMT.ipynb) · [15f](GameTheory-15f-Shapley-Groupes.ipynb) |
| 16 | Conception de mécanismes — [Python](GameTheory-16-MechanismDesign.ipynb) · [C#](GameTheory-16-MechanismDesign-Csharp.ipynb) | Principe de révélation, VCG et la non-monotonie de son revenu, appariement stable de Gale-Shapley | 65 min | Licence | [16b](GameTheory-16b-Automated-Mechanism-Design.ipynb) · [16c](GameTheory-16c-Extraction-de-Revenu-DSIC-IR.ipynb) · [16d](GameTheory-16d-Echange-de-Reins.ipynb) · [16e](GameTheory-16e-LLM-Players-Othman-Sandholm.ipynb) · sous-série [SocialChoice](SocialChoice/README.md) |
| 17 | Apprentissage multi-agent — [Python (WSL)](GameTheory-17-MultiAgent-RL.ipynb) · [C#](GameTheory-17-MultiAgent-RL-Csharp.ipynb) | Self-play, fictitious play, NFSP, PSRO, introduction à AlphaZero | 55 min | Licence | [17b](GameTheory-17b-Asymmetric-Information.ipynb) · [17c](GameTheory-17c-Lean-Lemons-Certificat.ipynb) · [17c bis](GameTheory-17c-Market-to-Balance-Sheet.ipynb) · [17d](GameTheory-17d-Lean-Screening-Signaling.ipynb) |

Les trois figures suivantes échantillonnent cette phase : l'apprentissage d'un équilibre en information imparfaite, la stabilité coopérative, la convergence d'agents en auto-apprentissage.

![CFR sur le poker de Kuhn : à gauche la valeur du jeu converge vers le Nash −0,0556 en 10 000 itérations, à droite les probabilités de mise par carte (J/Q/K) rejoignent le Nash théorique (étoiles).](assets/readme/gt13-cfr.png)

*`GameTheory-13-ImperfectInfo-CFR` — le Counterfactual Regret Minimization sur le poker de Kuhn. À gauche, la moyenne mobile (rouge) de l'utilité de J1 converge vers la valeur de Nash du jeu (−0,0556, pointillé vert) malgré le bruit par itération. À droite, les probabilités de mise apprises pour chaque carte (J/Q/K) rejoignent les étoiles du Nash théorique : l'algorithme reconstruit le bluff optimal sans jamais connaître la stratégie adverse.*

![Simplexe des allocations d'un jeu coopératif à 3 firmes (v(N) = 9) : le Core en vert, la valeur de Shapley marquée d'une étoile rouge au centre.](assets/readme/gt15-shapley.png)

*`GameTheory-15-CooperativeGames` — la répartition d'une valeur commune v(N) = 9 entre trois firmes A, B, C. Chaque point du triangle est un partage ; les points verts forment le **Core** (les partages qu'aucune coalition ne peut contester), et l'étoile rouge est la **valeur de Shapley**, ici à l'intérieur du Core, donc stable.*

![Apprentissage multi-agent sur Pierre-Feuille-Ciseaux : à gauche l'exploitabilité (le self-play naïf oscille, le fictitious play décroît), à droite les fréquences convergent vers le Nash uniforme.](assets/readme/gt17-marl.png)

*`GameTheory-17-MultiAgent-RL` — deux dynamiques d'apprentissage sur Pierre-Feuille-Ciseaux. À gauche (échelle log), le self-play naïf reste exploitable en oscillant, tandis que le fictitious play voit son exploitabilité décroître régulièrement. À droite, les fréquences du fictitious play convergent vers le Nash uniforme (1/3, 1/3, 1/3) : la convergence de Robinson (1951) en action.*

### Concepts clés du parcours

| Concept | Description | Palier |
|---------|-------------|--------|
| **Équilibre de Nash** | Profil de stratégies où aucun joueur ne gagne à dévier unilatéralement | 04 |
| **Minimax** | Stratégie qui minimise la perte maximale, en jeu à somme nulle | 05 |
| **Processus de Moran** | Dynamique stochastique en population finie : la dérive peut fixer une stratégie sous-optimale, ce que la dynamique du réplicateur, déterministe, ne fait pas | 06 |
| **Positions P/N** | Positions perdantes (*Previous*) et gagnantes (*Next*) d'un jeu combinatoire | 08 |
| **Sprague-Grundy** | Théorème qui ramène tout jeu combinatoire impartial à un tas de Nim | 08 |
| **SPE** | Équilibre parfait en sous-jeux : un Nash crédible dans chaque sous-jeu | 09-10 |
| **CFR** | Counterfactual Regret Minimization : convergence vers Nash en information imparfaite | 13 |
| **Valeur de Shapley** | Répartition équitable des gains d'un jeu coopératif | 15 |
| **Core** | Ensemble des allocations qu'aucune coalition ne peut contester | 15 |
| **VCG** | Mécanisme où dire la vérité est une stratégie dominante | 16 |
| **Théorème d'Arrow** | Impossibilité d'une agrégation parfaite des préférences | SocialChoice |
| **Information asymétrique** | Un agent connaît son type mieux que l'autre : contre-sélection, signal coûteux, screening | 17b |
| **Méta-action tarifée** | Réécrire ses propres préférences déclarées au prix d'échelons de rang : changer les règles a un coût, un seuil de migration et ses propres équilibres | 03e |

## Approfondissements

Une lettre creuse le palier dont elle porte le numéro. On l'ouvre pour aller plus loin sur ce palier, pas pour avancer dans la série : chaque table ci-dessous suppose le notebook du palier déjà lu, et signale les prérequis en plus quand il y en a. Les paliers 01, 07, 10, 12 et 14 n'en portent pas.

### Autour de 02 — forme normale

| Lettre | Notebook | Ce qu'il ajoute | Noyau | Public |
|--------|----------|-----------------|-------|--------|
| 02b | [Définitions en Lean](GameTheory-02b-Lean-Definitions.ipynb) | Formaliser un jeu 2×2, les stratégies mixtes et la définition de Nash en Lean 4 | Lean | Licence |
| 02c | Dilemme du voyageur — [Python](GameTheory-02c-Travelers-Dilemma.ipynb) · [C#](GameTheory-02c-Travelers-Dilemma-Csharp.ipynb) | Basu (1994) : l'élimination itérée des stratégies dominées mène à (2, 2), que contredit le comportement humain ; le bonus r* = 1 où le paradoxe se dissout | Python · C# | Licence |

### Autour de 03 — géométrie ordinale des jeux

Ces lettres prolongent la table périodique du 03 en une géométrie de l'espace des jeux : murs, distances, déformations, méta-actions. Lire 03b avant 03a et 03h, qui s'appuient sur ses murs ; 03e fait la synthèse.

| Lettre | Notebook | Ce qu'il ajoute | Noyau | Public |
|--------|----------|-----------------|-------|--------|
| 03b | [Chambres et murs](GameTheory-03b-Chambres-et-Murs.ipynb) | Les jeux stricts comme chambres d'un arrangement, les égalités comme murs : incidence mur/chambre, graphe des chambres, swaps en longueurs de Coxeter | Python | Recherche |
| 03a | [Chemins de swaps](GameTheory-03a-Chemins-de-Swaps.ipynb) | À quelle distance sont deux jeux : parcours en largeur, théorème de décomposition, certificat Lean indépendant du plus court chemin | Python | Licence |
| 03h | [Deux espèces de flèches](GameTheory-03h-Deux-Especes-de-Fleches.ipynb) | Le théorème fini du chemin minimal : quand un swap traverse un mur ; la conjecture naïve réfutée, la condition exacte vérifiée | Python | Recherche |
| 03c | [Le joueur LLM](GameTheory-03c-Le-Joueur-LLM.ipynb) | Un modèle de langage placé dans la table périodique et confronté à ses transformations ordinales | Python | Licence |
| 03d | [Plan de déformation](GameTheory-03d-Plan-de-deformation.ipynb) | Biens publics non linéaires et déformation continue de l'espace stratégique | Python | Licence |
| 03e | [Méta-actions tarifées](GameTheory-03e-Meta-Actions-Tarifees.ipynb) | Changer les règles comme action payante : coût en échelons de rang, seuil de migration, méta-jeu ; puis le parcours complet, du jeu nommé au coût de la méta-action | Python | Recherche |

### Autour de 04 — existence et nature de l'équilibre

| Lettre | Notebook | Ce qu'il ajoute | Noyau | Public |
|--------|----------|-----------------|-------|--------|
| 04b | [Existence de Nash en Lean](GameTheory-04b-Lean-NashExistence.ipynb) | Le cadre de la preuve d'existence formalisé en Lean 4 : simplexe, convexité, point fixe de Brouwer ; quelques étapes d'arithmétique flottante y restent admises | Lean | Licence |
| 04c | Point fixe discriminant — [Python](GameTheory-04c-NashExistence-Python.ipynb) · [C#](GameTheory-04c-NashExistence-Csharp.ipynb) | Brouwer rendu testable : la carte `perturbed_br` déplace un profil non équilibré et laisse fixe l'équilibre (voir [Pour aller plus loin](#pour-aller-plus-loin)) | Python · C# | Licence |
| 04d | [Marchandage asymétrique](GameTheory-04d-Marchandage-Asymetrique.ipynb) | Point de désaccord, faisceau de dépendance, contre-exemple au principe du moindre intérêt | Python | Licence |
| 04e | [Oracles réflexifs](GameTheory-04e-Reflective-Oracles.ipynb) | Fallenstein, Taylor et Christiano (2015) : un agent qui raisonne sur un modèle de lui-même, l'écart CDT/EDT, un Nash réflexivement cohérent | Python | Recherche |
| 04f | [Théories de la décision face à un prédicteur](GameTheory-04f-Theories-Decision-Predicteur.ipynb) | EDT, CDT et UDT sur Newcomb, la lésion de Fisher et d'autres problèmes dans un seul cadre générique ; 2TDT-1CDT ; inattention rationnelle | Python | Recherche |

### Autour de 05 — minimax

| Lettre | Notebook | Ce qu'il ajoute | Noyau | Public |
|--------|----------|-----------------|-------|--------|
| 05b | [Minimax en Lean](GameTheory-05b-Lean-Minimax.ipynb) | Le théorème de von Neumann prouvé sans `sorry` dans le lake `minimax_lean` (via Sion), vérifié dans le noyau Lean | Lean | Licence |

### Autour de 06 — jeux répétés, agents transparents et bornés

06c est le prolongement naturel du 06. Les lettres 06e à 06h forment un chantier sur les agents dont le programme est lisible ou le calcul borné, à lire dans l'ordre. Les lettres 06f et 06g sont chacune portées par deux notebooks ; la passe de renommage leur donnera des lettres distinctes.

| Lettre | Notebook | Ce qu'il ajoute | Noyau | Public |
|--------|----------|-----------------|-------|--------|
| 06c | Folk Theorem — [Python](GameTheory-06c-RepeatedGames-FolkTheorem.ipynb) · [C#](GameTheory-06c-RepeatedGames-FolkTheorem-Csharp.ipynb) | Horizon fini et effondrement par induction arrière, horizon infini et grim trigger, condition δ ≥ (T−R)/(T−P), Folk Theorem | Python · C# | Licence |
| 06b | [Jeux répétés en Lean](GameTheory-06b-Lean-RepeatedGames.ipynb) | Compagnon formel du 06c : les modules du lake `game_theory_lean/RepeatedGames` lus et exécutés, dont `grim_trigger_sustains_iff` prouvé sans `sorry` | Python, lit Lean | Licence |
| 06d | [Sympathie contre engagement](GameTheory-06d-Sympathie-vs-Engagement.ipynb) | Séparer empiriquement sympathie et engagement par statique comparative sur les gains d'autrui (prérequis en plus : 06c) | Python | Recherche |
| 06e | [Open-source game theory](GameTheory-06e-Open-Source-Game-Theory.ipynb) | Des programmes lisibles l'un par l'autre : l'engagement vérifiable change l'équilibre du dilemme | Python | Recherche |
| 06f | [Agents bornés](GameTheory-06f-Bounded-Agents-Python.ipynb) | Agents-programmes à budget de calcul explicite : ce que le plafond fait aux équilibres atteignables | Python | Recherche |
| 06f bis | [Preuves bornées](GameTheory-06f-Bounded-Proofs-Reasoning-Costs.ipynb) | À borne de calcul donnée, quelles propriétés restent prouvables : le coût du raisonnement comme paramètre du jeu | Python | Recherche |
| 06g | [Agents bornés en Lean](GameTheory-06g-Bounded-Agents-Lean.ipynb) | La borne de raisonnement formalisée et exécutée en Lean | Lean | Recherche |
| 06g bis | [Équilibres par simulation](GameTheory-06g-Simulation-Based-Program-Equilibria.ipynb) | Équilibres de programmes qui se simulent mutuellement | Python | Recherche |
| 06h | [Institutions transparentes](GameTheory-06h-Transparent-Institutions.ipynb) | La transparence du code comme mécanisme d'engagement institutionnel | Python | Recherche |

### Autour de 08 — jeux combinatoires

| Lettre | Notebook | Ce qu'il ajoute | Noyau | Public |
|--------|----------|-----------------|-------|--------|
| 08b | [Jeux combinatoires en Lean](GameTheory-08b-Lean-CombinatorialGames.ipynb) | Jeux combinatoires formels, Nim et Sprague-Grundy en Lean | Lean | Licence |
| 08c | Variantes — [Python](GameTheory-08c-CombinatorialGames-Python.ipynb) · [C#](GameTheory-08c-CombinatorialGames-Csharp.ipynb) | Périodicité des valeurs de Grundy, Wythoff, jeux composites, Chomp | Python · C# | Licence |
| 08d | [Bibliothèque canonique en Lean](GameTheory-08d-Lean-CGT-Native.ipynb) | La même théorie exécutée depuis `vihdzp/combinatorial-games` (lake `conway_cgt_lean`) : jeux, surréels, nimbers | Lean | Recherche |

### Autour de 09 — engagement et Stackelberg

| Lettre | Notebook | Ce qu'il ajoute | Noyau | Public |
|--------|----------|-----------------|-------|--------|
| 09b | [Engagement et Stackelberg](GameTheory-09b-Commitment-Stackelberg.ipynb) | L'engagement contraignant qui transforme la meilleure réponse d'autrui, l'annonce révocable dissoute par induction arrière, le seuil de crédibilité | Python | Licence |
| 09c | [Security game](GameTheory-09c-Stackelberg-SecurityGame.ipynb) | Le défenseur s'engage, l'attaquant observe avec bruit : robustesse du patrouilleur à un capteur imparfait | Python | Licence |

### Autour de 11 — jeux bayésiens

| Lettre | Notebook | Ce qu'il ajoute | Noyau | Public |
|--------|----------|-----------------|-------|--------|
| 11b | [Vickrey en Lean](GameTheory-11b-Lean-BayesianGamesExt.ipynb) | Le théorème de Vickrey (enchère au second prix : dire la vérité est dominant) prouvé sans `sorry` dans le lake `lean_game_defs_ext` | Lean | Licence |

### Autour de 13 — résolution de sous-jeux

| Lettre | Notebook | Ce qu'il ajoute | Noyau | Public |
|--------|----------|-----------------|-------|--------|
| 13b | [Résolution sûre de sous-jeux](GameTheory-13b-Safe-Subgame-Solving.ipynb) | Recoller un sous-jeu résolu à part : un mauvais recollement produit un témoin adversarial explicite | Python | Recherche |
| 13c | [Résolution sûre, jumeau C#](GameTheory-13c-Safe-Subgame-Solving-Csharp.ipynb) | Jumeau C# du 13b : reproduction, audit des poids de chemin, meilleure réponse énumérée ; la loi survit, les valeurs absolues non | C# | Recherche |
| 13d | [CFR optimiste](GameTheory-13d-Optimistic-CFR.ipynb) | OFTRL stable-prédictif : la variante qui stabilise la convergence par prédiction | Python | Recherche |

### Autour de 15 — coalitions et pouvoir

| Lettre | Notebook | Ce qu'il ajoute | Noyau | Public |
|--------|----------|-----------------|-------|--------|
| 15b | [Jeux coopératifs en Lean](GameTheory-15b-Lean-CooperativeGames.ipynb) | Axiomes de Shapley, Core et Bondareva-Shapley formels (lake `game_theory_lean/CooperativeGames`) | Lean | Licence |
| 15c | Exemples avancés — [Python](GameTheory-15c-CooperativeGames-Python.ipynb) · [C#](GameTheory-15c-CooperativeGames-Csharp.ipynb) | Jeu des gants, Core vide en majorité simple, indices de pouvoir | Python · C# | Licence |
| 15d | [Möbius sur les coalitions](GameTheory-15d-Mobius-Coalitions.ipynb) | Décomposition de Möbius sur le treillis des coalitions, dividendes d'interaction | Python | Recherche |
| 15e | [Pouvoir coalitionnel et SMT](GameTheory-15e-Coalition-Power-SMT.ipynb) | Calcul exhaustif, encodage SMT borné et preuve | Python | Recherche |
| 15f | [Shapley de groupe](GameTheory-15f-Shapley-Groupes.ipynb) | Évaluer une équipe comme une unité : le meilleur binôme n'est pas celui des deux meilleurs individus | Python | Recherche |

### Autour de 16 — mécanismes

| Lettre | Notebook | Ce qu'il ajoute | Noyau | Public |
|--------|----------|-----------------|-------|--------|
| 16c | [Extraction de revenu](GameTheory-16c-Extraction-de-Revenu-DSIC-IR.ipynb) | Le revenu sous contraintes d'incitation (DSIC) et de participation (IR) : ce que VCG laisse sur la table | Python | Licence |
| 16d | [Échange de reins](GameTheory-16d-Echange-de-Reins.ipynb) | Graphe de compatibilité, cycles et chaînes de donneurs, arbitrage entre cardinalité et équité | Python | Licence |
| 16b | [Conception automatique de mécanismes](GameTheory-16b-Automated-Mechanism-Design.ipynb) | Synthétiser un mécanisme sous contraintes, puis vérifier ses propriétés | Python | Recherche |
| 16e | [Joueurs LLM](GameTheory-16e-LLM-Players-Othman-Sandholm.ipynb) | Pilote : des agents de langage hétérogènes joueurs d'un mécanisme d'Othman-Sandholm | Python | Recherche |

L'agrégation des préférences (Arrow, vote, manipulation) se poursuit dans la [sous-série SocialChoice](#sous-série-socialchoice).

### Autour de 17 — information asymétrique

17b ne demande, en plus du 17, que le palier 11 (types privés).

| Lettre | Notebook | Ce qu'il ajoute | Noyau | Public |
|--------|----------|-----------------|-------|--------|
| 17b | [Information asymétrique](GameTheory-17b-Asymmetric-Information.ipynb) | Les modèles fondateurs : Akerlof (marché des citrons), Spence (signal coûteux), Rothschild-Stiglitz (screening), Wilson-Miyazaki | Python | Licence |
| 17c | [Certificat d'Akerlof en Lean](GameTheory-17c-Lean-Lemons-Certificat.ipynb) | Le certificat du lake `asymmetric_information_lean` exécuté : seuil de pooling exact, monotonie, spirale de prix | Lean | Recherche |
| 17d | [Screening et signaling en Lean](GameTheory-17d-Lean-Screening-Signaling.ipynb) | Les autres modules du même lake : non-existence de Rothschild-Stiglitz, intervalle séparateur de Spence et minimalité de Riley, Wilson-Miyazaki, pont bayésien | Lean | Recherche |
| 17c bis | [Du marché au bilan](GameTheory-17c-Market-to-Balance-Sheet.ipynb) | L'équilibre de marché lu comme un bilan d'espérances : le pont vers la théorie de la décision | Python | Licence |

La lettre 17c est portée par deux notebooks ; la passe de renommage leur donnera des lettres distinctes.

## Parcours transverses

Quatre itinéraires qui traversent paliers et lettres pour un public précis.

**Formalisation Lean** (~4h) — pour qui vient de la série [SymbolicAI/Lean](../SymbolicAI/Lean/README.md). Familiarité avec Lean 4 supposée (tactiques de base, types inductifs) ; les notebooks Python correspondants donnent l'intuition sans être des prérequis.

1. **02b** : jeu 2×2, stratégies mixtes, Nash
2. **04b** : Brouwer et le cadre de l'existence de Nash
3. **05b** : von Neumann par Sion, sans `sorry`
4. **08b**, puis **08d** : jeux combinatoires, puis la bibliothèque canonique
5. **15b** : axiomes de Shapley, Core
6. **SocialChoice 01b** : Arrow, Sen, électeur médian

**Applications** (~6h) — pour qui préfère les cas d'usage aux fondements.

1. **05** : programmation linéaire, dualité
2. **06** : émergence de la coopération
3. **13** : poker, minimisation du regret
4. **16** : enchères VCG, allocation, et le piège de la non-monotonie du revenu
5. **SocialChoice 03** : Condorcet, Borda, modèles électoraux

**Information asymétrique et assurance** (~4h30) — pour l'assurance, la banque ou la régulation : un agent en sait plus que l'autre (le client sur son risque, l'emprunteur sur sa solvabilité, le vendeur sur sa qualité).

1. **11** : types privés, croyances, équilibre bayésien
2. **12** : signaling, cheap talk
3. **16** : principe de révélation, contrat sous contrainte d'incitation
4. **17b** : Akerlof, Spence, Rothschild-Stiglitz, Wilson-Miyazaki
5. **17c** puis **17d** : les mêmes modèles certifiés dans le lake `asymmetric_information_lean`

**Informatique théorique** (~5h) — pour l'algorithmique et la complexité.

1. **02** : matrices de gains, dominance
2. **04** : Lemke-Howson, PPAD-complétude
3. **08** : Sprague-Grundy, nimbers
4. **13** : regret contrefactuel, convergence
5. **SocialChoice 04** : théorèmes encodés en SAT, preuves d'insatisfiabilité

## Sous-série SocialChoice

Le dossier [SocialChoice/](SocialChoice/README.md) traite l'agrégation des préférences : Arrow, Sen, méthodes de vote, encodage SAT/Z3, manipulation, comités. Son README porte son propre parcours et ses propres approfondissements.

Depuis le parcours principal, on y entre après le palier 16. Aucun notebook d'escalier ne la présente encore depuis la série mère : le palier 16 en tient lieu. Ses formalisations vivent pour l'instant dans les lakes de la série mère (`game_theory_lean/SocialChoice`, et le lake de référence `social_choice_lean_peters`).

| # | Notebook | Ce qu'on y apprend | Noyau | Public |
|---|----------|--------------------|-------|--------|
| 01 | Théorème d'Arrow — [Python](SocialChoice/01-Arrow-Impossibility-Theorem.ipynb) · [C#](SocialChoice/01-Arrow-Impossibility-Theorem-Csharp.ipynb) | L'impossibilité d'Arrow, par la preuve et par la simulation | Python · C# | Licence |
| 01b | [Choix social formel en Lean](SocialChoice/01b-Lean-SocialChoice-Formal.ipynb) | Arrow, Sen et l'électeur médian en Lean, et une visite du lake de référence de D. Peters | Lean | Recherche |
| 03 | Méthodes de vote — [Python](SocialChoice/03-Voting-Methods.ipynb) · [C#](SocialChoice/03-Voting-Methods-Csharp.ipynb) | Condorcet, Borda, Copeland, modèle de Downs, paradoxes électoraux | Python · C# | Découverte |
| 04 | Agrégation par SAT et Z3 — [Python (WSL)](SocialChoice/04-Computational-Aggregation-SAT-Z3.ipynb) · [C#](SocialChoice/04-Computational-Aggregation-SAT-Z3-Csharp.ipynb) | Arrow encodé en SAT, preuve d'insatisfiabilité, relaxations | Python · C# | Licence |
| 05 | [Gibbard-Satterthwaite](SocialChoice/05-Gibbard-Satterthwaite.ipynb) | La manipulation comme témoin : la manipulabilité exhibée par le code, pas postulée | Python | Licence |
| 06 | [Möbius, pouvoir et manipulation](SocialChoice/06-Mobius-Aggregation-Pouvoir-Manipulation.ipynb) | Dividendes de Harsanyi, poids contre pouvoir, manipulation pondérée | Python | Recherche |
| 07 | [Comités et Core](SocialChoice/07-Committees-Core.ipynb) | Élections de comité par approbation : core, quotas, certificats de paiement | Python | Recherche |

## Extensions au-delà du parcours

Les notebooks numérotés de 18 à 25 ne prolongent pas le parcours principal. Ce sont des extensions autonomes : chacune isole un geste qui modifie l'espace des jeux (composition, abstraction, témoin d'impossibilité) plutôt qu'une solution dans un jeu donné. Leur numéro nu est un héritage de leur livraison, pas une étape du parcours ; leur rattachement aux paliers est à l'étude avec la gradation de la série (#15615).

| # | Notebook | Ce qu'on y apprend | Noyau | Public |
|---|----------|--------------------|-------|--------|
| 18 | [Open games et lentilles](GameTheory-18-Open-Games-et-Lentilles.ipynb) | Une représentation locale qui modifie le contexte global dont elle est issue | Python | Recherche |
| 18b | [Casser la composition](GameTheory-18b-Casser-la-Composition.ipynb) | Contre-exemples à la compositionnalité des équilibres d'open games | Python | Recherche |
| 19 | [Abstraction à dette](GameTheory-19-Abstraction-a-Dette.ipynb) | Mesurer ce que perd une représentation simplifiée | Python | Recherche |
| 20 | [Chemin minimal](GameTheory-20-Chemin-Minimal-Robinson-Goforth.ipynb) | Un témoin de chemin minimal construit par un générateur, vérifié par un composant indépendant | Python | Recherche |
| 20b | [Témoins d'impossibilité](GameTheory-20b-Chemin-Minimal-Temoins-Impossibilite.ipynb) | Le chemin minimal qui ne peut pas exister, exhibé par le code | Python | Recherche |
| 20c | [Jeux ordinaux 3×2](GameTheory-20c-Chemin-Minimal-3x2-Ordinal.ipynb) | Le même théorème testé sur un second substrat | Python | Recherche |
| 21 | [Translateur Life](GameTheory-21-Loi-II-Translateur-Life.ipynb) | Synthèse d'un translateur du jeu de la vie, et certificat d'impossibilité quand la traduction échoue | Python | Recherche |
| 22 | [Ensembles limites](GameTheory-22-Ensembles-Limites-Poincare-Bendixson.ipynb) | Poincaré-Bendixson en dimension 2 : point fixe, orbite périodique ou cycle hétérocline, classés mécaniquement, et l'échec du théorème au-delà du plan | Python | Recherche |
| 23 | [Affectation de Kuhn-Munkres](GameTheory-23-Munkres-Assignment.ipynb) | L'affectation optimale en arithmétique entière exacte, certifiée par dualité LP, et le pont vers le cœur de Shapley-Shubik | Python | Licence |
| 23b | [Affectation en Lean](GameTheory-23b-Lean-Assignment-Native.ipynb) | Dualité et optimalité de Kuhn-Munkres exécutées depuis le lake `assignment_lean` | Lean | Recherche |
| 24 | [Banc humour](GameTheory-24-Humour-Banc.ipynb) | Banc de calibration : forme partagée contre stimulus, matrice de confusion | Python | Recherche |
| 24b | [Banc humour, passage à l'échelle](GameTheory-24b-Humour-Banc-Dur.ipynb) | Comparaison de modèles de langage, circularité, paires minimales | Python | Recherche |
| 25 | [Persuasion bayésienne](GameTheory-25-Bayesian-Persuasion.ipynb) | La concavification évaluée par deux méthodes indépendantes (programme linéaire et enveloppe concave) dont l'accord est vérifié, avec un contrôle négatif | Python | Recherche |

## Installation

Le noyau de chaque notebook figure dans la colonne **Noyau** des tables et dans ses métadonnées.

### Python natif (la plupart des notebooks)

```bash
pip install -r MyIA.AI.Notebooks/GameTheory/requirements.txt
# open_spiel échoue sous Windows : c'est attendu, seuls les notebooks marqués WSL en ont besoin
```

### Python sous WSL (OpenSpiel : notebooks 13 et 17)

OpenSpiel ne compile pas nativement sous Windows. Les notebooks marqués **WSL** utilisent le kernel `Python (GameTheory WSL + OpenSpiel)` :

```bash
# 1. Dans WSL Ubuntu
cd /mnt/d/CoursIA/MyIA.AI.Notebooks/GameTheory/scripts
bash setup_wsl_openspiel.sh
```

```powershell
# 2. Côté Windows (PowerShell)
cd D:\CoursIA\MyIA.AI.Notebooks\GameTheory\scripts
.\setup_wsl_kernel.ps1
```

### Lean 4 (notebooks marqués Lean)

Les notebooks marqués **Lean** utilisent le kernel `Lean 4 (WSL)` :

```bash
# 1. Dans WSL Ubuntu
cd /mnt/d/CoursIA/MyIA.AI.Notebooks/GameTheory/scripts
bash setup_wsl_lean4.sh    # installe elan, Lean 4, le REPL et lean4_jupyter
```

```powershell
# 2. Côté Windows (PowerShell)
cd D:\CoursIA\MyIA.AI.Notebooks\GameTheory\scripts
.\setup_lean4_kernel.ps1   # enregistre le kernel lean4-wsl
```

### C# (jumeaux .NET)

Les jumeaux C# s'exécutent avec .NET Interactive (.NET 9) :

```bash
dotnet tool install --global Microsoft.dotnet-interactive
dotnet interactive jupyter install
```

### Vérification et configuration

```bash
jupyter kernelspec list
# doit montrer python3, et selon vos besoins gametheory-wsl, lean4-wsl, .net-csharp
```

Détails et dépannage : [install_wsl_kernel.md](install_wsl_kernel.md). Les clés d'API sont optionnelles (`cp .env.example .env`, puis compléter).

### Premier lancement

```bash
pip install -r MyIA.AI.Notebooks/GameTheory/requirements.txt
jupyter notebook MyIA.AI.Notebooks/GameTheory/GameTheory-01-Setup.ipynb
# puis GameTheory-02-NormalForm, et la suite du parcours principal
```

## FAQ et dépannage

### J'ai un Windows, puis-je suivre toute la série ?

Oui. Tout le Python tourne nativement sous Windows (Nashpy, NumPy, SciPy, Matplotlib, Z3), sauf les notebooks marqués WSL, qui demandent OpenSpiel. Les notebooks Lean demandent aussi WSL, pour le kernel `lean4-wsl`. Les scripts d'installation sont dans `scripts/` (voir [Installation](#installation)).

### Quel est le prérequis mathématique minimum ?

Algèbre linéaire de base (produit matrice-vecteur) et probabilités (espérance, loi uniforme). Les concepts de théorie des jeux sont introduits depuis zéro.

### Faut-il faire les notebooks Lean ?

Non. Ce sont des approfondissements, jamais des prérequis du parcours principal. Ils s'adressent à qui veut comprendre ce que « prouver » veut dire dans un assistant de preuve. Si vous n'avez jamais touché à Lean, commencez par la série [SymbolicAI/Lean](../SymbolicAI/Lean/README.md).

### Quelle différence entre Nash pur et Nash mixte ?

Un équilibre **pur** est un choix déterministe : chaque joueur choisit une seule stratégie. Un équilibre **mixte** autorise les probabilités : chaque joueur randomise entre plusieurs stratégies. Le notebook 04 couvre les deux et montre que tout jeu fini a au moins un équilibre mixte (Nash, 1951).

### Je suis bloqué sur un exercice Lean

Vérifiez d'abord votre environnement avec [Lean-1-Setup](../SymbolicAI/Lean/Lean-1-Setup.ipynb). La référence est [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/). Les exercices de cette série n'exigent que les tactiques introduites dans les notebooks, pas une connaissance détaillée de Mathlib.

### open_spiel échoue à l'installation sous Windows

C'est attendu : seuls les notebooks 13 et 17 en ont besoin. Pour tous les autres, installez les dépendances de `requirements.txt` ; le sous-ensemble minimal courant est :

```bash
pip install nashpy z3-solver matplotlib numpy
```

### Le kernel lean4-wsl ne démarre pas

Le premier démarrage via WSL peut prendre de 30 à 60 secondes. Si le kernel échoue :

1. Vérifiez que WSL répond : `wsl -d Ubuntu -- echo OK`
2. Vérifiez le wrapper : `wsl -d Ubuntu -- test -f ~/.lean4-kernel-wrapper.py && echo OK`
3. Relancez le kernel. Si l'échec persiste, voir [wsl-kernels.md](../../.claude/rules/wsl-kernels.md).

### Nashpy retourne plusieurs équilibres

C'est normal : un jeu peut avoir plusieurs équilibres, purs ou mixtes, et Nashpy les retourne tous. Le notebook 04 explique comment les interpréter et les départager.

### Les calculs d'équilibres sont lents

La complexité croît vite avec le nombre de stratégies. Pour les petits jeux, `nashpy` avec `method="support-enumeration"` suffit ; pour les grands, le notebook 13 approche l'équilibre par itération (CFR). Vérifiez aussi que les lignes et les colonnes de la matrice de gains ne sont pas inversées.

### Z3 retourne UNSAT trop vite

Si l'encodage SAT d'Arrow (SocialChoice 04) semble trivial, vérifiez le nombre de votants et d'alternatives : l'impossibilité apparaît à partir de 3 alternatives et 2 votants. En dessous, le solveur trouve une règle satisfaisante.

### Un lake Lean ne se construit pas

Chaque lake du dossier est un projet Lake indépendant, avec sa propre toolchain (`lean-toolchain`). Pour construire le module SocialChoice :

```bash
cd MyIA.AI.Notebooks/GameTheory/game_theory_lean
lake build SocialChoice
```

Vérifiez que `lean --version` correspond à la toolchain du lake ; si les dépendances échouent, lancez `lake exe cache get` puis `lake build`. Les lakes actifs sont listés dans [Formalisations Lean](#formalisations-lean).

## Après la série

- **Approfondir la formalisation** : la série [SymbolicAI/Lean](../SymbolicAI/Lean/README.md) prolonge les approfondissements Lean. Elle développe les compétences de preuve (tactiques, types inductifs, Mathlib) qui sous-tendent `Arrow.lean`, `Shapley.lean` et les preuves d'existence d'équilibres.
- **Apprendre plutôt que calculer** : la série [RL](../RL/README.md) reprend la théorie des jeux sous l'angle de l'apprentissage, où les stratégies d'équilibre ne sont plus calculées mais apprises par interaction. La série [Search](../Search/README.md) partage les arbres de jeu, le minimax et l'induction arrière.
- **Concevoir des règles** : la [sous-série SocialChoice](SocialChoice/README.md) et le palier 16 ouvrent sur la conception de mécanismes, c'est-à-dire concevoir des règles qui poussent des agents égoïstes vers un résultat collectivement souhaitable. La série [SmartContracts](../SymbolicAI/SmartContracts/README.md) prolonge ces mécanismes en gouvernance on-chain.
- **Une tension à méditer** : reprenez le notebook 06 et le tournoi d'Axelrod, où la coopération *émerge* de l'égoïsme ; puis confrontez-le au théorème d'Arrow, qui montre que certaines agrégations parfaites sont *impossibles*. L'émergence optimiste face à l'impossibilité démontrée : c'est la tension vivante de la série.

La théorie des jeux déplace la question de la décision : non plus « quelle est la meilleure action ? », mais **« quelle est la meilleure action, sachant que les autres, aussi rationnels que moi, raisonnent de même ? »**. La série donne le formalisme (formes normale et extensive, Nash, SPE, minimax, Shapley), la double validation (simulation numérique et preuve formelle) et le sens des applications (enchères, appariement, poker, vote).

## Pour aller plus loin

Cette partie réunit la matière de niveau **Recherche** : notes techniques sur des résultats précis du parcours, formalisations Lean, liens avec les autres séries, organisation du dossier.

### Processus de Moran : la population finie (palier 06)

Le round-robin déterministe du notebook 06 donne une hiérarchie stable où Grudger et TitForTat dominent. La **dynamique de Moran** (librairie [`axelrod`](https://github.com/Axelrod-Python/Axelrod), Knight et al., *JORS* 2016) modélise un autre régime : une population **finie** où chaque étape copie un joueur proportionnellement à son fitness puis en élimine un uniformément au hasard. Le §7bis du notebook exécute cette dynamique sur 25 graines :

| Stratégie | Fixations sur 25 graines |
|---|---|
| **Defector** | **7/25 (28 %)** |
| **Grudger** | 6/25 (24 %) |
| Win-Stay Lose-Shift | 4/25 (16 %) |
| Random (p = 0,5) | 3/25 (12 %) |
| **Tit For Tat** | **3/25 (12 %)** |
| Cooperator | 2/25 (8 %) |

TitForTat, dominant au tableau du round-robin, ne se fixe que dans 12 % des trajectoires. Le processus de Moran est **stochastique** : la **dérive** peut fixer une stratégie sous-optimale par simple fluctuation d'échantillonnage, indépendamment de son fitness. C'est la distinction canonique entre dynamique du réplicateur **en champ moyen, déterministe** (§5) et processus de Moran **fini, stochastique** (§7bis).

1. **Population finie n'est pas champ moyen.** Quand $N \to \infty$, le processus de Moran converge vers la dynamique du réplicateur ; à $N$ fini, le bruit d'échantillonnage domine dès que $|f_A - f_B| \lesssim 1/N$.
2. **Lire la sortie, pas l'intuition.** Ce que le tableau du round-robin annonce, la trajectoire stochastique le dément.
3. **Lecture écologique.** Le processus de Moran est l'outil de référence de la théorie évolutionnaire des jeux (Nowak, *Evolutionary Dynamics*, 2006).

### Point fixe discriminant : pourquoi `regret = 0` définit l'équilibre (approfondissement 04c)

La carte `perturbed_br` du notebook 04c illustre le point fixe de Brouwer sur Matching Pennies : un point fixe de `perturbed_br` est un profil où le vecteur de **regret** est nul. Tester cette propriété **seulement** à l'équilibre `(0.5, 0.5)` serait tautologique : le regret y est nul par définition, la perturbation ne fait rien, et « `(0.5, 0.5)` est point fixe » est vrai par construction.

Le notebook lève la tautologie par un contraste à deux points de départ :

| Départ | Vecteur de regret | `perturbed_br` renvoie | Point fixe ? |
|---|---|---|---|
| `(0.8, 0.2)` (non équilibre) | `[0.24, 0]` | `[0.8047, 0.1953]` ≠ départ | **Non** : la carte déplace le point |
| `(0.5, 0.5)` (équilibre de Nash) | `[0, 0]` | `(0.5, 0.5)` = départ | **Oui** |

1. **Regret nul équivaut à point fixe** (apprentissage sans regret, Hart et Mas-Colell 2000) : appliqué à `perturbed_br`, Brouwer n'a rien de magique, c'est le critère qui définit la convergence vers Nash.
2. **Anti-tautologie.** Tout test de point fixe, d'optimalité ou de convergence exige au moins un point de départ non équilibré, qui doit être déplacé.
3. **Lien avec le 04b.** Le notebook Lean 04b pose le cadre formel de l'existence (simplexe, convexité, point fixe) ; le 04c l'illustre numériquement. Preuve et simulation se complètent sans se substituer.

### Formalisations Lean

La série aligne simulation numérique et preuve formelle : les notebooks motivent (Lemke-Howson, Axelrod, Gale-Shapley), les lakes prouvent. L'inventaire complet (toolchains, statut de build, `sorry` résiduels) est tenu dans [LEAN_INVENTORY.md](LEAN_INVENTORY.md) ; la table ci-dessous ne sert qu'à retrouver, pour chaque lake, les notebooks qui l'enseignent ou le consomment.

| Lake | Ce qu'il prouve | Notebooks |
|------|-----------------|-----------|
| `game_theory_lean` (module SocialChoice) | Impossibilité d'Arrow, caractérisation de Sen | SocialChoice 01b |
| `game_theory_lean` (module CooperativeGames) | Bondareva-Shapley sans `sorry` (#3954), Core non vide sous équilibrage | 15, 15b |
| `game_theory_lean` (module StableMarriage) | Gale-Shapley : existence et optimalité côté proposant | 15b, 16 |
| `game_theory_lean` (module RepeatedGames) | Grim trigger certifié sans `sorry` (#4880) ; le Folk Theorem complet reste ouvert (`Folk.lean`) | 06b, 06c |
| `game_theory_lean` (module Swaps) | Certificat du plus court chemin de swaps | 03a |
| `minimax_lean` | Théorème minimax de von Neumann, via Sion | 05b |
| `lean_game_defs`, `lean_game_defs_ext` | Types de jeux partagés ; Vickrey sans `sorry` | 02b, 08b, 11b, 17d |
| `conway_cgt_lean` | Visite de la théorie des jeux combinatoires de Conway (`vihdzp/combinatorial-games`) | 08d |
| `assignment_lean` | Dualité faible et optimalité à gap nul de Kuhn-Munkres (#12598) | 23, 23b |
| `asymmetric_information_lean` | Akerlof (seuil de pooling exact), Spence, Rothschild-Stiglitz, Wilson-Miyazaki | 17b, 17c, 17d |
| `social_choice_lean_peters` | Lake de référence externe (D. Peters, MIT) : Gibbard-Satterthwaite, Split Cycle et d'autres règles | SocialChoice 01b, 07 |

Les anciens lakes autonomes du choix social, des jeux coopératifs, du mariage stable et des jeux répétés ont été absorbés dans `game_theory_lean` (#4365) ; `social_choice_lean/` et `repeated_games_lean/` ne restent que comme coquilles documentaires. Au niveau du dépôt, voir le [hub SymbolicAI/Lean](../SymbolicAI/Lean/README.md) et la feuille de route Lean ([#4038](https://github.com/jsboige/CoursIA/issues/4038)).

### Liens avec les autres séries

| Cette série | Série liée | Pont |
|-------------|------------|------|
| Lakes Lean (Arrow, Sen, Shapley, Vickrey) | [SymbolicAI/Lean](../SymbolicAI/Lean/README.md) | Même toolchain WSL, Mathlib partagée |
| Apprentissage multi-agent (NFSP, PSRO) | [RL](../RL/README.md) | Stratégies d'équilibre apprises par interaction plutôt que calculées |
| Arbres de jeu, induction arrière, minimax | [Search](../Search/README.md) | Même structure d'arbre, du minimax à MCTS |
| Mécanismes VCG, appariement de Gale-Shapley | [SymbolicAI/SmartContracts](../SymbolicAI/SmartContracts/README.md) | La conception de mécanismes se prolonge en gouvernance on-chain |
| Encodage SAT/Z3 d'Arrow | [SymbolicAI/SMT](../SymbolicAI/SMT/README.md) | Même solveur Z3 |

### Organisation du dossier

```
GameTheory/
├── GameTheory-*.ipynb             # parcours principal, approfondissements, extensions
├── SocialChoice/                  # sous-série Choix social (son propre README)
├── assets/readme/                 # figures du README et leur MANIFEST
├── game_theory_utils.py           # utilitaires partagés
├── limit_sets.py                  # détecteur d'ensembles limites (extension 22)
├── cooperative_games/             # Shapley, Core, valeur de groupe, exemples
├── trust_simulation/              # stratégies, tournoi d'Axelrod, visualisation
├── examples/                      # scripts autonomes (dilemme, CFR sur Kuhn, VCG, Stackelberg...)
├── tests/                         # tests unitaires des modules Python
├── scripts/                       # installation des kernels WSL (OpenSpiel, Lean)
├── game_theory_lean/              # lake multi-module (voir Formalisations Lean)
├── minimax_lean/  assignment_lean/  asymmetric_information_lean/  conway_cgt_lean/
├── lean_game_defs/  lean_game_defs_ext/  social_choice_lean_peters/
├── repeated_games_lean/  social_choice_lean/     # coquilles documentaires (absorbées)
├── LEAN_INVENTORY.md              # inventaire des lakes
├── install_wsl_kernel.md          # installation des kernels WSL
└── requirements.txt
```

Les tests unitaires des modules Python :

```bash
cd MyIA.AI.Notebooks/GameTheory
python -m pytest tests/ -v
python examples/prisoners_dilemma.py
```

Pour valider ou exécuter un notebook : `python scripts/notebook_tools/notebook_tools.py validate <chemin>` et `... execute <chemin>`, depuis la racine du dépôt.

### Comptes et maturité

Le bloc `CATALOG-STATUS` en tête de ce fichier fait foi pour le nombre de notebooks et leur maturité. Il est régénéré automatiquement sur `main` ; le [catalogue](../../COURSE_CATALOG.generated.md) donne le détail notebook par notebook.

## Ressources

### Références académiques

| Référence | Couverture |
|-----------|------------|
| Osborne & Rubinstein, *A Course in Game Theory* (1994) | Manuel de référence, paliers 01 à 12 |
| Osborne, *An Introduction to Game Theory* (2004) | Manuel alternatif |
| Russell & Norvig, *AIMA*, 4e éd., ch. 17-18 | Cadre général des jeux et des mécanismes |
| Nash, « Non-Cooperative Games » (1951) | Palier 04 |
| von Neumann, « Zur Theorie der Gesellschaftsspiele » (1928) | Palier 05 |
| Axelrod, *The Evolution of Cooperation* (1984) | Palier 06 |
| Conway, Berlekamp & Guy, *Winning Ways* (1982) | Palier 08 |
| Shapley, « A Value for n-Person Games » (1953) | Palier 15, `Shapley.lean` |
| Roth (dir.), *The Shapley Value* (1988) | Jeux coopératifs |
| Geanakoplos, « Three Brief Proofs of Arrow's Impossibility Theorem » (2005) | SocialChoice 01, `Arrow.lean` |
| Sen, *Collective Choice and Social Welfare* (1970) | SocialChoice 01b, `Sen.lean` |

### En ligne

- [Game Theory (Stanford Encyclopedia of Philosophy)](https://plato.stanford.edu/entries/game-theory/)
- [The Evolution of Trust (Nicky Case)](https://ncase.me/trust/)
- [Robinson & Goforth, Topology of 2x2 Games](https://www.mdpi.com/2073-4336/6/4/495)
- [Sprague-Grundy Theorem (Wikipedia)](https://en.wikipedia.org/wiki/Sprague%E2%80%93Grundy_theorem)
- [Lessons in Play (Albert, Nowakowski, Wolfe)](https://www.routledge.com/Lessons-in-Play/Albert-Nowakowski-Wolfe/p/book/9781568812779)

### Bibliothèques

- [Nashpy](https://nashpy.readthedocs.io/)
- [OpenSpiel](https://openspiel.readthedocs.io/) et [ses algorithmes](https://openspiel.readthedocs.io/en/latest/algorithms.html)

### Formalisations Lean externes

- [math-xmum/Brouwer](https://github.com/math-xmum/Brouwer) : existence de Nash
- [MixedMatched/formalizing-game-theory](https://github.com/MixedMatched/formalizing-game-theory)
- [mathlib4, jeux combinatoires](https://leanprover-community.github.io/mathlib4_docs/Mathlib/SetTheory/PGame/Basic.html)
- [asouther4/lean-social-choice](https://github.com/asouther4/lean-social-choice) : Arrow (Lean 3, source originale)
- [DominikPeters/SocialChoiceLean](https://github.com/DominikPeters/SocialChoiceLean) : Gibbard-Satterthwaite, Split Cycle (Lean 4, MIT)

## Licence

Voir la licence du dépôt principal.

---

*Version 1.5.0 — Septembre 2026 (2026-09-25) — réorganisation en parcours à plusieurs vitesses (#3973) : parcours principal à numéros nus, approfondissements présentés palier par palier, sous-série SocialChoice et extensions 18-25 séparées du parcours, grammaire des noms de fichiers expliquée au lecteur, formalisations Lean réunies en une section. Les sections de statut et de statistiques renvoient désormais au catalogue.*

*Version 1.4.3 — Septembre 2026 (2026-09-22) — déchronologisation du parcours (tranche D2 #14442 : les résultats restent, les récits de livraison partent) et re-synchronisation des tables sur le disque.*

*Version 1.4.2 — Août 2026 (2026-08-26) — réconciliation de l'inventaire Lean #13138 : toolchains effectives, statuts des coquilles `repeated_games_lean` (#6146) et `social_choice_lean` (#6058), ajout des lakes `assignment_lean` (#12598) et `asymmetric_information_lean` (Epic #12844).*

*Version 1.4.1 — Juillet 2026 (2026-07-16) — réconciliation EPIC #4365 : retrait des lakes supprimés `cooperative_games_lean` et `stable_marriage_lean`, absorbés dans `game_theory_lean`.*

*Version 1.4.0 — Juillet 2026 (2026-07-07) — passe ascendante feuilles vers hub : intégration du marathon de parité C# #4956, comptes délégués au marqueur CATALOG-STATUS.*
