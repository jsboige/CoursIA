# Dynamics — de la répétition aux institutions

Sous-dossier de la série [GameTheory](../README.md), issu du palier 06. La **porte** reste [GameTheory-06 nu — évolution de la confiance](../GameTheory-06-EvolutionTrust-Python.ipynb), en racine : l'escalier se lit **après** elle, jamais à sa place. Le **capstone** [06i — Ensembles limites](../GameTheory-06i-Ensembles-Limites-Poincare-Bendixson-Python.ipynb) reste aussi en racine (voir [ci-dessous](#06i--capstone-resté-en-racine)).

Note de conception : [commentaire `6108947569` sur #20316](https://github.com/jsboige/CoursIA/issues/20316#issuecomment-6108947569) — elle justifie l'ordre et nomme ce que chaque marche ajoute ; cette page en est la mise en étalage.

## Deux vols et une greffe

| Vol | Marches | Anciennes lettres du palier 06 |
|---|---|---|
| **Jeux répétés** | 01 → 02 → 03 | 06c, 06b, 06d |
| **Agents transparents et bornés** | 04 → 05 → 06 → 07 → 08 | 06e, 06f×2, 06j, 06g, 06h |
| **Greffe N-personnes** | 09 | 03e (série 3) |

Ordre de lecture interne : `01 → 02 → 03 → 04 → 05 (Python puis Lean) → 06 → 07 → 08`, puis **06i en racine**, et **09 après [GT-03](../GameTheory-03-Topology2x2-Python.ipynb)** — sa cellule E1 est la carte d'entrée 2×2. Les jumeaux ne comptent pas comme marches : le C# de la marche 01 partage le slot de son Python, et le Lean de la marche 05 est sa moitié formelle (la lettre 06f n'est plus portée par deux fichiers).

## Les marches — le marchepied est l'écart, pas le sujet

| # | Carnet | Ce que la marche précédente ne donnait pas | Gradation |
|---|--------|---------------------------------------------|-----------|
| 01 | [Jeux répétés et Folk Theorem](Dynamics-01-Jeux-Repetes-Folk-Theorem-Python.ipynb) · [jumeau C#](Dynamics-01-Jeux-Repetes-Folk-Theorem-CSharp.ipynb) | **L'horizon** : le 06 nu joue une fois ; ici la répétition rend la coopération soutenable par menace (Folk). | Moyenne |
| 02 | [Jeux répétés en Lean](Dynamics-02-Jeux-Repetes-Lean-Python.ipynb) | La **preuve** du même énoncé — `grim_trigger_sustains_iff` certifié sans `sorry` (le Folk complet reste ouvert, `Folk.lean`). | Haute |
| 03 | [Sympathie contre engagement](Dynamics-03-Sympathie-vs-Engagement-Python.ipynb) | Le **type de l'autre** : statique comparative sur l'engagement (connu) contre la sympathie (inféré). | Haute |
| 04 | [Open-source game theory](Dynamics-04-Open-Source-Game-Theory-Python.ipynb) | **Le programme devient lisible** : lire le code de l'autre change l'équilibre. Tête du vol transparence. | Haute |
| 05 | [Agents bornés](Dynamics-05-Agents-Bornes-Python.ipynb) · [Lean](Dynamics-05-Agents-Bornes-Lean.ipynb) | L'agent n'est plus omniscient : **le calcul a un coût**. | Haute / **Très haute** (jumeau Lean) |
| 06 | [Preuves bornées et coût du raisonnement](Dynamics-06-Preuves-Bornees-Cout-du-Raisonnement-Python.ipynb) | Le coût porte sur **le raisonnement lui-même** (longueur de preuve), pas seulement sur le calcul. | Haute |
| 07 | [Équilibres par simulation](Dynamics-07-Equilibres-par-Simulation-Python.ipynb) | Les équilibres de programmes **qui se simulent** — la clôture opérationnelle du vol. | Haute |
| 08 | [Institutions transparentes](Dynamics-08-Institutions-Transparentes-Python.ipynb) | Le **paiement du vol** : la transparence institutionnelle comme capstone du vol. | **Très haute** |
| 09 | [Biens publics N-personnes](Dynamics-09-Biens-Publics-N-Personnes-Python.ipynb) | **La sortie du 2×2** : plan de déformation `(k, s, c/b)`, mur à mémoire, hystérésis/bifurcation (Archetti-Scheuring 2012). Greffe par GT-03. | Haute |

## La gradation #15615 comme colonne

L'ordre interne suit la gradation #15615 (fournée B, 06-10) lue **croissante** :

- **l'entrée est « Moyenne » par construction** — 01 est la suite directe de la porte 06 (elle-même « Moyenne ») ; lui donner une marche d'entrée « Haute » casserait la continuité ;
- le **plateau « Haute »** couvre 02 à 07 et 09 ;
- les deux **sommets « Très haute »** marquent **les deux cimes réelles** : la preuve bornée côté Lean (05, jumeau Lean) et l'institution transparente côté synthèse (08).

## 06i — capstone resté en racine

06i ne descend pas : il est **la théorie des issues de tout l'escalier** — « où peut finir une trajectoire ». Poincaré-Bendixson (point, orbite, hétéroclinique — pas de chaos en dimension 2), appliqué à la dynamique de replicateur (Czechowski-Piliouras 2021). Il consomme les trajectoires d'apprentissage du vol transparence (01 → 08) et la dynamique de replicateur héritée de la chaîne 06 ; c'est lui qui reçoit, en fin de lecture, les deux vols et la greffe. Il reste gradé « Haute » **parce qu'il est une synthèse, pas une difficulté nouvelle** — sa valeur est de rassembler, pas d'ajouter un cran.

## Pierre P1 — du tournoi au programme lisible

Le saut de la porte 06 (tournoi de stratégies : on observe le comportement de l'autre) à la marche 04 (le programme de l'autre est public : on lit son code) mérite son pont. En un tournoi, l'information sur l'autre est **comportementale** — un historique de coups, que le Folk de la marche 01 exploite par menace. Dans le vol transparence, elle est **structurelle** : le code source annonce la stratégie entière, coups contrefactuels compris, et ce qui change alors n'est pas la profondeur de la mémoire mais **la nature de l'engagement** — un programme lu ne peut pas bluffer sur ce qu'il fera hors de l'équilibre. D'où l'ordre du vol : 04 pose la lisibilité, 05 enlève l'omniscience de celui qui lit (le calcul a un coût), 06 renchérit le coût sur le raisonnement, 07 ferme la boucle (des programmes qui se lisent en se simulant), 08 paie le tout en institutions. *(Pierre posée en section README — sa forme complète, un carnet court, reste à écrire.)*

## Compagnons formels (lakes)

| Module du lake [`game_theory_lean`](../game_theory_lean/README.md) | Rôle dans l'escalier |
|---|---|
| [`RepeatedGames`](../game_theory_lean/RepeatedGames.lean) | Marches 01-02 : grim trigger certifié sans `sorry` ; Folk complet ouvert (`Folk.lean`) |
| [`ProgramGames/Bounded`](../game_theory_lean/ProgramGames/Bounded.lean) | Marches 05-06 : bornes sur les agents à programme (`import ProgramGames.Bounded` dans les deux 06f d'origine) |
| [`ProgramGames/FairBot`](../game_theory_lean/ProgramGames/FairBot.lean) | **Pièce non consommée** : nommé 75× en prose dans les anciens 06e/06j sans jamais être importé — soit les marches l'appellent, soit elle cherche sa marche (See #20379) |
| [`Abstraction`](../game_theory_lean/Abstraction/Basic.lean) | **Module orphelin** : le consommateur naturel est le carnet 19 « Abstraction à dette » (Metajeux-03), qui n'appelle rien — à câbler (See #20380) |

La table des lakes de la série, dans le [README racine](../README.md#formalisations-lean), reprend ces deux groupes. L'inventaire complet (toolchains, `sorry` résiduels) vit dans [LEAN_INVENTORY.md](../LEAN_INVENTORY.md).
