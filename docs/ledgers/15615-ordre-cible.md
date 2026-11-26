# Ledger — Issue #15615 (ordre cible de gradation de la série GameTheory)

> **Bornage strict** : ce ledger mesure `origin/main` au **2026-11-26**, tête `3b466e9ccb`. Périmètre = les **145 carnets `GameTheory-*` de la racine** `MyIA.AI.Notebooks/GameTheory/`, dans l'ordre des noms de fichiers — c'est l'ordre de la série. Les **73 carnets des sous-dossiers** (`SocialChoice` 25, `Dynamics` 26, `Metajeux` 16, `Coalitions` 5, `gateway` 1) sont gradués eux aussi (fournée E) mais forment des séries satellites : ils restent hors de cette mesure d'ordre. Ce ledger **ne renumérote rien, ne régrada rien, ne touche aucun carnet** — il propose. Il mesure l'ordre des **niveaux** et ce que les carnets **déclarent** ; il n'est pas un audit des prérequis des blocs 06 à 23 (limite au §2.4).
>
> **Révision du 2026-11-26 (second passage)**. La version du matin mesurait la série sur les sept fichiers de gradation du dépôt : 91 lignes, 79 noms de carnets, échelle en quatre mots, 79 carnets couverts sur 145. Le fil de l'issue porte une seconde passe, postérieure et complète : trois niveaux, un critère falsifiable, les 144 carnets de la racine alors présents. **Tout est re-mesuré sur cette passe.** Les chiffres du matin (les deux mesures, la bande 2,50–3,29, les exceptions des blocs 14 et 15, le bilan 11 → 7, les gestes G1 à G9) ne sont pas comparables et ne sont pas reproduits.

## Origine

Scope 2 du cadrage du 2026-10-03 (« proposer un ordre cible »). Le secrétariat a constaté (commentaire `7172850434`) que l'acceptation 1 est couverte par les fournées A à F et qu'il reste l'acceptation 2 — validation de l'ordre cible par le user ou le coordinateur, non vue dans le fil — puis les acceptations 3 et 4.

Demande user fondatrice (commentaire `15586`, 2026-09-11T13:43Z) : « la séquence refermée ne présente pas encore la cohérence qu'on retrouve dans les premiers numéros de la série ». Ce ledger mesure d'abord **si** c'est vrai, et où.

## 1. La base de mesure

### Deux passes de gradation, et laquelle fait autorité

| | Passe des fichiers | Passe du fil |
|---|---|---|
| Support | sept fichiers `docs/ledgers/15615-gradation-*.md` sur `main` | commentaires A `6901222471`, B `6901454254`, C `7076327188`, D `7076900285`, E `7153370491`, F `7153774442` |
| Dates | déposés le 2026-11-13 (le dernier modifié le 2026-11-23) | 15/11 → 25/11 |
| Échelle | quatre mots (Basse, Moyenne, Haute, Très haute) | trois niveaux (`I`, `II`, `III`) |
| Critère | cinq paliers nommés et définis par leurs carnets (Entrée, Cadre formel, Application, Twins enrichis et géométrie ordinale, Murs), sans critère par palier | publié et falsifiable (table ci-dessous) |
| Racine couverte | 79 carnets sur 145 | 144 sur 144 à la fournée F, puis 145 |
| Hors racine couverte | 0 sur 73 | 73 sur 73 (fournée E) |
| Lignes | 91 lignes, 79 noms distincts | 128 dans les tableaux A–D, 26 dans la table F |

La passe du fil fait autorité pour trois raisons : elle est complète, son critère est falsifiable, et le secrétariat la désigne comme couvrant l'acceptation 1.

**Le critère, verbatim de la fournée A** :

| Niveau | Critère |
|---|---|
| `I` | « outillage/installation, aucun concept mathématique mobilisé » |
| `II` | « définitions formelles + calcul outillé (nashpy, scipy, networkx), sans développement algorithmique propre » |
| `III` | « algorithme développé from-scratch, **ou** preuve formelle (Lean), **ou** théorème d'existence manipulé (point fixe, minimax, dualité, encodage SAT) » |

**Contrôle de reconstruction.** Les tableaux A à D donnent 128 lignes (47 + 18 + 33 + 30), dont 10 nomment des carnets de `SocialChoice/`. La table F en donne 26. Les 118 lignes de la racine et les 26 de F retrouvent chacune un carnet, sans doublon ni ambiguïté : **144 = 1 I / 28 II / 115 III**, exactement le total que la fournée F annonce pour l'état de la série. Le 145ᵉ, `21-Capstone-Choix-Social-CSharp`, est né après (PR #28691) et hérite du niveau de son jumeau Python par la règle des jumeaux — gémellité vérifiée sur pièce : titre H1 identique (« la sous-série SocialChoice en une heure »), 16 cellules markdown et 11 cellules de code dans les deux carnets.

**Ce que le changement de base emporte.** Les « deux mesures » du matin n'en font plus qu'une : tous les carnets ont un niveau, donc les 144 paires adjacentes sont toutes mesurables. Les moyennes par bloc du matin étaient calculées sur les seuls carnets gradués d'une échelle en quatre mots ; elles ne sont pas reprises.

### Ce qui existe déjà sur `main`

Ce ledger n'est pas le premier texte sur l'ordre de la série et il ne les remplace pas :

- **`docs/ledgers/15615-gradation-blocs-01-05-consolide.md`** publie déjà un « Ordre cible proposé (scope 2 de l'acceptation) » pour les blocs 01 à 05. C'est un **ordre de lecture**, « dérivé des prérequis **déclarés** dans les carnets — pas d'une préférence éditoriale » : `02 → 02-cs → 02-P2 → 02-P2-cs → 02b …`, puis « twins C# systématiquement après leur Python ». Il demande « **Aucun renommage.** #18001 vient de renuméroter 93 carnets ; renuméroter une seconde fois pour déplacer `03b` avant `03c` coûterait une vague équivalente pour un gain de lecture marginal » et « **Aucun remplissage de trou.** ».
- **`docs/ledgers/15615-gradation-reprise-blocs-06-21.md`** renvoie l'ordre cible à une étape séparée : « Sa proposition reste une étape séparée, pour arbitrage user/coordinateur conformément à l'acceptance de #15615. »
- **Le README de la série** porte déjà cet ordre de lecture : pour les 52 sujets cités avec leurs deux jumeaux, le Python est cité avant le C# ; au bloc 02, `[Python](GameTheory-02-NormalForm-Python.ipynb) ([suite](GameTheory-02-NormalForm-Part2-Python.ipynb)) · [C#](GameTheory-02-NormalForm-CSharp.ipynb) ([suite](GameTheory-02-NormalForm-Part2-CSharp.ipynb))`.
- **La sidebar du site** (`_quarto.yml`, 143 entrées) est rangée dans l'ordre alphabétique des noms : elle suit l'ordre des fichiers, donc range l'extension avant sa base et le C# avant le Python (50 sujets).

Ce ledger apporte le complément : les blocs 01 à 23 mesurés dans l'ordre sur la gradation complète (§2), et le replay des gestes (§4).

## 2. Ce que la mesure dit

### 2.1 La série est presque plate

**145 = 1 I / 28 II / 116 III.** Répartition par bloc (moyenne du niveau, I = 1, II = 2, III = 3) :

| Bloc | n | I | II | III | Moyenne | Bloc | n | I | II | III | Moyenne |
|---|---:|---:|---:|---:|---:|---|---:|---:|---:|---:|---:|
| 01 | 1 | 1 | 0 | 0 | 1,00 | 13 | 12 | 0 | 1 | 11 | 2,92 |
| 02 | 13 | 0 | 5 | 8 | 2,62 | 14 | 6 | 0 | 0 | 6 | 3,00 |
| 03 | 10 | 0 | 3 | 7 | 2,70 | 15 | 6 | 0 | 0 | 6 | 3,00 |
| 04 | 21 | 0 | 9 | 12 | 2,57 | 16 | 18 | 0 | 3 | 15 | 2,83 |
| 05 | 4 | 0 | 1 | 3 | 2,75 | 17 | 9 | 0 | 0 | 9 | 3,00 |
| 06 | 3 | 0 | 0 | 3 | 3,00 | 18 | 3 | 0 | 1 | 2 | 2,67 |
| 07 | 2 | 0 | 2 | 0 | 2,00 | 19 | 2 | 0 | 0 | 2 | 3,00 |
| 08 | 7 | 0 | 0 | 7 | 3,00 | 20 | 1 | 0 | 0 | 1 | 3,00 |
| 09 | 8 | 0 | 3 | 5 | 2,62 | 21 | 3 | 0 | 0 | 3 | 3,00 |
| 10 | 2 | 0 | 0 | 2 | 3,00 | 22 | 2 | 0 | 0 | 2 | 3,00 |
| 11 | 9 | 0 | 0 | 9 | 3,00 | 23 | 1 | 0 | 0 | 1 | 3,00 |
| 12 | 2 | 0 | 0 | 2 | 3,00 | | | | | | |

**Treize blocs sont entièrement de niveau III** (06, 08, 10, 11, 12, 14, 15, 17, 19 à 23). Les dix autres sont mixtes, le bloc 01 compris, qui ne contient que le carnet d'installation ; dans les neuf restants, la moyenne (de 2,00 à 2,92) mesure la **part des carnets II**, pas une pente. La fournée A l'avait écrit dès le 15/11 (§7.5) : « la série n'est pas graduée au sens d'une montée douce — elle est **avancée dès son deuxième bloc**, et le reste. Le seul carnet de niveau I est le carnet d'installation. (…) il n'y a presque pas de pente à réordonner, il y a des **prérequis à déclarer** et des **libellés à réconcilier** ».

Une conséquence pour la demande fondatrice : la rampe 1,00 → 2,62 → 2,70 → 2,57 → 2,75 des cinq premiers blocs n'est pas une montée. Elle s'arrête au carnet d'installation. Ce qu'un ordre peut corriger est borné par là, et la section 4 le mesure.

### 2.2 Les douze descentes

Une **descente** est un couple de carnets adjacents dont le niveau baisse. Sur 144 paires adjacentes : **12 descentes, toutes de un niveau — 11 intra-bloc, 1 de bord** (bord = dernier carnet d'un bloc, premier carnet du suivant).

Trois classes, définies par ce que le carnet descendant **déclare lui-même** (lu première main dans le markdown des carnets à `origin/main`) :

- **Classe A — cohérente avec un prérequis déclaré.** Le carnet de niveau II déclare un prérequis de niveau III. Il ne peut pas ouvrir son bloc, et la descente ne s'efface qu'en réordonnant les sujets à l'intérieur du bloc.
- **Classe B — calibration entre jumeaux.** Les deux carnets sont le même sujet, gradués différemment selon le noyau.
- **Classe C — îlot de niveau II sans prérequis de niveau III.**

| # | Rang | Paire (avant → après) | Lieu | Classe | Ce que le carnet descendant déclare |
|---|---:|---|---|---|---|
| 1 | 4 | `02-NormalForm-Part2-Python` (III) → `02-NormalForm-Python` (II) | 02 | C | l'extension se déclare « Suite de la tranche 1 » et trie avant sa base |
| 2 | 6 | `02b-Lean-Definitions-Lean` (III) → `02c-Travelers-Dilemma-CSharp` (II) | 02 | C | « palier parent » = `02-NormalForm` (II) ; ne déclare pas `02b` |
| 3 | 19 | `03b-Chambres-Murs-Chemins-Lean-Rust` (III) → `03d-Deux-Especes-de-Fleches-CSharp` (II) | 03 | A | « prolonge 03-Topology2x2 » (III) |
| 4 | 27 | `04b-Lean-NashExistence-Lean` (III) → `04c-NashExistence-CSharp` (II) | 04 | A | « Notebook 4 : Équilibre de Nash » (III) ; ne déclare pas `04b` |
| 5 | 35 | `04g-Supermodularite-Python` (III) → `04h-Routing-PriceOfAnarchy-CSharp` (II) | 04 | A | « 02 » et « 04 » (III) ; ne déclare pas `04g` |
| 6 | 37 | `04h-Routing-PriceOfAnarchy-Lean` (III) → `04h-Routing-PriceOfAnarchy-Python` (II) | 04 | B | même sujet ; la preuve de Rosenthal est en Lean |
| 7 | 46 | `05-ZeroSum-Minimax-CSharp` (III) → `05-ZeroSum-Minimax-Python` (II) | 05 | B | le C# « déroule tout à la main … simplexe from-scratch » |
| 8 | 52 | `06i-Ensembles-Limites-Poincare-Bendixson-Python` (III) → `07-ExtensiveForm-CSharp` (II) | bord | A | « carnets 1 à 6 » (tout le bloc 06 est III) |
| 9 | 63 | `09-BackwardInduction-Python` (III) → `09b-Commitment-Stackelberg-CSharp` (II) | 09 | A | « formes normales et induction à rebours » ; l'induction à rebours est `09-BackwardInduction` (III), le carnet qui précède |
| 10 | 91 | `13f-Ataraxos-Patron-Python` (III) → `13g-Ataraxos-Organe-Natif` (II) | 13 | A | « deuxième temps » de l'EPIC Ataraxos, le premier étant `13f` |
| 11 | 113 | `16c-Extraction-de-Revenu-DSIC-IR-Rust` (III) → `16d-LLM-Players-Othman-Sandholm-Python` (II) | 16 | A | la Proposition 6, « livrée dans `GameTheory-16-MechanismDesign-Python.ipynb` §4.6 » (III) |
| 12 | 135 | `18-Capstone-Metajeux-Python` (III) → `18c-Humour-Banc-Python` (II) | 18 | C | aucun prérequis déclaré |

**7 de classe A, 2 de classe B, 3 de classe C.** Une seule est une inversion au sens de l'ordre : la n°1, une extension rangée avant sa base.

### 2.3 Les jumeaux

Un **sujet** est un nom sans suffixe de noyau ; ses carnets sont ses **jumeaux**. Les 145 carnets de la racine se répartissent en **79 sujets** : 25 n'ont qu'un carnet, 54 en ont plusieurs. **52 sujets ont un jumeau Python et un jumeau C#** : niveaux égaux dans 51, C# au-dessus dans 1 (`05-ZeroSum-Minimax`), C# en dessous dans aucun. Deux sujets seulement ont un niveau mixte : `04h-Routing-PriceOfAnarchy` (C#, Python et Rust en II, Lean en III) et `05-ZeroSum-Minimax` (Python en II, C# en III).

La règle des jumeaux, verbatim de la fournée F : « Un jumeau hérite du niveau publié pour son carnet de référence ; il n'est pas re-gradé. La gémellité est vérifiée sur pièce, pas sur le nom. »

**L'ordre des fichiers ne range pas les jumeaux derrière leur carnet de référence.** Les 68 sujets qui ont un Python ont 66 jumeaux d'un autre noyau (C#, Lean, Rust). **53 se classent avant lui** — les 52 jumeaux C#, et le jumeau Lean de `04h` — parce que `CSharp` et `Lean` précèdent `Python` dans l'ordre des octets ; les 13 qui le suivent sont des jumeaux Rust. **64 sur 66 renvoient à leur Python** dans leur markdown ; les deux qui ne le font pas sont `02-NormalForm-Part2-CSharp` et `19-Capstone-Dynamics-CSharp`.

### 2.4 Les références entre carnets de la racine

Balayage mécanique du markdown des 145 carnets, chaque ligne relue : **984 références d'un carnet racine vers un autre carnet racine** (lien ou nom en code). **23** vont vers un carnet classé plus tard, dans un contexte de prérequis ou de navigation arrière (reconnaissance par mots-clés et par liens `<<` ou `<-`) :

| Nature | Lignes | Lecture |
|---|---:|---|
| l'extension vers sa base (descente n°1) | 2 | `02-NormalForm-Part2-Python` vers `02-NormalForm-Python` : la seule inversion |
| un jumeau vers son Python | 11 | `02c`, `04h`, `09c`, `13b`, `13h`, `14b`, `15`, `16c`, `16i`, `16j`, `16k` (« [<< … (track principal)] », « [Version Python] ») |
| un pointeur vers l'avant | 9 | prolongements (`04e` depuis `04`, `04b`, `04c` ; `14c` depuis `06`), lecture suivante (`04k` depuis `04j`, `05c` depuis `05`), jumeau Rust (`02c`) : cohérents avec l'ordre des fichiers |
| à trancher | 1 | `09-BackwardInduction-CSharp` : « Parité .NET ⇄ Python, suite de [GameTheory-11-BayesianGames-CSharp] » — provenance ou ordre de lecture, le carnet ne le dit pas |

**Aucune autre référence vers l'arrière n'a été trouvée.** Limite du balayage : il ne voit ni un prérequis écrit sans lien ni nom en code, ni une référence à un carnet d'un sous-dossier. Les prérequis des carnets descendants des douze descentes ont été lus première main (§2.2) ; ceux des autres carnets des blocs 06 à 23 n'ont pas été lus un par un.

## 3. Les règles de l'ordre cible

- **R1 — Une descente n'est un défaut que si le carnet descendant ne la déclare pas.** Une descente de classe A est la trace d'un prérequis : elle se déclare, elle ne se corrige pas.
- **R2 — Un sujet n'est pas séparé de ses jumeaux.** Une descente de classe B est une décision de gradation (re-grader un jumeau, ou l'accepter comme la fournée F l'a publié), pas un geste d'ordre.
- **R3 — Une extension suit sa base, toutes variantes comprises.**
- **R3 bis — Un jumeau se lit après son carnet de référence.** Règle du ledger consolidé (« twins C# systématiquement après leur Python »), reprise telle quelle. L'ordre des fichiers ne la respecte pour aucun des 52 jumeaux C# (§2.3) ; aucun renommage n'est proposé pour eux, pour la raison que le ledger consolidé a écrite.
- **R4 — Tout changement d'ordre est un renommage.** L'ordre de la série est l'ordre des noms de fichiers. Un geste retenu passe par `scripts/notebook_tools/rename_notebooks.py` : dry-run par défaut, application explicite, deux commits (les `git mv` seuls, puis les fichiers qui citent), jamais une cellule de code réécrite, jamais une sortie commitée touchée. Le renommage s'inscrit au `docs/reference/rename-ledger.tsv` (garde `check_rename_ledger.py`) et se vérifie par `check_notebook_nav_chain.py` et `check_slot_reservation.py`. L'organe le dit lui-même : « un numéro ou une lettre ne se propose JAMAIS : la renumérotation reste un acte pédagogique ».

## 4. Le replay des gestes

Chaque geste est rejoué sur la séquence réelle des 145 carnets, en déplaçant un **groupe nommé** (jamais d'échange à deux). Colonnes : carnets qui changent de rang, descentes retirées, descentes créées, total après le geste. Chaque geste part de l'état actuel (12).

### 4.1 Les neuf gestes de la version du matin

| Geste | Groupe déplacé, ancre | Rangs changés | Retirées | Créées | Total |
|---|---|---:|---:|---:|---:|
| G1' | `02-NormalForm-Python`, en tête du bloc 02 | 4 | 1 | 0 | **11** |
| G2 | `04-NashEquilibrium-CSharp` après `-Python` | 2 | 0 | 0 | 12 |
| G3 | `05-ZeroSum-Minimax-CSharp` après `-Python` | 2 | 1 | 1 | 12 |
| G4 | `06-EvolutionTrust-CSharp` après `-Python` | 2 | 0 | 0 | 12 |
| G5 | `07-ExtensiveForm-CSharp` après `-Python` | 2 | 1 | 1 | 12 |
| G6 | `04b-Lean-NashExistence-Lean` après les deux `04c` | 3 | 1 | 2 | **13** |
| G7 | `08b-Lean-CombinatorialGames-Lean` après les deux `08c` | 3 | 0 | 0 | 12 |
| G8 | sujet `15c` (deux carnets) avant `15` et `15b` | 5 | 0 | 0 | 12 |
| G9 | `08d-Lean-CGT-Lean` en tête du bloc 09 | **0** | 0 | 0 | 12 |
| **Les neuf, dans l'ordre du tableau** | | | 1 | 1 | **12** (10 intra / 2 bord) |

Ce que le replay dit, geste par geste :

- **G1' retire la descente n°1** (`02-NormalForm-Part2-Python` III → `02-NormalForm-Python` II). C'est le seul des neuf qui retire une descente.
- **G2, G4 et G7 ne font rien.** Les jumeaux C# et Python de `04`, `06`, `07` ont le même niveau sur cette passe, et `08b` comme `08c` sont III. Les gestes du matin calibraient des écarts qui n'existent que sur l'échelle en quatre mots.
- **G3 et G5 déplacent la descente, ils ne la retirent pas.** G3 : la paire `05-CSharp` (III) → `05-Python` (II) cède la place au bord `04k-Equilibre-Correle-Python` (III) → `05-ZeroSum-Minimax-Python` (II). G5 : le bord `06i-…-Python` (III) → `07-ExtensiveForm-CSharp` (II) cède la place au bord `06i-…-Python` (III) → `07-ExtensiveForm-Python` (II). Une descente intra devient une descente de bord ; le total ne bouge pas.
- **G6 crée une descente nette.** Il retire `04b` (III) → `04c-NashExistence-CSharp` (II) et en crée deux : `04-NashEquilibrium-Python` (III) → `04c-NashExistence-CSharp` (II) — le jumeau C# de `04` une fois G2 appliquée — et `04b-Lean-NashExistence-Lean` (III) → `04d-Marchandage-Asymetrique-CSharp` (II). La descente n°4 est de classe A : `04c` déclare le carnet `04` (III), donc il descend derrière lui où qu'il soit placé après lui. Total 12 → 13.
- **G8 réordonne un sujet, et ne change rien au compte.** Le sujet `15c` passe devant `15` et `15b` : cinq carnets changent de rang. `15`, `15b` et `15c` sont tous de niveau III ; aucune paire ne descend ni ne cesse de descendre.
- **G9 ne déplace rien.** `08d-Lean-CGT-Lean` est déjà le dernier carnet du bloc 08, immédiatement avant `09-BackwardInduction-CSharp`. Placer `08d` « en tête du bloc 09 » lui donne exactement le rang qu'il a : **zéro carnet ne change de rang**. Et sur cette passe les deux carnets sont de niveau III : la paire n'est pas une descente. Le geste ne traite donc rien — ni ne la reproduit.
- **Les neuf ensemble : 12 → 12, mais 11 intra → 10 intra et 1 bord → 2 bord.** Une descente intra disparaît (n°1, par G1'), une devient une descente de bord (n°7, par G3), une naît (par G6). Le total ne baisse pas.

### 4.2 Les gestes de la présente révision

| Geste | Effet sur l'ordre | Rangs changés | Retirées | Créées | Total |
|---|---|---:|---:|---:|---:|
| **T1** | `02-NormalForm-Python` entre `02-NormalForm-CSharp` et les deux `Part2` | 3 | 1 | 0 | **11** (10 intra / 1 bord) |
| T2 seul | sujet `02c` avant `02b` | 4 | 1 | 0 | 11 |
| T2 après T1 | même geste, après T1 | 4 | 1 | 1 | 11 |
| T3 | sujet `04h` après `04i` | 6 | 1 | 1 | 12 |
| **T4** seul | sujets `04h` et `04i` avant `04e` | 10 | 1 | 0 | 11 |
| **T4 après T1** | même geste, après T1 | 10 | 1 | 0 | **10** (9 intra / 1 bord) |
| — | `18c-Humour-Banc-Python` en tête du bloc 18 | 3 | 1 | 1 | 12 |
| — | tri complet des sujets par niveau, bloc par bloc | 116 | — | — | 9 (2 intra / 7 bord) |

- **T1 est le seul geste qui retire un défaut d'ordre.** La descente n°1 est une inversion : `02-NormalForm-Part2-Python` se déclare « Suite de la tranche 1 » et trie avant elle, parce que `-Part2-` précède `-Python` dans l'ordre des octets. T1 range les deux variantes de la base avant les deux de l'extension.
- **T2 est écarté.** Seul, il retire la descente n°2 en permutant les lettres d'accrétion `b` et `c` (quatre carnets renommés). Après T1, il ne retire plus rien : `02-NormalForm-Part2-Python` (III) → `02c-Travelers-Dilemma-CSharp` (II) naît à la place de celle qu'il retire.
- **T3 est écarté.** Il échange `04h` et `04i`, tous deux de niveau II : la descente n°5 devient `04g-Supermodularite-Python` (III) → `04i-Utilite-Esperee-Risque-CSharp` (II).
- **T4 est mesuré, il n'est pas proposé.** Il retire la descente n°5 en rangeant `04h` et `04i` avant `04e`, ce qui réécrit quatre lettres d'accrétion et renomme dix carnets ; les quatre sujets sont cités par 85 fichiers (`04e` 27, `04g` 18, `04h` 24, `04i` 16). Les prérequis déclarés par les quatre sujets déplacés sont respectés (lus première main). Ceux des carnets qui les citent n'ont pas tous été lus : c'est la raison pour laquelle le geste est mesuré et non proposé.
- **La descente n°12 ne s'efface pas.** En tête du bloc 18, `18c-Humour-Banc` (II) recrée la descente au bord `17f-Market-to-Balance-Sheet-Python` (III) → `18c-Humour-Banc-Python` (II).
- **Le tri complet n'est pas une option.** Ranger tous les sujets de chaque bloc par niveau ferait passer 116 carnets sur 145 à une autre place, pour 9 descentes : il ne supprime rien, il transfère les descentes aux bords de blocs (2 intra, 7 bord) et il réécrit la progression que les numéros portent.

**Meilleur compte atteint par les gestes mesurés : 10** (T1 puis T4), contre 9 pour un tri complet qui ne respecte aucun prérequis.

### 4.3 Le coût de T1, mesuré par l'organe de renommage

L'ordre visé n'est réalisable que par un renommage, puisque `-Part2-` précède `-Python`. Deux réalisations, toutes deux passées au dry-run de `rename_notebooks.py --mapping` (lecture seule, rien écrit) :

| Réalisation | Renommages | Fichiers qui citent | Occurrences | Refus de l'organe |
|---|---:|---:|---:|---|
| **T1-a** — l'extension devient `02-NormalForm-Tranche2-{CSharp,Python}` | 2 | **12** | **317** | aucun |
| **T1-b** — la base devient `02-NormalForm-Part1-{CSharp,Python}` | 2 | **54** | **642** | aucun |

Les deux donnent le même ordre et le même compte, 12 → 11. Ni l'une ni l'autre ne touche une cellule de code ni une sortie commitée : les occurrences dans les carnets sont toutes des cellules markdown (une dans `02-NormalForm-CSharp`, deux dans `02-NormalForm-Part2-Python`, zéro dans les sorties). **Aucune ré-exécution n'est due** (C.2 : une modification markdown seulement).

- **T1-a** reprend le mot des carnets eux-mêmes. La base C# s'intitule « Tranche 1 : Nash from-scratch » et annonce « la résolution générale (support enumeration) est l'objet de la **tranche 2** » ; la navigation de l'extension dit « GameTheory-2 tranche 1 ». Elle laisse inchangé le nom du carnet d'entrée de la série, cité par 57 fichiers — d'autres séries (`Dynamics`, `Complexity`), trois jeux de slides, des tests. Son prix : `-Tranche<N>-` n'est porté par aucun nom de carnet du dépôt aujourd'hui, alors que `-Part<N>` est un slot de la grammaire de nommage. L'index (`02`) ne change pas dans les deux réalisations.
- **T1-b** garde le slot `-Part<N>` et rend les deux parties symétriques. Son prix : elle renomme le carnet d'entrée, et 54 fichiers suivent.

Deux coûts à confirmer au moment de l'exécution, non mesurés ici : l'attestation de gémellité du couple (`twin_pairs.d/gametheory-2-normalform-part-2-support-enumeration.yaml`, six occurrences) porte une empreinte de contenu et se rescelle après le renommage ; le titre H1 des deux carnets d'extension dit « (Part 2) » et ne contient pas le nom du fichier, donc l'organe ne le réécrit pas — il s'aligne à la main si T1-a est retenue.

## 5. Ce que l'ordre ne règle pas

1. **La série est presque plate : 116 carnets sur 145 sont de niveau III.** C'est une question de gradation et de contenu, pas d'ordre. Une permutation ne fabrique pas une pente que le contenu n'a pas.
2. **Les deux écarts entre jumeaux** (`04h` en Lean, `05` en C#) sont des décisions de gradation, publiées par la fournée F.
3. **Les lettres d'accrétion portent l'identité des sujets.** Fermer un îlot de niveau II derrière un carnet III est un acte pédagogique, qui demande son argument écrit — l'organe de renommage l'exige.
4. **Les 73 carnets hors racine sont gradués** (fournée E : 1 I / 9 II / 63 III) mais appartiennent à des séries satellites. Leur ordre se mesure par série.
5. **Les sept fichiers de gradation du dépôt ne portent pas la passe du fil** : 79 noms sur une échelle en quatre mots, contre 145 sur trois niveaux qui n'existent que dans des commentaires d'issue. Les réconcilier est un grain distinct, à porter sur #15615.

## 6. Ce qui n'est pas exécuté

- **Aucune renumérotation, aucun renommage, aucune réévaluation de note.** Les gestes sont rejoués, pas appliqués.
- **Les deux dry-runs de l'organe de renommage n'ont rien écrit.**
- Le seul geste qui retirerait une inversion (T1) est un renommage ; l'acceptation 4 en mesure le coût (§4.3). Sous l'option c) du §8, aucune tranche n'est à exécuter.

## 7. Correspondance aux acceptations de #15615

| Acceptation | État après ce ledger |
|---|---|
| 1 — tableau de gradation publié | **couvert** par les fournées A à F : les 145 carnets de la racine ont un niveau, reconstruction vérifiée au §1. Les sept fichiers du dépôt n'en portent que 79 |
| 2 — ordre cible validé avant exécution | **devient décidable** : l'ordre de lecture des blocs 01 à 05 (ledger consolidé) vaut pour les blocs 06 à 23 — la mesure n'y trouve aucune inversion, dans les limites du §2.4 ; quatre règles (§3), douze descentes classées (§2.2), chaque geste rejoué (§4), options au §8 |
| 3 — tranches exécutées, preuve octet-à-octet | **dépend de 2** ; une tranche candidate (T1), dry-run fait — ou aucune, si l'option c) est retenue |
| 4 — liens croisés, labels, curriculum, READMEs réconciliés | **dépend de 3** ; coût mesuré au §4.3 |

## 8. La question, en forme fermée

Une lettre suffit :

- **a)** **T1-a** — renommer l'extension en `02-NormalForm-Tranche2-{CSharp,Python}` : 12 → 11 descentes, 2 carnets renommés, 12 fichiers, 317 occurrences.
- **b)** **T1-b** — renommer la base en `02-NormalForm-Part1-{CSharp,Python}` : même ordre, 2 carnets renommés, 54 fichiers, 642 occurrences.
- **c)** **Ne rien renommer** — retenir comme ordre cible l'ordre de lecture déjà publié pour les blocs 01 à 05 (ledger consolidé, README de la série), qui vaut pour les blocs 06 à 23 : l'ordre des fichiers, lu avec l'extension après sa base et chaque jumeau après son Python. Les douze descentes restent documentées (7 de classe A, 2 de classe B, 3 de classe C).

Je recommande **c)**, pour trois mesures :

1. **L'ordre de lecture existe déjà.** Le README de la série cite le Python avant le C# pour 52 sujets sur 52, et la base du bloc 02 avant sa « suite » ; 64 jumeaux sur 66 renvoient à leur Python.
2. **T1 ne ferme qu'un écart sur 53.** L'ordre des fichiers range 52 jumeaux C# avant leur Python, et une extension avant sa base. T1 corrige la seconde et aucune des premières : après T1, l'ordre des fichiers diffère encore de l'ordre de lecture aux 52 jumeaux C#, et aucun renommage n'est proposé pour eux.
3. **Le ledger consolidé a pris la même position** sur l'écart de même nature aux blocs 01 à 05 (`03b` avant `03c`) : « Aucun renommage ».

L'option **a)** est la bonne si l'on veut que l'ordre des fichiers lui-même respecte R3 au bloc 02 : c'est le seul geste mesuré qui retire une inversion, et son coût est faible (§4.3).

Dans les trois cas, les descentes qui restent sont de classe A (7), de classe B (2), ou sans geste qui les retire (n°2, n°5, n°12) : elles se documentent, elles ne se déplacent pas. T4 (12 → 10) est mesuré et n'est pas proposé (§4.2).

Une piste non mesurée, hors de ce ledger : la sidebar du site suit l'ordre alphabétique des noms. La porter à l'ordre de lecture ne demanderait aucun renommage, mais ses gardes n'ont pas été examinées.

See #14944 (epic renum — mécanique refermée, cette issue est le volet gradation pédagogique)
See #15586 (commentaire fondateur du user)
