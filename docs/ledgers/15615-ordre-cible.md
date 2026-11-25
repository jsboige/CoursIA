# Ledger — Issue #15615 (ordre cible de gradation de la série GameTheory)

> **Bornage strict** : ce ledger mesure `origin/main` au **2026-11-25**, tête `06cd3788510`. Périmètre gradué = les **144 carnets `GameTheory-*` de la racine** `MyIA.AI.Notebooks/GameTheory/`. Les **73 carnets des cinq sous-dossiers** (`SocialChoice` 25, `Dynamics` 26, `Metajeux` 16, `Coalitions` 5, `gateway` 1) restent hors périmètre : ils n'ont aucune ligne de gradation. Ce ledger **ne renumérote rien, ne régrade rien, ne touche aucun carnet** — il propose.

## Origine

Scope 2 du cadrage du 2026-10-03 (« proposer un ordre cible »), rendu decidable par l'acceptation 1 : sept ledgers de fournée ont publié le tableau de gradation — [fondations](15615-gradation-foundations.md), [fournées A](15615-gradation-fournee-a.md), [B](15615-gradation-fournee-b.md), [C](15615-gradation-fournee-c.md), [D](15615-gradation-fournee-d.md), [consolidé 01-05](15615-gradation-blocs-01-05-consolide.md), [reprise 06-21](15615-gradation-reprise-blocs-06-21.md). L'acceptation 2 (« ordre cible validé (user ou coordinateur) avant toute exécution ») était la seule non tranchée.

Demande user fondatrice (commentaire #15586, 2026-09-11T13:43Z) : « la séquence refermée ne présente pas encore la cohérence qu'on retrouve dans les premiers numéros de la série ». Ce ledger mesure d'abord **si** c'est vrai, et où.

## 1. La base de mesure — et ce qu'elle ne couvre pas

Les sept ledgers totalisent **142 entrées de gradation** pour **129 noms de carnets distincts**, sur une échelle en **mots** et non en chiffres romains (`I`/`II`/`III` n'apparaît dans aucun) : **Basse 6, Moyenne 29, Haute 73, Très haute 34**.

**Re-mesure du 2026-11-25** — le tableau a vieilli de deux façons, toutes deux mesurées :

| Constat | Mesure |
|---|---|
| Carnets `GameTheory-*` à la racine | **144** |
| dont porteurs d'une ligne de gradation | **79** (55 %) |
| dont **non gradés** | **65** |
| Noms des tables qui **n'existent plus** sous cette forme | **50 des 129** (relettrages postérieurs : `-Csharp` → `-CSharp`, `03h` → `03g`, blocs 18-20 déplacés) |
| Sujets (bloc + indice) présents à la racine | **78** |
| dont **sans aucune ligne de gradation** | **12** — `02e`, `04i`, `04j`, `04k`, `05c`, `11c`, `11e`, `11f`, `14b`, `14c`, `22`, `23` |

Deux conséquences, qui bornent ce que ce ledger peut affirmer :

- **Un ordre cible au niveau du nom de fichier n'est pas produisible** sur un demi-corpus : 50 des 129 noms des tables désignent des carnets renommés. L'ordre cible se propose donc **au niveau du sujet** (bloc + indice, stable à travers les renommages) et de la **variante de langue**.
- **Les blocs 22 et 23 n'ont jamais été gradés** : ils sont entrés dans la série après la fournée D, qui déclarait « la série s'arrête au bloc 20 ». Aucun ordre ne peut les situer autrement qu'à titre provisoire.

### La série a été restructurée depuis l'audit : 18-21 sont des portes

Mesure du 25/11 sur les blocs de queue : les carnets de contenu des blocs 18, 19 et 20 **ont quitté la racine** vers quatre séries satellites, et la racine ne porte plus que des **capstones** :

| Bloc racine | Carnets présents | Rôle mesuré |
|---|---|---|
| 18 | `18-Capstone-Metajeux-Python/-CSharp`, `18c-Humour-Banc-Python` | porte vers `Metajeux/` (16 carnets) |
| 19 | `19-Capstone-Dynamics-Python/-CSharp` | porte vers `Dynamics/` (26 carnets) |
| 20 | `20-Capstone-Coalitions-Python` | porte vers `Coalitions/` (5 carnets) |
| 21 | `21-Capstone-Choix-Social-Python/-Rust` | porte vers `SocialChoice/` (25 carnets) |

Les renommages sortants sont tracés par la fournée D (`→ Metajeux-01` à `Metajeux-06`, `→ GOL-08`, `GOL-09`). **Un capstone de porte n'est pas un sommet** : sa difficulté basse est un fait de conception, pas un défaut d'ordre.

## 2. Ce que la mesure dit de la gradation réelle

### Moyennes par bloc (carnets gradés seulement)

| Bloc | Gradés / présents | Moyenne | Bloc | Gradés / présents | Moyenne |
|---|---:|---:|---|---:|---:|
| 01 | 1 / 1 | 1,00 | 13 | 8 / 12 | 3,12 |
| 02 | 8 / 13 | 1,75 | 14 | 2 / 6 | 4,00 |
| 03 | 2 / 10 | 2,00 | 15 | 5 / 6 | 3,60 |
| 04 | 9 / 21 | 3,00 | 16 | 8 / 18 | 3,25 |
| 05 | 3 / 4 | 3,00 | 17 | 7 / 9 | 3,29 |
| 06 | 3 / 3 | 2,67 | 18 | 1 / 3 | 4,00 |
| 07 | 2 / 2 | 2,50 | 19 | 0 / 2 | — |
| 08 | 6 / 7 | 3,00 | 20 | 0 / 1 | — |
| 09 | 5 / 8 | 2,60 | 21 | 1 / 2 | 2,00 |
| 10 | 2 / 2 | 3,00 | 22 | 0 / 2 | — |
| 11 | 4 / 9 | 3,25 | 23 | 0 / 1 | — |
| 12 | 2 / 2 | 3,00 | | | |

**Lecture.** La rampe que le user décrit existe et elle est mesurable : **1,00 → 1,75 → 2,00 → 3,00 sur les quatre premiers blocs**. Puis la série **atteint son régime de croisière au bloc 04 et n'en ressort plus** : sur les blocs 05 à 17, les moyennes oscillent entre **2,50 et 3,29** sans tendance — six dixièmes d'amplitude totale, aucun palier franchi en treize blocs. La remontée n'arrive que tard et par sommets isolés (14 à 4,00, 15 à 3,60).

Ce n'est donc pas un défaut d'ordonnancement seul : **la distribution du corpus est plate** — 73 carnets sur 142 sont gradés Haute, 34 Très haute. Une permutation ne peut pas fabriquer une pente que le contenu n'a pas. Ce que l'ordre peut porter, c'est une **progressivité intra-bloc** ; la progressivité inter-blocs demanderait une réévaluation des notes, hors de ce scope.

### Les descentes réelles : 11, pas 27

Les tables consolidées donnaient 27 descentes sur 141 transitions. Cette mesure-là parcourait les noms **historiques**, donc des carnets renommés et des variantes comptées deux fois. Sur la séquence **réelle** (144 carnets, **49 transitions où les deux voisins sont gradés**) :

| Classe | Nombre |
|---|---:|
| Descentes totales | **11** (22 % des transitions gradées) |
| dont **intra-bloc** — le lecteur monte puis redescend dans le même bloc | **10** |
| dont **de bord** — fin d'un bloc vers le début du suivant | **1** |
| dont **variante ou sommet d'un sujet placé avant une variante moins notée du même sujet** | **8** des 11 |

Une descente de bord est une **ré-entrée** : un bloc repart plus bas, c'est un fait de conception. Une descente intra-bloc est le défaut que le user décrit. Les huit descentes de la dernière ligne sont une seule classe, et un seul type de geste les enlève.

### L'échelle de langue ne prédit pas la difficulté — mesure

Sur les 21 sujets portant au moins une variante Python et une variante non-Python gradées :

| Écart mesuré entre la variante Python et l'autre | Sujets |
|---|---:|
| l'autre est **+1** au-dessus de Python | **4** — 04, 05, 06, 07 |
| niveau **égal** | **14** |
| **Python est +1** au-dessus de l'autre | **3** — 13, 16, 17 |

Les blocs 13, 16 et 17 inversent la tendance des premiers blocs : le carnet Python y porte le contenu de référence (CFR, design de mécanismes, MARL) et le jumeau C# est un portage from-scratch, gradé plus bas. **Une règle « Python puis C# puis Lean » serait donc fausse** : la règle correcte est « par note graduée croissante, quelle que soit la langue ».

## 3. L'ordre cible proposé — cinq règles

**R1 — Dans un sujet, les variantes se rangent par note graduée croissante**, jamais par langue. Mesure de l'échelle au §2 : la langue ne prédit le niveau que dans quatre blocs sur vingt et un.

**R2 — Une extension suit sa base.** `02-NormalForm-Part2-*` après les deux variantes de `02-NormalForm-*`. Le défaut actuel est alphabétique : `NormalForm-Part2` trie avant `NormalForm-Python`.

**R3 — Le sommet d'un sujet se place après toutes les variantes du sujet voisin qu'il domine**, jamais en tête. Vise les descentes où un carnet Très haute (souvent Lean) précède une variante Haute du même sujet ou du sujet jumeau.

**R4 — Un bloc se termine sur son maximum.** Livrer un sommet Très haute au dernier carnet d'un bloc, pour ouvrir le suivant sur Moyenne, est la seule rupture dure de la série (`08d-Lean-CGT-Lean` → `09-BackwardInduction`) et la seule qui demande un **geste de contenu** (déplacer `08d` en tête de 09, ou l'y rattacher).

**R5 — Une porte n'est pas un sommet.** Les blocs 18 à 21 ouvrent les séries satellites ; leur note basse est acquise par conception et ne se corrige pas par déplacement. Une porte se déclare (titre, navigation) plutôt que de se reclasser.

## 4. Les onze descentes, classées, avec le geste

| # | Paire (avant → après) | Bloc | Delta | Classe | Geste |
|---|---|---|---:|---|---|
| 1 | `02-NormalForm-Part2-Python` (Mo) → `02-NormalForm-Python` (Ba) | 02 | −1 | extension avant base | **G1/R2** : regrouper la base avant `Part2` |
| 2 | `04-NashEquilibrium-CSharp` (H) → `04-NashEquilibrium-Python` (Mo) | 04 | −1 | variantes | **G2/R1** : C# après Python |
| 3 | `05-ZeroSum-Minimax-CSharp` (H) → `05-ZeroSum-Minimax-Python` (Mo) | 05 | −1 | variantes | **G3/R1** : C# après Python |
| 4 | `06-EvolutionTrust-CSharp` (H) → `06-EvolutionTrust-Python` (Mo) | 06 | −1 | variantes | **G4/R1** : C# après Python |
| 5 | `07-ExtensiveForm-CSharp` (H) → `07-ExtensiveForm-Python` (Mo) | 07 | −1 | variantes | **G5/R1** : C# après Python |
| 6 | `04b-Lean-NashExistence-Lean` (TH) → `04c-NashExistence-CSharp` (H) | 04 | −1 | sommet avant jumelle | **G6/R3** : `04b` après **les deux** variantes de `04c` |
| 7 | `08b-Lean-CombinatorialGames-Lean` (TH) → `08c-CombinatorialGames-CSharp` (H) | 08 | −1 | sommet avant jumelle | **G7/R3** : `08b` après **les deux** variantes de `08c` |
| 8 | `15b-Lean-CooperativeGames-Lean` (TH) → `15c-CooperativeGames-CSharp` (H) | 15 | −1 | sujet Très haute avant sujet Haute | **G8/R3** : le sujet `15c` avant le noyau formel `15`/`15b` |
| 9 | `08d-Lean-CGT-Lean` (TH) → `09-BackwardInduction` (Mo) | 08→09 | **−2** | **rupture de bord** | **G9/R4** : `08d` en tête du bloc 09 |
| 10 | `16-MechanismDesign-Python` (TH) → `16b-Automated-Mechanism-Design` (H) | 16 | −1 | note | **réévaluer** une des notes — l'ordre est pédagogiquement juste |
| 11 | `17c-Lean-Lemons-Certificat-Lean` (TH) → `17d-Lean-Screening-Signaling-Lean` (H) | 17 | −1 | note | **réévaluer** une des notes — adverse selection avant screening est l'ordre juste |

### Effet mesuré des gestes G1 à G8

Simulation sur la séquence réelle, groupes déplacés (pas d'échange à deux) :

| | Descentes totales | Intra-bloc | De bord |
|---|---:|---:|---:|
| État actuel | **11** | **10** | 1 |
| Après G1-G8 | **8** | **5** | 3 |

Les trois descentes gagnées ne sont pas supprimées : **elles changent de nature** — elles passent d'intra-bloc (défaut) à bord (ré-entrée légitime). C'est le résultat visé : plus aucun bloc ne redescend à l'intérieur de lui-même pour une raison de variante.

**Les cinq descentes intra-bloc restantes** sont : deux gestes de groupe incomplets dans la simulation (`04b` et `08b` doivent suivre *toutes* les variantes de leur sujet voisin, pas seulement la première — la règle R3 le dit), un réordonnancement de sujets au bloc 15, et les **deux questions de note** des lignes 10 et 11, qu'aucun ordre ne corrige puisque la séquence est juste.

### Le tri complet n'est pas retenu, et voici pourquoi

Un tri de chaque bloc par difficulté mesurée (sujets puis variantes) rend **7 descentes au total et 4 intra-bloc** — mais il **crée une descente qui n'existe pas** : `04-NashEquilibrium-CSharp` (H) → `04h-Routing-PriceOfAnarchy` (Mo), parce que le sujet `04h` est moins noté que le sujet `04`. Un gain apparent qui déplace le problème. **Les gestes chirurgicaux sont préférés** : ils ne touchent que des variantes à l'intérieur d'un sujet, ne créent aucune descente nouvelle, et se vérifient un par un.

## 5. Ce que l'ordre cible ne règle pas, et qu'il faut nommer

1. **65 carnets sans note** (45 % de la racine), dont les 12 sujets listés au §1 et les blocs 22 et 23 entiers. Aucune règle d'ordre ne les situe : il leur faut une **ligne de gradation**, grain distinct.
2. **Le plateau de la bande 05-17** : la moyenne ne monte plus après le bloc 04. Une permutation n'y peut rien ; seule une réévaluation des notes, ou une refonte de la distribution du corpus, le pourrait. Ce ledger ne le maquille pas en progrès.
3. **Les 73 carnets hors racine** (quatre séries satellites) : leur gradation est un chantier propre, par série.
4. **Les 50 noms périmés des tables** : les sept ledgers restent des mesures datées de leur arbre, pas une description du présent. Une consolidation nominative serait un grain séparé.

## 6. Ce qui n'est pas exécuté

- **Aucune renumérotation** : G1 à G9 sont décrits, pas appliqués. L'acceptation 2 exige la validation avant exécution.
- **Aucun carnet modifié, aucun renommage, aucune réévaluation de note.**
- **Aucun déplacement hors bloc** (G9) : il change la composition d'un bloc et demande un arbitrage explicite.
- Les blocs 22 et 23 ne sont **pas** situés : ils n'ont pas de note.

## 7. Correspondance aux acceptations de #15615

| Acceptation | État après ce ledger |
|---|---|
| 1 — tableau de gradation publié | **couvert** par les sept ledgers de fournée (142 entrées de gradation) ; couverture 79/144 carnets de la racine, réserve du §1 |
| 2 — ordre cible validé avant exécution | **devient décidable** : les règles R1-R5 et les onze descentes sont posées ci-dessus ; la validation revient au user ou au coordinateur |
| 3 — tranches exécutées, preuve octet-à-octet | **dépend de 2** ; non commencée, et rien à exécuter tant que 2 n'est pas tranchée |
| 4 — liens croisés, labels, curriculum, READMEs réconciliés | **dépend de 3** |

## 8. La question, en forme fermée

L'ordre cible est proposé. Ce qui reste à trancher tient en un choix, une lettre suffit :

- **a)** appliquer les **gestes G1 à G8** (chirurgicaux, sans risque : ils ne déplacent que des variantes à l'intérieur d'un sujet, sans changer un nom, une note ni un contenu) et laisser G9 de côté ;
- **b)** appliquer **G1 à G9** (y compris sortir `08d` du bloc 08 vers la tête du bloc 09) ;
- **c)** n'appliquer aucun déplacement et **grader d'abord** les 12 sujets et 65 carnets non gradés, puis revoir l'ordre sur une base complète.

Je recommande **a)** : il livre l'essentiel de la cohérence demandée sans toucher à un contenu. Le volet **c)** reste utile ensuite, sur une base entièrement graduée.

See #14944 (epic renum — mécanique refermée, cette issue est le volet gradation pédagogique)
See #15586 (commentaire fondateur du user)
