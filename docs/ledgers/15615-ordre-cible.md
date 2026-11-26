# Ledger — Issue #15615 (ordre cible de gradation de la série GameTheory)

> **Bornage strict** : ce ledger mesure `origin/main` au **2026-11-25**, tête `06cd3788510`. Périmètre gradué = les **144 carnets `GameTheory-*` de la racine** `MyIA.AI.Notebooks/GameTheory/`. Les **73 carnets des cinq sous-dossiers** (`SocialChoice` 25, `Dynamics` 26, `Metajeux` 16, `Coalitions` 5, `gateway` 1) restent hors périmètre : ils n'ont aucune ligne de gradation. Ce ledger **ne renumérote rien, ne régrada rien, ne touche aucun carnet** — il propose.
>
> **Révision du 2026-11-26**, sur réserve du coordinateur (26/11 08:53Z) : les exceptions 14 et 15 sont séparées et l'amplitude recalculée ; la simulation du 25/11 est remplacée par un **replay** des gestes sur la séquence réelle ; deux mesures sont publiées au lieu d'une ; G6, G7, G8 et G9 sont re-spécifiés ou écartés contre la **table des prérequis déclarés** ; le compte des sujets sans note est refait sur les noms réels (**21**, et non 12).

## Origine

Scope 2 du cadrage du 2026-10-03 (« proposer un ordre cible »), rendu décidable par l'acceptation 1 : sept ledgers de fournée ont publié le tableau de gradation — [fondations](15615-gradation-foundations.md), [fournées A](15615-gradation-fournee-a.md), [B](15615-gradation-fournee-b.md), [C](15615-gradation-fournee-c.md), [D](15615-gradation-fournee-d.md), [consolidé 01-05](15615-gradation-blocs-01-05-consolide.md), [reprise 06-21](15615-gradation-reprise-blocs-06-21.md). L'acceptation 2 (« ordre cible validé (user ou coordinateur) avant toute exécution ») était la seule non tranchée.

Demande user fondatrice (commentaire #15586, 2026-09-11T13:43Z) : « la séquence refermée ne présente pas encore la cohérence qu'on retrouve dans les premiers numéros de la série ». Ce ledger mesure d'abord **si** c'est vrai, et où.

## 1. La base de mesure — et ce qu'elle ne couvre pas

Les sept ledgers totalisent **142 entrées de gradation** pour **129 noms de carnets distincts**, sur une échelle en **mots** et non en chiffres romains (`I`/`II`/`III` n'apparaît dans aucun) : **Basse 6, Moyenne 29, Haute 73, Très haute 34**.

**Re-mesure du 2026-11-25** — le tableau a vieilli de deux façons, toutes deux mesurées :

| Constat | Mesure |
|---|---|
| Carnets `GameTheory-*` à la racine | **144** |
| dont porteurs d'une ligne de gradation | **79** (55 %) |
| dont **non gradés** | **65** |
| Noms des tables qui ne désignent plus aucun carnet de la racine | **47 des 129** — **50** si l'on ne tolère pas la casse `-Csharp` / `-CSharp` (trois noms) |
| Sujets (bloc + indice) présents à la racine | **78** |
| dont **aucun carnet ne porte de ligne de gradation** sous son nom actuel | **21** — voir le détail sous le tableau |

Les **21 sujets sans carnet gradué** se répartissent en trois groupes, mesurés l'un après l'autre :

- **12 sans aucune ligne dans les tables** : `02e`, `04i`, `04j`, `04k`, `05c`, `11c`, `11e`, `11f`, `14b`, `14c`, `22`, `23`.
- **6 dont la ligne existe sous un autre nom** : pour cinq, la ligne se retrouverait par une consolidation nominative — `03d-Deux-Especes-de-Fleches` est gradué sous `03g` et `03h`, `03e-Meta-Actions-Tarifees` sous `03e` sans suffixe puis sous `03f`, `15d-Shapley-Groupes` sous `15f`, `16d-LLM-Players-Othman-Sandholm` sous `16e`, `16e-Populations-Othman-Sandholm` sous `16g` ; le sixième, `03b-Chambres-Murs-Chemins-Lean`, réunit dans son nom deux titres gradués séparément (`Chemins-de-Swaps`, `Chambres-et-Murs`).
- **3 capstones jamais gradués** : `18`, `19` et `20` — les lignes de leur indice sont celles des carnets partis vers `Metajeux/`.

Deux conséquences, qui bornent ce que ce ledger peut affirmer :

- **Un ordre cible au niveau du nom de fichier n'est pas produisible** sur un demi-corpus : 47 des 129 noms des tables ne désignent plus aucun carnet de la racine, et les indices des blocs 03, 15 et 16 ont changé depuis les tables. L'ordre cible se propose donc **au niveau du sujet** et de la **variante de langue**, en nommant les carnets par leur nom actuel.
- **Les blocs 22 et 23 n'ont jamais été gradés** : ils sont entrés dans la série après la fournée D, qui déclarait « la série s'arrête au bloc 20 ». Aucun ordre ne peut les situer autrement qu'à titre provisoire.

### Deux mesures, et pourquoi la seconde est nécessaire

L'ordre réel est l'ordre des **noms de fichiers**. Une descente est un couple adjacent dont la note baisse. Deux façons de compter ont été mesurées sur la même séquence :

| Mesure | Définition | Paires comptées |
|---|---|---:|
| **1** — voisins immédiats | deux carnets adjacents, **tous deux gradés** | **49** sur 143 |
| **2** — gradés consécutifs | deux carnets gradés consécutifs, les carnets non gradés étant sautés | **78** sur 143 |

La mesure 1 est celle des ledgers précédents ; elle est conservée pour la comparabilité. Mais elle **sous-estime** : un carnet non gradé entre deux carnets gradés masque la paire, et **94 paires sur 143 échappent à la mesure 1** (65 carnets n'ont pas de note). La mesure 2 est donc publiée comme contrôle, et **un geste ne se lit comme retirant une descente que s'il la retire sous les deux mesures** — c'est la règle appliquée au §4.

### La série a été restructurée depuis l'audit : 18-21 sont des portes

Sur les blocs de queue, la racine ne garde que des **capstones**. Quatre séries satellites existent sous `GameTheory/` (72 carnets, aucun gradué), plus un carnet `gateway` isolé — 73 carnets hors racine au total —, et chaque capstone en ouvre une par son nom :

| Bloc racine | Carnets présents | Série ouverte |
|---|---|---|
| 18 | `18-Capstone-Metajeux-Python/-CSharp`, `18c-Humour-Banc-Python` | porte vers `Metajeux/` (16 carnets) |
| 19 | `19-Capstone-Dynamics-Python/-CSharp` | porte vers `Dynamics/` (26 carnets) |
| 20 | `20-Capstone-Coalitions-Python` | porte vers `Coalitions/` (5 carnets) |
| 21 | `21-Capstone-Choix-Social-Python/-Rust` | porte vers `SocialChoice/` (25 carnets) |

Les renommages sortants des blocs 18 à 20 sont tracés par la fournée D : six carnets vers `Metajeux-01` à `Metajeux-06`, deux vers la série GOL (`GOL-08`, `GOL-09`). **Un capstone de porte n'est pas un sommet** : sa difficulté basse est un fait de conception, pas un défaut d'ordre.

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

**Lecture, avec les deux exceptions séparées.** La rampe que le user décrit existe et elle est mesurable : **1,00 → 1,75 → 2,00 → 3,00 sur les quatre premiers blocs**. Puis la série atteint son régime au bloc 04.

Sur les blocs **05 à 17**, les moyennes vont de **2,50 à 4,00**, amplitude **1,50**. Deux blocs en sortent, et ce sont eux qui portent l'amplitude :

| Bloc | Moyenne | Gradés / présents | Ce qu'il est |
|---|---:|---:|---|
| 14 | 4,00 | **2 / 6** | deux carnets Très haute, quatre non gradés |
| 15 | 3,60 | **5 / 6** | coeur coopératif entièrement Très haute ou Haute |

**Hors ces deux exceptions**, les onze blocs restants (05 à 13, 16, 17) s'étalent de **2,50 à 3,29**, soit **0,79 d'amplitude** — huit dixièmes, et non « six » comme l'écrivait la version du 25/11. Le fait mesuré ne change pas de nature : **aucun palier n'est franchi en onze blocs**, la remontée n'arrive que par les deux sommets isolés ci-dessus, et la distribution du corpus reste plate (73 des 142 entrées de gradation sont Haute).

Ce n'est donc pas un défaut d'ordonnancement seul : une permutation ne peut pas fabriquer une pente que le contenu n'a pas. Ce que l'ordre peut porter, c'est une **progressivité intra-bloc** ; la progressivité inter-blocs demanderait une réévaluation des notes, hors de ce scope.

### Les descentes réelles, sous les deux mesures

Une mesure antérieure, faite sur les noms des tables plutôt que sur la séquence réelle, avait été annoncée à 27 descentes sur 141 transitions. Rejouée ce jour sur les 142 entrées des sept tables, dans l'ordre du fichier de mesure, elle donne **28 descentes sur 141 transitions** (26 sur 128 en ne retenant que la première apparition de chacun des 129 noms) : le chiffre de 27 n'est pas reproduit. Ces marches ne décrivent de toute façon pas la série — elles parcourent des noms historiques, avec 13 noms portés par deux entrées et 47 noms qui ne désignent plus aucun carnet de la racine. Sur la séquence **réelle** :

| Classe | Mesure 1 (49 paires) | Mesure 2 (78 paires) |
|---|---:|---:|
| Descentes totales | **11** | **19** |
| dont **intra-bloc** — le lecteur monte puis redescend dans le même bloc | **10** | **16** |
| dont **de bord** — fin d'un bloc vers le début du suivant | **1** | **3** |

Les **trois descentes de bord** de la mesure 2, nommées :

| Paire | Delta |
|---|---:|
| `05b-Lean-Minimax-Lean` (TH) → `06-EvolutionTrust-CSharp` (Ha) | −1 |
| `08d-Lean-CGT-Lean` (TH) → `09-BackwardInduction-CSharp` (Mo) | **−2** |
| `18c-Humour-Banc-Python` (TH) → `21-Capstone-Choix-Social-Python` (Mo) | **−2** |

Une descente de bord est une **ré-entrée** : un bloc repart plus bas, c'est un fait de conception. Une descente intra-bloc est le défaut que le user décrit. La deuxième ligne du tableau traverse la chaîne des portes 19-20 : elle relève de la règle R5, pas d'un déplacement.

### L'échelle de langue ne prédit pas la difficulté — mesure

Deux carnets sont **jumeaux** quand ils ne diffèrent que par la langue (`-Python`, `-CSharp`). **51 sujets de la racine** ont leurs deux jumeaux ; **21** en ont les deux notes :

| Note du jumeau C# face à celle du jumeau Python | Sujets |
|---|---:|
| **+1** au-dessus | **4** — 04, 05, 06, 07 |
| **égale** | **14** |
| **1 en dessous** | **3** — 13, 16, 17 |

Les blocs 13, 16 et 17 inversent la tendance des quatre premiers : le carnet Python y porte le contenu de référence (CFR complet, théorie des mécanismes, MARL) et le jumeau C# y est gradué une note plus bas. **Une règle « Python puis C# puis Lean » serait donc fausse** : la règle correcte est « par note graduée croissante, quelle que soit la langue ».

La convention **déclarée** est autre chose que la note, et elle se mesure aussi. **Dix carnets C#** (onze noms dans les tables, une ancienne orthographe comprise) **citent un carnet Python parmi leurs prérequis**, dont **neuf leur propre base** (le dixième, `04c-NashExistence-CSharp`, cite la base du sujet `04`). Les quatre sujets où le C# est noté au-dessus (04, 05, 06, 07) sont parmi ces neuf. L'ordre alphabétique les sépare pourtant, parce que `-CSharp` trie avant `-Python`.

## 3. L'ordre cible proposé — cinq règles

**R1 — Dans un sujet, les variantes se rangent par note graduée croissante, et derrière toute variante que leurs prérequis déclarent.** Mesure au §2 : la langue ne prédit le niveau que dans quatre sujets sur vingt et un, et neuf carnets C# déclarent leur propre base Python.

**R2 — Une extension suit sa base.** `02-NormalForm-Part2-*` après les deux variantes de `02-NormalForm-*`. Le défaut actuel est alphabétique : `NormalForm-Part2` trie avant `NormalForm-Python`.

**R3 — La place d'un sommet formel se lit dans la table des prérequis déclarés, jamais dans la note.** La version du 25/11 formulait l'inverse (« le sommet se place après toutes les variantes du sujet voisin qu'il domine »). La table la contredit sur ses trois cas :

| Sommet | Prérequis déclarés | Relation au sujet voisin |
|---|---|---|
| `04b-Lean-NashExistence-Lean` | `02b-Lean-Definitions` ; topologie ; tactiques Lean | **aucune** avec `04c` (qui déclare `04`) |
| `08b-Lean-CombinatorialGames-Lean` | `08-CombinatorialGames` + bases Lean 4 | **aucune** avec `08c` (qui déclare `08` aussi) ; `08d` déclare « suite 8b/8c » |
| `15b-Lean-CooperativeGames-Lean` | aucune — « compagnon formel du 15 » | `15c-Python` se déclare « **compagnon Python du 15b** » : la dépendance va du voisin vers le sommet, pas l'inverse |

Aucune « domination » n'est donc établie, et un geste qui déplace un sommet devant le carnet qui le déclare comme prérequis n'est pas un ordre : c'est un défaut de plus. La règle ne fonde qu'**un** geste, G7, qui ne déplace `08b` que derrière des carnets indépendants de lui, `08d` restant après les deux.

**R4 — Un bloc de contenu se termine sur son maximum, et son premier carnet n'est jamais un sommet qu'il abandonne.** La seule rupture de ce type entre deux blocs de contenu est `08d` (TH) → `09-BackwardInduction-CSharp` (Mo), −2 ; la seconde rupture −2 (`18c` → `21`) traverse la chaîne des portes et relève de R5. Une rupture de bord **ne se traite pas par un déplacement d'un cran** : les deux carnets sont déjà voisins, et les échanger ne change rien (mesure au §4, G9). Elle se déclare (R5) ou se traite par le contenu — rattacher `08d` au bloc 09 avec ses prérequis est une décision de sujet, pas un geste d'ordre.

**R5 — Une porte n'est pas un sommet.** Les blocs 18 à 21 ouvrent les séries satellites ; leur note basse est acquise par conception et ne se corrige pas par déplacement. Une porte se déclare (titre, navigation) plutôt que de se reclasser.

## 4. Les onze descentes, le replay de chaque geste, et ce qui est retenu

### Les onze descentes de la mesure 1, avec noms réels

| # | Paire (avant → après) | Mesures | Delta | Classe |
|---|---|---|---:|---|
| 1 | `02-NormalForm-Part2-Python` (Mo) → `02-NormalForm-Python` (Ba) | 1 et 2 | −1 | extension avant base |
| 2 | `04-NashEquilibrium-CSharp` (Ha) → `04-NashEquilibrium-Python` (Mo) | 1 et 2 | −1 | jumeau avant sa base |
| 3 | `05-ZeroSum-Minimax-CSharp` (Ha) → `05-ZeroSum-Minimax-Python` (Mo) | 1 et 2 | −1 | jumeau avant sa base |
| 4 | `06-EvolutionTrust-CSharp` (Ha) → `06-EvolutionTrust-Python` (Mo) | 1 et 2 | −1 | jumeau avant sa base |
| 5 | `07-ExtensiveForm-CSharp` (Ha) → `07-ExtensiveForm-Python` (Mo) | 1 et 2 | −1 | jumeau avant sa base |
| 6 | `04b-Lean-NashExistence-Lean` (TH) → `04c-NashExistence-CSharp` (Ha) | 1 et 2 | −1 | sommet formel avant son sujet |
| 7 | `08b-Lean-CombinatorialGames-Lean` (TH) → `08c-CombinatorialGames-CSharp` (Ha) | 1 et 2 | −1 | sommet formel avant ses variantes |
| 8 | `15b-Lean-CooperativeGames-Lean` (TH) → `15c-CooperativeGames-CSharp` (Ha) | 1 et 2 | −1 | sujet Très haute avant sujet Haute |
| 9 | `08d-Lean-CGT-Lean` (TH) → `09-BackwardInduction-CSharp` (Mo) | 1 et 2 | **−2** | rupture de bord |
| 10 | `16-MechanismDesign-Python` (TH) → `16b-Automated-Mechanism-Design-Python` (Ha) | 1 et 2 | −1 | note — l'ordre est juste (`16b` déclare GT-16) |
| 11 | `17c-Lean-Lemons-Certificat-Lean` (TH) → `17d-Lean-Screening-Signaling-Lean` (Ha) | 1 et 2 | −1 | note — l'ordre est juste (`17d` se déclare compagnon de `17c`) |

Les lignes 10 et 11 ne sont pas des défauts d'ordre : la cible déclare le carnet qui la précède, et la séquence est pédagogiquement juste. Elles ne se corrigent que par une note.

### Le replay : ce que chaque geste fait réellement

Chaque geste est rejoué sur la séquence réelle des 144 carnets (groupes déplacés, jamais d'échange à deux), sous les deux mesures, puis confronté à la table des prérequis **dans les deux sens** : ce que le groupe déplacé déclare, et ce qui le déclare. Aucun carnet ne déclare `04b`, `04d` ni `08d` ; `08b` et `08c` ne sont cités que par `08d`, comme suite de navigation (« Aucune déclarée — suite 8b/8c ») ; `15c-Python` se dit compagnon du `15b`, et `17d` compagnon du `17c`. Effet net sur le **total** des descentes :

| Geste | Groupe déplacé | Ancre | Mesure 1 | Mesure 2 | Prérequis déclarés | Verdict |
|---|---|---|---:|---:|---|---|
| **G1'** | `02-NormalForm-Python` | en tête du bloc 02, avant `02-NormalForm-CSharp` | −1 | −1 | `02-NormalForm-CSharp` déclare `01 + 02-Python` | **retenu** |
| G1 (écrit le 25/11) | `02-NormalForm-Python` | *après* `02-NormalForm-CSharp` | −1 | −1 | place la variante C# **avant** sa base déclarée | écarté |
| **G2** | `04-NashEquilibrium-CSharp` | après `04-NashEquilibrium-Python` | −1 | −1 | le C# déclare `04-Python` | **retenu** |
| **G3** | `05-ZeroSum-Minimax-CSharp` | après `05-ZeroSum-Minimax-Python` | −1 | −1 | le C# déclare `05-Python` | **retenu** |
| **G4** | `06-EvolutionTrust-CSharp` | après `06-EvolutionTrust-Python` | −1 | −1 | le C# déclare `06-Python` | **retenu**, coût nommé |
| **G5** | `07-ExtensiveForm-CSharp` | après `07-ExtensiveForm-Python` | **+1** | **+1** | le C# déclare `07-Python` | **retenu**, coût nommé |
| G6-a (écrit) | `04b-Lean-NashExistence-Lean` | après les deux variantes de `04c` | −1 | **0** | aucune | écarté : **déplace** |
| G6-b (option b)) | `04b-Lean-NashExistence-Lean` | après `04d-Marchandage-Asymetrique-Python` (Ha), avant `04e-Reflective-Oracles-Python` (TH) | −1 | −1 | aucune | option b) au §8, coût de sujet |
| G6-c | `04b-Lean-NashExistence-Lean` | après `04e-Reflective-Oracles-Python` | −1 | −1 | aucune | écarté : même gain que G6-b, déplacement plus long |
| **G7** | `08b-Lean-CombinatorialGames-Lean` | après les deux variantes de `08c` | −1 | −1 | `08b` et `08c` ne déclarent que `08` ; `08d` les suit | **retenu** |
| G8 (écrit) | sujet `15c` (deux carnets) | avant `15` et `15b` | −1 | **+1** | `15c-Python` se dit « compagnon Python du 15b » | **écarté** : place le compagnon avant ce qu'il accompagne |
| G9 (écrit) | `08d-Lean-CGT-Lean` | tête du bloc 09 | **0** | **0** | — | **écarté** : aucun rang ne change |

Quatre constats de ce replay, chacun mesuré :

1. **G1 écrit et G1' donnent le même compte** (−1) et ne se distinguent que par la table des prérequis : la version du 25/11 aurait placé `02-NormalForm-CSharp` avant sa base. Le compte ne suffit pas — c'est pourquoi la colonne des prérequis existe.
2. **G6 tel qu'écrit ne retire pas la descente, il la déplace** : de `04b` (TH) → `04c-NashExistence-CSharp` vers `04b` (TH) → `04d-Marchandage-Asymetrique-Python` (Ha). La mesure 1 ne le voit pas, parce que `04d-Marchandage-Asymetrique-CSharp` n'a pas de note et masque la paire. Seul le placement **G6-b** la retire sous les deux mesures : après `04d-Marchandage-Asymetrique-Python` (Ha) et avant `04e-Reflective-Oracles-Python` (TH), il ne crée aucune paire descendante.
3. **G8 réordonne bien un sujet entier, pas une variante** : le sujet `15c` (deux carnets) passe devant `15` et `15b`, cinq carnets changent de rang, le compagnon (`15c`) passe devant le `15b` dont il se dit l'illustration, et **sous la mesure 2** deux descentes de bord apparaissent (`14-DifferentialGames-Python` TH → `15c-CSharp` Ha ; `15b` TH → `16-MechanismDesign-CSharp` Ha) pour une retirée — la mesure 1 ne voit que la retirée, ses voisins immédiats étant non gradés.
4. **G9 ne change aucun rang** : `08d` est déjà immédiatement avant `09-BackwardInduction-CSharp`. Le geste ne fait que requalifier la paire de « bord » en « intra » — il reproduit la descente sous une autre étiquette.

### Ce que les chiffres du 25/11 contenaient

| Scénario | Mesure 1 | Mesure 2 |
|---|---|---|
| État actuel | 11 total / 10 intra / 1 bord | 19 total / 16 intra / 3 bord |
| G1 à G5 seuls — **les chiffres publiés le 25/11** | 8 / 5 / 3 | 16 / 11 / 5 |
| + G7 — **option a)** | 7 / 4 / 3 | 15 / 10 / 5 |
| + G6-b — **option b)** | 6 / 3 / 3 | 14 / 9 / 5 |
| G1 à G9 tels qu'écrits | 5 / 3 / 2 | **16 / 10 / 6** |

Trois corrections que ce tableau impose (mesure 1, sauf mention contraire) :

- Les chiffres publiés (**11 → 8**, intra **10 → 5**, bord **1 → 3**) sont ceux de **G1 à G5 seuls**. La feuille de calcul du 25/11 n'a pas été conservée ; ces chiffres ne peuvent venir d'une exécution qui aurait appliqué G6 et G7 tels qu'écrits (elle donnerait 6 / 3 / 3) ni G8 (5 / 2 / 3).
- La phrase « les trois descentes gagnées passent d'intra-bloc à bord » est fausse : le total perd trois descentes, donc **trois disparaissent** ; cinq quittent le compte intra et **deux** descentes de bord naissent, toutes deux créées par G5. La version du 25/11 attribuait à une conversion ce qui est une suppression plus une création.
- L'ordre cible **tel qu'écrit** (G1 à G9) ne retire que trois descentes réelles (19 → 16 en mesure 2), et sa baisse du compte de bord en mesure 1 (2 au lieu de 3) vient du reclassement de G9, pas d'un déplacement.

### Le coût de trois gestes, nommé

- **G4** retire une descente intra sous les deux mesures et, **sous la mesure 2**, approfondit la descente de bord `05b` (TH) → tête du bloc 06, de −1 (`06-CSharp` Ha) à −2 (`06-Python` Mo). La mesure 1 ne voit ni l'une ni l'autre : `05c-KKT-Dualite-Lagrangienne-Python`, non gradé, est intercalé entre `05b` et le bloc 06. La dépendance déclarée l'emporte, mais le coût est réel.
- **G5** retire une descente intra et **crée deux** descentes de bord (`06i-Ensembles-Limites-Poincare-Bendixson-Python` Ha → `07-Python` Mo ; `07-CSharp` Ha → `08-CombinatorialGames-CSharp` Mo) : **total +1**. Il est fondé par la dépendance déclarée (`07-Python`, pont twin), pas par le compte. Aucun placement ne l'évite tant que le bloc 06 se termine sur un carnet Haute et le bloc 08 commence sur Moyen.
- **G6-b** retire une descente sous les deux mesures, au prix de **séparer `04b` de son sujet** (`04c`, existence de Nash) pour l'installer après `04d` (marchandage). C'est un arbitrage pédagogique, pas un calcul.

Résultat du replay pour le bloc 08 après G7 : `08-CombinatorialGames-CSharp` Mo · `08-…-Python` Mo · `08-…-Rust` (non gradé) · `08c-CSharp` Ha · `08c-Python` Ha · `08b-Lean-…` TH · `08d-Lean-CGT-Lean` TH — le bloc devient strictement croissant sur ses carnets gradés.

### Le tri complet n'est pas une option

Un tri de chaque bloc par difficulté mesurée a été envisagé le 25/11 puis écarté. Ses chiffres d'alors (7 descentes au total, 4 intra-bloc) **ne sont pas reproduits ici** : ils avaient été obtenus sur les noms des tables, non sur la séquence réelle, et aucune feuille de calcul n'est conservée. Ce qui reste vrai sans chiffre : trier un bloc par note réordonne les **sujets** eux-mêmes, donc la progression pédagogique voulue par les numéros, et déplace les descentes vers les bords au lieu de les supprimer. Les gestes chirurgicaux sont préférés : ils touchent un groupe nommé, se vérifient un par un, et se rejouent.

## 5. Ce que l'ordre cible ne règle pas, et qu'il faut nommer

1. **65 carnets sans note** (45 % de la racine), dont les 21 sujets listés au §1, blocs 22 et 23 compris. Aucune règle d'ordre ne les situe : il leur faut une **ligne de gradation**, grain distinct. Tant qu'ils manquent, **94 paires adjacentes sur 143 restent hors de la mesure 1**.
2. **Le nommage est la cause racine des descentes 1 à 5.** L'ordre alphabétique, et non une décision pédagogique, place un carnet avant sa base déclarée : `NormalForm-Part2` trie avant `NormalForm-Python` (descente 1), et `-CSharp` trie avant `-Python` (descentes 2 à 5). Neuf paires dont le carnet C# déclare sa propre base sont ainsi inversées : **quatre** se voient au compte, **cinq** restent invisibles, leurs deux notes étant égales (`02-NormalForm`, `02-NormalForm-Part2`, `02c-Travelers-Dilemma`, `03-Topology2x2`, `08-CombinatorialGames`). Deux voies, qui demandent toutes deux l'acceptation 2 : déplacer les carnets un par un (ce ledger), ou **renommer les bases** en retirant le suffixe `-Python` — un renommage de série, hors périmètre.
3. **Le plateau de la bande 05-17** : la moyenne ne monte plus après le bloc 04. Une permutation n'y peut rien ; seule une réévaluation des notes, ou une refonte de la distribution du corpus, le pourrait. Ce ledger ne le maquille pas en progrès.
4. **Les 73 carnets hors racine** — quatre séries satellites (`SocialChoice` 25, `Dynamics` 26, `Metajeux` 16, `Coalitions` 5) et un carnet `gateway` isolé : leur gradation est un chantier propre, par série.
5. **Les 47 noms périmés des tables** (50 sans la tolérance de casse) : les sept ledgers restent des mesures datées de leur arbre, pas une description du présent. Une consolidation nominative serait un grain séparé.

## 6. Ce qui n'est pas exécuté

- **Aucune renumérotation** : les gestes sont décrits, rejoués, pas appliqués. L'acceptation 2 exige la validation avant exécution.
- **Aucun carnet modifié, aucun renommage, aucune réévaluation de note.**
- **Tout geste retenu est un renommage** : l'ordre de la série est l'ordre des noms de fichiers, donc déplacer un carnet change son nom, ses liens de navigation et les références qui le citent. La version du 25/11 écrivait « sans changer un nom » : c'était faux, et l'acceptation 4 (liens croisés, curriculum, READMEs) mesure ce coût. Une alternative existe — porter l'ordre de lecture dans la navigation plutôt que dans les noms — mais elle est un choix d'architecture de la série, pas un geste de ce ledger.
- Les blocs 22 et 23 ne sont **pas** situés : ils n'ont pas de note.

## 7. Correspondance aux acceptations de #15615

| Acceptation | État après ce ledger |
|---|---|
| 1 — tableau de gradation publié | **couvert** par les sept ledgers de fournée (142 entrées de gradation) ; couverture 79/144 carnets de la racine, réserve du §1 |
| 2 — ordre cible validé avant exécution | **devient décidable** : règles R1-R5, replay de chaque geste sous deux mesures, et options a/b/c au §8 ; la validation revient au user ou au coordinateur |
| 3 — tranches exécutées, preuve octet-à-octet | **dépend de 2** ; non commencée, et rien à exécuter tant que 2 n'est pas tranchée |
| 4 — liens croisés, labels, curriculum, READMEs réconciliés | **dépend de 3** ; le §6 chiffre ce que chaque geste y coûte (un renommage par carnet déplacé) |

## 8. La question, en forme fermée

Ce qui reste à trancher tient en un choix, une lettre suffit :

- **a)** appliquer les **six gestes fondés par la table des prérequis** — G1' (`02-NormalForm-Python` en tête du bloc 02), G2, G3, G4, G5, G7 — soit 11 → 7 descentes (mesure 1) et 19 → 15 (mesure 2), **aucune dépendance déclarée inversée**, avec les coûts nommés au §4 (G4 approfondit une descente de bord, G5 en crée deux) ;
- **b)** appliquer **a)** **plus G6-b** — `04b` après `04d-Python` — soit 11 → 6 (mesure 1) et 19 → 14 (mesure 2), au prix d'éloigner le compagnon formel de son sujet ;
- **c)** ne rien déplacer et **grader d'abord** les 65 carnets non gradés (dont les 21 sujets sans aucun carnet gradué, blocs 22 et 23 compris), puis revoir l'ordre sur une base complète.

Les gestes G8 et G9 ne sont plus des options : le premier place un compagnon devant le carnet dont il se dit l'illustration et, sous la mesure 2, ajoute une descente ; le second ne change aucun rang.

Je recommande **a)**, et **b)** laissé à l'arbitrage de contenu : a) prend tout ce que les prérequis déclarés justifient sans séparer un sujet de son compagnon. Le volet **c)** reste utile ensuite, sur une base entièrement graduée.

See #14944 (epic renum — mécanique refermée, cette issue est le volet gradation pédagogique)
See #15586 (commentaire fondateur du user)
