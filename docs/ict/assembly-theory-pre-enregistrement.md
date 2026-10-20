# Pré-enregistrement — Assembly Theory (case 20 : l'assembly index mesuré, contre la lecture « compression LZ »)

> **Grade C explicite.** Ce document **scelle** le protocole de la tranche Assembly Theory de la veille [#8182](https://github.com/jsboige/CoursIA/issues/8182) **AVANT toute écriture du banc de mesure** — héritage direct des tranches Metzinger ([#17159](https://github.com/jsboige/CoursIA/pull/17159)), Kastrup (case 18), Emilsson (case 17) et Butlin (case 19, [#20409](https://github.com/jsboige/CoursIA/pull/20409)) : sources primaires lues et archivées, pré-enregistrement commité avant l'implémentation et la mesure, verdict borné.
>
> **Cycle du 2026-10-20**, lane `myia-po-2025:CoursIA`. Claim : commentaire [6290583386](https://github.com/jsboige/CoursIA/issues/8182#issuecomment-6290583386) sur [#8182](https://github.com/jsboige/CoursIA/issues/8182). Tranche **3** de la décision ai-01 du 2026-10-05 (Bach → Schneider/Butlin → Assembly Theory), où la théorie est attendue **dans le registre émergence/MDL, jamais présentée comme théorie de la conscience**.

## 1. Sources primaires et archivage

**Source primaire** : Abhishek Sharma, Dániel Czégel, Michael Lachmann, Christopher P. Kempes, Sara I. Walker, Leroy Cronin, « Assembly theory explains and quantifies selection and evolution », *Nature* **622**, 321–328, publié le 4 octobre 2023, DOI [10.1038/s41586-023-06600-9](https://doi.org/10.1038/s41586-023-06600-9). **Open access**.

**Archivage gisement** ([bibliography-hygiene](../../.claude/rules/bibliography-hygiene.md)) : `G:\Mon Drive\MyIA\IA\Bibliographie IA\Consciousness\2023 - Sharma et al - Assembly theory explains and quantifies selection and evolution.pdf` — 3 298 161 octets, en-tête `%PDF-1.4`, sha256 `59c04099e11fcd24083ae7955d63993d2d1304633c605ad25994f509629ada6f`. Recherche préalable par auteur ET titre (`sharma`, `cronin`, `kempes`, `walkercee`, `assembl`) : **aucune copie préexistante**, un seul dépôt, rayon `Consciousness` (le rayon des sources de la veine #8182 — il porte déjà Butlin 2023 et Aaronson).

**Contre-claim** (la critique de compression-complexité, citée par l'issue comme le point de contact naturel) : Felipe S. Abrahão, Santiago Hernández-Orozco, Narsis A. Kiani, Jesper Tegnér, Hector Zenil, « Assembly Theory is an approximation to algorithmic complexity based on LZ compression that does not explain selection or evolution », *PLOS Complex Systems* **1**(1): e0000014, 23 septembre 2024, DOI [10.1371/journal.pcsy.0000014](https://doi.org/10.1371/journal.pcsy.0000014) ; preprint lu : **arXiv:2403.06629v6** (1er avril 2024), 38 pages.

**Archivage** : `G:\Mon Drive\MyIA\IA\Bibliographie IA\Consciousness\2024 - Abrahão et al - Assembly Theory is an approximation to algorithmic complexity based on LZ compression that does not explain selection or evolution (arXiv 2403.06629v6, OA).pdf` — 1 303 148 octets, `%PDF-1.5`, sha256 `1f8b2bf4a0630684fe80484a9a9e90cc417a9aa225315dd64c7bcf1265251bf8`. Même recherche préalable (`abrah`, `zenil`) : aucune copie.

**Méthode de lecture** : texte intégral du preprint extrait (`pypdf`, 38 pages, un fichier texte sans marqueurs) puis **relecture firsthand** par la lane des passages pivots cités ci-dessous (G.1 — aucune citation n'est propagée sans relecture directe ; le PDF primaire est lu en pages réelles, p. 321–323).

## 2. Le cadre en deux phrases

**AT** définit un objet non comme un point mais comme ce que ses **histoires de formation** permettent : « AT conceptualizes objects not as point particles, but as entities defined by their possible formation histories » (p. 321). L'**assembly index** d'un objet est « the length of the shortest assembly pathway that can generate the object » (p. 322), où l'on part des blocs élémentaires et l'on joint récursivement — « **the objects formed are added back to the assembly pool and are available for subsequent steps** » (p. 322). Pour un objet fini l'index est **calculable en temps fini** (« the number of total possible steps, although potentially large, is always finite for any finite object and thus the assembly index is computable in finite time », p. 322), et la figure 1b du papier l'instancie explicitement sur une **chaîne** (peptides `G G G F H H H V G`, blocs = lettres, « String assembly index: 8 », p. 323). L'équation d'assemblage `A = Σ_{i=1..N} e^{a_i} (n_i − 1) / N_T` (p. 323, éq. 1) combine index et nombre de copies pour quantifier « the total amount of selection necessary to produce an ensemble of observed objects ».

**Le contre-claim** soutient que cette procédure est **équivalente à une compression LZ**. Énoncés pivots (texte extrait du preprint, relecture firsthand) :

- résumé (l.18-27) : « We prove the full equivalence between Assembly Theory (AT) and Shannon Entropy via a method based upon the principles of statistical compression renamed "assembly index" that belongs to the LZ family […] we show that **the assembly index value is equivalent to the size of a minimal context-free grammar**. The statistical compressibility of such a method is bounded by Shannon Entropy and other equivalent traditional LZ compression schemes, such as LZ77, LZ78, or LZW. »
- §2.1, titre (l.128) : « **The assembly index is a compression algorithm of the LZ family** » ; l.180 : « the assembly index is fundamentally underpinned by the LZ encoding of the objects it measures » ; l.171-173 : les variantes sont « **qualitatively and quantitatively equivalent to the LZ compression algorithms introduced in the 1970s, such as LZ77/LZ78** ».
- §3, conclusions (l.408-413) : les exemples favoris des auteurs d'AT, « **ABRACADABRA and BANANA, are traditionally used to teach LZ77, LZ78, or LZW compression** in Computer Science courses at university level ».
- §3 (l.420-427), l'énoncé qui porte la charge quantitative : « **an object with a low assembly index has high LZ compressibility** (i.e., it is more compressible according to the LZ scheme), and therefore would necessarily display low entropy […] In the opposite direction, **an object with a high assembly index will have low LZ compressibility**, and therefore high entropy. This means that the methods based on AT, Shannon Entropy, and LZ compression algorithms are **indistinguishable from each other with regard to the quantification of complexity** of the assembling process. »

**Traduction pour un banc de chaînes — les deux camps s'accordent sur l'objet formel.** Sur une chaîne, l'assembly index est exactement la **taille minimale d'un programme linéaire (SLP)** qui génère `x` : le contre-claim l'énonce lui-même comme une équivalence (« equivalent to the size of a minimal context-free grammar », résumé ; « the assembly index is defined as the number of non-basis vertices », l.1090 ; théorème 7, l.1021-1104), et le primaire la rend « computable in finite time » (p. 322) par jointures avec **pool réutilisable**. La divergence n'est donc **pas** dans la formalisation : elle est dans la **conséquence quantitative** que le contre-claim en tire — que la mesure serait *indistinguable* de ce que produit un compresseur LZ hors-the-box (ZIP/GZIP, LZ77, LZ78, LZW).

## 3. Question falsifiable

L'**assembly index exact** d'une chaîne se comporte-t-il, sur des échelles contrôlées, comme **ce que produisent réellement les compresseurs LZ** — au sens fort du contre-claim (« indistinguables quant à la quantification de complexité ») et au sens de sa biconditionnelle directionnelle (l.420-427) ?

Trois tests bornés, un par énoncé distinct : **H1** l'index est-il déterminé par l'entropie de Shannon de l'objet ? **H2** sur des échelles structurées, l'index et les proxys LZ suivent-ils le même régime de croissance (et la direction de la biconditionnelle tient-elle) ? **H3** la direction grossière « bas index ↔ compressible » tient-elle globalement sur une batterie mixte ?

**Ce que ce banc n'est pas.** Il ne teste ni l'équation d'assemblage, ni le nombre de copies, ni la détection de vie — non mesurables dans un jouet de chaînes sans sur-claim. Il ne teste pas le théorème **ensembliste/statistique** du contre-claim (l'équivalence avec l'entropie de Shannon y est énoncée pour des *méthodes de compression statistique* sur des distributions ; H1, lui, mesure des **objets individuels** — la portée de chaque verdict est écrite à sa ligne). Il ne mesure aucune conscience.

## 4. Le substrat et l'instrument (scellés)

**Substrat** : chaînes binaires. Alphabet = blocs élémentaires `{0, 1}` (disponibles gratuitement, copies illimitées) ; opération de jointure = concaténation de deux pièces **déjà dans le pool** ; les pièces produites **restent** dans le pool (réutilisation, condition du primaire p. 322). `ai(x)` = nombre **minimal** de jointures pour que `x` soit dans le pool. Unicité de la forme pour un objet donné : toute pièce utile est une **sous-chaîne contiguë de `x`** (une pièce qui ne l'est pas ne peut apparaître dans aucun ancêtre de `x` dans un programme minimal) — le banc restreint donc la recherche aux intervalles de `x`, ce qui est exact et non une approximation.

**Instrument exact (deux implémentations indépendantes)** :
1. `exact_ai(x)` — parcours en largeur par niveaux de coût sur des états `frozenset` d'intervalles (jointures valides seulement), déduplication, budget d'états déclaré (`reach_exceeded` au-delà — jamais d'approximation silencieuse) ;
2. `brute_force_ai(x)` — seconde implémentation, énumération exhaustive d'un espace d'états **différent** (construction incrémentale des pools, multiensemble de pièces, sans restriction d'intervalles), pour les très petits `n`.

**Bornes certifiées (H2 en dépend)** :
- **borne de doublement (inférieure, universelle)** : chaque jointure fait au plus **doubler** la longueur de sa plus longue pièce ; partant de pièces de longueur 1, la plus longue pièce après `m` jointures est de longueur ≤ `2^m` ; produire `x` de longueur `n` exige donc `ai(x) ≥ ⌈log₂ n⌉`. C'est une preuve d'une ligne, sans énumération ;
- **construction de doublement (supérieure, famille périodique)** : pour `x = (01)^k`, `k = 2^j`, `n = 2k` : produire `01` (1 jointure), puis `p ← p·p` en doublant (`j` jointures) atteint `x` en **1 + log₂ k = log₂ n** jointures. Avec la borne inférieure : **`ai((01)^k) = log₂ n` exactement** (n = 2^m). Ce résultat est **certifié**, pas mesuré.

**Proxys LZ (définitions scellées, implémentées dans le banc)** :
- `zlib_len(x)` — longueur en octets de `zlib.compress(x, 9)` (LZ77 + Huffman, le « ZIP/GZIP » du résumé) ;
- `lz76_count(x)` — factorisation Lempel–Ziv 1976 : la phrase courante = **le plus long préfixe du reste déjà reproduisible depuis l'historique, augmenté d'un caractère** (définition Kaspar–Schuster, celle des usages en complexité algorithmique) ; compte des phrases ;
- `lz78_count(x)` — nombre de phrases du dictionnaire Lempel–Ziv 1978.

**Entropie** : `h0(x)` = entropie de Shannon de la distribution des symboles (bits) ; `h_block(x, 2)` = entropie de la distribution des blocs de longueur 2 (rapportées toutes deux, la seconde sans bande scellée).

## 5. Prédictions scellées (aucune bande ne sera recalibrée après mesure)

### Portes instrumentales (dormantes par construction, mesurées quand même)

| # | Porte | Critère | Si déclenchée |
|---|---|---|---|
| **G1** | accord des deux solveurs | `exact_ai == brute_force_ai` sur **les 2 046 chaînes binaires** de `n ≤ 10` **et** 200 chaînes tirées (graine 0) à `n ∈ {11, 12}` | `NON_CONCLUSIF_INSTRUMENT`, aucune hypothèse évaluée |
| **G2** | bornes | sur chaque ligne mesurée : `⌈log₂ n⌉ ≤ ai(x) ≤ UB` de la construction exhibée | bug : `NON_CONCLUSIF_INSTRUMENT` |
| **G3** | portée du solveur | budget déclaré (≤ 2·10⁶ états par objet, `n ≤ 20`) ; au-delà → ligne marquée `reach_exceeded`, **exclue** des mesures exactes | pas une porte : une limite déclarée |

### H1 — l'index n'est pas déterminé par l'entropie de Shannon de l'objet

Deux classes à **comptes fixés** (donc `h0 = 1.000` bit exactement pour toute la classe) : `n = 12` (6 uns), `n = 16` (8 uns). Membres scellés : `(01)^k`, `0^m 1^m`, et 5 aléatoires appariés (graines 0/1/7/42/99, même compte de uns), plus toute chaîne de la classe atteinte par G1.

**Critère scellé** : dans **chaque** classe, `max ai − min ai ≥ 2` (attendu : `(01)^6` → 4, `0^6 1^6` → 7, écart 3 ; attentes non contraignantes — le verdict se calcule sur l'écart). Verdict : `CONFIRMÉE` si les deux classes passent, `FALSIFIÉE` si une classe a un écart ≤ 1.

### H2 — régimes de croissance et direction de la biconditionnelle

**Échelles scellées** (`n` en puissances de deux) :

| Famille | Définition | `n` |
|---|---|---|
| **P** (périodique) | `(01)^k`, `k = 2^j` | 64 → 16 384 (j = 5…14) |
| **F** (Fibonacci) | préfixes du mot de Fibonacci, longueurs `|f_j|` | ≥ 64 → ≈ 16 384 |
| **TM** (Thue–Morse) | `τ_j = μ^j(0)`, `μ(0)=01, μ(1)=10` | 64 → 16 384 (j = 6…14) |

**H2a — la direction de la biconditionnelle (l.420-427), test direct.** Sur l'échelle **P**, `ai` **croît strictement** (certifié : `log₂ n`, de 6 à 14) ; prédiction scellée : `zlib_len` **reste constant** (≤ 64 octets sur les 10 lignes — une répétition pure se compresse en O(1)). Critère : **≥ 8/10 lignes** à `ai` strictement croissante et `zlib_len` non croissante ⇒ l'implication « high assembly index ⇒ low LZ compressibility » est **violée** sur ces lignes. Verdict H2a : `CONFIRMÉE` (violation mesurée) si ≥ 8/10 ; `FALSIFIÉE` sinon (la compressibilité zlib suivrait l'index).

**H2b — règle de décision mécanique par pentes (issue ouverte, décidée par règle fixe).** Sur chaque famille, ajustement log-log de `ai`, `zlib_len`, `lz76_count`, `lz78_count` sur les 10 lignes ; **règle scellée** : la revendication « indistinguables quant à la quantification de complexité » est **réfutée pour cette famille** ssi `|pente(X) − pente(ai)| ≥ 0.30` pour un proxy `X`, **les deux ajustements à `R² ≥ 0.98`** ; si aucun proxy ne franchit ce seuil sur aucune famille, la revendication **tient sur ces familles** (et le banc le dira tel quel). Verdict H2b : la liste des familles réfutées, ou `AUCUNE`.

**Verdict H2** : `CONFIRMÉE` si H2a tenue **et** H2b réfute ≥ 1 famille ; `PARTIELLE` si H2a seule ; `FALSIFIÉE` si H2a manquée.

### H3 — la direction grossière tient-elle globalement ?

Batterie mixte (objets mesurables exactement, `n ≤ 20`) : `P` tronquée, `F`/`TM` tronquées, classes H1, `0^m 1^m`, `ABRACADABRA`, `BANANA`.
**Prédiction scellée** : `ρ_spearman(ai, zlib_len) ≥ 0` (la direction grossière « bas index ↔ plus compressible » tient sur la batterie mixte). Critère : `ρ ≥ 0` ⇒ `CONFIRMÉE` ; `ρ < 0` ⇒ `FALSIFIÉE` (l'anti-corrélation serait le résultat).

### Contrôles mesurés (sans bande scellée — mesurés quand même, rapportés)

1. **Null adversarial permuté** : sur les classes H1, 5 permutations (graines 0/1/7/42/99) de `(01)^k` ; `ai` mesuré des deux côtés. Rapporté tel quel — y compris le cas honnête où l'écart serait nul au reach (`n = 12/16`), auquel cas c'est **une limite du reach**, pas une falsification de H1.
2. **Le pont des exemples du papier** : `ABRACADABRA` et `BANANA` (les deux exemples cités par le contre-claim, l.408-413) — `ai`, `lz76_count`, `lz78_count`, `zlib_len` rapportés côte à côte, sans verdict.
3. **Corroboration locale optionnelle** : `z3` (4.16.0, présent sur cette machine) encodera le même optimum (variables par intervalle, contrainte de fermeture par décomposition, minimisation) sur un échantillon `n ∈ {12, …, 20}` — **hors porte CI**, hors verdict, rapporté comme troisième lecture indépendante si la mesure aboutit.

## 6. Verdicts bornés

| Verdict global | Condition |
|---|---|
| `CONFIRMÉ` | G1 et G2 vertes, H1 `CONFIRMÉE`, H2 `CONFIRMÉE`, H3 `CONFIRMÉE` |
| `PARTIEL` | G1/G2 vertes, au moins une hypothèse `CONFIRMÉE` et au moins une non |
| `FALSIFIÉ` | G1/G2 vertes, aucune hypothèse `CONFIRMÉE` |
| `NON_CONCLUSIF_INSTRUMENT` | G1 ou G2 déclenchée |

Le verdict global est une **conjonction déclarée**, jamais une moyenne : le commentaire de livraison nomme chaque hypothèse et sa mesure. Aucun des verdicts ne porte sur : l'équation d'assemblage, le nombre de copies, la détection de vie, l'équivalence statistique/ensembliste du contre-claim (hors échelle), ni sur « l'AT comme théorie ».

## 7. Greffe sur la veine #8182 (lecture, jamais un claim)

Les cases 16-19 mesurent des dissociations de contenu et de procédure. La case 20 mesure une **dissociation entre un formalisme et ce que ses critiques lui attribuent** : les deux camps s'accordent que l'index est une taille minimale de grammaire, et le banc porte la question sur l'endroit où ils cessent de s'accorder — ce que *produisent* les compresseurs réels comparé à ce que *vaut* l'optimum. Elle fournit à la veine son premier témoin où **un théorème d'équivalence formelle est mis en regard d'un écart quantitatif mesuré** : trois grandeurs que la prose du contre-claim dit indistinguables, mesurées sur la même échelle, avec une règle de décision fixée d'avance.

Position de registre (décision ai-01 du 05/10, tenue) : l'AT est traitée ici comme **mesure de complexité en émergence/MDL** — jamais comme théorie de la conscience, jamais comme explication de la sélection. La tranche est un banc de complexité, pas une thèse sur l'esprit.

## 8. Honnêteté grade C (limites)

1. **Ce n'est pas un test de la théorie.** Aucun objet biologique, aucune molécule, aucun nombre de copies : des chaînes binaires. Le théorème ensembliste du contre-claim (AT ↔ entropie de Shannon sur des méthodes statistiques) est **hors échelle** — H1 mesure des objets individuels, et le verdict le dit.
2. **Le certificat est partiel par famille.** `ai((01)^k) = log₂ n` est **prouvé** (doublement + borne inférieure). Pour F et TM, seules les bornes `⌈log₂ n⌉ ≤ ai ≤ c·log₂ n` (construction par morphisme) sont certifiées — l'exactitude au-delà du reach du solveur n'est jamais revendiquée.
3. **Les proxys LZ sont des choix.** Trois définitions implémentées et scellées (`zlib` niveau 9 ; LZ76 Kaspar–Schuster ; LZ78). D'autres lectures du « LZ » existent (LZW, LZSS, LZMA, le LZAS du contre-claim) : le banc ne prouve rien sur celles qu'il n'implémente pas, et le dit.
4. **Le reach du solveur est une frontière honnête.** Les classes à comptes fixés vivent à `n = 12/16` ; les échelles vivent à `n ≥ 64` et ne sont accessibles qu'aux familles à construction exhibée. Le trou entre les deux (exact et certifié, mais pas les deux ensemble) est nommé ligne à ligne dans les résultats.
5. **La règle de décision H2b est un choix de seuil (0.30, `R² ≥ 0.98`).** Elle est fixée avant mesure ; si les ajustements sont instables, le verdict est `PARTIELLE` ou `FALSIFIÉE`, jamais un verdict adouci après coup.

## 9. Ce qui suit

1. **Ce document, commité, est le scellé.** Toute modification ultérieure des bandes se fait par amendement **pré-exécution** horodaté dans ce fichier, jamais silencieusement.
2. Le banc `MyIA.AI.Notebooks/IIT/ICT-Series/ict/assembly_index.py` + tests `ict/tests/test_assembly_index.py` + mesures `ict/results/assembly_index_results.json` vivront dans la même PR, commits ordonnés (la relation de parenté des commits porte l'antériorité — ce document est le **parent** du commit du banc).
3. Verdict rapporté sur [#8182](https://github.com/jsboige/CoursIA/issues/8182) avec les mesures brutes par ligne ; ligne de série dans `MyIA.AI.Notebooks/IIT/ICT-Series/README.md` et `docs/README.md`.
4. Réserve de suite nommée : un `lz_as` (le parseur « LZAS » du contre-claim) et un `lzma` compléteraient la batterie de proxys ; l'extension de la classe P aux longueurs non-puissances-de-deux testerait la constante exacte `1 + ⌈log₂ k⌉` (au-delà du certificat de puissance de deux).
5. Homologation : les sources sont archivées au gisement (`Consciousness`, deux fichiers, sha256 ci-dessus) — un relecteur peut rouvrir les deux PDF sans téléchargement.