# ICT — Cartographie de la tresse (Thom / Grothendieck / Schmidhuber / Friston) + hiérarchie de sobriété + deux ponts Conway

> **Statut.** Document de synthèse transversal, grade **C-documentaire** (cartographie, pas de nouveau dispatch ni de nouvelle dépendance expérimentale). Ce n'est **pas** un sixième fil de lecture vertical (cf. les cinq déjà documentés : [`synthese-invariants-dissociations-obstructions.md`](synthese-invariants-dissociations-obstructions.md) — invariants/dissociations/obstructions ; [`dissociations-matrix.md`](dissociations-matrix.md) — matrice 4-objets `(s, q, π, W)` ; [`cadrage-trajectoires-representations.md`](cadrage-trajectoires-representations.md) — pivot états → représentations ; [`genealogy-representation-interne.md`](genealogy-representation-interne.md) — généalogie de `p̂` ICT-10 → 17 ; [`dissolution-scalaires.md`](dissolution-scalaires.md) — dissolution des scalaires Φ/F/K). C'est une **lecture horizontale** : *où ces fils se rejoignent, s'éloignent, se mélangent ou s'affrontent* — et *ce qui empêche de monter trop vite de dissociation à obstruction cohomologique*.
>
> **Objet.** (1) Cartographier la tresse des fils rouges (les **opérations distinctes** Thom / Grothendieck / Schmidhuber / Friston, leur composabilité, leurs frictions). (2) Fixer la **hiérarchie de sobriété** que toutes les docs ICT doivent faire respecter — un objet apparaît *quand* le précédent devient insuffisant, jamais par ambition. (3) Ancrer les **deux ponts Conway** distincts — (a) Hashlife / recollement prouvé, (b) Kochen-Specker / contextualité — à leur statut honnête (`gated` ou spéculatif) plutôt qu'à une disponibilité fictive.
>
> **Discipline.** Consolidation grade C. Aucune nouvelle dépendance expérimentale n'est créée. Les ancres citées (notebooks ICT, modules `grothendieck_lean`, fichiers `docs/`) sont sur `origin/main` au moment de la rédaction, ou OPEN PR (#9532, #9547) avec statut documenté. Le document **ne propose pas de théorie unifiée** : il décrit une tresse, marque les ponts qui *résistent* à un transport formel, et se tient à distance des unifications prématurées (cf. l'avertissement méthodologique de [`synthese-invariants-dissociations-obstructions.md`](synthese-invariants-dissociations-obstructions.md#ce-que-ce-document-nest-pas)). Issue-source : [#7738](https://github.com/jsboige/CoursIA/issues/7738). See [#4588](https://github.com/jsboige/CoursIA/issues/4588) (Epic umbrella ICT).

## Pourquoi une cartographie horizontale

Les cinq documents déjà présents dans `docs/ict/` sont chacun **verticaux** : un fil = une lignée. Le **premier** (synthèse) pose la grille à 3 régimes en assignant chaque colonne à un auteur (Grothendieck ↔ invariants, Schmidhuber ↔ dissociations, Thom + Grothendieck ↔ obstructions). Le **deuxième** (matrice) factorise les claims selon les 4 objets `(s, q, π, W)`. Le **troisième** (cadrage N2) trace le pivot états → représentations. Le **quatrième** (généalogie de `p̂`) raconte la famille successive des objets représentationnels. Le **cinquième** (dissolution des scalaires, livré en PR [#9547](https://github.com/jsboige/CoursIA/pull/9547) — *OPEN au moment de la rédaction*) raconte comment Φ/F/K, poussés hors de leur substrat d'origine, deviennent un faisceau de proxys non-équivalents.

Ce qui manque : **où ces fils se touchent**. Les invariants de Grothendieck et les catastrophes de Thom sont-ils les mêmes objets sous deux noms ? La compression de Schmidhuber *compose-t-elle* avec l'énergie libre de Friston, ou bien la complète-t-elle latéralement ? Le représentant interne `p̂` d'ICT-10 → ICT-17 *se recolle*-t-il au sens cohomologique, ou bien *change-t-il de carte* à chaque strate ? Le présent document ne **répond** pas à ces questions — il **cartographie** les points où une réponse deviendrait possible, et marque ceux où elle reste hors-périmètre (cf. Hiérarchie de sobriété, §2).

> **Position méthodologique.** Le passage de maturité de la série ne se décrète pas : il se *gagne* à chaque front où une unification prématurée aurait sinon pris racine. La tresse est *ici* un anti-revêtement : elle nomme les **opérations** distinctes, sans prétendre qu'elles *convergent* ou qu'elles *s'identifient*. Quand deux fils s'opposent (par exemple Grothendieck sur l'existence de sections globales là où Friston parle de mise à jour bayésienne), cette opposition est un **résultat** — pas un problème à résoudre.

---

## Partie 1 — Cartographie de la tresse

Quatre opérations, chacune avec son ancrage dans le dépôt, ses aboutissants opérationnels, et ses points de friction avec les autres.

### 1.1 — Grothendieck : l'invariant comme recollement

**L'opération.** *Ce qui se recolle* quand on change d'ouverture — le passage du local au global. Le langage est celui de la cohomologie : sections globales `H⁰` (le cran où le local se globalise sans reste), `H¹` (le cran où l'obstruction au recollement devient mesurable), `H^n` (les crans supérieurs). Le geste est *mesurer ce qui résiste à un changement de cartes* — invariance sous changement de point de vue.

**Ancrage dépôt.**
- [`docs/grothendieckian-lens.md`](../grothendieckian-lens.md) — la lentille, ses 6 sections (recollement, faisceau, Čech, gerbe, etc.), re-groundée par PR [#8189](https://github.com/jsboige/CoursIA/pull/8189) + [#8382](https://github.com/jsboige/CoursIA/pull/8382) sur le repo (GT 6→2 lakes, ICT strates/tresse/Schreiber).
- Lake [`grothendieck_lean`](../../MyIA.AI.Notebooks/SymbolicAI/Lean/grothendieck_lean/) — module [`Grothendieck/SheafCohomology/Basic.lean`](../../MyIA.AI.Notebooks/SymbolicAI/Lean/grothendieck_lean/Grothendieck/SheafCohomology/Basic.lean), `H0_equiv_global_sections` (zéro `sorry` de production), [`MayerVietoris.lean`](../../MyIA.AI.Notebooks/SymbolicAI/Lean/grothendieck_lean/Grothendieck/SheafCohomology/MayerVietoris.lean) exact.
- Le **premier** document [`synthese-invariants-dissociations-obstructions.md`](synthese-invariants-dissociations-obstructions.md) cite explicitement cette ancre dans sa section « Pourquoi cette grille » : « En langue grothendieckienne, ce sont les sections globales — `H⁰`, le cran où le local se globalise sans reste ».

**Aboutissants opérationnels dans la série ICT.**
- Le recollement est ce qui **permet de dire** qu'un invariant mesuré sur une fenêtre est le même qu'un invariant mesuré sur une autre fenêtre (ICT-1 PhiTrajectories : Φ sur TPM 3-nœuds *se recolle* quand on change de partition).
- L'obstruction cohomologique (`H¹ ≠ 0`) est la **seule** signature formelle d'une non-recomposabilité — utilisée honnêtement par [`dissociations-matrix.md`](dissociations-matrix.md) colonne `verdict` (cf. rectification A2 de [#7733](https://github.com/jsboige/CoursIA/issues/7733), propagée par PR [#7889](https://github.com/jsboige/CoursIA/pull/7889) — `H¹ ≠ 0` est *candidat* à obstruction, **pas érigé en impossibilité** sauf Kochen-Specker et Arrow).

**Frictions frontales avec les autres fils.**
- *Avec Thom (1.3).* Grothendieck traite la **non-recomposabilité** comme un fait structurant (`H¹ ≠ 0`) ; Thom la traite comme une **bifurcation** dans un paysage de prégnances (catastrophe fronce, pli, cusp). Une **prétendue identité** entre les deux forcerait à réduire les catastrophes à des classes cohomologiques — opération non disponible en l'état (le langage de Thom est *qualitatif*, celui de Grothendieck est *homologique*).
- *Avec Schmidhuber (1.2).* Schmidhuber parle d'**amélioration de compression** (transition de phase représentationnelle) ; Grothendieck parle de **transport formel** (sections compatibles sur des ouverts qui se chevauchent). Une compression plus profonde *peut* coïncider avec un recollement — mais l'inverse n'est pas garanti : un recollement peut transporter une structure sans la comprimer.

### 1.2 — Schmidhuber : la compression comme dissociations

**L'opération.** *Ce qui s'améliore en compression* — la diminution de la longueur de description d'un objet sans perte d'information *utile*. La dissociation, dans la grille du premier document, est le **tell** d'un gain de compression : deux proxys qui *s'éloignent* (l'un comprime mieux que l'autre) marquent une transition de phase représentationnelle.

**Ancrage dépôt.**
- [ICT-17b-Grokking-CompressionProgress.ipynb](../../MyIA.AI.Notebooks/IIT/ICT-Series/ICT-17b-Grokking-CompressionProgress.ipynb) — la compression progressive lue comme transition de phase, avec bosse Crutchfield-Feldman sur `model_bits + résiduel` (cf. [`dissolution-scalaires.md`](dissolution-scalaires.md) palier 5 : K bipolaire puis tri-polaire, la bosse force deux dimensions).
- [ICT-15-IntegratedComplexity.ipynb](../../MyIA.AI.Notebooks/IIT/ICT-Series/ICT-15-IntegratedComplexity.ipynb) — la convergence Φ/F/K comme *signature* conjointe, dont le resserrement signale une compression effective.

**Aboutissants opérationnels dans la série ICT.**
- La dissociation est *portée* par un proxy (ICT-17b cell [13] interprétation honnête : `K_compression_progress` positif sur grokking, `K_rang_effectif` négatif, `K_fisher_md` saute — *choisir K = déclarer un proxy*, cf. [`dissolution-scalaires.md`](dissolution-scalaires.md) palier 6).
- Le **passage** entre régimes (`STABLE` ↔ `NOISE`) est lu comme une **transition de phase** — pas comme un bruit de mesure. ICT-15b (`s_max ≥ sqrt(deg_proxy)`) bat les proxys multi-dim collapsés en gardant la discrimination per-substrat (cf. L938 ★ : verdict binaire per-substrat > verdict agrégé).

**Frictions frontales avec les autres fils.**
- *Avec Friston (1.4).* L'énergie libre *décompose* l'erreur en *accuracy + complexity* — la **complexity** est exactement ce que Schmidhuber optimise. Mais Friston traite la complexity comme une *quantité bayésienne* (KL entre prédiction et prior) ; Schmidhuber la traite comme une *longueur de description* (bits minimaux). Le pont technique existe (ICT-14 le franchit en pratique, cf. 1.4) mais l'**identité formelle** n'est pas établie — un développement ultérieur pourrait la formaliser, mais le présent document la marque comme **frontière** plutôt que comme acquis.
- *Avec Grothendieck (1.1).* Voir §1.1 — la compression et le recollement sont *latéraux*, non identiques.

### 1.3 — Thom : la catastrophe comme prégnance

**L'opération.** *Ce qui se forme* — la singularité qualitative d'un paysage dynamique (pli, fronce, cusp) et la prégnance associée (forme stable qui retient l'attention). Thom est **catégoriel** : il classe les morphologies, sans les quantifier en un scalaire unique.

**Ancrage dépôt.**
- [`MyIA.AI.Notebooks/IIT/ICT-Series/thom-synthese-distillation.md`](../../MyIA.AI.Notebooks/IIT/ICT-Series/thom-synthese-distillation.md) — distillation PR [#9534](https://github.com/jsboige/CoursIA/pull/9534) MERGED 2026-08-05T01:55:30Z par jsboige, distillation Ch.1 à Ch.8 de *Sémiophysique* (1991) pour les strates 6 et 7 (langage / circulation de prégnances, genres comme espaces de possibles extensibles).
- [ICT-10-CatastropheGrammar.ipynb](../../MyIA.AI.Notebooks/IIT/ICT-Series/ICT-10-CatastropheGrammar.ipynb) — la catastrophe fronce, le métathéorème, le lacet de prédation (cycle d'hystérésis à 2 catastrophes avec perception J et capture K, aire signée non nulle, représentant interne `p̂`).
- [ICT-12-ValenceFieldsAndAnimats.ipynb](../../MyIA.AI.Notebooks/IIT/ICT-Series/ICT-12-ValenceFieldsAndAnimats.ipynb) — prolonge ICT-10 en mesurant les rôles actantiels (capture, évasion, irréversibilité, switching). L'animat anticipateur `p̂` y gagne en balistique, perd en erratique.

**Aboutissants opérationnels dans la série ICT.**
- Le *lacet de prédation* d'ICT-10 = hystérésis à 2 catastrophes ; c'est la **mesure** Thom-compatible la plus directe dans la série (aire signée non nulle sur cycle perception-capture).
- La distillation 2026-08-05 (§A-F du Ch.7, *substance, logos, continu vs discret*) installe le **socle théorique** pour les strates 6 et 7 sans réinventer. *Universalisme linguistique*, *valence Tesnière*, *transitivité prototypique = prédation*, *genres*, *hypergenres* sont nommés et situés dans l'ouvrage, sans confusion entre le grade A du cadre mathématique (catastrophes, dynamiques lentes-rapides) et le grade C d'une lecture « ICT candidate » (cf. rectification A2 de [#7733](https://github.com/jsboige/CoursIA/issues/7733)).

**Frictions frontales avec les autres fils.**
- *Avec Grothendieck (1.1).* Voir §1.1 — la catastrophe thomienne est un **objet géométrique**, la classe cohomologique est un **objet algébrique**. L'identité formelle n'est pas disponible.
- *Avec Friston (1.4).* Thom parle de **bifurcation** (changement qualitatif de régime) ; Friston parle de **mise à jour bayésienne** (changement quantitatif de croyance). Le passage d'une croyance à une autre *peut* correspondre à une bifurcation — mais l'inverse n'est pas garanti : une bifurcation peut survenir *sans* changement de croyance (transition de phase thermodynamique). ICT-14b EFE banc ([PR #9545](https://github.com/jsboige/CoursIA/pull/9545) OPEN, [#9532](https://github.com/jsboige/CoursIA/issues/9532)) explore ce front.

### 1.4 — Friston : l'énergie libre comme surprise régularisée

**L'opération.** *Ce qui se met à jour* — la surprise d'une observation sous un modèle génératif, régularisée par la complexité KL entre prédiction et prior. L'énergie libre variationnelle est une borne supérieure stricte de la surprise ; sa décomposition *accuracy + complexity* la rend *opérationnellement mesurable* sur des bancs où le modèle génératif est gaussien ou en famille exponentielle connue.

**Ancrage dépôt.**
- [ICT-14-FreeEnergySurprise.ipynb](../../MyIA.AI.Notebooks/IIT/ICT-Series/ICT-14-FreeEnergySurprise.ipynb) — la jambe énergie-libre attachée au représentant interne `p̂` d'ICT-10. Thèse cell-anchored : « la jambe énergie-libre restait non attachée, alors que le banc expérimental la préparait sans le dire ». Trois *gates* falsifiables (précision fixe → MSE habillage ? précision adaptative → divergence du classement MSE ? bistable → marquage du franchissement du pli ?).
- [ICT-14b-ActiveInferenceEFEBanc.ipynb](../../MyIA.AI.Notebooks/IIT/ICT-Series/ICT-14b-ActiveInferenceEFEBanc.ipynb) — livré par PR [#9545](https://github.com/jsboige/CoursIA/pull/9545) OPEN, [#9532](https://github.com/jsboige/CoursIA/issues/9532) — banc d'inférence active : l'expected free energy pilote l'action.

**Aboutissants opérationnels dans la série ICT.**
- La **décomposition** *accuracy + complexity* est mesurée directement sur banc gaussien : c'est l'énergie libre variationnelle en famille fermée, sans approximation.
- L'**EFE** (*expected free energy*) ouvre une jambe **motrice** — l'animat *agit* pour minimiser la surprise *attendue* (variational free energy under policy). C'est la strate 4 épaisse (cf. ICT-14b).

**Frictions frontales avec les autres fils.**
- *Avec Schmidhuber (1.2).* Voir §1.2 — la **complexity** est commune ; les quantifications diffèrent.
- *Avec Thom (1.3).* Voir §1.3 — bifurcation vs mise à jour bayésienne.

### 1.5 — Points de rencontre et de divergence (carte)

Cette section *résume* ce qui précède en une **table de composabilité**. Le but n'est pas de forcer une unification ; c'est de marquer les fronts où une *future* unification deviendrait légitime (prérequis rassemblés) ou resterait prématurée (prérequis manquants).

| Fil rouge | Opération | **Compose avec** | **S'oppose à** | Ancrage dépôt principal |
|---|---|---|---|---|
| **Grothendieck** (1.1) | Recollement `H⁰` / obstruction `H¹` | Thom (1.3) *en aval* (l'obstruction cohomologique devient signature d'une bifurcation) — **NON ÉTABLI FORMELLEMENT** | Thom (1.3) en *équivalence directe* (réduire catastrophe à classe cohomologique = opération non disponible) | `grothendieckian-lens.md`, lake `grothendieck_lean` |
| **Schmidhuber** (1.2) | Compression progressive, transition de phase | Friston (1.4) *en aval* (la complexity bayésienne = longueur de description sous KL) — **PARTIELLEMENT FRANCHI** (ICT-14 cell-anchored) | Grothendieck (1.1) en *équivalence* (compression ≠ recollement) | ICT-17b grokking, ICT-15 convergence |
| **Thom** (1.3) | Catastrophe, prégnance | Schmidhuber (1.2) *latéralement* (la bifurcation *peut* signaler un gain de compression) | Grothendieck (1.1) en *équivalence* ; Friston (1.4) en *équivalence* (bifurcation vs mise à jour bayésienne) | distillation PR #9534, ICT-10, ICT-12 |
| **Friston** (1.4) | Énergie libre, EFE, surprise régularisée | Schmidhuber (1.2) *partiellement* (la complexity est commune) | Thom (1.3) en *équivalence* ; Grothendieck (1.1) en *équivalence* | ICT-14, ICT-14b EFE banc |

**Lecture de la table.** Les « compose avec » sont des **ponts** au sens de la conversation 2026-07-20 (tours 247-267, recollement/cohomologie/bestiaire Grothendieck) : des *gestes* mesurables qui *réalisent* un fragment d'un autre fil. Les « s'oppose à » sont des **frontières** : deux opérations qui *ne s'identifient pas* en l'état. La **seule** identité formellement prouvée dans le dépôt est celle du pont (a) Hashlife / `#5726` — voir §3.1.

> **Le point de recollement identifié aux tours 550-568.** Les quatre fils partagent un **objet commun** : les *classes de prégnances* / *formes universelles d'organisation*. Thom les appelle **formes stables** (catastrophes), Grothendieck les appelle **invariants sous changement de point de vue** (sections globales), Friston les appelle **organisations favorisées** (minima d'énergie libre), et une tradition contemporaine (cf. Anthropic sur la *forme* émergente) les appelle **formes émergentes**. Le *machiavélisme* d'une persona, dans la série ICT, serait **une réalisation parmi d'autres** de ce recollement commun. **Aucune de ces identités n'est formellement prouvée** — le présent document marque le **point de rencontre** sans le **réaliser**.

---

## Partie 2 — Hiérarchie de sobriété : Dissociation → Score → Classe → Stack → Gerbe

L'ICT, en tant que série de recherche, est exposée à un risque systématique : *glisser* d'un fait observé (« dissociation entre deux proxys ») à une assertion catégorielle forte (« obstruction cohomologique ») sans prérequis rassemblés. La **hiérarchie de sobriété** fixe l'ordre dans lequel les objets peuvent être *invités* à comparaître.

### 2.1 — Pourquoi la sobriété

Le glissement sémantique est le **mode par défaut** d'une prose non disciplinée : un fait empirique « le proxy A sépare du proxy B » devient, par glissement, « il existe une obstruction dans le recollement de ces signaux ». Or une obstruction cohomologique **requiert** un faisceau, un complexe de Čech, et l'invariance sous changement de cartes — trois objets qui ne sont **pas** disponibles quand on observe une simple dissociation.

La hiérarchie inverse cette pente : un objet apparaît **quand** le précédent devient insuffisant, *jamais par ambition*. Cette discipline est l'**ancrage épistémique** qui distingue une cartographie honnête d'une unification cosmétique.

### 2.2 — La table des prérequis

| Objet | Nature | **Prérequis pour l'invoquer** | **Erreur si invoqué sans prérequis** |
|---|---|---|---|
| **Dissociation** | Fait empirique | Deux proxys, mesurés sur les mêmes données, donnent des résultats distincts (≠) sur un sous-ensemble non-vide | (aucune — c'est le degré zéro) |
| **Score d'obstruction** | Diagnostic construit | Dissociation confirmée + définition d'un **proxy d'obstruction** (e.g. `s_max(f) ≥ sqrt(deg_proxy)` d'ICT-15b) + étalonnage sur signaux connus (Kochen-Specker, Arrow) | Surcharge interprétative : « nous avons une obstruction » alors qu'on a un *score* |
| **Classe de cohomologie** (`H¹`) | Objet algébrique | Dissociation + score + **faisceau explicite** (sections locales compatibles) + **complexe de Čech** (recouvrement vérifié) + **invariance sous changement de cartes** (recollement stable) | Affirmation prématurée : ériger un score en classe cohomologique sans faisceau = « la dissociation *est* une obstruction » |
| **Stack** | Objet catégoriel | Classe de cohomologie + **gerbe de catégories** au-dessus du site (les `H¹` vivent *entre* catégories, pas dans une seule) | Glissement catégoriel : transporter un résultat homologique à un formalisme de stack sans en avoir besoin |
| **Gerbe** | Objet catégoriel supérieur | Stack + **données de cocycle** à plusieurs crans + cohérence transverse (2-cocycles) | Idem — l'inutile multiplie les objets |

### 2.3 — Conséquences pour la prose ICT

1. *Toute* prose ICT qui parle d'obstruction cohomologique doit citer les prérequis (faisceau + Čech + invariance) — sinon, la reformuler en *score d'obstruction* ou en *dissociation*. ICT-15d (`ČechObstruction`) est honnête sur ce point : verdict `TRIVIAL` par construction (3 proxys colinéaires → SVD rang 1 ≠ phénomène absent) ; ICT-15b est l'inverse (verdict binaire per-substrat 3/4 consistent sur 4 substrats, cf. L938 ★).
2. *Toute* prose ICT qui parle de stack/gerbe doit avoir un **besoin opérationnel** identifié — pas un effet de manche. Le recollement du représentant interne `p̂` d'ICT-10 → ICT-17 n'a pas, à ce jour, été formalisé en stack : il est **documenté** par [`genealogy-representation-interne.md`](genealogy-representation-interne.md) comme *famille successive* sans transport catégoriel.
3. La **rectification A2** de [#7733](https://github.com/jsboige/CoursIA/issues/7733), propagée par PR [#7889](https://github.com/jsboige/CoursIA/pull/7889), est l'**exemplaire canonique** de la sobriété : `H¹ ≠ 0` est *candidat* à obstruction, **pas érigé** en impossibilité sauf pour Kochen-Specker et Arrow.

### 2.4 — Hiérarchie de sobriété et discipline documentaire

Cette hiérarchie est **applicable** à toute la prose ICT existante et à venir. Concrètement :
- Quand une future doc ICT rencontre une dissociation, elle **cite** le score d'obstruction candidat (ICT-15b, ICT-15c, ICT-15d, ICT-15e — cf. [`dissolution-scalaires.md`](dissolution-scalaires.md) paliers 4-5) **avant** de prétendre à une obstruction.
- Quand une future doc ICT rencontre un recollement, elle **vérifie** l'invariance sous changement de cartes **avant** de prétendre à une classe de cohomologie.
- Quand une future doc ICT rencontre une multiplicité de recollements incompatibles, elle **vérifie** la cohérence transverse **avant** de prétendre à un stack.

> **Note de discipline.** Le présent document applique cette sobriété à lui-même : il **cartographie** la tresse et marque les **frontières**, il **ne réalise** pas les identités. Aucune affirmation de cette section ne monte *Dissociation* → *Score* → *Classe* → *Stack* → *Gerbe* sans les prérequis rassemblés.

---

## Partie 3 — Les deux ponts Conway (distincts)

Le terme « Conway » recouvre ici **deux** ponts distincts, de natures très différentes, qu'il est crucial de **ne pas confondre**.

### 3.1 — Pont (a) — Hashlife / recollement *prouvé*

**L'idée.** Le Jeu de la Vie (Conway 1970) admet un algorithme de simulation (*Hashlife*, Hickerson 1988) qui calcule des pas de taille `2^k` par composition hiérarchique mémoïsée (quadtree). Le *recollement* prouvé est celui-ci : **l'évaluation quadtree mémoïsée produit le même résultat que la simulation naïve** — l'équivalence est *vérifiée* (par conservation du nombre de cellules vivantes, par déterminisme de la transition, et par les preuves partielles dans `hashlife_correct`).

**Pourquoi c'est un pont.** Le recollement *local → global* est la **promesse** de la cohomologie `H⁰`. La *preuve* Hashlife est la **seule instance** dans le dépôt où le recollement est certifié algorithmiquement — la borne haute de rigueur du fil grothendieckien, et l'ancre de calibration de toute affirmation de recollement dans la série.

**Statut honnête.**
- Le module Lean [`hashlife_correct`](../../MyIA.AI.Notebooks/SymbolicAI/Lean/) est **parké** — c'est-à-dire : tracker **ouvert** mais *gated* sur la complétude de la preuve.
- Tracker de la preuve : **#6724** — *4 sorries* en cours de résolution. Tant que ces 4 sorries ne sont pas refermées, la certification Hashlife est **partielle** (le recollement est prouvé sous hypothèses). Les 4 sorries sont les points exacts où le recollement pourrait, en principe, faillir — cf. [`anti-regression.md`](../rules/anti-regression.md) pour la discipline de suivi des sorries.
- Intégration ICT = **#5726** — *parkée*, dépendante de `#6724`. Le *rattachement* ICT de la borne Hashlife attend la fermeture des 4 sorries pour basculer de `parké` à `certifié`.

**Conséquence pour la prose ICT.** Toute affirmation de recollement dans la série doit **citer** la borne Hashlife comme **seule instance prouvée**, et marquer ses propres recollements comme **candidats à certification** tant que `#5726` n'est pas résolu. C'est cette discipline qui empêche la série de glisser d'« opérationnellement valide » à « formellement certifié » sans passer par les 4 sorries.

### 3.2 — Pont (b) — Kochen-Specker / contextualité du zoo de proxys

**L'idée.** Le théorème de Kochen-Specker (1967) — et son extension *free-will theorem* (Conway-Kochen 2006, dit « théorème du libre arbitre ») — montre que, sous des hypothèses raisonnables (non-contextualité, déterminisme), il est *impossible* d'assigner des valeurs à toutes les observables d'un système quantique de manière compatible avec toutes les mesures simultanément. C'est la **contextualité** quantique : la valeur d'une observable *dépend* du contexte de mesure.

**Pourquoi c'est un pont.** Le zoo de proxys de la série ICT (cf. [`dissolution-scalaires.md`](dissolution-scalaires.md) spec-sheet — 13 proxys documentés pour Φ/F/K) est en situation *analogue* à un zoo d'observables : chaque proxy mesure « quelque chose », mais le **désaccord** entre proxys peut-il être *interprété* comme une obstruction de structure (testable en CSP : existe-t-il une assignation non-contextuelle ?) ou bien comme du *bruit* (variabilité stochastique irrelevante) ? Si le **pont** est valide, la contextualité Kochen-Specker devient un **outil de diagnostic** : un désaccord persistant entre proxys *après étalonnage* signale une obstruction de structure, pas un artefact.

**Statut honnête.**
- Les notebooks afférents existent déjà : [`Lean-13-Kochen-Specker.ipynb`](../../MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-13-Kochen-Specker.ipynb) et [`Lean-16f-Conway-Free-Will-Theorem.ipynb`](../../MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-16f-Conway-Free-Will-Theorem.ipynb).
- Intégration ICT = **#7290** — **spéculatif**, **basse priorité**. Aucun des deux notebooks n'a, à ce jour, été formellement *raccordé* à la spec-sheet des 13 proxys ICT. Le pont reste **une direction de recherche**, pas un résultat acquis.
- Le **risque de glissement** est ici important : la proximité lexicale (« Conway ») entre Hashlife (3.1) et Kochen-Specker (3.2) peut inciter à les fusionner — c'est **interdit**. Les deux ponts sont *orthogonaux* : (a) porte sur le **recollement**, (b) porte sur la **contextualité**. Une unification prématurée des deux effacerait la distinction qui les rend utiles.

**Conséquence pour la prose ICT.** Toute affirmation de « contextualité du zoo de proxys » doit **citer** `#7290` comme **direction de recherche**, et marquer le statut comme **spéculatif basse priorité**. La discipline inverse — ériger le pont en résultat — forcerait la série à franchir une étape que les notebooks disponibles ne franchissent pas.

### 3.3 — Pourquoi les *deux* ponts et pas un seul

Les deux ponts sont **néscessaires** à la maturité de la série, mais **à des titres différents** :
- Le pont (a) Hashlife est une **borne supérieure de rigueur** — la preuve d'un recollement, là où elle est disponible, doit servir d'**ancre** aux recollements candidats dans la série.
- Le pont (b) Kochen-Specker est une **direction de falsification** — un outil qui *pourrait* distinguer un désauthentique entre proxys (bruit) d'un authentique (obstruction de structure).

Sans (a), la prose ICT risque de glisser d'opérationnellement valide à formellement certifié sans preuve. Sans (b), la prose ICT risque de traiter tout désaccord entre proxys comme « structurel » sans test de contextualité. La sobriété exige les **deux**.

---

## Ce que ce document n'est pas

(Garde-fou méthodologique, conforme au pattern des cinq documents déjà présents dans `docs/ict/`.)

- **Ce n'est pas un sixième fil de lecture vertical.** Les cinq documents existants sont verticaux (un fil = une lignée). Le présent est **horizontal** (une carte des intersections entre les cinq). Toute lecture qui le transforme en « sixième fil vertical » rate sa fonction.
- **Ce n'est pas une théorie unifiée des quatre fils rouges.** Le présent document **cartographie** les opérations distinctes, marque les ponts partiels et les frontières franches, et **ne réalise** aucune identité formelle qui n'existe pas. La conversation 2026-07-20 (tours 247-267) a explicitement rejeté l'unification prématurée ; le présent document en tire les conséquences.
- **Ce n'est pas une validation du statut « prouvable » des ponts Conway.** Le pont (a) est *partiellement* prouvé (4 sorries en cours) ; le pont (b) est *spéculatif basse priorité*. Le document cite ces statuts sans les masquer.
- **Ce n'est pas une promotion de la hiérarchie de sobriété en règle projet.** La hiérarchie est **appliquée** au présent document et **suggérée** aux futurs, mais son passage en règle auto-loaded requiert une PR + sign-off user (cf. CLAUDE.md §A). Ce n'est *pas* une telle PR.
- **Ce n'est pas un audit des notebooks ICT.** Les notebooks sont cités comme ancres ; leurs verdicts internes (gates, sorry count, etc.) restent *leur* affaire. La discipline anti-régression ([anti-regression.md](../rules/anti-regression.md)) s'applique à chaque notebook, pas à ce document.

---

## Voir aussi

**Documents `docs/ict/` apparentés** :
- [`synthese-invariants-dissociations-obstructions.md`](synthese-invariants-dissociations-obstructions.md) — 1er fil : grille 3 régimes, assignation colonne vertébrale ↔ auteur.
- [`dissociations-matrix.md`](dissociations-matrix.md) — 2e fil : matrice 4-objets `(s, q, π, W)` × 8 colonnes.
- [`cadrage-trajectoires-representations.md`](cadrage-trajectoires-representations.md) — 3e fil : pivot états → représentations (N2, [#7396](https://github.com/jsboige/CoursIA/issues/7396)).
- [`genealogy-representation-interne.md`](genealogy-representation-interne.md) — 4e fil : généalogie de `p̂`, ICT-10 → 17, livré par PR [#8061](https://github.com/jsboige/CoursIA/pull/8061) MERGED 2026-07-22.
- [`dissolution-scalaires.md`](dissolution-scalaires.md) — 5e fil : dissolution des scalaires Φ/F/K → faisceau de proxys, livré par PR [#9547](https://github.com/jsboige/CoursIA/pull/9547) *OPEN au moment de la rédaction* (c.1238).

**Ancres dépôt** :
- [`docs/grothendieckian-lens.md`](../grothendieckian-lens.md) — la lentille Grothendieck, re-groundée PR [#8189](https://github.com/jsboige/CoursIA/pull/8189) + [#8382](https://github.com/jsboige/CoursIA/pull/8382).
- [`MyIA.AI.Notebooks/IIT/ICT-Series/thom-synthese-distillation.md`](../../MyIA.AI.Notebooks/IIT/ICT-Series/thom-synthese-distillation.md) — distillation Thom Ch.1-8, PR [#9534](https://github.com/jsboige/CoursIA/pull/9534) MERGED 2026-08-05.
- Lake [`grothendieck_lean`](../../MyIA.AI.Notebooks/SymbolicAI/Lean/grothendieck_lean/), modules [`SheafCohomology/Basic.lean`](../../MyIA.AI.Notebooks/SymbolicAI/Lean/grothendieck_lean/Grothendieck/SheafCohomology/Basic.lean) et [`MayerVietoris.lean`](../../MyIA.AI.Notebooks/SymbolicAI/Lean/grothendieck_lean/Grothendieck/SheafCohomology/MayerVietoris.lean).
- Notebooks ICT ancres : ICT-10, ICT-12, ICT-14, ICT-14b (PR [#9545](https://github.com/jsboige/CoursIA/pull/9545) OPEN, [#9532](https://github.com/jsboige/CoursIA/issues/9532)), ICT-15, ICT-15b/c/d, ICT-17, ICT-17b, ICT-21, ICT-22.

**Issues-mères** :
- [#7738](https://github.com/jsboige/CoursIA/issues/7738) — issue-source du présent document.
- [#4588](https://github.com/jsboige/CoursIA/issues/4588) — Epic umbrella ICT strate 5.
- [#7733](https://github.com/jsboige/CoursIA/issues/7733) — rectification A2 (`H¹ ≠ 0` candidat à obstruction, pas érigé).
- [#7395](https://github.com/jsboige/CoursIA/issues/7395) — méta-proxy ICT (prérequis spec-sheet, cf. [`dissolution-scalaires.md`](dissolution-scalaires.md)).
- [#5726](https://github.com/jsboige/CoursIA/issues/5726) — intégration ICT Hashlife (parkée, *gated* sur `#6724`).
- [#6724](https://github.com/jsboige/CoursIA/issues/6724) — tracker 4 sorries `hashlife_correct`.
- [#7290](https://github.com/jsboige/CoursIA/issues/7290) — intégration ICT Kochen-Specker (spéculatif basse priorité).

**Règles et discipline** :
- [`.claude/rules/anti-regression.md`](../rules/anti-regression.md) — discipline `sorry` Lean, ne pas substituer une preuve par un stub vide.
- [`.claude/rules/catalog-pr-hygiene.md`](../rules/catalog-pr-hygiene.md) — catalogue byte-identique à `main`, marqueurs `CATALOG-STATUS` inchangés sur la branche.
- [`.claude/rules/readme-french-first.md`](../rules/readme-french-first.md) — nouveau contenu doc = français.
- [`.claude/rules/pr-review-discipline.md`](../rules/pr-review-discipline.md) §D.5 — diagnostic dérive obligatoire pour ré-alignement doc/output.
