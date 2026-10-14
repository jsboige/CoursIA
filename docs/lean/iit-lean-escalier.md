# Escalier `iit_lean` — note de conception

**Issue** : #20414 · **Epic** : #16781 (Aaronson, veine 5 — « l'objet qui a mordu IIT, en Lean ») ·
**Lake livré par** : #18599 · **Carte Lean phase 1** : #17545 (c.6108479114 : « chaque tranche
commence par une note de conception » ; rattachement c.6108531719).
**Mesure d'origine** : `git grep -l "iit_lean" -- "*.ipynb"` → 0 hit sur `main` au 2026-10-12 —
le lake n'a aucun carnet consommateur, et la carte le range explicitement hors de ses tranches
(« lakes sans carnet consommateur : à traiter à part, hors carte »).

Cette note suit les quatre points du mandat : inventaire, escalier, capstone, modules non
exposés. Elle est vérifiable ligne à ligne contre
[`IIT/Integration.lean`](../MyIA.AI.Notebooks/SymbolicAI/Lean/iit_lean/IIT/Integration.lean)
(19 déclarations, 0 `sorry`, sans dépendance Mathlib, paire i18n FR/EN pattern A).

## 1. Inventaire nominatif — quoi est exposé, où

L'inventaire mécanique (`grep -E "^(abbrev|structure|def|theorem)"`) rend 19 déclarations,
regroupées ici en 13 items pédagogiques. « Exposé » signifie : un carnet de l'escalier importe
l'item et le fait travailler (pas seulement le mentionner).

| # | Item (noms) | Lignes | Rôle dans le lake | Exposition |
| --- | --- | --- | --- | --- |
| 1 | `State`, `System` | 37, 40 | valuation booléenne `Fin n → Bool` ; système = fonction d'états | Marche 1 |
| 2 | `Cut` (+ champs `sel`, `ha`, `hb`) | 43-49 | coupe non triviale : deux côtés non vides | Marche 1 |
| 3 | `projT`, `projF` | 52, 56 | motifs d'un côté (bits de l'autre à `false`) | Marche 1 |
| 4 | `cutIndep` | 62 | indépendance : tout couple de motifs séparément réalisables est réalisable ensemble | Marche 1 |
| 5 | `decomposable`, `integrated` | 67, 70 | existence / absence de coupe indépendante | Marche 1 |
| 6 | `cutIndep_of_sides_independent` | 80 | **Théorème A** : dynamiques latérales indépendantes ⇒ coupe indépendante (témoin constructif : le mélange des entrées) | Marche 1 |
| 7 | `product_decomposable` | 102 | alias de A sous le **nom figé n° 1 de #18599** | Marche 1 (mentionné comme contrat d'issue, pas exposé en propre) |
| 8 | `parity` | 119 | parité par récurrence sur `n` (tête + queue décalée) | Marche 2 |
| 9 | `broadcast` | 125 | le système broadcast-parité : l'état suivant est uniformément la parité | Marche 2 (aperçu mesuré en marche 1, § teaser) |
| 10 | `parity_allFalse`, `parity_allTrue`, `parity_oneHot_zero`, `parity_const` | 129-174 | escalier interne de la preuve de B | Marche 2 (lus comme les marches de la preuve, pas de carnet propre) |
| 11 | `broadcast_integrated` | 183 | **Théorème B** : le broadcast est intégré pour toute coupe | Marche 2 |
| 12 | `broadcast_two_cycle` | 206 | **Théorème C** : toute orbite atteint un point fixe en deux pas | Capstone |
| 13 | `broadcast_trivial_dynamics` | 216 | alias de C sous le **nom figé n° 3 de #18599** | Capstone (mention, idem 7) |

Le jumeau EN `IIT/Integration_en.lean` (namespace `IIT_en`) est byte-identique hors docstrings
(paire sibling pattern A) : il n'a pas d'exposition séparée — un carnet consomme le module FR,
l'existence du jumeau est rappelée en marche 1.

## 2. L'escalier — trois marches

Le fil directeur : la critique d'Aaronson (« construire un objet à intégration énorme et à
comportement trivial ») ne devient un énoncé mathématique qu'après avoir posé **ce que coupe
veut dire**. La marche 1 paie ce vocabulaire ; la marche 2 construit l'objet ; le capstone lit
les deux ensemble. Chaque marche est un grain distinct (#20414 : note + marche 1 ; les
suivantes en grains séparés).

### Marche 1 — Coupe et décomposabilité (théorème A)

**Carnet** : [`IIT-07-Coupe-et-Decomposabilite-Lean.ipynb`](../MyIA.AI.Notebooks/IIT/IIT-07-Coupe-et-Decomposabilite-Lean.ipynb) · kernel `lean4-wsl`.

- **Marchepieds** : aucun carnet Lean préalable exigé — le carnet est autonome pour un lecteur
  du 06 ou d'IIT-01 ; les définitions sont relues sur des instances `Fin`/`Bool` calculées
  (`#eval`), la syntaxe Lean introduite au fil de l'eau.
- **Ce qu'elle ajoute** : les items 1-7 du tableau — un état, un système, une coupe, le motif
  d'un côté, l'indépendance comme produit d'images relire sur instance, décomposable/intégré ;
  puis le théorème A et son **témoin constructif** (le mélange `z` des entrées) exhibé sur un
  système concret à deux moitiés indépendantes ; l'alias figé `product_decomposable` lu comme
  contrat d'issue.
- **Teaser mesuré pour la marche 2** : vérification exhaustive (énumération finie, `n = 2`)
  que le broadcast est intégré — une preuve par énumération qui motive la preuve générale
  (comment prouver pour **tout** `n` et **toute** coupe ?).
- **3 exercices C.1** : construire une coupe et ses motifs ; appliquer A sur un nouveau système
  local (écrire `hA`/`hB` soi-même) ; montrer que l'identité est décomposable (l'insight :
  A s'applique, la localité y est triviale).

### Marche 2 — Le broadcast-parité (théorème B)

**Carnet** : `IIT-08-*` (à créer en son grain). Items 8-11.

- **Marchepieds** : marche 1 (le vocabulaire de coupe est acquis).
- **Ce qu'elle ajoute** : `parity` par récurrence sur `n` ; `broadcast` et son image (deux
  états constants) ; les quatre lemmes de parité lus comme **l'escalier interne de la preuve**
  (pourquoi la récurrence sur `n` seule ne généralise pas `s`, pourquoi `omega` ferme la
  bascule modulo 2) ; le théorème B — le couple de motifs (côté A diffusé vrai, côté B diffusé
  faux) n'est jamais réalisé ensemble alors que chaque motif l'est séparément.

### Capstone — L'objet qui a mordu IIT, en théorèmes (A ∧ B ∧ C)

**Carnet** : `IIT-09-*` (à créer en son grain).

- **Marchepieds** : marches 1 et 2.
- **Ce qu'il ajoute** : le théorème C (dynamique triviale) et la **lecture conjointe** —
  intégration pour toute coupe + comportement trivial = le contenu formel de la critique
  d'Aaronson, en deux théorèmes rendus par le noyau. Dialogue avec la moitié empirique
  ([`IIT-06`](../MyIA.AI.Notebooks/IIT/IIT-06-L-Objet-qui-a-Mordu-IIT-Python.ipynb) :
  Vandermonde et le hack W en Φ_DM, grille XOR en Φ 3.0) : le lake formalise la *classe* de
  l'objet, le 06 mesure des *instances* numériques. Le grade du proxy (sur-montée interdite :
  pas d'information sous perturbation, pas de MIP, pas de Φ numérique — Phase 2 renvoyée)
  et les portes ouvertes.

## 3. Le capstone — ce qu'il consomme, ce qu'il montre, sa place

- **Consomme** : le théorème A (marche 1) comme contrepoint — A dit qu'un système vraiment
  modulaire est décomposable ; B dit que le broadcast ne l'est pour **aucune** coupe ; C dit
  que sa dynamique est triviale. Le capstone n'apporte pas de nouveau théorème du lake : il
  apporte la **conjonction** et son acuité — c'est précisément le couple B ∧ C qui « mord ».
- **Montre** : que l'objection de 2014 (« Φ énorme, comportement trivial ») est un théorème
  dans un proxy relationnel déterministe — avec le grade honnête : le proxy mesure la
  décomposition déterministe de l'image, il ne capture ni l'information effective sous
  perturbation, ni la partition minimale au sens MIP, ni une valeur numérique de Φ. La source
  est un billet de blog (2014), pas une publication formelle : le lake **crée** l'objet
  formel, il n'en est pas une transcription.
- **Place dans la série mère (IIT)** : suite directe du 06 — même veine critique, l'autre
  moitié de la frontière entre formalisations. Le 06 exécute l'échange Aaronson/Tononi sur
  instances numériques ; l'escalier 07-09 le formalise. Placement détaillé au §4.

## 4. Placement et nommage — décision tranchée

**Décision** : les carnets de l'escalier vivent dans la **série IIT**
(`MyIA.AI.Notebooks/IIT/`), numérotés à la suite du 06 : `IIT-07-Coupe-et-Decomposabilite-Lean`,
puis `IIT-08-*` (broadcast), puis `IIT-09-*` (capstone). Suffixe de langue `-Lean` (kernel
`lean4-wsl`), cohérent avec le `-Python` des carnets 01-06.

**Motifs** :

1. **Le carnet est la moitié formelle du 06** — le 06 porte la moitié empirique (Φ_DM sur
   F_p, grilles PyPhi) et n'importe pas le lake ; l'issue #20414 appelle explicitement sa
   « porte d'entrée pédagogique ». La porte d'entrée d'une série, c'est la série.
2. **Le risque nommé par l'acceptance ne s'applique pas** : la renumérotation en cours (tranche
   T7 de la carte #17545) vise les carnets numérotés `Lean-NN` de `SymbolicAI/Lean/` ; la
   série IIT (01-06 stable, extension `ICT-Series/` numérotée à part) n'est pas sous
   renumérotation. Poser `IIT-07` n'entre pas dans le risque « numéro nu pendant T7 ».
3. **Précédent de structure** : `game_theory_lean` a ses carnets consommateurs dans la série
   GameTheory (06k), pas dans le lake ; le lake reste la formalisation, la série porte la
   pédagogie.

**Non-décision explicite** : le nom définitif des marches 2 et 3 (`IIT-08-*`, `IIT-09-*`) est
proposé ici mais chaque marche reste un grain distinct — son nom se fige au moment de son
carnet, pas avant.

## Modules non exposés — décisions explicites

| Module | Décision | Motif |
|---|---|---|
| `product_decomposable`, `broadcast_trivial_dynamics` (noms figés #18599) | **pas d'exposition en propre** | alias de A et C sous des noms de contrat d'issue ; mentionnés dans la marche qui expose leur cible (1 et capstone), en nommant leur statut de nom figé |
| `parity_allFalse`, `parity_allTrue`, `parity_oneHot_zero`, `parity_const` | **pas de carnet propre** | escalier **interne** de la preuve de B : leur intérêt pédagogique est exactement leur rôle dans la preuve — ils se lisent dans la marche 2, en situation |
| `IIT/Integration_en.lean` | **pas d'exposition séparée** | jumeau i18n byte-identique hors docstrings ; consommer le module FR suffit, l'existence du jumeau est rappelée |

Tout le reste du lake (items 1-6, 8, 9, 11, 12) est couvert nominativement par l'escalier :
après livraison du capstone, l'inventaire ci-dessus n'aura plus aucune ligne « non exposé ».

## État de livraison

| Livrable | État | Trace |
|---|---|---|
| Note de conception (ce document) | livré | PR #20414 |
| Marche 1 — `IIT-07-Coupe-et-Decomposabilite-Lean` | livré | PR #20414 |
| Marche 2 — `IIT-08-*` | à créer | grain distinct |
| Capstone — `IIT-09-*` | à créer | grain distinct |
