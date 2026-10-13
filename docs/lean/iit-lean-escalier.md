# Escalier du lake `iit_lean` — note de conception

**Statut** : étape 0 de l'escalier (aucun carnet consommateur n'existe encore).
**Lake** : `MyIA.AI.Notebooks/SymbolicAI/Lean/iit_lean/`, livré par #18599 (veine 5 de l'Epic Aaronson #16781, moitié formelle).
**Sous-grain** : #20414.
**Mesures** : 2026-10-12, sur `main`, lane `myia-po-2024:CoursIA`.

## Pourquoi cette note existe

Le mainteneur a posé la règle pour toute tranche Lean : « **Chaque tranche commence par une note de conception** », structurée en quatre points — inventaire du lake, escalier, capstone, modules non exposés (#17545, c.6108479114). La carte Lean phase 1 range ce lake **hors de ses tranches** : « Lakes sans carnet consommateur (`differential_lean`, `iit_lean`) : à traiter à part, hors carte ».

Le constat qui motive la note, mesuré et non supposé :

```bash
git grep -l "iit_lean" -- "*.ipynb"      # main @ 2026-10-12 : 0 hit
```

Le carnet `IIT-06-L-Objet-qui-a-Mordu-IIT.ipynb` porte la moitié **empirique** de la veine 5 (Φ_DM sur `F_p`, grilles et anneaux sous PyPhi) et n'importe pas le lake. La moitié formelle — l'objet d'Aaronson **énoncé en théorèmes** — n'a aujourd'hui aucune porte d'entrée pédagogique. Cette note décide la forme de cette porte avant qu'on écrive la première marche.

## 1. Inventaire du lake

Le lake est un **module unique** plus sa racine et son jumeau i18n : `IIT/Integration.lean` (avec docstrings FR), `IIT/Integration_en.lean` (namespace `IIT_en`), `IIT.lean` (racine qui importe les deux). **Sans dépendance Mathlib** : `lake build` se fait en secondes, sans `lake exe cache get`. `sorry` baseline `0` (`scripts/lean/ci_lakes.json`).

**19 déclarations**, toutes **non exposées** (aucun `.ipynb` du dépôt ne cite le lake) :

| # | Déclaration | Genre | Ligne | Énoncé | Carnet qui l'expose |
|---|---|---|---|---|---|
| 1 | `State n` | `abbrev` | 37 | valuation booléenne des `n` éléments | **non exposé** |
| 2 | `System n` | `abbrev` | 40 | fonction d'états (déterministe) | **non exposé** |
| 3 | `Cut n` | `structure` | 43 | coupe non triviale : `sel`, `ha` (A non vide), `hb` (B non vide) | **non exposé** |
| 4 | `projT` | `def` | 52 | motif du côté A (bits B mis à `false`) | **non exposé** |
| 5 | `projF` | `def` | 56 | motif du côté B (bits A mis à `false`) | **non exposé** |
| 6 | `cutIndep` | `def` | 62 | l'image du système est le produit des images des deux parties | **non exposé** |
| 7 | `decomposable` | `def` | 67 | il existe une coupe indépendante | **non exposé** |
| 8 | `integrated` | `def` | 70 | aucune coupe n'est indépendante | **non exposé** |
| 9 | `cutIndep_of_sides_independent` | `theorem` | 80 | dynamiques latérales indépendantes ⟹ coupe indépendante (témoin : mélange des entrées) | **non exposé** |
| 10 | `product_decomposable` | `theorem` | 102 | *énoncé figé n° 1 de #18599* — alias de 9, conclusion `decomposable f` | **non exposé** |
| 11 | `parity` | `def` | 119 | parité d'un état, par récurrence sur `n` | **non exposé** |
| 12 | `broadcast` | `def` | 125 | système broadcast-parité : l'état suivant est uniformément la parité de l'état courant | **non exposé** |
| 13 | `parity_allFalse` | `theorem` | 129 | parité d'un état tout-faux = `false` | **non exposé** |
| 14 | `parity_allTrue` | `theorem` | 139 | parité d'un état tout-vrai = imparité de `n` | **non exposé** |
| 15 | `parity_oneHot_zero` | `theorem` | 159 | le bit unique d'indice 0 rend la parité impaire, pour `n > 0` | **non exposé** |
| 16 | `parity_const` | `theorem` | 170 | parité d'un état constant : `false` si le bit est faux, parité de `n` sinon | **non exposé** |
| 17 | `broadcast_integrated` | `theorem` | 183 | **l'objet qui a mordu IIT** : le broadcast-parité est intégré pour toute coupe | **non exposé** |
| 18 | `broadcast_two_cycle` | `theorem` | 206 | toute orbite du broadcast atteint un point fixe en deux pas | **non exposé** |
| 19 | `broadcast_trivial_dynamics` | `theorem` | 216 | *énoncé figé n° 3 de #18599* — alias de 18 | **non exposé** |

**Les six théorèmes et leurs alias forment trois familles** : le verdict de décomposition (9, 10), la parité comme outil (13-16), et le couple qui porte la critique d'Aaronson (17, 18, 19). Les définitions 1-8 sont le vocabulaire de la famille 1 ; 11 et 12 celui de la famille 3.

## 2. L'escalier

Trois marches. Chaque marche est un carnet ; chaque carnet suit la grammaire de nommage (`<Préfixe>-<NN><lettre?>-<Titre>-<Noyau>`, noyau obligatoire et dernier, cf `notebook-accretion-numbering.md`).

### Marche 1 — « La coupe et le verdict »

**Expose** : 1-10 (vocabulaire + verdict de décomposition).
**Ce qu'elle ajoute** : le lecteur tient un système déterministe fini comme un objet Lean, écrit une coupe, et **fait rendre un verdict** (`decomposable` / `integrated`). Un système-produit instancié prouve `decomposable` en invoquant `product_decomposable` ; la même machinerie, appliquée au broadcast-parité, bute sur `integrated` — ce qui prépare la marche 3 sans la consommer.
**Marchepied** : les définitions `projT`/`projF` sont montrées comme motifs (ce qu'elles projettent, sur un état concret) avant d'être utilisées dans `cutIndep` — sinon la définition 6 se lit comme une formule opaque.

### Marche 2 — « La parité, de bout en bout »

**Expose** : 11-16.
**Ce qu'elle ajoute** : la parité est **calculée** sur des états concrets (`n = 3`, `n = 4`, tout-faux, tout-vrai, bit unique), et les quatre lemmes cessent d'être des obligations de preuve pour devenir des faits vérifiables à la main. C'est la marche qui rend la marche 3 lisible : sans elle, `broadcast` tombe du ciel.
**Marchepied** : `parity_oneHot_zero` est le seul lemme de la famille qui **exige** l'hypothèse `0 < n` ; la marche le dit, et c'est l'occasion de montrer pourquoi `n = 0` est un cas dégénéré du lake (aucun élément à couper).

### Marche 3 — « L'objet qui a mordu IIT, en théorèmes » (capstone)

**Expose** : 17-19, et renvoie à `IIT-06-L`.
**Ce qu'elle ajoute** : le couple de théorèmes qui **est** la critique d'Aaronson sous forme formelle — « intégration maximale au sens du proxy » (`broadcast_integrated`) **et** « comportement trivial » (`broadcast_two_cycle` / `broadcast_trivial_dynamics`), les deux sur le **même** système. Le carnet met ce couple en regard des mesures Φ_DM du carnet Python, et conclut sur ce que le proxy **ne** capture pas.

## 3. Le capstone — ce qu'il consomme, ce qu'il montre, sa place

- **Consomme** : le verdict (marche 1) pour énoncer `integrated` sans le redéfinir ; la parité (marche 2) pour lire `broadcast` ; et, hors lake, les mesures Φ_DM du carnet Python `IIT-06-L`.
- **Montre** : que la critique d'Aaronson est **formalement tenable** — un système peut maximiser le proxy d'intégration et n'avoir qu'une dynamique à deux pas. C'est exactement la posture défendue par le lake, et c'est ce que quelques dizaines de lignes de Lean montrent plus sûrement qu'un paragraphe.
- **Grade honnête, porté par le carnet lui-même** : le proxy mesure la décomposition déterministe de l'**image** ; il ne capture ni l'information effective sous perturbation, ni la partition minimale au sens MIP, ni une valeur numérique de Φ. Le carnet Python mesure Φ ; le lake formalise un **proxy**. Les deux ne se comparent pas terme à terme — le capstone le dit au lieu de le laisser croire.
- **Sa place dans la mère** : série `IIT/`, après `IIT-06-L` (dont il est la moitié formelle). La marche 1 et la marche 2 peuvent vivre dans la même série ou dans `SymbolicAI/Lean/` — c'est la décision de placement ci-dessous.

## 4. Modules non exposés — ce qui mérite un carnet, ce qui reste interne

Les 19 déclarations sont non exposées ; toutes ne méritent pas de devenir des marches :

| Destin | Déclarations | Motif |
|---|---|---|
| **Deviennent des marches** | 1-10 (marche 1), 11-16 (marche 2), 17-19 (capstone) | chacune est soit un concept (une définition qui se lit sur un exemple), soit un résultat (un théorème qui se vérifie) |
| **Restent internes comme objets d'exposition, mais apparaissent en exercice** | `projT`, `projF` (4, 5), `parity_oneHot_zero` (15) | ce sont des rouages : les exposer comme marches ferait un carnet d'implémentation, pas d'idées. Ils se montrent sur un état concret, à l'intérieur de la marche qui les utilise |
| **Restent internes, non exposés** | aucun | — |

Les deux alias figés (10, 19) n'ont pas de marche propre : ils sont nommés comme **noms d'issue** dans la marche qui porte leur théorème, parce que c'est la forme sous laquelle le lake s'est engagé à les livrer.

## 5. Décisions de placement et de nommage — et ce qui reste à trancher

**Ce que la note tranche** : la série d'accueil est `IIT/` (le carnet d'exposition appartient à la veine 5 de l'Epic Aaronson, comme la note de rattachement du 11/10 l'établit — c.6108531719), et le noyau est `lean4-wsl`, donc le nom se termine par `-Lean`.

**Ce que la note ne tranche pas, et le dit** : le **numéro**. Deux raisons, toutes deux mesurables :

1. La tranche **T7** de la carte Lean phase 1 exécute une renumérotation compacte (la file 20-38 devient les paliers 18 à 25, « exécutée en dernier »). Poser un numéro nu dans une série pendant que la carte le réécrit, c'est se condamner à renommer deux fois.
2. Le préfixe de la série `IIT/` porte déjà un cas qui ne suit pas la grammaire : `IIT-06-L-…` lit `L` comme une **lettre d'accrétion majuscule**, alors que la convention constate des lettres minuscules et que le noyau va en dernier. Le carnet à écrire hérite de cette anomalie s'il se nomme `IIT-07-L-…`.

**Proposition, à confirmer** : nommer la marche 1 `IIT-07-L-Integration-Par-Coupes-Lean.ipynb`, le noyau `-Lean` en dernier, et **ne pas** reconduire le `L` comme lettre d'accrétion — soit en le retirant, soit en le documentant comme le marqueur de la paire formelle de la série. Le geste de nommage est un acte pédagogique (il déclare ce qui est canonique et ce qui est approfondissement) : il revient au mainteneur ou au coordinateur, et le premier carnet ne s'écrit pas avant cette réponse.

## Portée non vérifiée

- L'inventaire a été lu dans `IIT/Integration.lean` **sur `main`** (lignes citées), pas dans le jumeau `_en` — les 19 déclarations y sont par construction (paire sibling, byte-identité hors docstrings, vérifiée par `scripts/lean/check_i18n_siblings.py`), mais je ne l'ai pas recompté.
- L'absence de consommateur est mesurée par `git grep` sur `main` au 2026-10-12 ; une PR ouverte non encore mergée qui citerait le lake ne serait pas vue.
- Je n'ai **pas** exécuté `lake build` sur ce lake dans ce cycle ; le « build en secondes » est repris du README du lake, pas remesuré ici.

See #20414, See #16781, See #18599.