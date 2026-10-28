# Etape 3 de #19741 — les depots lanyonai, mesures sur l'amont

Mesure posee le 2026-10-28 par la lane `myia-po-2028:CoursIA`, cycle c.2451, depuis
`main` a `62691e121`. Elle sert l'etape 3 de l'issue #19741 (chaine Gorard,
entretien *The Physicist Revolutionizing Physics With AI*) : decider **si un carnet
du depot peut consommer ces depots comme organe**, au sens de la regle
[organ-first](../../.claude/rules/organ-first-implementation.md), et **ce qu'une
preuve y etablit exactement**.

Toutes les valeurs de ce document sont mesurees a la date ci-dessus, sur l'API
GitHub et sur le contenu brut des fichiers. Elles ne se recopient pas : elles se
remeusurent.

## 1. Inventaire — licence, forme, tete

| Depot | Licence | Taille | Dernier push | Tete mesuree |
|---|---|---|---|---|
| `lanyonai/gkeyll` | MIT | 196 650 Ko | 2026-10-27 | `5f1935680e89` |
| `lanyonai/AdvectionDiffusion` | **aucune** | 329 Ko | 2026-09-09 | `71d2724e9d5b` |
| `lanyonai/BurgersEquation` | MIT | 278 Ko | 2026-09-09 | `dd9b081228ea` |
| `lanyonai/CompressibleEuler` | MIT | 323 Ko | 2026-08-10 | `a736aa5f8b17` |
| `lanyonai/MaxwellEquations` | MIT | 229 Ko | 2026-07-20 | `801558f7f5e5` |
| `lanyonai/GeneralRelativisticMaxwell` | MIT | 210 Ko | 2026-07-27 | `b13da44d9e93` |
| `lanyonai/IdealMHD` | MIT | 71 Ko | 2026-08-27 | `beeff1a31d5b` |
| `lanyonai/ElectrostaticVlasov` | MIT | 341 Ko | 2026-07-21 | `f43676e2eb1c` |
| `lanyonai/LanyonScripts` | MIT | 7 Ko | 2026-08-27 | `850d032210ff` |

`AdvectionDiffusion` n'a **aucun fichier de licence** : il se cite, il ne se
reutilise pas. Les sept autres solveurs sont MIT, donc reutilisables avec
attribution.

## 2. Aucun depot ne declare sa version de Lean — verifie sur les huit arbres

Recherche de `lean-toolchain`, `lakefile.lean`, `lakefile.toml` et
`lake-manifest.json` sur l'arbre recursif complet de chaque depot de solveur :
**aucun des huit n'en porte un**. Nos lakes sont epingles en
`leanprover/lean4:v4.33.0` ; la version sous laquelle ces preuves compilent n'est
donc declaree nulle part, et ne se deduit pas du depot.

| Depot | fichiers | `.lean` | `.c`/`.h` | `lean-toolchain` | `lakefile` |
|---|---|---|---|---|---|
| `BurgersEquation` | 92 | 21 | 21 | absent | absent |
| `AdvectionDiffusion` | 92 | 21 | 21 | absent | absent |
| `CompressibleEuler` | 32 | 6 | 6 | absent | absent |
| `MaxwellEquations` | 32 | 6 | 6 | absent | absent |
| `GeneralRelativisticMaxwell` | 32 | 6 | 6 | absent | absent |
| `IdealMHD` | 31 | 6 | 6 | absent | absent |
| `ElectrostaticVlasov` | 32 | 6 | 6 | absent | absent |
| `LanyonScripts` | 10 | 0 | 0 | absent | absent |

La forme est strictement la meme partout : `specifications/`,
`implementations/` (C), `proofs/` (fichiers Lean 4 isoles), `screencaps/`.
Ce sont **des fichiers de preuve, pas un projet Lean** : sans `lakefile` ni
`lean-toolchain`, ils ne s'ouvrent pas par `lake build` ; il faut fabriquer
l'environnement autour d'eux.

## 3. Les nombres annonces par l'amont sont exacts

Le README de `BurgersEquation` annonce 20 329 lignes de Lean 4, 977 definitions,
582 theoremes et 17 835 lignes de C verifie. Mesure sur les 21 fichiers
`proofs/*.lean` de ce depot :

| Grandeur | Annonce amont | Mesure | Verdict |
|---|---|---|---|
| Theoremes | 582 | **582** | exact |
| Lignes de Lean | 20 329 | **20 308** | exact a 0,1 % pres |
| Fichiers de preuve | (non annonce) | 21 | — |

Un ecart de 21 lignes sur 20 329 n'est pas une contradiction : la mesure compte
les fins de ligne du fichier, l'amont a pu compter avec le fichier de
specification. Ce n'est donc pas la ou le bat blesse.

## 4. Ce que les preuves etablissent — la question que l'issue pose

Chaque fichier porte `import Mathlib` en unique import, et **aucun** ne relie le
modele Lean au code C : pas de FFI, pas de `@[extern]`, pas d'extraction, pas de
generation de code. Mesure sur les **21 fichiers de preuve** du depot, pas sur un
echantillon : `import` reduit a `import Mathlib` dans 21/21, et **0 occurrence**
de `@[extern]`, `axiom`, `unsafe`, `implemented_by` ou `FFI`. Les occurrences de
`C.` rencontrees sont la variable `Coordinates` des enonces, pas un lien vers le C.

Les theoremes portent sur une **transcription Lean des fonctions de flux du
solveur** (structures `Coordinates`, `State`, `Parameters`, `Flux` et leurs
expressions). Sur les 582 theoremes de `BurgersEquation`, **180 (31 %) se
referment en une seule tactique** — et ce sont precisement les enonces les plus
spectaculaires qui sont les plus vides. Trois exemples lus dans
`proofs/inviscid_burgers_1d.lean` :

- `xHyperbolicity` enonce `∃ r1 : Real, r1 = lambda1`, prouve par
  `refine ⟨lambda1, rfl⟩` : il dit que la valeur propre **existe**, pas que le
  systeme est hyperbolique ;
- `xDiffusiveFluxConsistency` enonce `diffusive_flux_f = 0` la ou
  `xDiffusiveFluxExprs` **definit** `diffusive_flux_f := 0.0` : la preuve est
  `simp only [...]` puis `norm_num`, soit `0 = 0` ;
- `xWaveStability` enonce `|mu1| ≥ |lambda1|` et se referme par `simp` sur les
  deux definitions.

Les 69 % restants ne sont pas vides pour autant : ce sont de vraies chaines
algebriques. Extrait de `xFluxConservative`
(`proofs/inviscid_burgers_3d.lean`) : `simp` sur les definitions de flux, puis
`ring_nf`, puis `repeat field_simp [Speed1Nondegenerate, Speed2Nondegenerate]`,
puis de nouveau `ring_nf`. La conservativite du flux est donc etablie sur des
expressions rationnelles, **sous hypotheses de non-degenerescence explicites**.
C'est du travail honnete, a condition de dire sur quoi il porte.

**Verdict honnete** : ces preuves etablissent des proprietes **du modele Lean**
du schema (consistance des reconstructions, conservativite, conditions de saut).
Elles n'etablissent **pas** que le code C s'y conforme, ni qu'un resultat
numerique soit correct. La formule de l'amont — « specification, code C et
preuve generes » — est vraie comme fait de generation ; elle ne constitue pas une
preuve de bout en bout du couple code/schema, et un carnet qui la reprendrait
telle quelle revendiquerait plus que ce qui est demontre.

## 5. Ce qui n'a pas ete mesure ici

- **La compilation.** Les preuves n'ont pas ete elargies sur ce siege : aucun
  Mathlib n'y est construit, et la version requise n'est declaree nulle part.
  Verdict `RECOVERABLE-LOCAL`, geste nomme : creer un lake de travail epingle,
  `lake exe cache get`, puis `lake env lean proofs/inviscid_burgers_1d.lean`.
  Tant que ce geste n'est pas fait, **aucune preuve de ces depots n'est
  verifiee** — le fait qu'elles aient ete produites par le systeme Lanyon ne
  remplace pas la mesure.
- **Le code C.** Ni sa compilation ni son execution n'ont ete mesurees.
- **La partition des 180 clotures triviales par famille d'enonce**, qui dirait si
  la vacuite se concentre sur l'hyperbolicite et la consistance diffusive ou si
  elle est dispersee.

## 6. Decision pour la serie

1. Un carnet peut **citer** ces depots, jamais les presenter comme « solveurs
   verifies de bout en bout » sans la phrase du §4.
2. **`AdvectionDiffusion` ne se reutilise pas** (aucune licence) ; il se cite.
3. Un carnet qui veut montrer un solveur verifie **invoque le depot amont**
   (clonage, build reel, sortie reelle) ; il ne reimplemente pas une version
   jouet, et il ne recopie pas non plus les preuves sans leur environnement.
4. Le prealable a toute consommation est le geste du §5 : un lake de travail avec
   un Mathlib construit, et la plus petite preuve elargie. C'est ce qui
   transforme « annonce par un tiers » en « verifie ici ».
