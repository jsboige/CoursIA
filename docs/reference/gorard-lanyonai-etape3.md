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

Le README de `BurgersEquation` annonce un volume de Lean 4, un nombre de
definitions, un nombre de theoremes et un volume de C verifie. La mesure porte
sur **l'ensemble** des fichiers `proofs/*.lean` du depot, et elle concorde :

| Grandeur | Annonce amont | Mesure | Verdict |
|---|---|---|---|
| Theoremes | 582 | **582** | exact |
| Definitions | 977 | (non mesure) | — |
| Lignes de Lean | 20 329 | **20 308** | exact a 0,1 % pres |
| Lignes de C | 17 835 | (non mesure) | — |
| Fichiers de preuve | (non annonce) | 21 | — |

L'ecart sur les lignes de Lean est de 0,1 % : ce n'est pas une contradiction, la
mesure compte les fins de ligne du fichier et l'amont a pu compter avec le
fichier de specification. Ce n'est donc pas la ou le bat blesse.

## 4. Ce que les preuves etablissent — la question que l'issue pose

Chaque fichier porte `import Mathlib` en unique import, et **aucun** ne relie le
modele Lean au code C : pas de FFI, pas de `@[extern]`, pas d'extraction, pas de
generation de code. Mesure sur **tous** les fichiers de preuve du depot, pas sur
un echantillon : `import` reduit a `import Mathlib` dans 21/21, et **0 occurrence**
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
- **La partition des 180 clotures triviales par famille d'enonce** pour
  `BurgersEquation`, qui dirait si la vacuite se concentre sur l'hyperbolicite et
  la consistance diffusive ou si elle est dispersee. **Faite pour
  `GeneralRelativisticMaxwell`** : voir le §7 (mesure du 2026-11-04).

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

## 7. Inventaire par declaration — corpus relativiste (mesure du 2026-11-04)

Cette section remplit la troisieme puce du §5 sur **un seul** depot,
`lanyonai/GeneralRelativisticMaxwell`, et sert la **precondition 2 de l'issue
#24439** (« l'inventaire du contenu exact des theoremes relativistes de la
famille amont est fait et ecrit »). La partition reste **non faite** pour
`BurgersEquation` ; le §5 continue de valoir pour ce depot.

Mesure prise sur un clone a la tete `b13da44d9e93` (inchangee depuis le
2026-07-27, comme le releve le §1), six fichiers `proofs/*.lean`. Instrument :
pour chaque declaration `theorem`/`lemma`, l'ensemble des tetes de tactique de sa
preuve, range en classe de fermeture. Aucune compilation n'a ete lancee ; tout se
lit sur l'arbre clone.

### 7.1 Les nombres annonces par l'amont, recoupes

| Grandeur | Annonce du README | Mesure ici | Verdict |
|---|---|---|---|
| Theoremes | 156 | **156** | exact |
| Definitions (`noncomputable def`) | 270 | **270** | exact |
| Lignes de Lean | 24 614 | **24 608** (+6) | exact, ecart explique |
| Lignes de C | 11 730 | **11 724** (+6) | exact, ecart explique |
| Structures | non annonce | 192 declarations, 58 noms distincts | — |
| `sorry` / `axiom` / `native_decide` | non annonce | **0 / 0 / 0** | — |
| `@[extern]` / FFI vers le C | non annonce | **0** | M1 confirmee sur ce depot |

L'ecart de six lignes n'est pas une approximation. **Les douze fichiers
(`proofs/*.lean` et `implementations/*.c`) n'ont pas de saut de ligne final**, et
`wc -l` compte les sauts de ligne : 24 608 + 6 = 24 614 et 11 724 + 6 = 11 730,
soit exactement les chiffres annonces. Le §3 supposait que « l'amont a pu compter
avec le fichier de specification » ; la cause est plus simple, et elle est mesuree.

### 7.2 Repartition des 156 declarations par classe de fermeture

| Classe | Declarations | Part |
|---|---|---|
| `constructor` + `ring_nf` + `simp` | 48 | 31 % |
| `constructor` + `field_simp` + `ring_nf` | 36 | 23 % |
| structurelle seule (`constructor` / `exact` / `rfl`) | 24 | 15 % |
| `norm_num` seule | 12 | 8 % |
| `ring_nf` seule | 12 | 8 % |
| `constructor` + `exact` + `field_simp` + `rfl` | 12 | 8 % |
| `constructor` + `field_simp` + `ring_nf` + `simp` | 12 | 8 % |

Aucune autre classe. L'union des tactiques employees sur les 156 preuves est
**{`constructor`, `exact`, `rfl`, `simp`, `ring_nf`, `field_simp`, `norm_num`}** :
trois de charpente et quatre de normalisation algebrique. Zero `induction`, zero
`linarith`/`nlinarith`, zero `positivity`, zero `decide`.

Consequence mesurable : **aucune preuve du corpus ne fait d'analyse de cas sur un
objet du domaine, ni ne raisonne sur une inegalite qui ne soit pas une identite
algebrique.** Ce qui est etabli, c'est la coherence interne d'une transcription de
formules de flux ecrites en `Real`.

### 7.3 Ce que les treize noms de propriete etablissent

Le corpus est **13 proprietes x 3 directions (x, y, z) x 2 familles** (Maxwell,
Maxwell parfaitement hyperbolique) = 13 x 6 x 2 = 156 declarations.

Deux enonces sont vides, et ce sont les deux dont le nom promet le plus :

- **`xHyperbolicity`** enonce `∃ r_i : Real, r_i = (…).lambda_i` pour i = 1..10,
  ferme par dix `refine ⟨_, rfl⟩`. Il etablit que ces dix champs existent comme
  reels — ce que leur type `Real` disait deja. Il ne dit rien du caractere reel,
  distinct ou physique des vitesses caracteristiques. C'est le meme defaut que
  celui releve au §4 sur `BurgersEquation`.
- **`xWaveStability`** enonce `|mu_i| ≥ |lambda_i|`, ferme par `simp`. Mesure :
  **les deux definitions sont identiques terme a terme dans les six fichiers** —
  `xWaveSpeedExprs` et `xFluxJacobianEigenExprs` portent les memes expressions
  (`mu1..4 = lambda1..4 = -αc - β_x` en double, puis `αc - β_x` en double ;
  `mu5..10 = lambda5..10 = 0.0`). L'enonce se reduit donc a `a ≥ a`. Il ne dit
  rien d'une condition de stabilite.

Les onze autres enonces portent sur des formules non triviales — familles d'ondes,
flux diffusif, fluctuations et reconstructions gauche/droite, conditions de saut —
et se ferment par `field_simp` puis `ring_nf`. Ce sont de vraies chaines
algebriques, conformes a ce qu'une verification de consistance ou de
conservativite demande, **a condition de dire qu'elles portent sur la
transcription et non sur le schema**.

### 7.4 Deux hypotheses portees, jamais dischargees

`xFluxConservative` prend en arguments `Speed1Nondegenerate` et
`Speed2Nondegenerate`. Mesure : **aucune declaration du corpus ne conclut l'une de
ces deux hypotheses** — 60 occurrences, toutes en position d'hypothese (deux par
fichier en arguments, le reste en usage dans les preuves). La conservativite du
flux est donc etablie **sous une condition que le depot suppose et ne demontre
pas**.

### 7.5 Ce que cela change pour la serie

1. **Precondition 2 de #24439 : satisfaite** par cette section.
2. Le carnet de mesure (precondition 3) ne peut ecrire que des faits **sur la
   transcription**. En particulier il n'ecrit pas « hyperbolicite prouvee » : sur
   ce corpus, l'enonce qui porte ce nom est un existential tautologique, et
   l'enonce de stabilite est une reflexivite.
3. Le §6 reste inchange : ni build ni code C ne sont mesures ici.

### 7.6 Ce qui reste non mesure

- La **compilation** — inchange, `RECOVERABLE-LOCAL`, aucun Mathlib construit ici.
- Le **code C** : ni compile ni execute — son volume est au §7.1, pas ici.
- La **partition pour `BurgersEquation`** : le §5 reste vrai pour ce depot.
- La **correction des expressions de valeurs propres** : le corpus definit
  `lambda_i` comme des combinaisons de `alpha`, `c`, `beta_x` ; il ne demontre
  pas que ce sont les valeurs propres du jacobien du flux. Le verifier demande de
  calculer ce jacobien symboliquement et de comparer — non fait, non revendique.
