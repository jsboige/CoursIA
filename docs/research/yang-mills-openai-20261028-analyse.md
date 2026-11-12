# Yang–Mills OpenAI (2026-10-28) — cartographie sourcée de la soumission formelle

**Cible.** Issue [#25826](https://github.com/jsboige/CoursIA/issues/25826), ouverte
par la sous-série `Physique/Jauge` de l'EPIC #23161. **Source externe.**
[`yang-mills-group/OpenAI-YM-20261028`](https://github.com/yang-mills-group/OpenAI-YM-20261028),
dépôt Lean de la soumission « Wilson Yang–Mills construction », **Apache-2.0**
(`LICENSE`, `NOTICE`, `THIRD_PARTY.md`). **Pin.** `main` @ 2026-11-05, clone local
utilisé pour cette analyse : `D:/tmp/ym-src` (9 508 fichiers, commit unique).

**Statut documentaire.** Cette analyse est une **lecture de source formelle**, pas
une validation de compilation. Deux plans sont à ne pas confondre :

| Plan | Statut de chaque affirmation |
|---|---|
| Intégrité des sources, cloisonnement des imports, absence de `sorry`/`axiom` hors référence, épinglage des versions | **VÉRIFIÉ** ici, par rejouage automatisé (`scripts/ym_openai_20261028/inventory.py`) |
| Compilation Lean, replay noyau, réélaboration des 9 457 modules | **RAPPORTÉ** — journaux de la soumission (`verification/*.log`), **non rejoués** ici (obstacle : voir §6) |

**Ce que cette analyse n'établit pas.** La soumission **n'est pas** une solution du
problème Clay : le README de la soumission exclut explicitement l'écart de masse
(§5). Aucune affirmation de ce document ne doit être lue comme « le problème Yang–Mills
est résolu ».

---

## 1. L'objet : une existence conjointe, pas un théorème unique

Le théorème unique de la soumission est `YangMills.jointExistence`
(`Solution.lean:4`), dont le type est l'énoncé `YangMills.JointExistence` défini
dans la spécification publique :

```lean
-- ChallengeSpec.lean:186-188
def JointExistence : Prop := ∀ g : GaugeGroup, g.IsSimple → ∃ C : WilsonFamily g,
  WilsonRegularity C ∧ ∀ p : ℕ → ℕ, StrictMono p → ∃ q : ℕ → ℕ, StrictMono q ∧
    ∃ T : Hierarchy C, T.Properties (p ∘ q)
```

Lecture : **pour tout** groupe de jauge compact à algèbre de Lie réelle simple
non abélienne, il existe **une** famille de Wilson sur réseau, **une** hiérarchie de
continuum, et quatre propriétés simultanément satisfaites. La preuve
(`Solution.lean:4-11`) est une projection d'un théorème de construction bien plus
fort, `YangMills.constructed` (`Construction.lean:15`), qui construit la famille,
la table, la reconstruction, le lecteur d'OPE et les devices de contact en un seul
choix cohérent.

La spécialisation `SU(2)` est explicite (`ConcreteSU2.lean:8-18`) : `su2` est
défini par sa représentation définitoire, `su2Simple` est un théorème de
simplicité, et `su2Theory` en découle par application directe de `jointExistence`.

## 2. Les quatre propriétés demandées, et leur contenu exact

`Properties` (`ChallengeSpec.lean:177-181`) exige quatre choses **sur la même
hiérarchie** — la force du théorème est là, pas dans l'existence d'un objet isolé.

| Propriété | Structure | Fichier:ligne | Ce qu'elle exige concrètement |
|---|---|---|---|
| Origine de Wilson | `WilsonRegularity` | `ChallengeSpec.lean:12-22` | Pente positive fixée **avant** le choix de la famille : `\|β/log(mesh⁻¹) − slope\| < ε` uniformément en volume ; insertions **continues**, **invariantes de jauge**, à **support local** (un stencil fini contrôle toute mesure) |
| Reconstruction de Wightman | `Reconstructed` | `ChallengeSpec.lean:117-143` | Axiomes W0–W3, **fidélité**, injectivité et surjectivité des étiquettes, **normalisation** de la mesure de phase, **support plein**, symétrie de permutation, **lissabilité**, **mélange** des caractères, **analytique** sur le tube de temps ordonnés, et **continuité** entre l'axe imaginaire et les moments de Wightman |
| OPE séparée à tous les ordres | `OperatorProductExpansion` | `ChallengeSpec.lean:70-80` | Un **système unique** de coefficients, à chaque degré de troncature et dans chaque phase ; bornes `r^(j − weight − ε)` uniformes ; reste borné en `r^(D+1 − weight − ε)`. Les spectateurs sont lus **de la même hiérarchie** que le mot entier (`grouped`, `ChallengeSpec.lean:58-61`) |
| Test de non-liberté | `TraceTest` | `ChallengeSpec.lean:168-175` | Trace centrée d'ordre 4 : `r⁸ log²(1/r) · traceTwo r → 3·dim(g)/π⁴ > 0`, et **aucune** somme finie de profils de Wick mass-shell ne peut égaler `traceTwo` au voisinage de 0 |

La mécanique de la partie « origine de Wilson » est entièrement dans la spécification
publique : `plaquette`, `wilsonEnergy`, `wilsonLaw` (mesure de Haar × `exp(−β·énergie)`)
en `PublicWilson.lean:20-33` ; la limite « maillage d'abord, volume ensuite » est
`WilsonFamily.Converges` (`PublicWilson.lean:85-90`), qui exige le moment **fini**
(`finiteMoment`, `PublicWilson.lean:54-57`) avant toute limite.

**Le coefficient `3·dim(g)/π⁴` n'est pas une convention de lecture.** Il est *prouvé*
égal au « prix » interne de la trace, dans le pont qui relie l'API publique à
l'implémentation :

```lean
-- TraceBridge.lean:24-25
private theorem award_eq (hg : g.IsSimple) :
    YM.Trace.Verse.award g.core = 3 * (Module.finrank ℝ g.lieAlgebra : ℝ) / Real.pi^4
```

et `publicTrace` (`TraceBridge.lean:35-44`) en déduit `TraceTest` : il substitue
`award_eq` à l'hypothèse `H.positive`, puis fait passer l'exclusion des profils de
Wick par `Wick.euclidean_excludes` et l'identité `profile_eq`
(`TraceBridge.lean:19-22`, qui identifie le profil de la hiérarchie au profil Wick
natif). C'est ce qui rend la clause d'exclusion **opposable** plutôt que décorative.

## 3. Architecture : 613 lignes de spécification, ~988 000 lignes d'implémentation

Le dépôt sépare strictement le **référentiel** (l'énoncé, non implémenté) de la
**solution** (l'implémentation) :

```text
Challenge.lean            -- le statement du défi + un `sorry` (le placeholder)
  └── ChallengeSpec.lean  -- l'énoncé complet, en 190 lignes
        └── PublicWilson.lean   -- réseau de Wilson, loi, limite (92 lignes)
              └── PublicTheory.lean  -- groupes de jauge, Wightman W0–W3 (325 lignes)
                    └── Mathlib
```

Cinq fichiers à la racine portent le chainage ; `SOURCES.sha256` couvre **9 507**
entrées ; le dépôt compte **9 477** fichiers `.lean` pour **987 586** lignes.

La mesure décisive est le **cloisonnement** : la closure d'imports du référentiel
ne touche **aucun** module d'implémentation. Mesuré par notre outil de façon
indépendante (`inventory.py`, contrôle `cloisonnement_reference`) :

```text
closure = 4 module(s) de specification (Challenge, ChallengeSpec, PublicTheory, PublicWilson)
          + 1 externe(s) ; 0 module(s) d'implementation atteint(s)
```

et corroboré par le journal de la soumission lui-même
(`verification/archive-graph.log:2`) :

```text
Challenge transitive modules 8642 YM implementation modules 0
Solution transitive modules 18105 YM implementation modules 9456
```

À l'inverse, la closure de `Solution.lean` atteint **9 467** modules du projet et
263 modules externes : le travail est bien du côté de l'implémentation, pas du
côté de l'énoncé.

**Le `sorry` est unique et il est au bon endroit.** La soumission le dit
(`README.md`, section « Verification »), et la mesure le confirme : **1** occurrence
de `sorry` dans tout le dépôt, en `Challenge.lean:6` — le placeholder du *défi*.
Hors référence : **0**. Même décompte pour les admissions : `axiom` **0**,
`opaque` **0**, `native_decide` **0**, `unsafe` **0** dans tout le dépôt.
`Classical.choice` apparaît **210** fois : c'est l'admission classique de Mathlib,
autorisée et déclarée.

Deux `partial def` **privés** existent (`YM/UVExtension/Orchard/Barrel.lean:36`
et `:43`, métaprogrammation de compilation) : ils ne sont pas des interruptions
de preuve — l'organe d'audit de la soumission rejette explicitement toute
dépendance `unsafe` ou `partial` atteignable depuis les résultats annoncés
(`Verify.lean:42-43`). Notre inventaire les compte et les nomme plutôt que de
les ignorer.

## 4. Les contrôles que la soumission déclare (et ce que nous en retenons)

| Journal | Contenu mesuré | Portée |
|---|---|---|
| `verification/build.log:1` | `BUILD_PASS modules=9457` | compilation des 9 457 modules YM |
| `verification/build.log:4` | `DECLARATION_SCAN declarations=249713 directSorryAx=0 projectAxioms=0` | aucun `sorryAx`, aucun axiome du projet |
| `verification/build.log:6` | `USAGE_PASS headlines=13 project=249713 used=99822 outside=149891 modules=9457 modulesWithNoUsedDeclaration=2950` | **2 950 modules** ne contribuent aucune déclaration utilisée |
| `verification/joint-check.log:56` | `REPLAY_PASS project=100168 external=14364 endpoints=17 duplicateAliases=0` | replay noyau de 100 168 déclarations projet, 17 points d'entrée |
| `verification/joint-check.log:58` | `PASS VerifyJoint` | le comparateur passe |
| `verification/negative-controls.log:1-3` | 2 `REJECTED_AS_EXPECTED` + `NEGATIVE_CONTROLS_PASS` | les **contrôles négatifs** sont bien des contrôles : un énoncé affaibli et un axiome non prouvé sont **rejetés** |
| `verification/source-match.log:1,6` | 9 458 sources YM comparées, `SOURCE_INPUT_MATCH_PASS` | les sources correspondent aux entrées de compilation |

Le contrôle négatif est le plus instructif : la soumission **aime** que ses
propres vérifications échouent sur des entrées dégradées. C'est la bonne posture
pour un résultat qu'on ne peut pas recompiler soi-même.

Deux chiffres méritent d'être lus ensemble : `endpoints=17` au replay noyau et
`headlines=13` au contrôle d'usage. Ils ne mesurent pas la même chose (points
d'entrée rejoués vs racines effectivement *utilisées* par l'analyse d'usage) ;
les deux sont reproduits tels quels plutôt que réconciliés.

**Nuance d'échelle.** `modulesWithNoUsedDeclaration=2950` et
`outside=149891` disent qu'une part majoritaire du corpus n'est pas atteignable
des 17 résultats annoncés. La soumission le déclare elle-même
(`README.md`, « Source coverage » : « The 17 audited theorems reach 100,168 of
250,319 imported project declarations »). C'est un fait de structure du dépôt,
pas un défaut de preuve — mais c'est aussi la raison pour laquelle « 9 477 fichiers
Lean » ne doit pas être lu comme « 9 477 lemmes utiles ».

## 5. Ce qui est explicitement **hors** périmètre — donc ce que ce n'est pas

Le README de la soumission est net, et c'est le point le plus important de cette
analyse :

| Exclu | Source |
|---|---|
| **Écart de masse** positif, exclusion générale des champs libres généralisés à masse continue, ajustement MS-bar à tous les ordres | `README.md:26` |
| **Unicité** sur d'autres prescriptions de contact, convergence « cutoff brut » sur les **diagonales de collision** | `README.md:23` |
| Unicité de la prescription de champ (seule l'unicité du **vide** de Wightman est dans le périmètre) | `README.md:26` |

Autrement dit : la soumission établit l'**existence** d'une hiérarchie de Yang–Mills
4D constructible (famille de Wilson → limite de volume → reconstruction de
Wightman → OPE séparée → non-liberté), avec le **gap de masse laissé ouvert** et
l'unicité de la théorie laissée à l'unicité du vide seulement. Le problème Clay
demande l'existence **et** l'unicité d'une théorie YM 4D non abélienne **avec gap
de masse**. **Ce n'est pas la même chose**, et la distinction doit survivre à la
distillation.

Ce que la soumission appelle « non-freeness test » est, lui, un contenu
substantiel : le coefficient `3·dim(g)/π⁴` de la fonction à deux points de la trace
centrée d'ordre 4, et l'exclusion de **toute** somme finie de profils de Wick
mass-shell. Ce test est **numériquement illustrable** : le carnet `Jauge-03` en fait
la démonstration (section §8).

## 6. Obstacle : la compilation Lean n'est pas rejouée ici

**Verdict user du 01/11/2026** : le build Lean local est interdit sur cette machine ;
la compilation est du ressort de la CI. Conséquence, énoncée telle quelle :

- tout ce que cette analyse dit de la **compilation**, du **replay noyau** et de la
  **réélaboration** est **rapporté** depuis les journaux de la soumission, pas
  vérifié par nous ;
- le maximum que nous vérifions par rejeu automatisé est **l'intégrité des sources**
  (9 507 empreintes recalculées), **le cloisonnement des imports**, **l'absence de
  `sorry`/`axiom`/`native_decide` hors référence**, **l'épinglage des versions** et
  **la présence des contrôles négatifs** ;
- aucun verdict « la soumission compile » n'est prononcé ici, ni dans le carnet, ni
  dans le corps de la PR.

Un obstacle méthodologique mérite d'être signalé parce qu'il a faussé une première
mesure : sur un poste Windows où `core.autocrlf = true`, le **checkout** convertit
les fins de ligne, si bien que le fichier de travail ne porte plus l'empreinte
SHA-256 du blob commité — **9 506 fichiers sur 9 507** sont dans ce cas. Une
vérification naïve par hachage du fichier de travail conclut « sources altérées ».
La bonne méthode est de hacher le **blob** (`git cat-file --batch`), ce que fait
l'outil : les **9 507** empreintes correspondent alors, et les 9 506 écarts de
checkout sont **comptés et nommés** (`normalises_par_checkout`) au lieu d'être
silencieusement absorbés.

## 7. L'outil rejouable

```bash
python scripts/ym_openai_20261028/inventory.py --repo <clone-local>          # rapport texte
python scripts/ym_openai_20261028/inventory.py --repo <clone-local> --json   # sortie structuree
```

Code de sortie : `0` si les neuf contrôles passent, `1` sinon, `2` si le clone est
illisible. Aucune dépendance hors bibliothèque standard ; **aucun Lean requis**.

Les neuf contrôles : `integrite_manifeste`, `cloisonnement_reference`,
`travail_dans_la_solution`, `placeholder_unique`, `admissions_declarees`,
`reduction_naturelle`, `controles_negatifs`, `headlines`, `versions`. Le rapport
`--json` porte, pour chacun, la preuve (chiffres) et les détails (occurrences
`fichier:ligne`).

Sortie mesurée sur le pin audité :

```text
[PASS] integrite_manifeste       9507 fichiers verifies sur 9507 annonces
[PASS] cloisonnement_reference    0 module(s) d'implementation atteint(s)
[PASS] travail_dans_la_solution   9467 module(s) projet, 263 externe(s)
[PASS] placeholder_unique         1 `sorry` au total, 0 hors referentiel
[PASS] admissions_declarees       axiom=0, opaque=0
[PASS] reduction_naturelle        native_decide=0
[PASS] controles_negatifs         2 rejets attendus, succes=True
[PASS] headlines                  17 headline(s) annonce(s)
[PASS] versions                   leanprover/lean4:v4.32.0 / mathlib 81a5d257c8e4
```

## 8. Attribution et licence

La soumission est **Apache-2.0** (`LICENSE`). `NOTICE` porte les attributions
obligatoires, dont celles des lemmes de Mathlib adaptés par le projet (par exemple
`YM/Next/STATIONARY/OneLoop/WilsonVertices.lean`, © 2025 Yury Kudryashov ;
`YM/Work/F05/PiDensity.lean`, © 2023 Xavier Roblot ; les modules d'alignement
gaussien d'`YM/AnalyticBridge/`, © 2026 Rémy Degenne et Etienne Marion).
`THIRD_PARTY.md` épingle les neuf dépôts de compilation (Lean `v4.32.0`, Mathlib
`81a5d257c8e4`, batteries, aesop, Qq, ProofWidgets4, plausible, importGraph,
LeanSearchClient) avec leur licence.

**Contrainte de distillation.** Aucun code Lean de la soumission n'est recopié dans
CoursIA : le livrable est une **analyse** (cartographie + outil de relecture
Python) et une **section pédagogique** du carnet `Jauge-03`, dont le code est
original et ne dépend d'aucun code tiers. Le carnet reste donc autonome et
rejouable sans la soumission.

## 9. Ce que la sous-série `Physique/Jauge` en retient

1. Le fil « symétries → jauge → réseau » **atteint maintenant une existence
   formelle** : il n'y a plus de « veille », il y a un énoncé précis et un
   test de non-liberté calculable.
2. Le **test de non-liberté** est le morceau le plus falsifiable : on peut le
   recalculer en Python (carnet `Jauge-03`, §8) et vérifier qu'aucun profil libre
   n'atteint le coefficient `3·dim(g)/π⁴`.
3. Le **gap de masse** n'est pas résolu par cette soumission : l'énoncer comme
   ouvert, dans le carnet comme dans le README de la sous-série, serait une
   faute.

---

### Références

- Source : `yang-mills-group/OpenAI-YM-20261028` @ `main` (2026-11-05), Apache-2.0.
- Annonce : OpenAI, « Working with academic communities to build scientific understanding », 26/10/2026 — [openai.com](https://openai.com/index/building-scientific-understanding-with-academic-communities/) (page consultée le 12/11 ; annonce de la découverte physique, distincte de la publication formelle du 28/10).
- Outil de rejeu : [`scripts/ym_openai_20261028/inventory.py`](../../scripts/ym_openai_20261028/inventory.py).
- Carnet associé : [`MyIA.AI.Notebooks/Physique/Jauge/Jauge-03-Action-Wilson-Confinement-Python.ipynb`](../../MyIA.AI.Notebooks/Physique/Jauge/Jauge-03-Action-Wilson-Confinement-Python.ipynb) (§8).
- Licence et attributions : `LICENSE`, `NOTICE`, `THIRD_PARTY.md` du dépôt source.
- Issue de rattachement : #25826 · parent #23161.
