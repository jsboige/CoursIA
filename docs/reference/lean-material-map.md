<!-- fichier genere par scripts/lean/lean_material_map.py -- ne pas editer a la main ; relancer le generateur -->

# Carte du materiel Lean du depot

Une ligne par lac. Les colonnes sont des mesures rejouables, pas des appreciations : `Modules` compte les fichiers `.lean` propres du lac, `Miroirs` les freres `_en`, `Naissance` la date du commit qui a ajoute le `lakefile` a son chemin actuel -- un fichier re-ajoute y prend la date de son re-ajout, la colonne ne remonte pas plus loin que git. La colonne `Gate axiomes` reprend le verdict de `scripts/lean/check_axiom_gate_coverage.py`. Les deux colonnes de conformite -- `Site = consommateur` (R1) et `Doublons declares` (R4) -- sont definies dans `docs/reference/lean-lakes-doctrine.md` et mesurees plus bas.

Cette page est regeneree par `scripts/lean/lean_material_map.py`. Une table recopiee a la main derive au premier merge : c'est la maladie que #23097 soigne, et `--check` est le garde-fou.

`sans gate` n'est pas un defaut : la couverture est une mesure, pas un verdict de surete (#17097 critere 3). Un lac sans gate doit seulement etre **connu** comme tel.

| Lac | Modules | Miroirs | CI | Gate axiomes | Site = consommateur | Doublons declares | Naissance |
|---|---|---|---|---|---|---|---|
| `MyIA.AI.Notebooks/SymbolicAI/Lean/GROTH/grothendieck_lean` | 100 | 98 | declare | couverte | 1 hors site (4 carnets) | - | 2026-05-31 |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/GOL/conway_lean` | 57 | 41 | declare | couverte | 1 hors site (9 carnets) | 0 / 2 | 2026-05-28 |
| `MyIA.AI.Notebooks/GameTheory/game_theory_lean` | 42 | 26 | declare | couverte | ok (4) | 1 / 3 | 2026-07-10 |
| `MyIA.AI.Notebooks/Search/discrepancy_lean` | 34 | 26 | declare | couverte | ok (1) | - | 2026-08-25 |
| `MyIA.AI.Notebooks/ML/learning_theory_lean` | 32 | 30 | declare | couverte | 1 hors site (5 carnets) | - | 2026-06-25 |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/KNOTS/knot_lean` | 25 | 24 | declare | couverte | non consomme | - | 2026-10-08 |
| `MyIA.AI.Notebooks/Compression/Compression_lean` | 15 | 2 | declare | couverte | ok (1) | - | 2026-10-12 |
| `MyIA.AI.Notebooks/GameTheory/lean_game_defs_ext` | 15 | 14 | declare | couverte | ok (1) | - | 2026-06-10 |
| `MyIA.AI.Notebooks/Probas/DecisionTheory/decision_theory_lean` | 15 | 14 | declare | couverte | ok (2) | - | 2026-10-02 |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/sensitivity_lean` | 12 | 10 | declare | couverte | ok (4) | - | 2026-05-15 |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/tegmark_muh_lean` | 11 | 0 | declare | couverte | ok (1) | - | 2026-09-21 |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Langlands/hecke_lean` | 9 | 8 | declare | couverte | ok (1) | - | 2026-11-02 |
| `MyIA.AI.Notebooks/Probas/Applications/Percolation/percolation_lean` | 8 | 7 | declare | couverte | 1 hors site (4 carnets) | - | 2026-09-06 |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/formal_logic_lean` | 8 | 0 | declare | couverte | 1 hors site (5 carnets) | 0 / 2 | 2026-09-11 |
| `MyIA.AI.Notebooks/SymbolicAI/Tweety/argumentation_lean` | 8 | 6 | declare | couverte | ok (1) | - | 2026-06-24 |
| `MyIA.AI.Notebooks/GameTheory/assignment_lean` | 7 | 6 | declare | couverte | 1 hors site (3 carnets) | - | 2026-08-23 |
| `MyIA.AI.Notebooks/Search/search_lean` | 7 | 6 | declare | couverte | ok (1) | - | 2026-07-09 |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Geometry/geometry_lean` | 7 | 0 | declare | couverte | non consomme | - | 2026-10-04 |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/serre100_lean` | 7 | 6 | declare | couverte | 1 hors site (2 carnets) | - | 2026-09-19 |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/mimo_lean` | 7 | 6 | declare | couverte | ok (2) | - | 2026-08-15 |
| `MyIA.AI.Notebooks/GameTheory/asymmetric_information_lean` | 6 | 6 | declare | couverte | ok (2) | - | 2026-08-26 |
| `MyIA.AI.Notebooks/GameTheory/lean_game_defs` | 6 | 6 | declare | couverte | non consomme | 1 / 1 | 2026-06-10 |
| `MyIA.AI.Notebooks/QuantConnect/kelly_lean` | 6 | 5 | declare | couverte | ok (1) | - | 2026-06-24 |
| `MyIA.AI.Notebooks/Sudoku/sudoku_lean` | 6 | 5 | declare | couverte | ok (14) | - | 2026-06-24 |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/calibration_lean` | 6 | 5 | declare | couverte | ok (4) | 0 / 2 | 2026-05-29 |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/formal_groups_lean` | 6 | 5 | declare | couverte | ok (1) | - | 2026-09-06 |
| `MyIA.AI.Notebooks/GameTheory/minimax_lean` | 5 | 4 | declare | couverte | ok (1) | - | 2026-06-24 |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/GALOIS/galois_lean` | 5 | 2 | declare | couverte | ok (1) | - | 2026-10-31 |
| `MyIA.AI.Notebooks/SymbolicAI/SmartContracts/erc20_lean` | 5 | 4 | declare | couverte | 1 hors site (2 carnets) | - | 2026-06-24 |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/ANALYSE/kls_lean` | 4 | 0 | hors CI | hors matrice | non consomme | - | 2026-10-08 |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Riemann200/riemann200_lean` | 4 | 0 | declare | couverte | non consomme | - | 2026-10-18 |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/mathlib_examples` | 4 | 2 | declare | couverte | non consomme | - | 2026-01-29 |
| `MyIA.AI.Notebooks/SymbolicAI/Planners/planning_lean` | 4 | 3 | declare | couverte | ok (1) | - | 2026-06-24 |
| `MyIA.AI.Notebooks/IIT/iit_lean` | 3 | 1 | declare | couverte | ok (4) | - | 2026-10-24 |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/differential_lean` | 3 | 2 | hors CI | hors matrice | non consomme | - | 2026-10-07 |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/finiteness_lean` | 3 | 1 | declare | couverte | non consomme | - | 2026-06-15 |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/torchlean_lean` | 3 | 0 | hors CI | hors matrice | ok (1) | - | 2026-10-22 |
| `MyIA.AI.Notebooks/GameTheory/conway_cgt_lean` | 2 | 1 | declare | sans gate | ok (1) | - | 2026-06-05 |
| `MyIA.AI.Notebooks/GameTheory/SocialChoice/social_choice_lean_peters` | 0 | 0 | declare | vendu | non consomme | - | 2026-10-05 |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/agent_tests/prover/session_state/reference_docs/stable_marriage/upstream` | 0 | 0 | hors CI | vendu | non consomme | - | 2026-05-16 |
| `docs/lean/darksnail/build-evidence-2026-10-31` | 0 | 0 | hors CI | hors matrice | non consomme | - | 2026-10-31 |

## Ce que la carte etablit

39 lacs propres, plus 2 dossier vendu. Les lacs hors CI sont listes ci-dessous : ce sont eux qui rendent une consolidation invisible depuis la matrice de build.

### Reconciliation

507 modules + 382 miroirs attribues a un lac + 11 fichiers hors lac + 26 fichiers ecartes (dossier vendu, ou extension `.lean` portee par un fichier qui n'est pas du Lean) = 926 fichiers `.lean` traces, soit la population entiere de `git ls-files '*.lean'`. Un fichier qui n'apparait dans aucune de ces quatre colonnes a ete perdu en route : c'est le defaut que cette reconciliation rend visible.

### Lacs hors CI

Ces lacs existent dans l'arbre et aucun workflow ne les nomme : ni `scripts/lean/ci_lakes.json`, ni un fichier de `.github/workflows/`. Aucun build de matrice ne les couvre.

- `MyIA.AI.Notebooks/SymbolicAI/Lean/ANALYSE/kls_lean` — 4 modules, ne le 2026-10-08
- `MyIA.AI.Notebooks/SymbolicAI/Lean/differential_lean` — 3 modules, ne le 2026-10-07
- `MyIA.AI.Notebooks/SymbolicAI/Lean/torchlean_lean` — 3 modules, ne le 2026-10-22
- `docs/lean/darksnail/build-evidence-2026-10-31` — 0 modules, ne le 2026-10-31

### Lacs de la matrice sans gate d'axiomes

Declares au CI, donc construits, mais le job `lean-axiom` ne les atteint pas : rien ne rougit si un axiome interdit y entre.

- `MyIA.AI.Notebooks/GameTheory/conway_cgt_lean` — 2 modules

### Fichiers `.lean` hors lac

Traces par git, mais dans aucun dossier portant un `lakefile` : ils ne sont construits par aucun lac, et aucune matrice ne les voit.

- `MyIA.AI.Notebooks/GameTheory/examples/arrow_simple.lean`
- `MyIA.AI.Notebooks/SymbolicAI/Lean/examples/basic_logic.lean`
- `MyIA.AI.Notebooks/SymbolicAI/Lean/examples/basic_logic_en.lean`
- `MyIA.AI.Notebooks/SymbolicAI/Lean/examples/llm_assisted_proof.lean`
- `MyIA.AI.Notebooks/SymbolicAI/Lean/examples/llm_assisted_proof_en.lean`
- `MyIA.AI.Notebooks/SymbolicAI/Lean/examples/mathlib_examples.lean`
- `MyIA.AI.Notebooks/SymbolicAI/Lean/examples/mathlib_examples_en.lean`
- `MyIA.AI.Notebooks/SymbolicAI/Lean/examples/quantifiers.lean`
- `MyIA.AI.Notebooks/SymbolicAI/Lean/examples/quantifiers_en.lean`
- `MyIA.AI.Notebooks/SymbolicAI/Lean/examples/tactics_demo.lean`
- `MyIA.AI.Notebooks/SymbolicAI/Lean/examples/tactics_demo_en.lean`

## R1 — le site suit le consommateur

La doctrine demande qu'un lac vive dans le dossier de la (sous-)serie dont les carnets l'importent. La consommation se mesure sur le seul signal objectif disponible sans build : une ligne `import <Module>` d'un carnet, ou `<Module>` est un fichier `.lean` du lac. Les imports de paquets (`Mathlib`, `Batteries`) ne rattachent un carnet a aucun lac -- sans cette restriction, tout carnet Lean consommerait tous les lacs. Un carnet est « au site » quand il vit sous le dossier du lac, « hors site » sinon.

30 lacs sur 39 sont consommes, dont 8 depuis un dossier hors site. Ce n'est pas un defaut en soi : c'est le fait que R1 rend arbitrable, et que la ligne nomme.

- `MyIA.AI.Notebooks/SymbolicAI/Lean/GROTH/grothendieck_lean` — 4 carnets, hors site : `MyIA.AI.Notebooks/SymbolicAI/Lean`
- `MyIA.AI.Notebooks/SymbolicAI/Lean/GOL/conway_lean` — 9 carnets, hors site : `MyIA.AI.Notebooks/SymbolicAI/Lean`
- `MyIA.AI.Notebooks/ML/learning_theory_lean` — 5 carnets, hors site : `MyIA.AI.Notebooks/SymbolicAI/SymbolicLearning`
- `MyIA.AI.Notebooks/Probas/Applications/Percolation/percolation_lean` — 4 carnets, hors site : `MyIA.AI.Notebooks/SymbolicAI/Lean/ANALYSE`
- `MyIA.AI.Notebooks/SymbolicAI/Lean/formal_logic_lean` — 5 carnets, hors site : `MyIA.AI.Notebooks/SymbolicAI/Tweety`
- `MyIA.AI.Notebooks/GameTheory/assignment_lean` — 3 carnets, hors site : `MyIA.AI.Notebooks/SymbolicAI/Lean/ANALYSE`
- `MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/serre100_lean` — 2 carnets, hors site : `MyIA.AI.Notebooks/SymbolicAI/Lean`
- `MyIA.AI.Notebooks/SymbolicAI/SmartContracts/erc20_lean` — 2 carnets, hors site : `MyIA.AI.Notebooks/SymbolicAI/Lean`

## R4 — les doublons de theoreme, et leur declaration

Un nom de `theorem`/`lemma` porte par deux lacs est un doublon au sens de la doctrine. Il est **declare** quand chaque occurrence porte le renvoi croise qui nomme l'autre maison dans sa docstring ; une seule occurrence muette laisse le doublon non declare. La colonne « par cote » se lit par lac : elle localise le cote qui manque au renvoi, la colonne « occurrences » restant le total des deux. Le renvoi compte quand il **nomme le lac** ; un lien conceptuel formule autrement ne compte pas — c'est une definition de la mesure, pas un jugement sur la qualite du lien.

La colonne « nature » compare la **formulation**, pas le resultat, et cet écart est deliberate : une « formulation identique » est un resultat prouve deux fois, sans ambiguite ; une « formulation differente » ne tranche rien et demande un regard de domaine, parce que deux encodages d'un meme theoreme y tombent au meme titre que deux enonces sans rapport. La tete comparee est ce qui suit le nom sur la ligne de declaration — une comparaison de premiere ligne, qui ne conclut pas quand l'enonce passe a la ligne.

| Theoreme | Lacs | Occurrences | Citent l'autre maison | Par cote | Nature | Verdict |
|---|---|---|---|---|---|---|
| `dayOfWeek_add_seven` | `conway_lean`, `calibration_lean` | 4 | 0 | conway_lean 0/2, calibration_lean 0/2 | formulation identique | non declare |
| `fairBot_unexploitable` | `game_theory_lean`, `formal_logic_lean` | 3 | 0 | game_theory_lean 0/2, formal_logic_lean 0/1 | formulation differente | non declare |
| `fairBot_vs_defectBot` | `game_theory_lean`, `formal_logic_lean` | 3 | 0 | game_theory_lean 0/2, formal_logic_lean 0/1 | formulation differente | non declare |
| `nimSum_single` | `conway_lean`, `calibration_lean` | 4 | 0 | conway_lean 0/2, calibration_lean 0/2 | formulation identique | non declare |
| `sen_impossibility` | `game_theory_lean`, `lean_game_defs` | 4 | 4 | game_theory_lean 2/2, lean_game_defs 2/2 | formulation differente | declare |

**Cet inventaire sous-compte, et c'est mesure.** La detection est par nom : un meme resultat prouve sous deux noms differents lui echappe. Le controle negatif est `Arrow`, declare des deux cotes (`game_theory_lean/SocialChoice/Arrow.lean` : `arrow` ; `lean_game_defs/SocialChoice.lean` : `arrow_impossibility`), et absent de la table ci-dessus. Un verdict « 0 doublon » ne se lit donc jamais comme « aucun resultat n'est prouve deux fois ». La table ne tranche pas davantage l'identite mathematique : elle compare des formulations, et une « formulation differente » peut etre le meme theoreme encode deux fois — le cas se rencontre dans ce depot, ou une maison abstraite et une maison specialisee prouvent le meme resultat a des generalites differentes. L'organe qui tranche est celui de #24183 (tranche T0) ; cette page en est l'inventaire, pas le juge.

## Regle d'accretion d'un lac

Un lac nouveau dans une serie existante est legitime si (1) sa toolchain diverge de celle du lac de la serie, (2) sa theorie est distincte au sens de la clause anti-god-lake (#4365), ou (3) a toolchain egale il est le compagnon de construction d'un arc numerote de carnets -- importe par au moins un carnet Lean de cet arc, sans import croise avec le lac de la serie, et sans lui imposer une dependance (un path dep d'un lac tiers deviendrait sinon facteur commun). A defaut, c'est un module de plus du lac de la serie.

Verdicts tranches par la mesure (T2 #23097) :

| Lac | Cas | Verdict | Mesure fondatrice |
|---|---|---|---|
| `assignment_lean` | (3) compagnon d'arc | legitime-documente | Arc 16f : `GameTheory-16f-Lean-Assignment-Lean.ipynb` importe `Assignment.KuhnMunkres`. Toolchain et pin Mathlib identiques a `game_theory_lean` (v4.33.0, db584cd6), zero import croise, theorie (affectation hongroise, Kuhn-Munkres) absente des 8 branches du lac de la serie. |
| `asymmetric_information_lean` | (3) compagnon d'arc | legitime-documente | Arc 17b-17e : `GameTheory-17c-Lean-Lemons-Certificat-Lean.ipynb` importe `AsymmetricInformation.Lemons`, `GameTheory-17d-Lean-Screening-Signaling-Lean.ipynb` en importe 4 modules. Path dep non negociable vers `lean_game_defs_ext` (#12848) : la fusion imposerait ce pont aux 38 modules de `game_theory_lean`. Zero import croise. |

Les cas (1) toolchain divergente et (2) theorie distincte sont deja tranches : `social_choice_lean_peters` pour (1) (INTRINSIC #7081), `minimax_lean` et `conway_cgt_lean` pour (2).
