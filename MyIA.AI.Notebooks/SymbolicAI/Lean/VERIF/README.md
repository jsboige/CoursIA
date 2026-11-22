# VERIF — Vérification formelle (invariants, cohérence, limites)

Sous-série de la série [Lean](../README.md) — **îlots de vérification formelle** de la gradation #17545 : les carnets qui ne se contentent pas de **déclarer** une propriété, mais l'**exhibent** — un invariant de conservation mesuré sur un état concret, un témoin de Dutch book qui certifie l'absence de livre, des limites de calculabilité certifiées au noyau — en lecture statique Python et en exécution **native** (kernel `lean4-wsl`, `#check` / `#eval` / `#print axioms`). Le fil rouge : **la preuve est un témoin, pas une assertion** — qu'un énoncé *type-checke* n'est pas la même chose qu'il soit *résolu*, et un axiome se compte, il ne se suppose pas.

Les anciens identifiants (ex. `Lean-23` → `VERIF-02`, `Lean-34b` → `VERIF-07`) sont consignés dans `docs/reference/rename-ledger.tsv`.

## Le fil

| Carnet | Contenu | Durée |
|---|---|---|
| [VERIF-01-Confiance-Preuves-Native](VERIF-01-Confiance-Preuves-Native.ipynb) | La fiabilité d'un certificat formel, piste Dougherty/von Hippel 2026 (*Lies, Damned Lies, and Proofs*) : une mis-définition rendant la preuve trivialement vraie, les axiomes de secours mesurés par `#print axioms` (`sorryAx` transitif, `native_decide`, `Classical.choice` whitelisté par nom), l'implosion depuis `False` (0 axiome) — kernel `lean4-wsl`, lake `mathlib_examples`, 3 exercices | 30 min |
| [VERIF-02-ERC20-Invariant-Companion](VERIF-02-ERC20-Invariant-Companion.ipynb) | L'invariant de conservation d'un jeton ERC-20 (`Σ balances = totalSupply`) : traces jouets en Python, lectures statiques des 17 déclarations du lake `erc20_lean`, propreté axiomatique par absence de `sorry`, Monte-Carlo sur la tolérance numérique (#11710) — kernel `python3` | 40 min |
| [VERIF-03-Lean-ERC20-Native-Companion](VERIF-03-Lean-ERC20-Native-Companion.ipynb) | Compagnon **natif** (kernel `lean4-wsl`) du lake `erc20_lean` : les 17 déclarations **résolues par le kernel** (`#check`), l'invariant et les transitions `mint`/`burn`/`transfer` **évalués** sur un état concret (`by decide`), `#print axioms` natif sur les 5 théorèmes phares, la pyramide op → trace `Reachable` → invariant type-checkée avec ses gardes (#11721) | 30 min |
| [VERIF-04-Calibration-Native-Companion](VERIF-04-Calibration-Native-Companion.ipynb) | Compagnon **natif** (kernel `lean4-wsl`) du lake `calibration_lean` : les cibles de calibration du prouveur multi-agents (Epic #1453, P1-P5) importées et exécutées — chaque définition/théorème interrogé par `#check`/`#eval`/`#print axioms`, sorties du compilateur Lean | 35 min |
| [VERIF-05-Coherence-et-Temoin](VERIF-05-Coherence-et-Temoin.ipynb) | Cohérence de de Finetti et témoin (Dutch book) : miroir Python **exact** (`fractions.Fraction`) du lake `decision_theory_lean` — un livret encaisse l'écart d'inclusion-exclusion uniformément dans les 4 états, balayage borné exhaustif (390,625 combinaisons, sorties du carnet : `{combis:,}` sur `[-12,12]^4`) qui certifie l'absence de livre sur le système réparé, stabilité affine vNM mesurée — kernel `python3` | 40 min |
| [VERIF-06-Calculabilite-et-Limites](VERIF-06-Calculabilite-et-Limites.ipynb) | **Tranche E** de l'Epic #15066 : calculabilité, diagonalisation et limites — témoins exécutables (diagonale de l'arrêt bornée, point fixe diagonal) puis certification au noyau via le lake `formal_logic_lean` : Church, arrêt→incomplétude, Gödel I/II, Rosser, Tarski et Löb, `#check`/`#print axioms` audités — kernel `python3`, 3 exercices | 45 min |
| [VERIF-07-FairBot-Loeb](VERIF-07-FairBot-Loeb.ipynb) | Approfondissement de [VERIF-06](VERIF-06-Calculabilite-et-Limites.ipynb) : FairBot et le théorème de Löb appliqués au dilemme du prisonnier en un coup (Barasz et al. 2014), sur trois niveaux — témoin syntaxique, interface modale L2, module L3 `FormalLogic.FairBotLoeb` où Löb est un théorème de FFL ; coopération, inexploitabilité, défection vraie mais non prouvable, `#check`/`#print axioms` — kernel `python3`, 3 exercices | 60 min |

## À qui, et d'où

**Entrée** : les carnets de la série parente [Lean](../README.md) qui ont déjà posé la distinction *type-checker* vs *résolvant* et le rôle du `sorry` comme marqueur de dette.

**Sortie** : [Lean-26-Munkres-Tribute](../Lean-26-Munkres-Tribute.ipynb) et au-delà, ou les autres îlots de la gradation #17545 (GALOIS, Langlands, GROTH, ANALYSE).

**Prérequis d'entrée** : les deux compagnons ERC-20 (VERIF-02 puis VERIF-03) forment le cœur et suffisent à la première lecture ; VERIF-05/06/07 reprennent le vocabulaire de la logique formelle (théorème, axiome, témoin) sans l'avoir formalisé.

## Statut

Carnets **exécutés** : les cellules code tournent sans erreur (les trois compagnons natifs exigent le kernel `lean4-wsl` et le lake correspondant). Le décompte des cellules figure au catalogue (`COURSE_CATALOG.generated.json`).
