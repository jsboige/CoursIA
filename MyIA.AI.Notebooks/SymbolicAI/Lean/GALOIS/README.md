# GALOIS — le problème inverse de Galois, M₂₃ refermé

Sous-série de la série [Lean](../README.md) — **îlot à une entrée** de la gradation #17545 (décision du 24/09, note de conception c.6408913452) : le problème inverse de Galois descend ici avec son lac [`galois_lean`](galois_lean/README.md). Pas de capstone dédié (décision du 11/10 : le capstone reste MIMO-only) — l'îlot se réduit à son carnet et à son lac, le lac y est exposé en entier (sections 3-4 et annexes A-B du carnet).

L'ancien identifiant de série (`Lean-22` → `GALOIS-01`) est consigné dans `docs/reference/rename-ledger.tsv`.

**Escalier depuis la série principale** : l'entrée se fait depuis [MIMO-04 — Capstone](../MIMO/MIMO-04-Capstone-Digestion-Python.ipynb), sortie de la sous-série MIMO ; l'îlot se referme sur GALOIS-01 et le parcours principal reprend à [Lean-23 (ERC-20)](../Lean-23-ERC20-Invariant-Companion.ipynb).

| Carnet | Contenu | Durée |
|---|---|---|
| [GALOIS-01-Probleme-Inverse-M23-Python](GALOIS-01-Probleme-Inverse-M23-Python.ipynb) | Le problème inverse de Galois refermé (arXiv:2608.08538, 9 août 2026) : M₂₃ prouvé simple d'ordre 10 200 960 **à l'écran** (`card_M23`/`simple_M23` exécutés, `#print axioms` = liste blanche), design de Witt S(4,7,23) vérifié des deux côtés (253 heptades), polynôme f₁ de degré 23 manipulé pour de vrai (empreinte, irréductibilité, discriminant 383 chiffres, Frobenius mod p) — les deux énoncés distingués : prouvé vs cité | 45 min |

**Prérequis d'entrée** : Python 3 (NumPy, sympy). Le lac `galois_lean` est résolu par `find_lean_project` — le lac est frère du carnet dans l'îlot, aucune configuration manuelle.

**Statut du lac** : `galois_lean` est **sorry-free** (mode `real` : 0 `sorry` tactique, 0 `native_decide`, 0 `axiom` déclaré) — preuve M₂₃ *vendored* Apache-2.0 depuis [`KitaKen1/finite-simple-groups-lean`](https://github.com/KitaKen1/finite-simple-groups-lean), axiomes `{propext, Classical.choice, Quot.sound}` (whitelist §B), gardé par la CI `lean-galois.yml`. Détail : [`galois_lean/README.md`](galois_lean/README.md).
