# KNOTS — théorie des nœuds, du récit au lac

Sous-série de la série [Lean](../README.md) (décision de gradation #17545, 24/09) : la théorie des nœuds descend ici avec son lac [`knot_lean`](knot_lean/README.md). L'arc interne va du récit mathématique (Conway, la sliceness du nœud 11n34 et la preuve de Piccirillo) vers le lac réel : chaque carnet finit par interroger les déclarations `Knots.*` qui vivent dans ce dossier.

La série principale garde son tutoriel (numéros 1 à 14) et ses hommages (16a pour Conway l'homme) ; le présent dossier porte l'arc nœuds. Les numéros de la table ci-dessous renvoient à l'ancien identifiant de série (`Lean-17a` → `KNOTS-01`, etc. — table de correspondance dans `docs/reference/rename-ledger.tsv`).

**Escalier depuis la série principale** : [Lean-16a — Conway, l'homme et l'œuvre](../Lean-16a-Conway-Man-and-Work.ipynb) présente Conway ; KNOTS-01 en explore la face cachée (le nœud de Conway, la question de sa sliceness ouverte 50 ans, résolue par Lisa Piccirillo en moins d'une semaine).

| Carnet | Contenu | Durée |
|---|---|---|
| [KNOTS-01-Conway-Proofs-Lean-Python](KNOTS-01-Conway-Proofs-Lean-Python.ipynb) | Conway et la théorie des nœuds : le nœud de Conway (11n34), Fox 3-colorabilité, mutants, la preuve de sliceness de Piccirillo (2020) et la question connexe de Lidman (2026) — interrogation de `Conway.lean` et `Lidman.lean` du lac | ~45 min |
| [KNOTS-02-Invariants-Python](KNOTS-02-Invariants-Python.ipynb) | Compagnon calculatoire : invariants de nœuds présentés dans KNOTS-01, calculés et vérifiés en Python open source (SnapPy, matplotlib) ; le jumeau formel de ces invariants vit dans `knot_lean` | ~30 min |
| [KNOTS-03-Companion-Formel-Lean-Python](KNOTS-03-Companion-Formel-Lean-Python.ipynb) | Compagnon formel : le lac `knot_lean` par ses déclarations — les modules que KNOTS-01 ne cite pas (`Basic.lean`, structures fondamentales), paires i18n FR/EN et intégrité des jumeaux | ~30 min |

**Prérequis d'entrée** : le tutoriel de la série principale (numéros 1 à 6, tactiques et Mathlib) ; la lecture de [Lean-16a](../Lean-16a-Conway-Man-and-Work.ipynb) donne le contexte humain, sans être bloquante.

**Statut du lac** : `knot_lean` est en research-HOLD théorie des nœuds (#2874) — baseline sorry réelle 8, synchronisée avec `lean-knot.yml` et `LEAN_INVENTORY.md` (cf. `knot_lean/README.md`, table des sorries).
