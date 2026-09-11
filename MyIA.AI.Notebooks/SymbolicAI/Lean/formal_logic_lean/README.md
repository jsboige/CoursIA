# formal_logic_lean — pont Tweety ↔ Lean (EPIC #15066, pilote #15520)

Lake du companion `Lean-3b-Formalized-Formal-Logic.ipynb` : le notebook exécute
les formules avec le vrai raisonneur Tweety (JVM via jpype), ce lake certifie les
mêmes formules avec le noyau Lean via la bibliothèque
[Formalized Formal Logic](https://github.com/FormalizedFormalLogic/Foundation).

## Dépendances (CONSUMER_PINNÉ, verdict #15520)

| Dépendance | Pin | Rôle |
|---|---|---|
| `FormalizedFormalLogic/Foundation` | `81810b9f` | syntaxe/sémantique/métathéorie propositionnelles (`Formula`, `val`, `Entailment.Cl`, `Tait.completeness!`) |
| `mathlib4` | `v4.33.1` | transitif de Foundation (et toolchain du lake) |

Aucun module FFL n'est vendu ou adapté ici — l'upstream est importé au commit
exact. La fermeture d'imports de l'API consommée (Propositional + Logic +
Vorspiel) est de **17 modules** (mesure pilote #15520) : les parties lourdes
(FirstOrder, Arithmetic, Incompleteness) ne fuient pas dans ce lake.

## Structure

- `FormalLogic/Bridge.lean` — les formules du notebook (`φPeirce`, `φOr`),
  les quatre lignes de la table de vérité comme théorèmes d'évaluation
  (`simp [models_iff_val, val]` — la sémantique FFL est Prop-valuée,
  `Valuation α := α → Prop`, un `decide` y est structurellement impossible),
  `peirce_valid` (validité par exhaustivité de la table), le contre-modèle
  `or_not_valid`, le contrôle négatif satisfiable-non-valide, et
  `peirce_provable` (versant preuve, reprise de `FFL.Entailment.peirce`).

## Build

```bash
cd MyIA.AI.Notebooks/SymbolicAI/Lean/formal_logic_lean
lake exe cache get   # oleans Mathlib 4.33.1
lake build
```

Voir aussi : `Lean-3b-Formalized-Formal-Logic.ipynb` (le notebook),
`../Tweety/Tweety-5d-Stable-Synthesis-Lean.ipynb` (le patron générateur →
certificat), `../../../docs/lean/` (pièges tactiques).
