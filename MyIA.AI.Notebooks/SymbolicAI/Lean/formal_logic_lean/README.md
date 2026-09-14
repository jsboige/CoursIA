# formal_logic_lean — pont Tweety ↔ Lean et logique de prouvabilité

Lake du companion `Lean-3b-Formalized-Formal-Logic.ipynb` : le notebook exécute
les formules avec le vrai raisonneur Tweety (JVM via jpype), ce lake certifie les
mêmes formules avec le noyau Lean via la bibliothèque
[Formalized Formal Logic](https://github.com/FormalizedFormalLogic/Foundation).

## Dépendances (CONSUMER_PINNÉ, verdict #15520)

| Dépendance | Pin | Rôle |
|---|---|---|
| `FormalizedFormalLogic/Foundation` | `81810b9f` | syntaxe/sémantique propositionnelles et métathéorie arithmétique |
| `FormalizedFormalLogic/ProvabilityLogic` | `01628c51` | calcul GL, modèles de Kripke finis, points fixes et interprétation arithmétique |
| `mathlib4` | `v4.33.1` | transitif commun et toolchain du lake |

Aucun module upstream n'est vendu ou adapté ici : les deux bibliothèques sont
consommées à des commits exacts. Le nom Lake `Foundation`, sensible à la casse,
est déclaré à la racine afin que le pin `81810b9f` remplace bien la dépendance
transitive de même nom de `ProvabilityLogic`, plutôt que de cloner deux copies.

Le verdict du pilote #15916 est **CONSUMER_PINNÉ** : l'API upstream suffit sans
port ni adaptation locale. La fermeture propositionnelle historique reste légère
(17 modules, mesure du pilote #15520). Le fragment GL modal a compilé 1107 jobs ;
le module `FormalLogic.GLBridge`, puis le lake complet avec sa fermeture
arithmétique, ont compilé respectivement 1356 et 1361 jobs. L'import arithmétique
est volontairement isolé dans `GLBridge` : il apporte les développements
FirstOrder, Arithmetic et Incompleteness nécessaires au théorème de correction
arithmétique.

`Foundation` et `ProvabilityLogic` déclarent Apache-2.0. Deux dépendances
transitives nouvelles, `Forgive@32667a19` et `LeanTypst@888d8656`, ne portent
aucun fichier de licence racine détecté à ces pins. Elles ne sont pas vendues
dans CoursIA, mais ce caveat doit être levé avant toute redistribution autonome
de la fermeture complète.

## Structure

- `FormalLogic/Bridge.lean` — les formules du notebook (`φPeirce`, `φOr`),
  les quatre lignes de la table de vérité comme théorèmes d'évaluation
  (`simp [models_iff_val, val]` — la sémantique FFL est Prop-valuée,
  `Valuation α := α → Prop`, un `decide` y est structurellement impossible),
  `peirce_valid` (validité par exhaustivité de la table), le contre-modèle
  `or_not_valid`, le contrôle négatif satisfiable-non-valide, et
  `peirce_provable` (versant preuve, reprise de `FFL.Entailment.peirce`).
- `FormalLogic/GLBridge.lean` — le schéma de Löb dérivé dans le calcul de
  Hilbert, une instance concrète de membership, la disponibilité de la décision
  GL sans `native_decide`, un contre-modèle fini certifiant que `¬□⊥` n'est pas
  un théorème, une spécialisation du point fixe de de Jongh–Sambin et le pont
  vers la correction arithmétique sous les conditions de Hilbert–Bernays–Löb.

La procédure de décision GL est exposée comme instance `Decidable`. Sur le
schéma concret de Löb, sa réduction par `decide` reste bloquée dans la réduction
noyau de `search0`; le certificat de membership utilise donc la dérivation de
Hilbert. Le projet n'emploie pas `native_decide`, interdit par l'audit d'axiomes.

## Build

```bash
cd MyIA.AI.Notebooks/SymbolicAI/Lean/formal_logic_lean
lake exe cache get   # oleans Mathlib 4.33.1
lake build
```

Voir aussi : `Lean-3b-Formalized-Formal-Logic.ipynb` (le notebook),
`../Tweety/Tweety-5d-Stable-Synthesis-Lean.ipynb` (le patron générateur →
certificat), `../../../docs/lean/` (pièges tactiques).
