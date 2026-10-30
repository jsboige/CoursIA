# VoI cross-engine — Infer.NET × PyMC sur un contrat JSON commun

Tranche 3/3 de l'acceptance cross-engine #13569 (VOI / valeur de l'information).
Le notebook DecInfer-06 (`DecInfer/`) calcule la VOI avec Infer.NET, DecPyMC-5
(`PyMC/`) avec PyMC — mais jamais sur le **même problème au même moment** avec
comparaison des sorties. Ce répertoire ferme ce trou : **un contrat JSON,
deux adaptateurs indépendants, un comparateur** qui exécute les deux et
journalise l'accord/désaccord **depuis leurs sorties**, jamais depuis des
constantes.

## Structure

| Élément | Rôle |
|---|---|
| `problems/forage-petrolier.json` | Problème de forage extrait de DecInfer-06 cell. 32/35 + DecPyMC-5 cell. 33 (contrôle discriminant) |
| `problems/forage-non-informatif.json` | Contrôle négatif : vraisemblance indépendante de l'état → EVSI = 0 |
| `InferNetVoi/` | Adaptateur C# : **Infer.NET réel** (`Microsoft.ML.Probabilistic`) infère les postérieurs de chaque signal et les marginales du signal |
| `pymc_voi.py` | Adaptateur Python : **PyMC réel** échantillonne le même modèle génératif (prior predictive seedé, conditionnement empirique) |
| `run_comparison.py` | Runner : exécute les deux moteurs, produit la table accord/désaccord + vérifie les contrôles sur les valeurs mesurées |
| `lean_voi_adapter.py` | Adaptateur vers l'organe formel : convertit les mêmes contrats en une `NoisyProblem` du lake `lean_game_defs_ext` (fractions exactes, refus explicites), et émet la source Lean des instances |
| `tests/` | Tests pytest (contrat, comparateur, adaptateur PyMC, adaptateur Lean) |
| `comparison.json` | Sortie du dernier run de comparaison (artefact de preuve) |

## Le contrat JSON

Objets **imbriqués partout, aucune matrice** — chaque adaptateur mappe
explicitement vers sa convention interne (C# `Utilities[action, state]`,
Python `U[state, action]`) : l'ambiguïté d'axes ne peut pas surgir.

```json
{
  "states": ["petrole", "pas_petrole"],
  "priors": {"petrole": 0.3, "pas_petrole": 0.7},
  "actions": ["forer", "vendre"],
  "utilities": {"forer": {"petrole": 1500000, "pas_petrole": -500000}, ...},
  "signals": ["positif", "negatif"],
  "likelihood": {"positif": {"petrole": 0.9, "pas_petrole": 0.2}, ...},
  "test_cost": 60000
}
```

`likelihood[signal][etat]` = P(signal | état). Portée : **contrat binaire**
(2 états × 2 signaux), fidèle aux notebooks sources.

## Sorties (identiques pour les deux moteurs)

`eu_no_info`, `action_no_info`, `evpi`, `evsi_brute`, `evsi_nette`
(= brute − `test_cost`), `decision` (`observer` si nette > 0, sinon
`agir_sans_test`), plus les quantités inférées (`posteriors`,
`signal_marginals`) pour audit.

## Tolérances (écrites, divergence rapportée sans lissage)

| Quantité | Tolérance absolue | Justification mesurée |
|---|---|---|
| Utilités (EUR) | 20 000 | Infer.NET (EP exact sur Bernoulli conjugué) rend les valeurs exactes ; PyMC (200k draws, seed 42) écarte de 204 EUR sur EVSI — la tolérance couvre >10× ce bruit |
| Probabilités | 0,01 | Écart maximal observé : 0,0013 sur P(pétrole\|négatif) |

## Utilisation

```bash
python run_comparison.py                # exécute les deux moteurs + compare
python -m pytest tests/ -q              # tests (contrat, comparateur, PyMC)
```

## Troisième comparaison : la valeur exacte en Lean

Les deux moteurs infèrent ou échantillonnent ; aucun ne dit quelle est la bonne
réponse. `lean_voi_adapter.py` transpose les **mêmes** fichiers
`problems/*.json` dans l'organe formel
(`MyIA.AI.Notebooks/GameTheory/lean_game_defs_ext/Bayesian/VoiBench.lean`) et
fait calculer la valeur exacte par le noyau Lean.

- **Conversion documentée** : poids joints `prior × vraisemblance` mis à
  l'échelle par `Lp`, utilités par `Lu`, coût par `Lp × Lu`. Aucun arrondi : le
  JSON est lu en fractions exactes (`Fraction`), et les deux facteurs restent
  distincts — mettre les utilités à l'échelle des probabilités multiplierait la
  valeur par `Lp` au carré et rendrait le nombre Lean inutilisable comme
  contrôle.
- **Refus explicites plutôt que blanchiment** : poids négatif, prior ou
  vraisemblance qui ne somme pas exactement à 1, clé manquante, coût négatif.
  Un **signal impossible** (masse nulle) n'est pas un refus : sa contribution
  vaut exactement zéro.
- **Parité garantie** : un test compare le bloc d'instances du module Lean à la
  sortie courante de l'adaptateur, et les nombres des théorèmes à l'évaluation
  exacte. Éditer une instance Lean à la main fait rougir.

Résultat sur le forage informatif : **253 000 EUR** d'EVSI brute. Infer.NET rend
cette valeur exactement ; PyMC s'en écarte de 204 EUR. L'écart est mesurable
comme bruit d'échantillonnage **parce que** la valeur exacte existe
indépendamment des deux moteurs. Sur le contrôle négatif, la table est factorisée
et le zéro est certifié par le théorème d'Evans, puis retrouvé par `decide` —
deux instruments indépendants l'un de l'autre.

```bash
python lean_voi_adapter.py problems/*.json            # valeurs exactes, deux échelles
python lean_voi_adapter.py problems/*.json --emit     # source Lean des instances
```

## Ce que ce répertoire n'est pas

Pas un remplacement des notebooks pédagogiques (aucun modifié — cf claim
#13569) : un **socle exécutable** qui prouve l'accord des deux moteurs sur le
même problème, réutilisable par la série pour toute évolution du contrat.
