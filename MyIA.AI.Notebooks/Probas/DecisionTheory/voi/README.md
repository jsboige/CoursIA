# VoI cross-engine — Infer.NET × PyMC × Lean sur un contrat JSON commun

Tranche 3/3 de l'acceptance cross-engine #13569 (VOI / valeur de l'information).
Le notebook DecInfer-06 (`DecInfer/`) calcule la VOI avec Infer.NET, DecPyMC-5
(`PyMC/`) avec PyMC — mais jamais sur le **même problème au même moment** avec
comparaison des sorties. Ce répertoire ferme ce trou : **un contrat JSON,
deux adaptateurs indépendants, un comparateur** qui exécute les deux et
journalise l'accord/désaccord **depuis leurs sorties**, jamais depuis des
constantes.

Une **troisième colonne** (#22374) porte la valeur **exacte** de l'organe Lean
`Bayesian.InformationNoisy` (lake `lean_game_defs_ext`) : conversion du contrat
en poids joints entiers par Fractions (aucun flottant), puis théorèmes de
valeur **décidés par le kernel**. Là où les deux moteurs s'écartent de 204 EUR
sur l'EVSI, la colonne Lean donne la valeur entière — la tolérance sert à
comparer, pas à absoudre.

## Structure

| Élément | Rôle |
|---|---|
| `problems/forage-petrolier.json` | Problème de forage extrait de DecInfer-06 cell. 32/35 + DecPyMC-5 cell. 33 (contrôle discriminant) |
| `problems/forage-non-informatif.json` | Contrôle négatif : vraisemblance indépendante de l'état → EVSI = 0 |
| `InferNetVoi/` | Adaptateur C# : **Infer.NET réel** (`Microsoft.ML.Probabilistic`) infère les postérieurs de chaque signal et les marginales du signal |
| `pymc_voi.py` | Adaptateur Python : **PyMC réel** échantillonne le même modèle génératif (prior predictive seedé, conditionnement empirique) |
| `lean_bridge.py` | Pont **Probas → Lean** : conversion exacte du contrat, émission du fichier de vérification, exécution par le kernel (`scripts/lean/lean_exec.py`), comparaison aux deux moteurs |
| `run_comparison.py` | Runner : exécute les deux moteurs, produit la table accord/désaccord + vérifie les contrôles sur les valeurs mesurées, et ajoute la colonne Lean |
| `tests/` | Tests pytest (contrat, comparateur, adaptateur PyMC, pont Lean et ses cinq contrôles) |
| `comparison.json` | Sortie du dernier run de comparaison (artefact de preuve, colonne Lean incluse) |

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

## Sorties (identiques pour les moteurs du banc)

`eu_no_info`, `action_no_info`, `evpi`, `evsi_brute`, `evsi_nette`
(= brute − `test_cost`), `decision` (`observer` si nette > 0, sinon
`agir_sans_test`), plus les quantités inférées (`posteriors`,
`signal_marginals`) pour audit. La colonne Lean porte les mêmes grandeurs,
calculées en entiers puis divisées par l'échelle exacte du contrat
(`scaled.no_info`, `scaled.signal`, `scaled.perfect`, `scaled.scale`), avec le
verdict du kernel sous `kernel.rc`.

## Tolérances (écrites, divergence rapportée sans lissage)

| Quantité | Tolérance absolue | Justification mesurée |
|---|---|---|
| Utilités (EUR) | 20 000 | Infer.NET (EP exact sur Bernoulli conjugué) rend les valeurs exactes ; PyMC (200k draws, seed 42) écarte de 204 EUR sur EVSI — la tolérance couvre >10× ce bruit |
| Probabilités | 0,01 | Écart maximal observé : 0,0013 sur P(pétrole\|négatif) |

## Utilisation

```bash
python run_comparison.py                # deux moteurs + colonne Lean + compare
python run_comparison.py --lean-only    # recolle la colonne Lean sans relancer
                                        #   les deux moteurs (lit comparison.json)
python run_comparison.py --skip-lean    # sans la colonne Lean (toolchain absente)
python lean_bridge.py problems/forage-petrolier.json --run   # pont seul
python -m pytest tests/ -q              # tests (contrat, comparateur, PyMC, Lean)
```

La colonne Lean exige `scripts/lean/lean_exec.py` et le lake
`GameTheory/lean_game_defs_ext`. Toolchain absente : la comparaison se poursuit
sur les deux moteurs et le runner **le dit** (`colonne lean ABSENTE`) — le
contrôle n'est jamais blanchi en silence ; l'installation est le geste attendu.

## Ce que ce répertoire n'est pas

Pas un remplacement des notebooks pédagogiques : un **socle exécutable** qui
prouve l'accord des moteurs sur le même problème, réutilisable par la série pour
toute évolution du contrat. Le seul notebook touché l'est par **exposition** :
DecInfer-06 section 9 exécute le pont et affiche les valeurs exactes du kernel ;
les 54 cellules d'origine gardent leur **source inchangée**, la notebook ayant
été ré-exécutée intégralement (règle C.2).
