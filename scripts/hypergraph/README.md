# `scripts/hypergraph/` — réécriture d'hypergraphes (pli 5)

Instruments et verdicts du pli 5 de l'Epic Origami-Wolfram (#19742, issue #23093).
Même rôle que `scripts/hashlife/` pour les plis 3 à 9 : les mesures d'un pli vivent
ici comme instruments et verdicts, vérifiables, avant d'être portées à un lecteur
par un carnet.

## Contenu

| Fichier | Rôle |
|---|---|
| `SETREPLACE-VERDICT.md` | Le verdict d'outil (grain A) : `RECOVERABLE-LOCAL`, avec les trois branches, les preuves et les limites |
| `setreplace_pypi_control.py` | Contrôle de correction du paquet **tiers** `setreplace` de PyPI, exécutable seul |
| `setreplace_pypi_control.json` | Rapport de la dernière exécution (19/19 cas) |
| `libsetreplace_build_proof.txt` | Sortie verbatim de la construction et des tests du cœur **officiel** `libSetReplace` |

## État

Le verdict est rendu : le cœur C++ officiel `libSetReplace` (MIT) se construit et
passe ses 17 tests sans Wolfram Engine. Les grains B (exposant d'échelle du
multiway) et C (structure causale, pont Gorard) ne sont donc pas bloqués par une
décision de mainteneur.

Rien ici n'est encore un carnet : l'hôte du carnet reste à argumenter et à
trancher au design-gate, comme l'exige l'issue.

## Vérifier

```bash
python -m pip install setreplace==0.2.0
python scripts/hypergraph/setreplace_pypi_control.py
```

Sortie attendue : `RESUME: 19/19 cas PASS`, code de sortie 0.
