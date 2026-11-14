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

## Mesure multiway (grain B)

`MULTIWAY-PROTOCOLE.md` fixe le système, le témoin et le seuil avant le relevé ;
`multiway.cpp` énumère les états avec `HypergraphMatcher::allMatches()` et
vérifie leur contenu à chaque pas. `multiway_results.json` conserve les médianes, extrêmes et l'ajustement de `measure_multiway.py`.

Sur ce relevé, les profondeurs 16 à 48 donnent exactement 17 à 49 états.
L'exposant du temps total en fonction des états finaux est **2,751** (R² =
0,971), sur cinq médianes. La dispersion des durées à 48 pas (0,568 à 1,388 s)
limite la précision : il s'agit d'une observation sur ce programme et cette
machine partagée, pas d'une loi du moteur ni d'une preuve d'irréductibilité.
Le témoin mesure des états distincts d'un système particulier ; il ne compte
pas les histoires qui se rejoignent et ne quotient pas par isomorphisme.
Le temps comprend aussi le contrôle exhaustif ; il ne mesure pas le matcher
isolément. Le pont causal (grain C) et le choix d'hôte restent ouverts.

Pour rejouer avec le cœur officiel, disposer de CMake et d'un compilateur C++17 :

```bash
git clone https://github.com/maxitg/SetReplace.git /tmp/SetReplace
# Épingler le moteur : le relevé utilise exactement cette révision.
git -C /tmp/SetReplace checkout 44c868bf4622e4542b306846ffdcc47c19d0bba8
cmake -S /tmp/SetReplace -B /tmp/setreplace-build -DCMAKE_BUILD_TYPE=Release
cmake --build /tmp/setreplace-build -j 4
c++ -O2 -std=c++17 -I /tmp/SetReplace/libSetReplace scripts/hypergraph/multiway.cpp /tmp/setreplace-build/libSetReplace.a -o /tmp/multiway
python scripts/hypergraph/measure_multiway.py /tmp/multiway --output /tmp/multiway-results.json --raw /tmp/multiway-raw.json
```

Chaque appel de l'exécutable échoue si un seul état diffère du témoin ; le
script rejette aussi une profondeur, un nombre d'états ou un verdict incohérent.

Les 25 mesures brutes de ce relevé sont dans `work/terra30/12-multiway-raw.json`
sur la machine d’exécution ; le JSON versionné en conserve les agrégats. Le
contrôle positif et une faute injectée (suppression de la seconde règle) sont
exécutés avant le relevé. Chaque processus est limité à 512 Mio et 40 secondes ;
le calcul borne aussi la profondeur à 48 et les états à 49.
