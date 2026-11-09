# WOLFRAM-VERDICT-CROSS-CLASSES — mesure falsifiable K_trajectory sur 4 classes

**Suite directe** : [WOLFRAM-VERDICT.md](WOLFRAM-VERDICT.md) (pli 3, c.109) couvre Rule 30 + Rule 110. Ce document pli 4 etend a 4 classes.

**Correction du 2026-10-09** : le verdict initial (`WOLFRAM-4CLASSES-III/IV-INVERSE`, « 2/4 contredisent ») etait mesure a `n_cells = 64`, **sous le plancher de cadrage zlib**. Hors saturation, R30 et R110 se separent et la contradiction tombe a 1/4.

## Perimetre

Mesure `K_trajectory` (compression LZ fenetree, instrument `scripts/hashlife/k_trajectory.py --mode wolfram-4classes`) sur les 4 classes canoniques de Wolframe (Wolfram 2002 ch. 2-3, Cook 2004) :

| Regle | Classe | Comportement attendu                                          |
|-------|--------|---------------------------------------------------------------|
| 0     | I      | Uniforme (constance, K tend vers 0)                           |
| 4     | II     | Periodique (periode courte, K collapse rapidement)            |
| 30    | III    | Chaotique (entropie non triviale, K ne collapse pas completement) |
| 110   | IV     | Turing-complet (auto-entretien, K ne collapse pas)            |

## La zone saturee a n_cells = 64

A `n_cells = 64`, chaque fenetre packee reste sous le plancher de cadrage zlib : `K(W=1) = 1026` et `K(W=64) = 523 = 512 + 11` sont **identiques pour R30 et R110**, et le ratio publie (0.510) est le meme pour les deux. L'instrument n'y mesure pas le contenu des regles, mais son propre cadrage.

Le tell est direct : R30 (chaotique) et R110 (Turing-complet) ne peuvent pas avoir la meme trajectoire LZ-compressee a l'octet pres. L'egalite est une signature d'instrument, pas un resultat.

L'instrument declare desormais `WOLFRAM-SATURATED` sous `n_cells < 512` (`WOLFRAM_MIN_N_CELLS`) : dans cette zone, aucune classification — confirmation comme refutation — n'est concluante.

## Mesure hors saturation (n_cells = 1024, n_steps = 1024, seed = 33)

Mesure canonique, `wolfram_cross_classes_results.json` committe :

| Regle | Classe | K(W=1) | K(W=64) | Ratio | Verdict attendu | Verdict observe |
|-------|--------|--------|---------|-------|-----------------|-----------------|
| 0     | I      | 709    | 37      | 0.053 | COLLAPSED       | CLASS-I-CONFIRMED |
| 4     | II     | 1024   | 24      | 0.023 | COLLAPSED       | CLASS-II-CONFIRMED |
| 30    | III    | 1026   | 946     | 0.922 | WEAK-COLLAPSE / ENTREPRENED | CLASS-III-CONFIRMED (WEAK-COLLAPSE) |
| 110   | IV     | 1026   | 585     | 0.571 | WEAK-COLLAPSE / ENTREPRENED | CLASS-IV-REFUTED (COLLAPSED) |

**Verdict final cross-classes** : `WOLFRAM-4CLASSES-III/IV-INVERSE (1/4 contredisent -- faux negatif sur entropie)`.

Controle a `n_cells = 64` (zone saturee) : `WOLFRAM-4CLASSES-SATURATED (4/4 classes sous le plancher de cadrage zlib)`.

## Resultats falsifiables

### 1. Classes I et II : confirmees a toutes les echelles
- **R0 (uniforme)** : ratio 0.030 a n=64, 0.053 a n=1024. LZ capture la constance.
- **R4 (periodique)** : ratio 0.027 a n=64, 0.023 a n=1024. LZ capture la periode courte.

### 2. La separation III / IV apparait hors saturation
- A n=64, R30 et R110 rendent le **meme** ratio (0.510) : non-discrimination.
- A n=1024, R30 rend **0.922** (WEAK-COLLAPSE) et R110 **0.571** (COLLAPSED) : les deux regles se separent, de 0.35 de ratio.

### 3. Ce que la separation signifie — et ne signifie pas
R110 est **plus compressible** que R30. Sa trajectoire est **reguliere** (fond periodique, gliders) ; LZ la capture partiellement. La Turing-completude de R110 ne se manifeste pas dans l'incompressibilite d'une trajectoire particuliere : elle vit dans la diversite des configurations accessibles.

La classification « IV doit avoir une entropie partielle » reste donc refutee pour R110 — mais c'est l'**hypothese** qui est refutee, pas l'instrument qui echoue a mesurer. La version precedente lisait ce meme fait comme un « faux negatif », ce qui supposait acquise la these (Turing-complet => incompressible) que la mesure contredit.

### 4. Une seule classe contredit encore
Le verdict passe de « 2/4 contredisent » (n=64, sature) a « 1/4 contredisent » (n=1024). La contradiction residuelle porte sur R110 et sur la direction attendue, non sur une incapacite de l'instrument.

## Interet epistemologique

Le resultat central du pli 4, corrige, est double :

1. **L'instrument discrimine** chaos et structure des que la mesure sort du cadrage : R30 et R110 ne sont plus confondus.
2. **Discriminer la structure n'est pas mesurer la Turing-completude.** LZ fenetre mesure la **redondance locale** d'une trajectoire. Un automate regulier non universel produirait le meme profil. Pour approcher la Turing-completude elle-meme, l'instrument doit viser le **programme**, pas la trajectoire :
   - **Kolmogorov structure function** (Vereshchagin & Vitanyi) — pli 7, instrumentee (#19826).
   - **Block decomposition** (Zenil et al.) — pli 8, instrumentee (#19836).
   - **SAT-based minimal program** — mesure directe de Kolmogorov.

## Sources

- Wolfram, S. (2002). *A New Kind of Science*. Wolfram Media. Ch. 2-3 (classifications), ch. 6 (Rule 30), ch. 7 (Rule 110).
- Cook, M. (2004). *Universality in Elementary Cellular Automata*. Complex Systems 15(1): 1-40. (Turing-completude de Rule 110).
- Vereshchagin, N. & Vitanyi, P. (2004). *Kolmogorov structure functions and model selection*. IEEE Trans. Info. Theory 50(12): 3265-3290.
- Li, M. & Vitanyi, P. (2019). *An Introduction to Kolmogorov Complexity and Its Applications*. Springer. 4th ed. Ch. 6-7 (LZ et K).

## Reproduction

```bash
# PYTHONPATH necessaire pour ict.wolfram_step (pli 2 PR #19793)
export PYTHONPATH=MyIA.AI.Notebooks/IIT/ICT-Series

# Zone saturee (verdict WOLFRAM-4CLASSES-SATURATED attendu)
python scripts/hashlife/k_trajectory.py --mode wolfram-4classes --n-cells 64

# Mesure canonique (JSON committe)
python scripts/hashlife/k_trajectory.py --mode wolfram-4classes --n-cells 1024 \
    --json-out scripts/hashlife/wolfram_cross_classes_results.json

python -m pytest scripts/hashlife/tests/ -v
```

## Limites

- **n_cells = 1024** : la mesure est hors du plancher de cadrage, mais le cout croit avec `n x 2^W`. Un comptage de facteurs LZ76 remplacerait zlib sans changer la nature du resultat.
- **Seed = 33 unique** : pas de multi-seed. La robustesse de l'ecart R30/R110 (0.922 vs 0.571) a la densite initiale reste a mesurer — c'est precisement l'objet du pli 9 (#19847).
- **Seuil 0.7 non recalibre** : la frontiere COLLAPSED / WEAK-COLLAPSE a ete calee sur des mesures 2-D. Sa valeur n'est pas remise en cause par cette correction, mais elle n'a pas ete re-derivee pour le 1-D a n grand.
- **zlib comme approximateur de K** : borne superieure atteignable, sensible au build (~3 % mesure entre postes).

## Suite Origami (pli 5+)

- **Pli 5** : regles de reecriture d'hypergraphes sur les graphes de lakes Lean (programme = regle ; trajectoire = derivation). Le discriminant est temporel (O(n) vs O(log n)).
- **Pli 6** : extraction du graphe multiway d'un lake Lean (`game_theory_lean/CooperativeGames/`), mesure de la profondeur et largeur de branchement.
- **Pli 7+** : instruments non-locaux de complexite de regle (KSF, block decomposition, SAT-based minimal program).

## Conclusion

Mesure hors saturation, K_trajectory **separe** Rule 30 (0.922, faible collapse) de Rule 110 (0.571, collapse) et confirme les classes I et II. Le verdict « III/IV indistinguables » etait un artefact de cadrage a `n_cells = 64`.

Ce que l'instrument ne fait toujours pas : mesurer la **Turing-completude**. Il detecte la **regularite** d'une trajectoire — ce qui suffit a separer chaos et structure, mais pas a distinguer un automate universel d'un automate regulier non universel. Le discriminant de la Turing-completude doit viser le programme, non la trajectoire.
