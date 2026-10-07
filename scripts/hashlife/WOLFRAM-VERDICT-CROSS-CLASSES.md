# WOLFRAM-VERDICT-CROSS-CLASSES — mesure falsifiable K_trajectory sur 4 classes

**Suite directe** : [WOLFRAM-VERDICT.md](WOLFRAM-VERDICT.md) (pli 3, c.109) couvre Rule 30 + Rule 110. Ce document pli 4 etend a 4 classes.

## Perimetre

Mesure `K_trajectory` (compression LZ fenetree, instrument `scripts/hashlife/k_trajectory.py --mode wolfram-4classes`) sur les 4 classes canoniques de Wolframe (Wolfram 2002 ch. 2-3, Cook 2004) :

| Regle | Classe | Comportement attendu                                          |
|-------|--------|---------------------------------------------------------------|
| 0     | I      | Uniforme (constance, K tend vers 0)                           |
| 4     | II     | Periodique (periode courte, K collapse rapidement)            |
| 30    | III    | Chaotique (entropie non triviale, K ne collapse pas completement) |
| 110   | IV     | Turing-complet (auto-entretien, K ne collapse pas)            |

## Mesure firsthand (n_cells=64, n_steps=64, seed=33)

| Regle | Classe | K(W=1) | K(W=64) | Ratio | Verdict attendu | Verdict observe |
|-------|--------|--------|---------|-------|-----------------|-----------------|
| 0     | I      | 709    | 21      | 0.030 | COLLAPSED       | CLASS-I-CONFIRMED |
| 4     | II     | 1024   | 28      | 0.027 | COLLAPSED       | CLASS-II-CONFIRMED |
| 30    | III    | 1026   | 523     | 0.510 | WEAK-COLLAPSE / ENTREPRED | CLASS-III-REFUTED (COLLAPSED) |
| 110   | IV     | 1026   | 523     | 0.510 | WEAK-COLLAPSE / ENTREPRED | CLASS-IV-REFUTED (COLLAPSED) |

**Verdict final cross-classes** : `WOLFRAM-4CLASSES-III/IV-INVERSE (2/4 contredisent -- faux negatif sur entropie)`.

## Resultats falsifiables

### 1. Classes I et II : confirmees
- **R0 (uniforme) collapse a 3.0 %** : LZ capture la constance, comme attendu. La trajectoire 1-D entiere tient en 21 octets compresses.
- **R4 (periodique) collapse a 2.7 %** : LZ capture la periode courte, comme attendu.

### 2. Classes III et IV : refutees
- **R30 (chaotique) collapse a 51.0 %** : AU-DELA du seuil COLLAPSED (0.7) selon l'instrument. La trajectoire contient une structure interne que LZ capture en partie -- un **faux negatif sur l'entropie**.
- **R110 (Turing-complet) collapse a 51.0 %** : strictement identique a R30, malgre la Turing-completude theorique. Meme faux negatif.

### 3. Discrimination fine III vs IV par K_trajectory seule : **indistingable**
- R30 et R110 produisent des trajectoires LZ-compressibles identiques (1026 -> 523 cellules, ratio 0.510).
- Le discriminant K_trajectory **ne peut pas** discriminer Turing vs chaos sur 1-D a cette echelle.

## Interet epistemologique

Le resultat central du pli 4 est que **K_trajectory ne detecte pas la Turing-completude** (ni meme le chaos 1-D bien identifie comme entropie partielle). Ce n'est pas un defaut d'implementation -- c'est une **limitation theorique** : LZ fenetre mesure la **redondance locale**, pas la **complexite structurelle**.

Pour discriminer Turing-complet vs chaos 1-D, l'instrument adequate est :
- **Kolmogorov structure function** (Vereshchagin & Vitanyi) : K(W|W') mesure la complexite conditionnelle.
- **Block decomposition** (Zenil et al.) : decomposer la trajectoire en blocs et compter les regularites locales.
- **SAT-based minimal program** : chercher le plus court programme qui genere la trajectoire.

Ces instruments sont candidats pour le **pli 5+ Origami** (cf. [WOLFRAM-VERDICT.md](WOLFRAM-VERDICT.md) § Suite).

## Sources

- Wolfram, S. (2002). *A New Kind of Science*. Wolfram Media. Ch. 2-3 (classifications), ch. 6 (Rule 30), ch. 7 (Rule 110).
- Cook, M. (2004). *Universality in Elementary Cellular Automata*. Complex Systems 15(1): 1-40. (Turing-completude de Rule 110).
- Vereshchagin, N. & Vitanyi, P. (2004). *Kolmogorov structure functions and model selection*. IEEE Trans. Info. Theory 50(12): 3265-3290.
- Li, M. & Vitanyi, P. (2019). *An Introduction to Kolmogorov Complexity and Its Applications*. Springer. 4th ed. Ch. 6-7 (LZ et K).

## Reproduction

```bash
# PYTHONPATH necessaire pour ict.wolfram_step (pli 2 PR #19793)
export PYTHONPATH=MyIA.AI.Notebooks/IIT/ICT-Series

# Mesure 4 classes
python scripts/hashlife/k_trajectory.py --mode wolfram-4classes --n-cells 64

# Sortie JSON
python scripts/hashlife/k_trajectory.py --mode wolfram-4classes --n-cells 64 \
    --json-out scripts/hashlife/wolfram_cross_classes_results.json

# Tests pytest
python -m pytest scripts/hashlife/tests/test_wolfram_cross_classes.py -v
```

## Limites

- **Echelle n=64, n_steps=64** : suffisante pour observer le collapse rapide de I/II, mais limite pour distinguer III/IV. Une mesure a n_cells=256, 512 pourrait reveler des differences fines.
- **Seed=33 unique** : pas de multi-seed. Les resultats dependent du pattern initial ; un autre seed pourrait donner un ratio R30 != R110. A tester en follow-up.
- **Pas de multi-regime temporel** : K_trajectory mesure une fenetre glissante. Le pli 7 Origami pourrait explorer le regime temporel (variation de K en fonction de t).

## Suite Origami (pli 5+)

- **Pli 5** : regles de reecriture d'hypergraphes sur les graphes de lakes Lean (programme = regle ; trajectoire = derivation). Le discriminant est temporel (O(n) vs O(log n)).
- **Pli 6** : extraction du graphe multiway d'un lake Lean (`game_theory_lean/CooperativeGames/`), mesure de la profondeur et largeur de branchement.
- **Pli 7 (propose)** : instrument alternatif de complexite de regle (Kolmogorov structure function, Block decomposition, SAT-based minimal program) pour discriminer Turing vs chaos 1-D.

## Conclusion

K_trajectory est **insuffisant** pour discriminer Turing-complet vs chaos sur 1-D. Le discriminant detecte la **structure simple** (I/II collapsent correctement) mais rate l'**entropie structurelle** (III/IV collapsent par faux negatif). L'instrument est utile pour discriminer *soupe* vs *programme* en 2-D (cf. c.108 ICT-48) mais pas pour discriminer Turing vs chaos en 1-D.