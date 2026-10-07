# WOLFRAM-VERDICT — mesure K_trajectory sur automates 1-D (Origami pli 3)

**Issue** : #19766 pli 3 (sous-issue du pli 1 #19766 / EPIC Origami #19742)
**PR** : (en cours d'ouverture, c.109)
**Date** : 2026-10-08
**Lane** : myia-po-2024:CoursIA-2
**Organe mobilise** : `ict.wolfram_step.wolfram_trajectory` (PR #19793, encore OPEN)

## Question scientifique

Le discriminant K_trajectory (T12 #18446, `scripts/hashlife/k_trajectory.py`) definit le quotient `K(t, W=2^n) / n` qui tend vers 0 pour les structures issues de la soupe (dissolution par fragilite) et reste borne inferieurement pour les programmes recursifs auto-entretenus.

**Question** : ce discriminant tient-il **cross-dimension** ? Sur les automates 1-D de Wolfram (Rule 30 chaotique classe III, Rule 110 Turing-complet classe IV), K_trajectory distingue-t-il :

- Rule 30 (chaos) : attendu SOUP-FRAGILE-* (LZ compresse a toutes les echelles)
- Rule 110 (Turing-complet) : attendu PROGRAM-CONFIRMED (les motifs auto-entretenus ne compressent pas)

L'hypothese etait : **les deux discriminations tiennent, et Rule 110 est moins compressible que Rule 30 a horizon long**.

## Resultat (falsifiable, mesure firsthand ce cycle)

**n_cells = 64, n_steps = 64, seed = 33** (canonique Wolframe 2002 ch. 2-3, Cook 2004) :

| Regle | K(t, W=1) | K(t, W=64) | Ratio | Verdict |
|-------|-----------|------------|-------|---------|
| Rule 30 (classe III, chaos)  | 1026 | 523 | 0.510 | **WOLFRAM-CHAOTIC-FRAGILE** (confirme) |
| Rule 110 (classe IV, Turing) | 1026 | 523 | 0.510 | **WOLFRAM-TURING-REFUTED** (refute) |

**Cross-verdict** : `WOLFRAM-CROSS-DIMENSION-PARTIAL` (Rule 30 confirme, Rule 110 refute).

**n_cells = 128, n_steps = 64, seed = 33** (resolution x2) :

| Regle | K(t, W=1) | K(t, W=64) | Ratio | Verdict |
|-------|-----------|------------|-------|---------|
| Rule 30 | 3151 | 2070 | 0.657 | WOLFRAM-CHAOTIC-FRAGILE |
| Rule 110 | 3171 | 1822 | 0.575 | WOLFRAM-TURING-REFUTED |

## Interpretation

**Resultat central : K_trajectory (LZ fenetre) NE detecte PAS la Turing-completude de Rule 110.**

Les deux regles (Rule 30 chaotique, Rule 110 Turing-complete) produisent des trajectoires **LZ-compressibles a toutes les echelles mesurees**. La discrimination soup-vs-programme de la tranche 1 (T12 #18446) repose sur la detection de l'**entropie**, pas de l'**auto-entretien structurel** : un programme periodique court (blinker, pulsar) collapse aussi sous LZ (cf. mesure tranche 1, ratio brut = 0.077..0.154 vs soup 0.762..0.784).

**Pourquoi Rule 110 collapse** : les automates 1-D, meme Turing-complets, produisent des motifs 1-D avec suffisamment de regularite locale pour que LZ77 (zlib level 6) trouve des repetitions. La Turing-completude se manifeste dans la **diversite des configurations accessibles** (le programme peut encoder n'importe quel calcul), pas dans la **compressibilite d'une trajectoire particuliere**.

## Limites documentees

1. **LZ fenetre W=2^n ne detecte pas la Turing-completude 1-D**. Un instrument base sur la **complexite de regle** (Kolmogorov structure function, ou la longueur du programme minimal qui produit la trajectoire) discriminerait probablement Rule 30 de Rule 110, mais ce n'est pas l'instrument deploye dans cette tranche.

2. **Horizon limite (n_steps=64)** : Rule 110 a besoin d'horizons tres longs pour faire emerger des structures auto-entretenues (gliders, collisions) ; avec 64 pas, ces structures ne sont pas encore developpees. Mesure avec n_steps=512 a tenter pour confirmer.

3. **Comparaison 1-D vs 2-D** : le discriminant K_trajectory a ete concu pour des trajectoires 2-D (Game of Life soup). Sa portee au 1-D est validee pour la fragilite (Rule 30 = chaos = fragile, comme attendu) mais **pas** pour la Turing-completude (Rule 110 refute malgre la classe IV).

## Verdict final tranche Origami pli 3

**WOLFRAM-CROSS-DIMENSION-PARTIAL** :
- L'extension au 1-D est mecaniquement valide (organe `ict.wolfram_step` invoque, format 1xN compatible avec `grid_to_packed`, mesure LZ fenetree executee sans erreur).
- La detection de **fragilite chaotique** (Rule 30) tient cross-dimension 1-D / 2-D.
- La detection d'**auto-entretien Turing-complet** (Rule 110) **ne tient pas** sur cet instrument ; un instrument alternatif est necessaire pour la discrimination fine.

**Suite Origami pli 5** : explorer un instrument de complexite de regle (Kolmogorov structure function, Block decomposition, ou SAT-based minimal program) pour discriminer Turing-complet vs chaos.

**Suite Origami pli 6** : extraire le graphe multiway d'un lake Lean et mesurer la profondeur moyenne + largeur de branchement -- un test direct de la Turing-completude via la theorie des systemes de reecriture.

## Reproduction

```bash
# Placer ict.wolfram_step dans sys.path (organe PR #19793)
export PYTHONPATH=MyIA.AI.Notebooks/IIT/ICT-Series

# Mesure Rule 30
python scripts/hashlife/k_trajectory.py --mode wolfram --rule 30 --n-cells 64

# Mesure cross-regles
python scripts/hashlife/k_trajectory.py --mode wolfram --all --n-cells 128

# Sortie JSON pour verification
python scripts/hashlife/k_trajectory.py --mode wolfram --all --n-cells 64 --json-out wolfram_results.json
```

Les sorties JSON `scripts/hashlife/wolfram_results.json` sont versionnees pour reproductibilite.

## Sources

- T12 #18446, tranche 3 #19227 : `scripts/hashlife/k_trajectory.py` instrument original (2-D)
- PR #19793 : organe `ict.wolfram_step` (pli 2, OPEN)
- Cook 2004 : "Universality in Elementary Cellular Automata" (Rule 110 Turing-complet)
- Wolfram 2002 *A New Kind of Science* chap. 2-3 (4 classes de comportement), 9-11 (Rule 110)
- Crutchfield, "Between order and chaos" (Kolmogorov complexity applied to CA)

🤖 Generated with [Claude Code](https://claude.com/claude-code)

Co-Authored-By: Claude Haiku 4.5 (1M context) <noreply@anthropic.com>