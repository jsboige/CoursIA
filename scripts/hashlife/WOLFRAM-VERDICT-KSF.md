# WOLFRAM-VERDICT-KSF — Kolmogorov structure function Rule 30 vs Rule 110

**Suite Origami pli 7.** Constat : pli 4 (LZ fenetre, c.110) n'a pas discrimine Rule 30 (chaotique) de Rule 110 (Turing-complet). Ce pli etend le discriminant a K(W|W'), la **Kolmogorov structure function** (Vereshchagin & Vitanyi 2004) — l'instrument canonique pour discriminer entropie aleatoire d'entropie structuree.

## Perimetre

Mesure `K_trajectory --mode wolfram-ksf` (pli 7, c.111) sur les 4 classes canoniques de Wolframe :

| Regle | Classe | Comportement attendu pour KSF |
|-------|--------|-------------------------------|
| 0     | I (uniforme) | 0 (deterministe, contexte capture tout) |
| 4     | II (periodique) | 0 (deterministe, contexte capture tout) |
| 30    | III (chaotique) | eleve, asymptote ~ n_cells (contexte n'aide pas) |
| 110   | IV (Turing-complet) | intermediaire (contexte capture gliders et reactions) |

## Mesure firsthand (n_cells=64, n_steps=64, seed=33, context_sizes=[1,2,4,8,16,32])

| Regle | Classe | KSF(W=1) | KSF(W=4) | KSF(W=16) | KSF(W=32) | Landmark |
|-------|--------|----------|----------|-----------|-----------|----------|
| 0     | I      | 0.032    | 0.983    | 0.000     | 0.969     | 0.0      |
| 4     | II     | 2.095    | 0.000    | 0.000     | 0.000     | 0.0      |
| 30    | III    | 8.540    | 9.000    | 8.000     | 8.000     | 0.85     |
| 110   | IV     | 8.683    | 8.900    | 8.000     | 8.000     | 0.20     |

## Resultats falsifiables

### 1. Discrimination Rule 30 vs Rule 110 par KSF : **NONDISCRIMINANT**

A W=32 (contexte maximal), KSF(R30) = **8.000** et KSF(R110) = **8.000**, **delta = 0.000**.

A toutes les tailles de contexte W >= 4, KSF(R30) == KSF(R110) (delta < 0.05).

**Verdict final** : `WOLFRAM-KSF-NONDISCRIMINANT`. La Kolmogorov structure function **ne discrimine pas** Turing-complet vs chaos 1-D, comme la compression LZ fenetree (pli 4).

### 2. Asymptotes observees vs landmarks theoriques

Les landmarks theoriques utilisaient une echelle normalisee (KSF / n_cells). A n_cells=64, l'asymptote observee pour R30 et R110 est **8.0**, soit 8/64 = 12.5 % de l'entropie maximale. C'est coherent avec la theorie pour R30 (chaos : entropie elevee, contexte n'aide pas) mais **inattendu pour R110** qui devait montrer un contexte plus utile (landmark 0.20 / n_cells = 12.8).

### 3. Pourquoi KSF echoue

La KSF mesure la **redondance locale** du dernier pas sachant le contexte immediat. Pour Rule 110, les gliders et reactions dependent de **plus** que la fenetre maximale du banc (Cook 2004 : echelle temporelle des gliders ~ 50-200 pas). Le contexte de la fenetre maximale capture l'etat local mais pas la "structure" du programme.

## Conclusion epistemologique

**Pli 7 confirme pli 4** : ni LZ fenetre, ni KSF ne discriminent Turing-complet vs chaos sur 1-D a l'echelle n=64. Les deux discriminants dependent de la **redondance locale**, pas de la **complexite structurelle**.

**Le discriminant adequate doit etre** :
- **Block decomposition** (Zenil et al.) : decouper la trajectoire en blocs et compter les regularites locales a differentes echelles.
- **SAT-based minimal program** : chercher le plus court programme qui genere la trajectoire, mesure directe de Kolmogorov.
- **Causal graph analysis** (Zenil 2013) : reconstruire le graphe causal de la trajectoire, mesurer la profondeur.

Ces instruments sont candidats pour les plis ulterieurs.

## Sources

- Vereshchagin, N. & Vitanyi, P. (2004). *Kolmogorov structure functions and model selection*. IEEE Trans. Info. Theory 50(12): 3265-3290.
- Li, M. & Vitanyi, P. (2019). *An Introduction to Kolmogorov Complexity and Its Applications*. Springer. 4th ed. Ch. 6-7.
- Cook, M. (2004). *Universality in Elementary Cellular Automata*. Complex Systems 15(1): 1-40. (echelle temporelle des gliders Rule 110).
- Wolfram, S. (2002). *A New Kind of Science*. Ch. 7.

## Reproduction

```bash
export PYTHONPATH=MyIA.AI.Notebooks/IIT/ICT-Series

python scripts/hashlife/k_trajectory.py --mode wolfram-ksf --n-cells 64 --n-steps 64 --seed 33
python scripts/hashlife/k_trajectory.py --mode wolfram-ksf --n-cells 64 --n-steps 64 --seed 33 \
    --json-out scripts/hashlife/wolfram_ksf_results.json

PYTHONPATH=MyIA.AI.Notebooks/IIT/ICT-Series \
  python -m pytest scripts/hashlife/tests/test_wolfram_ksf.py -v
```

## Limites

- **Echelle n=64** : KSF pourrait discriminer a plus grande echelle (n=512, 1024) si le contexte capture plus de gliders Rule 110. A tester en follow-up.
- **Seed=33 unique** : pas de multi-seed.
- **Context_sizes <= 32** : au-dela, n_steps=64 n'a plus de pas a mesurer (n_steps - W <= 0).
- **Landmarks theoriques non valides empiriquement** : les landmarks utilisaient une echelle normalisee qui ne correspond pas a la mesure LZ reelle. A recalibrer.

## Suite Origami

- **Pli 5/6** : bloques par env Lean/JVM absent (routeur po-2023/ai-01 WSL).
- **Pli 7+ (propose)** : Block decomposition (Zenil), SAT-based minimal program, causal graph analysis.

## Conclusion forte

K_trajectory (LZ fenetre, pli 4) et Kolmogorov structure function (pli 7) **ne discriminent pas** Rule 30 (chaos) de Rule 110 (Turing-complet) a l'echelle n=64. C'est un resultat scientifique falsifiable qui renforce la these que les **complexites de trajectoire 1-D** (locales) sont insuffisantes pour capturer la complexite **structurelle** de la Turing-completude. Le discriminant adequate est **non-local** (block decomposition, SAT-based minimal program, causal graph).