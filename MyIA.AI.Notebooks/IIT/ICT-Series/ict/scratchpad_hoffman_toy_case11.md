# Case 11 — Hoffman interface theory : toy falsifiable

## Pré-enregistrement (bandes scellées, avant le code du jouet)

### Setup

- **World `W`** : `W = {0, 1, 2, 3}` (4 ontic states, identifiés à `{00, 01, 10, 11}`)
- **Perception `f`** : `W → {0, 1}` (binary partition). Il y a `2^4 = 16` perceptions distinctes.
- **Two landscapes** :
  - `L_even` (parity-even good) : `survive(0)=1, survive(1)=0, survive(2)=0, survive(3)=1` (XNOR=1 alive)
  - `L_odd` (parity-odd good) : `survive(0)=0, survive(1)=1, survive(2)=1, survive(3)=0` (XNOR=0 alive)
- **Two evolutions** :
  - **Truth-track** : sélection naturelle maximise `I(f(W); W)` — la perception **révèle** le monde (W uniforme a priori)
  - **Fitness-track** : sélection naturelle maximise `E[survive_L(W) | f(W) = 0] × P(f=0) + E[survive_L(W) | f(W) = 1] × P(f=1)`
- **Algorithme évolutionniste** : génétique simple, population `N=200`, génome = 4 bits (perception tabulaire), mutation rate `μ=0.01/bit/génération`, sélection **truncation** (top 50%), `T=2000` générations, **5 seeds** `s ∈ {0, 1, 7, 42, 99}`.

### Prédictions scellées

**P1 — Convergence** : les deux trackers convergent sur leur paysage d'entraînement.
- P1a (truth-track) : la perception finale est **`XNOR` ou `NOT-XNOR`** (les deux sont truth-tracking pures : `I=2 bits`). Après `T=2000` générations, on s'attend à l'**un des deux exclusivement**.
- P1b (fitness-track sur `L_even`) : la perception finale **bipartitionne W selon XNOR=1 vs XNOR=0** — donc `XNOR` (l'unique perception utile non-dégénérée sur `L_even`).
- P1c (fitness-track sur `L_odd`) : `NOT-XNOR`.

**P2 — Transfert cross-paysage (test critique)** :
- P2a (truth-track, entraîné `L_even`, transféré à `L_odd` SANS ré-entraînement) : survie moyenne **inchangée** (~50%) — la perception `XNOR` **continue** à bipartitionner correctement parce qu'elle révèle la structure (parité), donc le transfert marche quel que soit le signe du label.
- P2b (fitness-track, entraîné `L_even`, transféré à `L_odd` SANS ré-entraînement) : survie moyenne = **0%** — la perception `XNOR` met `W=00, 11` dans le même groupe, mais sur `L_odd` ces deux états sont **l'un bon, l'autre mauvais** : la perception fitness-track n'a aucune information au-delà du label de paysage, et le label a **changé**.
- P2c (fitness-track ré-entraîné sur `L_odd`) : converge à `NOT-XNOR`, et **redevient** survie 100% — l'organisme fitness-track s'adapte mais il a **changé de perception**.

**P3 — Asymétrie des variances inter-seeds** :
- P3a (truth-track) : la perception finale est la même **5/5 seeds** (XNOR ou NOT-XNOR — basculement binaire symétrique entre les deux). Faible variance.
- P3b (fitness-track) : la perception finale est `XNOR`/`NOT-XNOR` strictement dictée par paysage (5/5 seeds convergent au même point). **Aussi** faible variance.

**P4 — Reconnaissance d'icône vs structure** (le test Hoffman authentique) :
- On définit `structure-revealing` = perception `f` t.q. `∀w1, w2 : w1 XOR w2 ∈ {1,2} ⇒ f(w1) ≠ f(w2)` (i.e. adjacent-bit-differ).
- Les perceptions structure-revealing pour W = {0,1,2,3} sont exactement : `XNOR` (= f(00)=0, f(01)=1, f(10)=1, f(11)=0), `NOT-XNOR` (idem inversé), `f(00)=0, f(01)=0, f(10)=1, f(11)=1` (bit0), `NOT-bit0`, `bit1`, `NOT-bit1`.
- P4a : truth-track converge **sur l'une des 6 perceptions structure-revealing**, 5/5 seeds.
- P4b : fitness-track converge **sur `XNOR` ou `NOT-XNOR` exclusivement** (les perceptions structure-revealing dont le partitionnement **collabore** avec le label de fitness, c-à-d qui préservent la structure utile). Donc 5/5 seeds.

### Contrôles négatifs

- **N1 (constant perception)** : une perception constante `f(w)=0 ∀w` atteint `I(f;W) = 0` (vérité zéro) — c'est le **plancher** truth-track, et la fitness maximale sur n'importe quel landscape est exactement `0.5` (pure chance).
- **N2 (random perception post-entraînement)** : un tracker qui n'aurait **pas convergé** donnerait `I(f;W) = 0.5 ± 0.3 bits` (bruit binomial 4 essais) — c'est le null.
- **N3 (anti-Hoffman)** : un tracker conçu pour **imiter** l'icon-théorie de Hoffman mais sur les **mauvaises** perceptions (e.g. `f(00)=0, f(01)=1, f(10)=0, f(11)=1` = `NOT-XOR`, qui **ne révèle pas la parité**) doit avoir `I(f;W)=1` (le XOR est l'information, le NOT-XOR révèle le XOR comme `f(XOR=0)=0, f(XOR=1)=1`, soit `f=bit0` ⊕ `bit1` qui **est** information-théoriquement la même que XNOR), donc c'est **aussi** structure-revealing. Prière de ne pas le placer en null.

### Métriques

- `I_fW` = information mutuelle `f` ↔ `W` en bits
- `survival_rate` = `E[survive_L(W) | f(W)]` sous paysage `L`
- `perception_is_XNOR` = `(f(0), f(1), f(2), f(3)) == (0, 1, 1, 0)`
- `perception_is_NOT_XNOR` = `(f(0), f(1), f(2), f(3)) == (1, 0, 0, 1)`
- `perception_is_structure_revealing` = ci-dessus

### Verdict attendu

**CONFIRMÉ** si :
- P1a/P1b/P1c tiennent en 5/5 seeds
- P2a (truth transfert) ≥ 0.90 survie moyenne, P2b (fitness transfert) ≤ 0.10 survie moyenne (gap ≥ 0.80)
- P4a/P4b : 5/5 seeds dans l'ensemble structure-revealing

**FALSIFIÉ** si :
- P2a ET P2b ≤ 0.10 (les deux trackers meurent au transfert → ils sont équivalents) — ce qui invaliderait la **dissociation** Hoffman
- OU P1 ne tient pas (tracker ne converge pas)

**INCONCLUSIF** si :
- Quelque chose entre les deux (e.g. un seed sur 5 diverge, ou les deux trackers survivent à 50% au transfert)

### Honnêteté de portée (grade C)

- Le toy ne teste **que** la dissociation « icon vs spacetime » dans un cadre **discret à 2 bits**. Il ne reproduit pas la phénoménologie de la perception humaine.
- Aucune claim sur la conscience, le qualia, ou l'évolution biologique réelle. La case teste une **classe de mécanisme** (sélection naturelle sous pression fitness vs truth), pas une théorie de la conscience.
- L'évolution par mutation/sélection est **totalement** neutre par rapport à toute assertion évolutionniste réelle : c'est un banc d'essai formel.

### Format de sortie

Code dans `MyIA.AI.Notebooks/IIT/ICT-Series/ict/hoffman_interface_toy.py` (grade C).
Artefact `MyIA.AI.Notebooks/IIT/ICT-Series/ict/results/hoffman_interface_toy_results.json` (verdicts + bandes).
Tests `MyIA.AI.Notebooks/IIT/ICT-Series/ict/tests/test_hoffman_interface_toy.py`.
Distillation `docs/ict/hoffman-interface-distillation.md` (grade C, case 11 #8182).
Ligne ajoutée dans `docs/ict/dissociations-matrix.md`.
