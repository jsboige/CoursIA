# Case 12 (#8182) — Hoffman FBT toy N=8 — pré-enregistrement scellé

> **Statut.** Case **12** du tracker de veille/distillation #8182 (TOE ↔ conscience, Hoffman FBT).
> Suite directe de la case 11 (PR #14535). Toy Prakash et al. 2017 §4, **N=8 ontic states (3 bits)**, M=2 sensory states. Compression 4:1 — premier régime où la borne FBT devient non triviale.

## Setup

| Élément | Spécification |
|---|---|
| Ontic states `W` | `{0, 1, ..., 7}` (3 bits, identifiés à `{000, 001, ..., 111}`) |
| Sensory states `X` | `{0, 1}` (compression 4:1) |
| Compression canonique | `canonical(w) = w % 2` (bit0, identique à case 11) |
| Canal `P(x \| w)` | Chaîne markovienne α, `P(x=canonical(w)\|w) = α`, sinon `1-α` |
| Paysages `L(w)` | Mêmes 4 patterns que case 11 (L_bit0, L_bit1, L_parity, L_anti) + 4 nouveaux (L_bit2, L_bit2_complement, L_pairity_3bit, L_random_3bit) pour exposer l'asymétrie cross-bit |
| Stratégie Truth | `argmax_x f(MAP(x))`, MAP = `argmax_w P(x\|w) g(w)` |
| Stratégie Fitness-only | `argmax_x F(x) = E[f(W) \| x]` |
| Évolution | Sélection truncée sur α ∈ [0, 1] (200 pop × 500 gen × 10 seeds) |

## Prédictions scellées (P1-P4)

- **P1a (truth-track)** : α*_truth converge sur la structure compressionnée (MAP non-dégénérée grâce à l'asymétrie cross-fibre). Pour L_bit0 et L_bit1, l'asymétrie est exactement celle de case 11 (bit0 favorise x=0/1) — donc α*_truth ≈ α*_case11.
- **P1b (fit-track, XNOR strict)** : `argmax_x E[f(W)|x]` calcule la moyenne de fitness sur la fibre `{w : canonical(w) = x}`. Pour L_bit0 et L_bit1, c'est le même qu'à N=4.
- **P1c (fit-track, NOT-XNOR strict sur L_odd)** : idem, structure symétrique → moyenne identique.
- **P2 (transfert cross-paysage)** : pour L_bit2 et L_bit2_complement, le **bit2** est orthogonal au canal (le canal ne discrimine pas entre fibres bit2=0 vs bit2=1, toutes deux ont la même moyenne sur le bit0) → la stratégie Truth doit **dépendre** de bit2 mais le canal ne l'expose pas. C'est la dissociation clé.
- **P3 (variance inter-seeds)** : 10 seeds → variance plus faible que case 11 (N plus grand = paysage plus contrasté).
- **P4 (structure-revealing)** : Truth track expose bit2 via MAP même si canal ne le porte pas (posterior `P(w|x) ∝ P(x|w)g(w)` non-trivial grâce à la structure du paysage).

## Nulls adversariaux (N1-N3)

- **N1** : α=0 → canal inversé → fibre `{w : canonical(w) = x}` reste la même, mais l'inverse signifie que les deux stratégies pick l'opposé. Vérifier que la dissociation persiste.
- **N2** : α=0.5 → bruit maximal → les deux stratégies pick le max de moyenne → équivalence attendue pour les paysages symétriques (L_parity), dissociation attendue pour L_bit0/L_bit1/L_bit2.
- **N3** : α=1 → canal déterministe → MAP unique sauf ties → dissociation attendue sur L_bit2 où bit2 crée un tie-breaking.

## Verdict attendu (scellé)

- **Sur L_bit0, L_bit1, L_parity, L_anti** : gap ≤ 0.05 (héritée de case 11, structurellement neutre).
- **Sur L_bit2, L_bit2_complement, L_pairity_3bit, L_random_3bit** : **gap ≥ 0.10** attendu (la dissociation FBT devient mesurable).
- **Global** : au moins UN paysage avec gap ≥ 0.10 ET α*_truth ≠ α*_fit. Si ce n'est pas le cas, INCONCLUSIVE — borne supérieure du régime où le toy 2-bit est testable.

## Critères d'acceptation

1. **Toy N=8 implémenté** avec 8 paysages, 10 seeds, tests invariants ≥ 14 (analogues à case 11 + bit2/fibre-decomposition).
2. **Verdict mesuré** : gap α*_truth vs α*_fit par paysage, self+transfer payoffs identiques OU distincts.
3. **Distillation grade C** : `docs/ict/hoffman-interface-distillation-case12.md` (~150 lignes).
4. **Ligne matrice dissociations** : update `docs/ict/dissociations-matrix.md` strate 5.
5. **Pre-enregistrement scellé** AVANT code (pattern case 8/10).
6. **Bibliographie Prakash et al. 2017 archivée GDrive** (déjà fait case 11).

## Hors scope

- N=16+ (cas 13+) — scalings futurs.
- Algorithme génétique sur la structure de la map (vs α seul) — case 14+.
- Cas conscient/qualias — jamais prétention.
- Claim sur la perception humaine.

## Plan d'exécution

1. Commit ce scratchpad (scellé) AVANT code.
2. Créer `MyIA.AI.Notebooks/IIT/ICT-Series/ict/hoffman_interface_toy_n8.py` (fork case 11 → N=8).
3. Créer `tests/test_hoffman_interface_toy_n8.py` (≥ 14 invariants).
4. Exécuter pytest (5-10 min sur 10 seeds).
5. Capturer `results/hoffman_interface_toy_n8_results.json`.
6. Rédiger distillation grade C.
7. Update matrice dissociations.
8. PR `feat(ict,#8182,case12): Hoffman FBT toy N=8 — émergence attendue gap ≥ 0.10`.

— myia-po-2024:CoursIA-2, scellé c.895 avant tout code
