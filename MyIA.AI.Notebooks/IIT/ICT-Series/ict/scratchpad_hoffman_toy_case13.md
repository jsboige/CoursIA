# Case 13 (#8182) — Hoffman FBT toy : mise a l'echelle N=16 (4 bits), compression M=2

> **Statut.** Pre-enregistrement scelle AVANT tout code du jouet.
> Pattern case 8/10/11/12 : prediction (bandes, nulls, verdict attendu) scelee au commit
> AVANT implementation. Si les bandes ne sont pas tenues, le jouet est repeint,
> pas la prediction.
>
> **Suite directe case 11 (PR #14535, null N=4/M=2) + case 12 (PR #14544, dissociation emergente N=8/M=2).**
> Cette case passe a **N=16 ontic states (4 bits)** avec M=2 sensory states (compression 8:1).
> Premier regime ou la borne FBT (X-3)/(X-1) est non triviale et ou la fibre atteint
> la cardinalite 8 -- ce qui multiplie par 2 la richesse intra-fibre par rapport a case 12.

## Setup (Prakash et al. 2017 §4)

| Element | Specification |
|---|---|
| Ontic states `W` | `{0, 1, ..., 15}` (4 bits, identifies a `{0000, ..., 1111}`) |
| Sensory states `X` | `{0, 1}` (compression 8:1) |
| Compression canonique | `canonical(w) = w % 2` (bit0) |
| Canal `P(x \| w)` | Chaine markovienne parametree par `alpha in [0, 1]` |
| Paysages `L(w)` | 16 patterns non-uniformes (heritables cases 11/12 + nouveaux paysages bit3 family) |
| Strategie Truth | `argmax_x f(MAP(x))`, MAP = `argmax_w P(x\|w) g(w)` |
| Strategie Fitness-only | `argmax_x F(x) = E[f(W) \| x]` |
| Evolution | Selection truncée sur `alpha in [0, 1]` (60 pop × 150 gen × 5 seeds) |

**Paysages prevus** (16) :
- 4 herites case 11 : `L_bit0`, `L_bit1`, `L_parity`, `L_anti`
- 4 herites case 12 : `L_bit2`, `L_bit2_complement`, `L_pairity_3bit`, `L_random_3bit`
- 8 nouveaux bit3 family : `L_bit3`, `L_bit3_complement`, `L_bit01`, `L_bit23`,
  `L_bit01_xor`, `L_bit3_weighted`, `L_random_4bit_seed1`, `L_random_4bit_seed2`

**Reduction parametres** : 60 pop × 150 gen × 5 seeds × 16 paysages × 2 strategies = 144K evaluations
(case 12 etait ~80K ; case 13 doit rester sous 10 min). Ajustement empirique apres run 1.

## Predictions (bandes P1-P4, nulls N1-N3)

### P1 : convergence sous chaque pression

- **P1a** truth-track exploite **bit3** via MAP sur la fibre cardinal 8.
  Cible : `alpha*_truth >= 0.85` sur `L_bit3` family (cible elevee car structure intra-fibre
  plus discriminante que case 12).
- **P1b** fit-track = bit0-moyenne stricte (heritee case 11/12).
  Cible : `alpha*_fit ≈ 0.45` (moyenne du bruit uniforme, independante du cardinal fibre).
- **P1c** `L_random_4bit` = NOT-XNOR strict sur bit aleatoire (herite case 12).
  Cible : gap = 0.000.

### P2 : transfert cross-paysage

- **P2a** truth-tracker transfere sur `L_bit3` survit (cible `>= 0.85`).
- **P2b** fitness-tracker meurt sur paysages `L_bit3` (cible `<= 0.10`).
- **P2c** gap cible `>= 0.70` sur paysages bit3 family (vs `>= 0.36` case 12, vs `= 0.000` case 11).

### P3 : variance inter-seeds

5/5 seeds convergent sur le meme pattern de dissociation (variance inter-seeds `< 0.05`).

### P4 : structure-revealing 5/5 seeds

truth-track sur bit3 family exploite structure intra-fibre 5/5 seeds ;
fit-track = bit0-moyenne stricte 5/5 seeds.

## Nulls attendus

- **N1** : `L_bit0` (compression-aligned, herite case 12) — gap attendu `+0.30 a +0.40`
- **N2** : `L_bit1`, `L_parity`, `L_anti`, `L_random_4bit_seed*` (structure symetrique/heritee) — gap = 0.000
- **N3** : `L_pairity_3bit` (direction inversee, herite case 12) — gap attendu `~-0.20`

## Verdict attendu (scelle)

**Score FBT attendu** : `gap >= 0.30` sur **au moins 6/16 paysages** (bit0 family + bit2 family + bit3 family),
direction du gap dependante du paysage (coherent avec FBT Theorem 4 et case 12).

Si la prediction P2c (gap >= 0.70) est tenue sur bit3 family, c'est une confirmation forte
de la mise a l'echelle. Si elle est tenue a 0.40-0.60, c'est une confirmation moderee.
Si le gap reste sous 0.30 sur bit3 family, c'est un signal que la borne FBT sature a N=16
(compression 8:1) ou qu'il faut revoir le setup.

## Prédictions de mise a l'echelle (résumé cross-case)

| Regime | N | M | Compression | Gap attendu | Verifie |
|---|---|---|---|---|---|
| Toy 2-bit case 11 | 4 | 2 | 2:1 | 0.000 (null) | ✓ PR #14535 |
| Toy 3-bit case 12 | 8 | 2 | 4:1 | >= 0.10 (4/8 paysages) | ✓ PR #14544 |
| Toy 4-bit case 13 | 16 | 2 | 8:1 | >= 0.30 (6+/16 paysages) | **attendu ce cycle** |
| Toy 5-bit case 14+ | 32 | 2 | 16:1 | >= 0.50 (8+/32 paysages) | future |
| FBT sature | N → ∞, M fixe | M | → ∞ | → 1 (FBT Theorem 4) | asymptotique |

## Limites assumées

- Le toy 4-bit est **computationnellement plus lourd** (fibre cardinal 8 vs 4 vs 2). Reduction pop/gen
  compense. Si les runs depassent 15 min, vectoriser numpy (slice sur les fibres).
- 5 seeds × 60 pop × 150 gen : compromis vitesse/robustesse. Variance inter-seeds mesuree.
- Le setup reste canonique bit0 (compression), l'evolution porte sur `alpha` seul.
  Relachement complet = case 14+.

## Verification C.1 / C.2 / C.3 / H.1

- C.1 : grep `raise NotImplementedError \| assert False \| 1/0` = 0
- C.2 : artefact `results/hoffman_interface_toy_n16_results.json` commite
- C.3 : scope strict ; pas de modification cellules ICT existantes
- H.1 : 18+ tests pytest verts (test_hoffman_interface_toy_n16.py)
- bibliography-hygiene : PDF Prakash et al. 2017 archive GDrive (deja fait case 11)

## Crédits / Suite

- **Source primaire** : Prakash, Stephens, Hoffman, Singh & Fields (2017), arXiv:1505.04322
- **Antécedent direct** : Case 11 (PR #14535, N=4) + Case 12 (PR #14544, N=8)
- **Issue tracker** : #8182 (Veille & distillation TOE ↔ conscience)
- **EPIC parent** : ICT (#4588)
- **Strate dissociations** : `docs/ict/dissociations-matrix.md` (strate 5)

Date de scellement : 2026-09-04 (cycle c.896)
Lane : myia-po-2024:CoursIA-2
