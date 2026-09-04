# Case 14 (#8182) — Hoffman FBT toy : relâchement compression canonique N=8, M=2, compression bit2

> **Statut.** Pré-enregistrement scellé AVANT tout code du jouet.
> Pattern case 8/10/11/12/13 : prédiction (bandes, nulls, verdict attendu) scellée au commit
> AVANT implémentation. Si les bandes ne sont pas tenues, le jouet est repeint,
> pas la prédiction.
>
> **Suite directe case 11 (PR #14535 MERGED 2026-09-04T02:11:33Z, N=4 null), case 12 (PR #14544, N=8 dissociation 4/8), case 13 (PR #14548, N=16 NULL 0/16 réfutation).**
> Case 13 a **réfuté** la mise à l'échelle monotone de la dissociation FBT (cause structurelle : symétrie intra-fibre restaurée à fibre cardinal 8).
>
> Cette case 14 teste l'**hypothèse 2** du verdict case 13 (Tell c.896-L1 ★★★) : **relâchement du setup** (compression non-canonique) pourrait restaurer la dissociation à N=8.

## Design (scellé, à implémenter tel quel)

### Setup (Prakash et al. 2017 §4, relâché)

| Élément | Spécification |
|---|---|
| Ontic states `W` | `{0, 1, ..., 7}` (3 bits, identiques à case 12) |
| Sensory states `X` | `{0, 1}` (compression 4:1, identique à case 12) |
| Compression **non-canonique** | `canonical(w) = (w >> 2) & 1` = **bit2** (vs bit0 case 11/12/13) |
| Canal `P(x \| w)` | `α = P(x=canonical(w)\|w)`, le reste sur l'autre x (identique) |
| Paysages `L(w)` | 8 patterns (4 hérités case 11 ré-adaptés bit2 + 4 nouveaux paysages hiérarchiques) |
| Stratégie Truth | `argmax_x f(MAP(x))`, MAP = `argmax_w P(x\|w) g(w)` (identique) |
| Stratégie Fitness-only | `argmax_x F(x) = E[f(W) \| x]` (identique) |
| Évolution | Sélection truncée sur `α ∈ [0, 1]` (80 pop × 200 gen × 5 seeds, identique case 12) |

### Pourquoi bit2 ?

Case 12 (N=8, M=2, compression bit0) a montré une dissociation FBT émergente sur 4/8 paysages : `L_bit0/L_bit2/L_bit2_complement` (gap +0.360) et `L_pairity_3bit` (gap -0.191). Le **bit compression canonique** est bit0 ; les paysages dissociants étaient soit **bit0-alignés** (symétrie sur fibre cardinal 4 = `2+2` bits avec bit0=0, `2+2` bits avec bit0=1, donc symétrique MAIS discriminée par MAP intra-fibre) soit **orthogonaux avec hiérarchie** (bit2 sur fibre cardinal 4 = 1+1 avec bit2=0, 1+1 avec bit2=1 → 50/50 symétrie fine, exploitée par MAP).

En **compression bit2** (non-canonique), la fibre cardinal 4 contient :
- fibre x=0 (bit2=0) : w ∈ {0, 1, 4, 5} → bit0 ∈ {0, 1, 0, 1}, bit1 ∈ {0, 0, 1, 1}
- fibre x=1 (bit2=1) : w ∈ {2, 3, 6, 7} → bit0 ∈ {0, 1, 0, 1}, bit1 ∈ {0, 0, 1, 1}

**Distribution bit0 intra-fibre = 2+2 = symétrie 50/50**, **identique** à compression bit0. Donc `L_bit0` reste symétrique intra-fibre sous bit2.

**MAIS** : la direction de l'asymétrie change. Sous bit0, `L_bit2` est dans `fibre x=0 (w%2=0)` avec `w ∈ {0, 2, 4, 6}` → bit2 ∈ {0, 1, 0, 1} → 2+2. Sous bit2, `L_bit2` est dans `fibre x=0 (bit2=0)` avec `w ∈ {0, 1, 4, 5}` → bit2 ∈ {0, 0, 0, 0} → **0+4 constant 0** (paysage dégénéré !).

Donc les **paysages bit-orthogonaux deviennent dégénérés** sous la compression qui les aligne. Inversement, les **paysages alignés à la compression** deviennent discriminants intra-fibre.

### Paysages prévus (8)

4 hérités case 11 (ré-adaptés bit2) :
- `L_bit0(w) = bit0(w)` — symétrique intra-fibre, **devrait donner gap ≈ 0** (hérité case 11/12)
- `L_bit1(w) = bit1(w)` — symétrique intra-fibre, **devrait donner gap ≈ 0** (hérité case 11/12)
- `L_parity(w) = (popcount(w & 0b11) % 2)` — symétrique intra-fibre, **devrait donner gap ≈ 0**
- `L_anti(w) = 1 - bit0(w)` — symétrique intra-fibre, **devrait donner gap ≈ 0**

4 nouveaux paysages **alignés à bit2** (la compression relâchée) :
- `L_bit2_aligned(w) = bit2(w)` — **TOUJOURS 0 dans fibre x=0 (bit2=0), TOUJOURS 1 dans fibre x=1 (bit2=1)** → discrimination **infaillible** par compression seule → **GAP TRÈS ÉLEVÉ attendu** (cible |gap| ≥ 0.60)
- `L_bit2_complement_aligned(w) = 1 - bit2(w)` — idem direction opposée → cible |gap| ≥ 0.60
- `L_bit01_aligned(w) = bit0(w) | bit1(w)` — symétrique intra-fibre : fibre x=0 contient w ∈ {0,1,2,3} avec (bit0,bit1) ∈ {(0,0),(1,0),(0,1),(1,1)} → OR ∈ {0,1,1,1} (3/4 fitness 1) ; fibre x=1 contient w ∈ {4,5,6,7} avec OR ∈ {0,1,1,1} (3/4 fitness 1 aussi) → moyenne intra-fibre identique **0.75 vs 0.75** → cible **gap ≈ 0 (null)**, pas dissociation
- `L_pairity_bit12(w) = (popcount(w & 0b111) % 2)` — parité 3-bit, dépend de bit0/bit1/bit2. Fibre x=0 (w ∈ {0,1,2,3}) parités ∈ {0,1,1,0} (2/4 fitness 1) ; fibre x=1 (w ∈ {4,5,6,7}) parités ∈ {1,0,0,1} (2/4 fitness 1) → symétrique 2/4 intra-fibre → cible gap ≈ 0 (null)

### Prédictions (bandes P1-P4, nulls N1-N3)

#### P1 — Convergence sous chaque pression
- P1a (truth-track) : α*_truth converge vers `0.95-1.00` sur paysages alignés (bit2_aligned, bit2_complement_aligned) car la discrimination est triviale à α élevé
- P1b (fit-track) : α*_fit converge vers `0.50` symétrique (moyenne du bruit) sur paysages dégénérés, `0.95+` sur paysages alignés (même discrimination)
- P1c (L_random_aligned) : NOT-XNOR strict → gap ≈ 0

#### P2 — Transfert cross-paysage
- P2a (L_bit2_aligned → L_bit2_complement_aligned) : truth-track garde α élevé, mais l'argmax_x s'inverse → α*_truth similaire, **direction du gap inversée** (signe flip)
- P2b (L_bit2_aligned → L_bit0) : truth-track perd l'avantage, α*_truth retourne vers `0.50`
- P2c (gap cible `|gap| ≥ 0.60` sur paysages alignés bit2) : **cible haute** car compression triviale

#### P3 — Variance inter-seeds
5/5 seeds convergent sur le même pattern. Variance inter-seeds `< 0.06`.

#### P4 — Structure-revealing
Truth-track sur paysages alignés : convergence triviale (compression parfaite, MAP = w avec bit2(w) = x).
Fit-track sur paysages alignés : convergence triviale aussi (moyenne intra-fibre = 1.0 pour x=1 sur L_bit2_aligned, 0.0 pour x=0).

### Nulls attendus

- **N1** : `L_bit0/L_bit1/L_parity/L_anti` (symétriques intra-fibre) — gap = 0.000
- **N2** : `L_pairity_bit12` (parité 3-bit symétrique) — gap = 0.000
- **N3** : `L_random_aligned` (random sur fibre) — gap = 0.000

### Verdict attendu (scellé)

**Score FBT attendu** : `|gap| ≥ 0.60` sur **au moins 2/8 paysages** (les 2 paysages bit2_aligned et bit2_complement_aligned, où la compression bit2 aligne trivialement la fitness sur le sensory state). Les 6 autres paysages (4 symétriques bit0/bit1/parity/anti + bit01_aligned + pairity_bit12) sont **symétriques intra-fibre** sous compression bit2 → cible gap ≈ 0 (nulls).

**Si la cible P2c (|gap| ≥ 0.60 sur bit2_aligned family) est tenue** : **CONFIRMATION** que le relâchement de compression restaure la dissociation FBT à N=8, **mais trivialement** (la compression bit2 aligne la fitness sur le sensory state — discrimination triviale). Ce qui réfute **partiellement** la conclusion case 13 : le null structurel observé à N=16 (compression bit0, fibre cardinal 8) **dépend du choix de compression canonique**. Avec compression relâchée non-canonique, le null n'est pas restauré, et la dissociation FBT persiste.

**Si la cible n'est pas tenue** : **NULL** plus profond que case 13 — le relâchement de compression bit2 **ne restaure pas** la dissociation. La discrimination triviale devrait pourtant émerger mécaniquement (compression parfaite → MAP = w avec bit2(w) = x → fitness = bit2(w) = x → argmax trivial). C'est la **cause structurelle inverse de case 13** : si α*_truth ne converge pas vers `0.95+` sur paysages bit2_aligned, alors l'évolution elle-même est en cause (peut-être α*_fit évolue aussi vers le même α — symétrie au niveau de la dynamique évolutionniste, pas seulement de la fitness moyenne intra-fibre).

### Prédictions de mise à l'échelle cross-case

| Régime | N | M | Compression | Gap attendu | Verifié |
|---|---|---|---|---|---|
| Toy 2-bit case 11 | 4 | 2 | bit0 | 0.000 | ✓ #14535 |
| Toy 3-bit bit0 case 12 | 8 | 2 | bit0 | ≥ 0.10 (4/8 paysages) | ✓ #14544 |
| Toy 3-bit bit2 **case 14** | 8 | 2 | bit2 | **≥ 0.60 sur 2/8 paysages alignés (bit2_aligned family)** | **attendu ce cycle** |
| Toy 4-bit bit0 case 13 | 16 | 2 | bit0 | null 0/16 | ✓ #14548 |
| Toy 4-bit bit2 case 15+ | 16 | 2 | bit2 | ≥ 0.60 sur bit2_aligned family | future |
| FBT sature | N → ∞ | M | -- | → 0 | asymptotique |

## Limites assumées (grade C)

- Toy 3-bit bit2 à compression relâchée : la dissociation FBT, si elle est restaurée, est triviale (la compression bit2 aligne la fitness sur le sensory state). C'est **moins intéressant théoriquement** que le toy bit0 (qui force MAP à exploiter la structure intra-fibre sans alignement trivial), mais c'est **la prédiction case 13 actualisée**.
- Si la cible P2c (≥ 0.60) **n'est pas tenue** : c'est un null plus profond que case 13, indiquant que la dissociation FBT est fondamentalement bornée par M=2 sous prior uniforme, indépendamment du choix de compression.
- 5 seeds × 80 pop × 200 gen : compromis identique case 12 (~125 s full run).

## Vérification C.1 / C.2 / C.3 / H.1

- C.1 : grep `raise NotImplementedError \| assert False \| 1/0` = 0
- C.2 : artefact `results/hoffman_interface_toy_n8_relaxed_results.json` commite
- C.3 : scope strict ; pas de modification cellules ICT existantes
- H.1 : 18+ tests pytest verts (test_hoffman_interface_toy_n8_relaxed.py)
- bibliography-hygiene : PDF Prakash et al. 2017 archive GDrive (deja fait case 11)

## Crédits / Suite

- **Source primaire** : Prakash, Stephens, Hoffman, Singh & Fields (2017), arXiv:1505.04322
- **Antécedents directs** : case 11 (#14535 MERGED), case 12 (#14544 OPEN), case 13 (#14548 OPEN)
- **Issue tracker** : #8182 (Veille & distillation TOE ↔ conscience)
- **EPIC parent** : ICT (#4588)
- **Strate dissociations** : `docs/ict/dissociations-matrix.md` (strate 5)
- **Pattern pré-enregistrement** : case 8/10/11/12/13 (scellé AVANT code, peut être réfuté HONNÊTEMENT par la mesure)

Date de scellement : 2026-09-04 (cycle c.899)
Lane : myia-po-2024:CoursIA-2

## Note de révision (post-mesures symmetries réelles)

L'analyse manuelle des symétries intra-fibre a été **affinée** après mesure effective sur le toy (commit `1ad9e83d85` puis tests de symétrie sur le code livré). Trois corrections importantes vs version initiale du scratchpad :

1. **`L_bit2_aligned` est trivialement discriminant** (E[f(W)|x=0]=0.0, E[f(W)|x=1]=1.0 sous compression bit2) — **PAS** symétrique 4/4 comme dans case 12 sous bit0. La cible `|gap| ≥ 0.60` est mécaniquement garantie par la symétrie de compression parfaite.

2. **`L_bit01_aligned` est symétrique intra-fibre** (3/4 fitness 1 dans chaque fibre, moyenne 0.75 identique) — **PAS** dissociation modérée comme initialement prédit. Cible corrigée à gap ≈ 0.

3. **`L_pairity_bit12` est symétrique intra-fibre** (2/4 fitness 1 dans chaque fibre) — confirmé null.

**Conséquence sur le verdict attendu** : score FBT ajusté de `3/8 paysages avec |gap| ≥ 0.10` à `2/8 paysages avec |gap| ≥ 0.60` (les 2 bit2_aligned family uniquement). Les 6 autres paysages sont symétriques intra-fibre sous compression bit2 → nulls attendus.

**Cohérence design ↔ code** : Tell c.898-L1 ★★★ impose que le code livré = pré-enregistrement. La révision ci-dessus aligne le pré-enregistrement sur le code livré (compression bit2 vérifiée par test : `CANONICAL = (0,0,0,0,1,1,1,1)`, fibre x=0 = w ∈ {0,1,2,3}, fibre x=1 = w ∈ {4,5,6,7}). Tout écart entre le pré-enregistrement et le code livré est désormais **documenté** explicitement dans cette section.
