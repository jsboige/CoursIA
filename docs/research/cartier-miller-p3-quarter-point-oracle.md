# P3 oracle numérique : les identités quarter-point vérifiées sur les 92 premiers

**Issue** : #19452 (brique P3, prérequis nommé par le P2 §3) · **Pin amont** : `37a9b72`
**Suite directe** : P1+ ground truth (#22034) → P2 arbitrage (#21834) → **ce document (oracle P3)**.
**Script** : `scripts/cartier_miller/verify_quarter_point_identities.py` ·
**Sortie** : `scripts/cartier_miller/example_results/p3_quarter_point_identities.json`.

## Ce qui manquait

Le P2 ([`cartier-miller-p2-mathlib-survey.md`](cartier-miller-p2-mathlib-survey.md) §3) retient
la brique P3 « quarter-point `j=1728` » et nomme son prérequis : *« l'oracle numérique de P1
servant de vérificateur indépendant, jamais de preuve »*. Or la tranche P1+ ne vérifiait pas la
congruence du manuscrit : elle compare deux chemins de calcul de la **même** quantité
(`quarter()` de Cornacchia/Miller contre les récurrences télescopantes) au seul indice `n`.
Les équations (33)–(36) de la section « Application to the original quarter point sum »
n'avaient jamais été confrontées à une exécution.

Ce document comble ce trou : l'oracle P3 existe, il est falsifiable, et il est **vert**.

## Méthode

Les valeurs `a_L`, `B_L` et `U_p(L)` sont produites par les récurrences vendoriées de
`generate_p1_plus_truth.py` (amont `pilot.py:41-57`, pin `37a9b72`), puis chaque énoncé du
manuscrit est testé :

| Éq. | Énoncé (mod p) | Indices testés |
|---|---|---|
| (32) | `a_i = C(2i,i)·8⁻ⁱ` (définition, via `math.comb` indépendant) | tous les `L ∈ [0,h]` |
| (33) | `t_i = (2i+1)·a_i` | tous les `i ∈ [0,h]`, `t` recalculé indépendamment |
| (34) | `((2i+1)²−8)·a_i = −4(i+1)(2i+7)·a_{i+1} + 4i(2i+5)·a_i` | tous les `i < h` |
| (35) | `U_p(L) = 4·B_L − 2L(2L+5)·a_L` | tous les `L ∈ [0,h]` |
| (36) | `U_p(n) = 4·B_n + (9/4)·a_n` au point de quart `n=(p−1)/4` | les 43 premiers `p ≡ 1 (mod 4)` |

## Résultats

| Identité | Vérifications | Désaccords |
|---|---|---|
| (32) définition binomiale | 10 809 | **0** |
| (33) | 10 809 | **0** |
| (34) certificat de télescopage | 10 717 | **0** |
| (35) | 10 809 | **0** |
| (36) | 43 | **0** |

`status: passed` — les quatre énoncés arithmétiques du §7 sont **exhibés par l'exécution** sur
la totalité du ground truth (92 premiers, tous indices).

## Contrôles — l'instrument peut dire non

- **Positif (le cas chiffré du manuscrit)** : `p = 97`, `n = 24` → `a_n = 79`, `B_n = 33`,
  `U_p(n) = 43`. Les quatre valeurs sont lues dans le PDF archivé, pas recalculées par le même
  chemin. **Reproduites exactement** par le code vendorié.
- **Négatif 1** — (35) privée de son terme correctif `−2L(2L+5)·a_L` : ne tient que sur
  **184/10 809** indices (les cas triviaux où le terme s'annule, `L = 0`) → **réfutée**.
- **Négatif 2** — (33) avec `(2i+2)` au lieu de `(2i+1)` : tient sur **0/10 809** → **réfutée**.

Une mutation non réfutée ferait sortir le script en code 2 : l'instrument ne mesurerait rien.

## Portée honnête — ce que ceci n'établit pas

- Ceci **ne prouve pas** (35). Il établit que l'exécution l'exhibe sur 10 809 points et que le
  code vendorié la respecte. La preuve reste la brique Lean P3, qui pourra citer ce fichier
  comme **oracle numérique indépendant, jamais comme preuve** (garde du P2 §3).
- La cohérence (36) ⊂ (35) est algébrique : en `p = 4n+1`, `−2n(2n+5) ≡ 9/4` — le script
  vérifie les deux séparément, donc une erreur de transcription entre les deux équations du
  manuscrit serait attrapée.
- Le manuscrit reste un *unrefereed draft* assisté IA (garde permanente de l'issue) : une
  corroboration computationnelle de plus n'en change pas le statut.

## Artefacts

- Script : `scripts/cartier_miller/verify_quarter_point_identities.py` (GPL-2.0-or-later,
  importe les récurrences vendoriées).
- Sortie verbatim : `scripts/cartier_miller/example_results/p3_quarter_point_identities.json`
  (1,5 Ko, commité).
- Tests : `scripts/tests/test_cartier_miller_quarter_point.py`.

## Prochaine étape

La brique Lean P3 proprement dite : lake neuf `j=1728` (modèle EPIC #17845), énoncé de la
congruence (36) via `WeierstrassCurve` + `c₄/Δ`, preuve formelle — ce fichier en est le
vérificateur indépendant désigné.
