# Conway Lean Scripts

## hashlife.py

Pure Python implementation of Bill Gosper's HashLife algorithm (1984),
adapted from [johnhw/hashlife](https://github.com/johnhw/hashlife).

### Usage

```python
from hashlife import construct, advance

# Build quadtree from list of (row, col) live cells
node = construct([(0,0), (1,0), (2,0), (2,1), (1,2)])

# Advance N generations using HashLife
result = advance(node, 1000)
print(f"Population after 1000 gens: {result.n}")
```

### Performance

| Pattern | Cells | Generations | Time |
|---------|-------|-------------|------|
| Glider | 5 | 1 000 000 | <0.1s |
| Gosper gun | 36 | 10 000 | ~0.1s |
| OTCA metapixel | 64 691 | 35 328 | ~1.4s |
| Turing machine | 36 549 | 1 000 | ~5.2s |

Patterns with >500K cells (e.g., Gemini) may require Golly's native
C++ implementation for acceptable performance.

## novelty_probe.py

Probe empirique de l'axe **nouveauté** de l'issue #11162 (axe efficacité) :
mesure si l'arbre de macrocells d'une trajectoire produit des nœuds distincts
au fil des générations — la quantité qui rend HashLife rapide (cache de
mémoïsation touche, tout est déjà vu) ou lente (tout est neuf). Orthogonal à
l'axe confinement (`jumpCaptured`, #11007) : un pattern à croissance tuilée
s'étend sans borne mais répète ses tuiles (rapide) ; un methuselah reste borné
mais invente des structures (lent).

### Métrique

- **Nœuds distincts** : parcours du quadtree en collectant les `id()` — les
  sous-arbres structurellement identiques sont le même objet Python
  (mémoïsation de `join`), donc chaque nœud distinct compte une fois.
- **Pente log-log** : pente des moindres carrés de `log2(distinct)` contre
  `log2(t)`. Verdicts : `< 0.25` FAST (arbre stable, cache-friendly) ;
  `< 0.5` intermédiaire ; `≥ 0.5` SLOW (nouveauté persistante).

### Usage

```bash
python novelty_probe.py                       # tous les patterns, checkpoints 0..2048
python novelty_probe.py --patterns acorn      # un seul pattern
python novelty_probe.py --checkpoints 0,64,512,4096
```

Le self-check à deux étages valide le substrat **et** l'identité des patterns
avant toute mesure : (1) identité — population initiale attendue, croissance
exacte par période pour les patterns périodiques (attrape une transcription
fabriquée : la v1 du gun, 36 cellules fausses, passait le check de règle) ;
(2) règle — `advance()` contre `baseline_life()` sur 8 générations, exact à
translation près.

### Résultats mesurés (checkpoints 0..2048)

| Classe | Pattern | Pente | Verdict |
|---|---|---|---|
| still_life | block | 0.000 | FAST |
| oscillator_p2 | blinker | −0.006 | FAST |
| tiled_growth | gosper_gun | 0.190 | FAST |
| methuselah | r_pentomino | 0.410 | intermédiaire |
| methuselah | acorn | 0.462 | intermédiaire |

Confrontation à la théorie : le gun (croissance non bornée, tuiles répétées)
reste sous-linéaire — la croissance de population n'implique PAS la nouveauté
d'arbre ; les methuselahs inventent des structures à toutes les échelles
jusqu'à stabilisation (r-pentomino se stabilise à la génération 1103 : son
Δ nœuds passe négatif à t=2048, la transition chaos → stabilité est visible
dans la courbe). Le space-filler (remplaçant théorique pour l'axe FAST à
croissance d'échelle) n'est pas embarqué : RLE non sourçable (LifeWiki 403),
et une transcription de mémoire invaliderait le probe en silence — le gun
démontre le même point théorique.

## axis_orthogonality_probe.py

Probe **deux-axes** de l'issue #11162 (jambe empirique, acceptance item 2) :
mesure nouveauté ET confinement sur les mêmes trajectoires, et confronte la
classification au tableau de l'issue. Là où `novelty_probe.py` mesure l'axe
nouveauté seul (l'orthogonalité y est affirmée, pas éprouvée), ce probe
instrumente en plus le **taux de hit du cache** (hits/(hits+misses) de
join/successor, cumulatif et par intervalle) et l'axe **confinement** en
cadre absolu : `advance_abs` réplique `advance` en traquant l'origine du
canvas (centre : −S/2 ; successor/inner : +S/4), de sorte que l'échappement
par translation pure soit visible — un glider ne grandit jamais (bbox
constante) mais s'échappe à c/4 ; une mesure sur la seule bbox lui serait
aveugle.

### Métriques

- **front_speed** : pente LSQ de la demi-étendue de Chebyshev des cellules
  vivantes (depuis le centre initial) contre t — capte tout échappement,
  front ou translation. Seuil ÉCHAPPE ≥ 0.05 cell/gén (c/4 = 0.25).
- **bulk90_speed** : pente du rayon contenant 90 % de la population — la
  masse, pas le front.
- **novelty_slope** : pente log-log des nœuds distincts (comparable Grain 1).
- **hit cumulatif / par intervalle** : taux de hit des caches join/successor.
- **pic de join-misses par intervalle** : la nouveauté TRANSITOIRE (le
  chaos d'un methuselah est un pic, pas une pente — cf résultats).

### Contrôles (à chaque exécution, échouent bruyamment)

règle B3/S23 (`advance` == `baseline_life`, 8 générations × 9 instances) ;
géométrie du cadre absolu (bloc immobile à la cellule près, glider translaté
d'exactement une diagonale par 4 générations) ; compteur de cache vivant
(blinker 4 cycles → hits ≥ 1) — « 0 nouveauté détectée » et « rien regardé »
ne rendent pas la même valeur.

### Résultats mesurés deux-axes (checkpoints 0..2048, fenêtre 384×384, 9 instances / 6 familles)

| famille | instance | front | bulk90 | pente | hit cum. | pic miss | CONFINEMENT | NOUVEAUTÉ |
|---|---|---|---|---|---|---|---|---|
| still_life | block | 0.000 | 0.000 | 0.000 | 0.980 | 28 | TIENT | FAST |
| oscillator_p2 | blinker | 0.000 | 0.000 | −0.006 | 0.977 | 31 | TIENT | FAST |
| tiled_growth | gosper_gun | 0.243 | 0.109 | 0.190 | 0.922 | 483 | ÉCHAPPE | FAST |
| methuselah | r_pentomino | 0.242 | 0.234 | 0.410 | 0.892 | 25 354 | ÉCHAPPE | SLOW |
| methuselah | acorn | 0.216 | 0.030 | 0.462 | 0.906 | 53 095 | ÉCHAPPE | SLOW |
| spaceship | glider | 0.250 | 0.000 | 0.238 | 0.929 | 125 | ÉCHAPPE | FAST |
| random_soup | soup_s42 | 0.235 | 0.025 | 0.033 | 0.885 | 13 455 | ÉCHAPPE | SLOW |
| random_soup | soup_s7 | 0.238 | 0.216 | −0.040 | 0.873 | 6 272 | ÉCHAPPE | SLOW |
| random_soup | soup_s99 | 0.208 | 0.044 | 0.214 | 0.916 | 165 367 | ÉCHAPPE | SLOW |

Spearman(front_speed, pente nouveauté) = +0.36 ; Spearman(front_speed, hit
cumulatif) = −0.34 — association faible : les axes sont largement
décorrélés, pas parfaitement.

### Confrontation au tableau de l'issue — verdict mesuré

1. **Colonne nouveauté : CONFORME, et affinée.** Gun FAST (pente 0.190, hit
   0.922), methuselahs SLOW — mais la pente seule les laissait
   « intermédiaire » (0.410/0.462 < 0.50, la classification Grain 1) ; le
   **pic de join-misses** les classe SLOW avec un écart ×52-×110 sur le gun.
   Le pic requalifie aussi les soups (pente ≈ 0 après stabilisation, mais
   pics 6 272-165 367) : la nouveauté d'une soupe est un transitoire, pas
   une pente. « Golly-slow » = transitoires coûteux, pas lent partout : le
   hit-rate par intervalle remonte à 0.92+ après stabilisation.
2. **Colonne confinement : CONTREDITE en lecture extrémale.** Le tableau
   dit methuselah « tient (borné sur l'horizon) » — mesuré, ses gliders
   s'échappent à ~c/4 (front 0.242/0.216), indiscernables du gun (0.243).
   À horizon 2048 la vitesse de front ne sépare PAS le gun du R-pentomino.
   La colonne « tient » n'est vraie que **pondérée par la masse** : bulk90
   de l'acorn 0.030 (la masse reste dans la boîte) vs r-pentomino 0.234,
   gun 0.109.
3. **L'orthogonalité tient là où elle importe.** La paire critique de
   l'issue (space-filler vs methuselah) est quasi identique sur l'axe
   confinement (front 0.243 vs 0.242) et séparée de ×52 sur le pic de
   misses (483 vs 25 354) : la nouveauté sépare ce que le confinement ne
   distingue pas — c'est la thèse, vérifiée sur la paire qui la fonde.
   Le glider en est le témoin pur : échappement exact à c/4 (0.250), zéro
   croissance de masse, hit 0.929 — ÉCHAPPE+FAST.

### Usage

```bash
python axis_orthogonality_probe.py                          # 9 instances, contrôles compris
python axis_orthogonality_probe.py --patterns glider,acorn  # sous-ensemble
python axis_orthogonality_probe.py --checkpoints 0,16,256,4096
```

### License

The original hashlife.py is released under the MIT license by John H. Williamson.
See the original repository for details.
