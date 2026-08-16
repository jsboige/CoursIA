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

### License

The original hashlife.py is released under the MIT license by John H. Williamson.
See the original repository for details.
