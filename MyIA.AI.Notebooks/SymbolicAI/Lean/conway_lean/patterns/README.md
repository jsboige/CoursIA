# Conway's Game of Life — RLE Pattern Archive

Source: [copy.sh/life](https://copy.sh/life/) mirror of [LifeWiki](https://conwaylife.com/wiki/Main_Page) patterns.

## Patterns

| File | Pattern | Author | Size | Grid | Period |
|------|---------|--------|------|------|--------|
| `otcametapixel.rle` | OTCA Metapixel | Brice Due (2006) | 165 KB | 2058x2058 | 35 328 |
| `turingmachine.rle` | Turing Machine | Paul Rendell (2000) | 104 KB | variable | N/A |
| `p5760unitlifecell.rle` | p5760 Unit Life Cell | David Bell | 15 KB | 499x499 | 5 760 |
| `gemini.rle` | Gemini self-replicator | Andrew Wade (2010) | 5.3 MB | huge | 33 699 586 |

## Pillars.lean mapping

These RLE files correspond to the witness theorems scaffolded in
`Conway.Life.Pillars`:

| Pillar theorem | RLE file | Generation count |
|----------------|----------|-----------------|
| `otca_metapixel_witness` | `otcametapixel.rle` | 35 328 |
| `unitcell_witness` | `p5760unitlifecell.rle` (closest available) | 4 096 |
| `gemini_witness` | `gemini.rle` | 33 699 586 |
| `cpu_witness` | not yet available | 1 048 576 |

## Download

```bash
# From copy.sh mirror (accessible without bot detection)
MIRROR="https://copy.sh/life/examples"
curl -L -A "Mozilla/5.0" "$MIRROR/otcametapixel.rle" -o otcametapixel.rle
curl -L -A "Mozilla/5.0" "$MIRROR/gemini.rle" -o gemini.rle
curl -L -A "Mozilla/5.0" "$MIRROR/turingmachine.rle" -o turingmachine.rle
curl -L -A "Mozilla/5.0" "$MIRROR/p5760unitlifecell.rle" -o p5760unitlifecell.rle
```

## Note on Gemini

`gemini.rle` (5.3 MB) is gitignored due to size. It can be re-downloaded
from the copy.sh mirror using the command above. The notebook's `fetch_rle()`
function handles this gracefully with disk caching.
