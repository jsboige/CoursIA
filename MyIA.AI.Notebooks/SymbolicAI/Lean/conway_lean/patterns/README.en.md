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
| `otca_initial_population` | `otcametapixel.rle` | 35 328 (published cycle; closed system measured; period witness: measured ceiling > 2 h) |
| `unitcell_initial_population` | `p5760unitlifecell.rle` | 5 760 (measured period) |
| `gemini_witness` | `gemini.rle` | 33 699 586 |
| `cpu_witness` | not yet available | 1 048 576 |

**The "Unit cell" pillar and the file present here are not the same pattern.**
`Pillars.lean` targeted Beluchenko's UnitCell (2011, period 4 096); the archive
holds only the p5760 of David Bell, kept as the "closest available". The 5 760
period of the file present here was measured on 2026-10-09 (500 × 500 torus,
first repetition generation 11324 == 5564). Beluchenko's pattern remains absent
from the archive; the authorship of the file present here (David Bell in this
file, Beluchenko 2011 in `Pillars.lean`) is **not** settled by the measurement.

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
