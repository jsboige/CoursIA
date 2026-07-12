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

### License

The original hashlife.py is released under the MIT license by John H. Williamson.
See the original repository for details.
