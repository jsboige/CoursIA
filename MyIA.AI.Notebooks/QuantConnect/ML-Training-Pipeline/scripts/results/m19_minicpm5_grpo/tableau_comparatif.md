| Modele | Etage | Graines | eval pre | eval post | delta | +- 1 std | courbes saines |
|---|---|---:|---:|---:|---:|---:|---|
| MiniCPM5-2B | 0.8-2B | 2 | 0.0250 | 0.0469 | +0.0219 | 0.0031 | oui |
| Qwen3.5-0.8B | 0.8-2B | 2 | 0.0219 | 0.0281 | +0.0063 | 0.0063 | non |
| **moyenne etage 0.8-2B** | 0.8-2B | 4 | | | +0.0141 | 0.0092 | non |
| Qwen3-8B | 8-14B | 3 | 0.0479 | 0.1000 | +0.0521 | 0.0290 | oui |
| **moyenne etage 8-14B** | 8-14B | 3 | | | +0.0521 | 0.0290 | oui |

Verdict inter-etage (0.8-2B vs 8-14B) : comparable=True · intervalles disjoints=False · BEATS=False.

Regle : comparaison inter-etage : deux etages, >= 2 graines chacun, delta moyen de l'etage haut > etage bas avec intervalles +-1 std disjoints, et courbes saines des deux cotes
