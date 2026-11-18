| Modele | Etage | Graines | eval pre | eval post | delta | +- 1 std | courbes saines | steps satures | verdict saturation |
|---|---|---:|---:|---:|---:|---:|---|---:|---|
| MiniCPM5-2B | 0.8-2B | 2 | 0.0250 | 0.0469 | +0.0219 | 0.0031 | oui | 0.92 | SIGNAL_PARTIEL |
| Qwen3.5-0.8B | 0.8-2B | 2 | 0.0219 | 0.0281 | +0.0063 | 0.0063 | non | 0.97 | SIGNAL_NUL |
| **moyenne etage 0.8-2B** | 0.8-2B | 4 | | | +0.0141 | 0.0092 | non | 0.95 | moyenne sur les bras |
| Qwen3-8B | 8-14B | 3 | 0.0479 | 0.1000 | +0.0521 | 0.0290 | oui | 0.65 | SIGNAL_PARTIEL |
| **moyenne etage 8-14B** | 8-14B | 3 | | | +0.0521 | 0.0290 | oui | 0.65 | moyenne sur les bras |

Verdict inter-etage (0.8-2B vs 8-14B) : comparable=True · intervalles disjoints=False · BEATS=False.

Regle : comparaison inter-etage : deux etages, >= 2 graines chacun, delta moyen de l'etage haut > etage bas avec intervalles +-1 std disjoints, et courbes saines des deux cotes

Saturation : `steps satures` est la fraction **mediane** (par bras) de steps tronquees au budget de completion, mesuree par l'organe `scripts/analyse_dapo_saturation.py` ; le verdict est **par bras** (le seuil s'applique au bras, pas au lot de graines) et n'est donc pas fusionne entre etages. La ligne d'etage est une moyenne de branches, pas un chiffre de l'organe.
