# Option Wheel Strategy (ID: 20216898)

Strategie Wheel classique sur SPY avec variantes.

## Fichiers
- `main.py` - Version principale (IB Cash, cash-secured)
- `covered_puts.py` - Variante covered puts
- `margin_account.py` - Variante margin (IB Margin, SetHoldings)
- `current.py` - Version simplifiee sans IB
- `updates.py` - Version avec logging ameliore
- `research.ipynb` - Analyse options chains, signaux, primes

## Concepts enseignes
- Wheel strategy complete (PUT sell -> assignment -> CALL sell)
- Cash-secured vs margin comparison
- Position sizing et exposure management
