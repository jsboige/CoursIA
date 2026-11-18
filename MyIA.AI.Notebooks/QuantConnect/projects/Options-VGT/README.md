# Trading Options sur VGT Equities (ID: 21113806)

Stratégie d'options (PUTs/CALLs) sur 5 valeurs tech (NVDA, ORCL, CSCO, AMD, QCOM).

## Architecture
- `main.py` - Wheel strategy multi-equity avec seuils OTM personnalisés
- `quantbook.ipynb` - QuantBook de recherche : stratégie Wheel sur actions tech (exploration des chaînes d'options et distributions)

## Concepts enseignés
- Options trading (PUT selling, covered CALL)
- OTM threshold personnalisé par actif
- Exposure validation et cash-secured positions
