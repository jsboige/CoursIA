# BTC Machine Learning (ID: 21047688)

Prediction de direction BTC avec ML (RandomForest, SVC, XGBoost).

## Architecture
- `main.py` - Algorithme enhanced (9 features: SMA, RSI, EMA x4, ADX, ATR)
- `main-simple.py` - Version simple (3 features: SMA20, RSI, DailyReturn)
- `research.ipynb` - Training enhanced (ta, sklearn, xgboost)
- `research-simple.ipynb` - Training simple (RF seulement)

## Concepts enseignes
- Feature engineering (indicateurs techniques -> features ML)
- Object Store pour persistance modele
- Train/test split temporel
- Comparaison modeles (RF vs SVC vs XGBoost)

## Note pedagogique
Le modele simple fonctionne mieux - le modele enhanced a "trop appris" le regime baissier.
