# Gaussian-Direction-Classifier

**Classe d'actifs :** actions américaines (8 valeurs technologiques : AAPL, MSFT, GOOGL, AMZN, NVDA, META, TSLA, NFLX)
**Projet QC Cloud d'origine :** 29398513 (versions v1.0 et v2.0, mesures de mars 2026)

## Description

Classifieur bayésien naïf gaussien (GaussianNB, écrit à la main dans `main.py` pour ne pas dépendre de sklearn sur QC Cloud), d'après l'exemple 15 de *Hands-On AI Trading*. Il prend les rendements passés sur 2, 5, 10 et 21 jours et prédit le sens du rendement du lendemain, titre par titre. Le modèle est réentraîné tous les 21 jours de bourse sur une fenêtre d'un an. Chaque jour, le portefeuille retient au plus 3 titres dont la probabilité de hausse dépasse 0.60, pondérés par leur excès de probabilité au-dessus de 0.5. Il n'achète que quand SPY cote au-dessus de sa moyenne mobile à 200 jours ; sinon il vend tout et reste en liquidités.

## Exécution

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/Gaussian-Direction-Classifier"`
**QC Cloud :** copier `main.py` dans un projet Python, compiler, puis lancer le backtest. La fenêtre (2015-01-01 -> 2026-01-01), le capital et le courtage sont codés dans `initialize`.

## Résultats mesurés

QC Cloud, 2026-11-06, espace ESGF_School, projet 39006161, backtest `7f1a0d2d2e7aaee75e26a695d47eb966`, `main.py` de ce dossier, fenêtre codée 2015-01-01 -> 2026-01-01, compte sur marge et modèle de courtage tels que codés dans `initialize`.

| Mesure | Stratégie | Témoin SPY détenu |
|--------|-----------|-------------------|
| Sharpe (QC, avec taux sans risque) | 0.715 | 0.537 |
| PSR (QC) | 8.0 % | 2.5 % |
| CAGR | 21.4 % | 13.4 % |
| Drawdown max | 40.2 % | 33.6 % |
| Bêta (QC) | 0.533 | 0.995 |
| Ordres | 5098 | 1 |

Le témoin SPY tourne avec la même fenêtre, le même capital et les mêmes réglages (projet 39006369). La stratégie le bat en Sharpe et en CAGR, mais son drawdown maximal est plus profond.

Le même jour, le code d'avant #23301 (projet 39006302) et un rejeu dans le projet d'origine 29398513 rendent exactement les mêmes chiffres.

**Historique.** La v2.0 annonçait Sharpe 0.761, CAGR 23.1 %, drawdown max 25.6 % : ce sont les mesures du 2026-03-28, retrouvées le 2026-06-15 par #3073 avec 4999 ordres. Le même code rend aujourd'hui 5098 ordres et les chiffres du tableau, dans l'un et l'autre espace : l'écart tient à la date du calcul (données ou version du moteur côté QC), pas au code ni à l'espace. Les comparaisons v1.0/v2.0 écrites dans le docstring ne valent que pour les mesures de mars.

## Fichiers

- `main.py` : la stratégie (v2.0), avec ses résultats mesurés dans le docstring.
- `research.ipynb` : carnet de recherche autonome (données yfinance 2014-2024, GaussianNB de sklearn). Cinq plis temporels à fenêtre expansive : chaque pli s'entraîne sur toutes les dates qui précèdent son bloc de test. La décision prise à la clôture d'un jour encaisse le rendement du lendemain, avec 10 points de base de frais sur le montant échangé (chaque entrée ou sortie d'une ligne échange un tiers du portefeuille) ; le témoin est un portefeuille à poids égaux des mêmes titres, sur les mêmes dates. **Verdict committé : NO BEATS** — hors échantillon (2289 séances, fin 2015 à fin 2024), Sharpe 0.90 contre 1.24 pour le témoin. Le modèle perd sur 4 plis sur 5, mais l'écart n'est pas significatif (z entre plis −1.29, t de Newey-West de l'écart journalier −0.99). Sans frais, la même sélection fait 1.30 (t = 1.91, non significatif) : le signal égale à peu près le témoin, ce sont les frais (5,4 points de base par séance) qui font perdre le modèle. Les 4 graines rendent des résultats identiques (GaussianNB est déterministe). Le carnet documente donc une **absence** d'edge de cette famille de variables, pas une validation.
- `_generate_research.py` : script qui génère `research.ipynb`.
