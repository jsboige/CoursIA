# Checklist Upload Soutenance ESGF 2026

**Deadline** : J-2 avant la soutenance (17 mai 2026, 23h59)

---

## Checklist avant upload

### Code

- [ ] `main.py` compile sans erreur sur QuantConnect (BuildSuccess)
- [ ] Parametres de la strategie clairement definis en debut de `initialize()`
- [ ] Pas de hardcode de chemins locaux ou de credentials
- [ ] Noms de variables clairs et descriptifs
- [ ] `README.md` a la racine du projet avec :
  - [ ] Description de la strategie (1 paragraphe)
  - [ ] Liste des indicateurs utilises
  - [ ] Parametres et leur justification
  - [ ] Instructions pour lancer le backtest

### Backtest

- [ ] Backtest le plus recent avec periode >= 2 ans
- [ ] Resultats visibles dans le projet (screenshot ou export)
- [ ] Comparaison avec benchmark (SPY pour equities, BTC pour crypto)
- [ ] Metriques cles : Sharpe, CAGR, MaxDD, Win Rate, # Trades

### Presentation

- [ ] `slides.md` (Slidev) dans le repertoire du projet
- [ ] Graphiques d'equity curve inclus (PNG dans le meme dossier)
- [ ] Tableau de metriques complete
- [ ] Analyse des sous-periodes
- [ ] Slide de conclusion avec points d'amelioration

### Documentation

- [ ] `requirements.txt` ou liste des dependances
- [ ] Commentaires dans le code pour les decisions cle
- [ ] Si utilisation de fichiers annexes (alpha.py, portfolio.py) : les documenter
- [ ] Seed fixe pour la reproductibilite (si applicable)

---

## Procedure d'upload

1. Creer un repo dans l'org ESGF : `2026-ESGF-Soutenance-Equipe-XX`
2. Pousser le code complet (main.py + README + slides + assets)
3. Verifier que le repo est accessible par les evaluateurs
4. Confirmer l'upload par email/canal du cours

## Format du repo

```
2026-ESGF-Soutenance-Equipe-XX/
├── main.py              # Strategie LEAN (obligatoire)
├── README.md            # Documentation (obligatoire)
├── slides.md            # Presentation Slidev (obligatoire)
├── equity_curve.png     # Graphique P&L (obligatoire)
├── research.ipynb       # Notebook de recherche (optionnel)
├── alpha.py             # Module alpha separe (optionnel)
└── requirements.txt     # Dependances (optionnel)
```

---

## Sanctions

- **Retard** : -5 points par jour de retard
- **Code non compilable** : 0/20 sur la partie Code
- **Pas de backtest** : 0/30 sur la partie Backtest
- **Pas de presentation Slidev** : -10 points sur la partie Presentation
