# RiskParity Strategy

**Statut** : Plafond structurel confirmé — contre-exemple à visée pédagogique.

## Performance

| Métrique | Valeur | Source |
|----------|--------|--------|
| Sharpe Ratio | **0.544** | research.ipynb cell[10]·out[0] |
| CAGR | 7.28 % | research.ipynb cell[10]·out[0] |
| Volatilité | 9.71 % | research.ipynb cell[10]·out[0] |
| Max Drawdown | **-20.26 %** | research.ipynb cell[10]·out[0] |
| Période | 2015-2026 | research.ipynb cell[10]·out[0] |

> **Note métriques** : la valeur historique « Sharpe 0.399 » rapportée par le README pré-c.454 et la table « Comparaison aux alternatives » provenait d'une mesure pré-revision ; le notebook de recherche `research.ipynb` cell[10]·out[0] documente le verdict effectif **Risk Parity Sharpe 0.544** (MaxDD -20.26 %), confirmé par audit G.1 firsthand lors de la PR c.454 (audit vision fondateur, `assets/readme/MANIFEST.md`).

## Figures du notebook de recherche

Le notebook [`research.ipynb`](research.ipynb) documente l'analyse complète de la parité de risque : exploration des actifs, inverse-volatility weighting (H1), backtest (H2), impact de TLT en 2020-2023 (H3), sensibilité au lookback de volatilité (H4) et analyse par régime de marché. La stratégie atteint un plafond structurel (Sharpe 0.544) — contre-exemple pédagogique. Provenance détaillée : [`MANIFEST.md`](assets/readme/MANIFEST.md).

**Exploration — l'analyse des actifs (§2).** Le **dual-panel** juxtapose la courbe « Rendements cumulés 2015-2026 » sur 6 actifs (SPY/EFA/GLD/DBC/TLT) avec la heatmap de la matrice de corrélation. Les stats annualisées cell[4]·out[1] révèlent **GLD = meilleur Sharpe 0.81** (CAGR 12.02 %) avec **corrélation SPY 0.04** — diversifieur clé du portefeuille, tandis que **DBC sous-performe** (Sharpe 0.20, CAGR 3.45 %). La lecture visuelle confirme que GLD est l'actif qui contribue le plus à la diversification : l'inverse-vol weighting amplifie mécaniquement sa pondération face aux actifs les plus risqués.

<p align="center">
  <img src="assets/readme/rp-exploration.png" alt="Dual-panel exploration 2015-2026 : gauche « Rendements cumules 2015-2026 » ($1 investi, 5 actifs — DBC bleu/EFA orange/GLD vert/SPY rouge/TLT violet) — SPY final ~3.4×, GLD ~3.2×, EFA ~1.85×, DBC ~1.2×, TLT ~0.8×. Droite « Matrice de correlation » heatmap 5×5 SPY/EFA/GLD/DBC/TLT palette YlGn (colorbar -1.0→1.0) : SPY×DBC 0.35 / EFA×DBC 0.85 / SPY×TLT -0.17 / GLD×DBC 0.04 / GLD×SPY 0.26. GLD = meilleur diversifieur (corr SPY 0.04)." width="840"/><br>
  <em>Exploration — courbe Rendements cumulés + heatmap Matrice de corrélation ; GLD = meilleur Sharpe 0.81 + diversifieur (corr SPY 0.04), DBC sous-performant (S=0.20, cell[4]·out[1]).</em>
</p>

**H1 — inverse-volatility weighting égalise les contributions au risque.** Le **triple-panel bar chart** cell[6]·out[1] compare 3 méthodes de pondération (60/40, 1/N, Risk Parity) sur le partage entre capital et contribution au risque pour les 5 actifs. Verdict cell[6]·out[1] verbatim : **« 60/40 : SPY+EFA contribue 78.9 % du risque ; Risk Parity : SPY+EFA contribue 49.7 % du risque »**. L'inverse-vol **réduit mécaniquement** la domination des actions sur la contribution au risque : SPY passe de 53.9 % (60/40) à 24.0 % (RP) du risque total. La structure pondère GLD à 22.2 % du capital pour 20.0 % du risque — l'effet inverse-vol joue son rôle redistributeur.

<p align="center">
  <img src="assets/readme/rp-h1-inversevol.png" alt="Triple-panel bar chart « Capital vs Contribution au Risque selon la methode de ponderation » (axe Y Proportion 0→0.9, 5 actifs SPY/EFA/GLD/DBC/TLT, bleu=Poids capital, orange=Contribution risque) : (1) 60/40 Classique — SPY capital 0.40 / risque 0.54 ; TLT capital 0.40 / risque 0.21 ; EFA capital 0.20 / risque 0.25 ; GLD+DBC=0 (sous-pondere). (2) 1/N Egal — chaque actif capital 0.20 / risque varie 0.16-0.28 ; TLT risque 0.06 (sous-contributeur). (3) Risk Parity — capital inverse-vol : SPY 0.19 / EFA 0.19 / GLD 0.22 / DBC 0.18 / TLT 0.22 ; risques quasi-egalises 0.20-0.25 sauf TLT 0.09. SPY+EFA : 78.9% risque en 60/40 → 49.7% en RP." width="840"/><br>
  <em>H1 — triple-panel 60/40 / 1/N / RP ; SPY+EFA passe de 78.9 % à 49.7 % du risque, l'inverse-vol égalise (cell[6]·out[1]).</em>
</p>

**H2 — backtest Risk Parity 2015-2026.** Le **dual-panel** cell[8]·out[1] juxtapose les courbes de rendement cumulé « Risk Parity vs Benchmarks (2015-2026) » (haut) avec l'allocation Risk Parity au fil du temps en aires empilées (bas) — les poids dynamiques sont dominés par SPY en bull (40-60 %) puis basculent vers GLD/TLT en stress. Verdict cell[10]·out[0] : **Risk Parity Sharpe 0.544 < SPY Sharpe 0.655** (MITIGÉ — SPY domine sur la période bull 2015-2026), mais **RP MaxDD -20.26 % vs SPY -33.72 %** — RP perd ~17 % en Sharpe mais divise le drawdown par ~1.7×. Le verdict du notebook mentionne explicitement : « Risk Parity brille davantage sur les cycles complets (incluant 2000-2010) ».

<p align="center">
  <img src="assets/readme/rp-h2-backtest.png" alt="Dual-panel « Rendements cumules: Risk Parity vs Benchmarks (2015-2026) » : haut 4 strategies superposees (Risk Parity bleu continu final ~2.15× / SPY B&H rouge pointille final ~4.05× / 1/N egal vert pointille final ~2.10× / 60/40 SPY/TLT orange tirets final ~2.45×). Bas « Allocation Risk Parity au fil du temps » stacked area 0-1 (DBC bleu bas / EFA orange / GLD vert / SPY rouge / TLT violet haut ~20% stable). H2 verdict MITIGE : SPY domine bull 2015-2026, RP perd ~17% Sharpe vs SPY mais divise MaxDD par ~1.7×." width="840"/><br>
  <em>H2 — dual-panel equity + allocation ; RP Sharpe 0.544 < SPY 0.655 mais RP MaxDD -20.26 % vs SPY -33.72 % (cell[10]·out[0]).</em>
</p>

**H3 — impact TLT pendant la hausse des taux 2020-2023.** Le **quad-panel** cell[12]·out[0] analyse la « TLT Pain period (2020-2023) » sous 4 angles : (1) TLT vs SPY vs GLD base 100 — TLT perd ~40 %, SPY progresse ; (2) Volatilité roulante 60j annualisée — TLT explose en 2022 ; (3) Poids Risk Parity — TLT surpondéré mécaniquement par inverse-vol en période de stress ; (4) Performance relative. Métriques 2020-2023 cell[12]·out[1] : **RP +24.1 % ≈ 60/40 +24.5 % mais SPY +55.8 %** sur la fenêtre — RP perd ~32 pp face à SPY mais préserve l'isolation relative. Le diagnostic confirme le « problème TLT » : l'inverse-vol amplifie involontairement la baisse de l'obligation longue en période de hausse des taux.

<p align="center">
  <img src="assets/readme/rp-h3-tlt.png" alt="Quad-panel « Analyse de la periode TLT Pain (2020-2023) » : (haut-gauche) « TLT vs SPY vs GLD (2020-2023, base 100) » — SPY monte ~1.55 / TLT chute ~0.75 (perte ~25%) / GLD resilience ~1.30. (haut-droite) « Volatilite roulante 60j annualisee » (%) — spike COVID 2020 SPY 60% / TLT 35%, puis range 10-30%. (bas-gauche) « Poids Risk Parity » step chart 0.15-0.30 (5 lignes DBC/EFA/GLD/SPY/TLT entrelacees). (bas-droite) « Performance relative (2020-2023, base 100) » — SPY orange 1.55 / RP bleu 1.25 / 60/40 vert 1.25. RP perd ~32 pp vs SPY sur fenetre TLT pain, preserve isolation relative." width="840"/><br>
  <em>H3 — quad-panel TLT Pain ; RP 24.1 % ≈ 60/40 24.5 % « SPY 55.8 % sur la fenêtre (cell[12]·out[1]).</em>
</p>

**H4 — sensibilité au lookback de volatilité, robustesse confirmée.** Le **dual-panel** cell[14]·out[1] juxtapose « Sharpe selon la fenêtre de volatilité » et « Max Drawdown selon la fenêtre de volatilité » pour 5 lookbacks (20j/40j/60j/90j/120j). Verdict cell[14]·out[2] verbatim : **« Meilleur lookback = 40j ; La robustesse entre 40j et 120j confirme que le signal n'est pas overfitté »**. Range Sharpe 0.544-0.580 quasi-plat sur 5 valeurs (< 7 % de variation) = robustesse non-ajustée. Le 40j est marginal winner (S=0.580, MaxDD -19.29 %), 60j est la valeur par défaut. Pas de sur-ajustement à observer.

<p align="center">
  <img src="assets/readme/rp-h4-lookback.png" alt="Dual-panel sensibilite au lookback de volatilite : gauche « Sharpe selon la fenetre de volatilite » (5 barres bleues 20j/40j/60j/90j/120j range 0.544-0.580 quasi-plat, ligne rouge pointillee « Moyenne » ~0.56, winner marginal 40j S=0.580 / baseline 60j S=0.544 plus basse / range <7% variation = robustesse). Droite « Max Drawdown selon la fenetre de volatilite » (5 barres saumon quasi-identiques toutes ~-20%, variation <1%). H4 verdict : range Sharpe 0.544-0.580 = pas d'overfit, sweet-spot 40j, 60j baseline production." width="840"/><br>
  <em>H4 — dual-panel 5 lookbacks ; range Sharpe 0.544-0.580 quasi-plat = robustesse ; winner 40j S=0.580 / MaxDD -19.29 % (cell[14]·out[2]).</em>
</p>

**Analyse par régime — RP perd 2× moins en inflation 2022.** Le **bar chart mono-panel** cell[16]·out[2] juxtapose les rendements par régime (« Risk Parity vs SPY ») sur 5 régimes (Bull 2015-2019 / COVID 2020 / Recovery 2021 / Inflation 2022 / Recovery 2023-2025). Verdict cell[16]·out[3] verbatim : « Risk Parity devrait mieux résister en régimes de stress (COVID, Inflation 2022) au prix d'un retard en bull market (SPY domine en 2021, 2023-2025) ». **Bull 2015-19** : RP +29.7 % vs SPY +76.1 % (alpha -46.4 pp, RP sous-performe massivement). **Inflation 2022** : **RP -9.8 % vs SPY -18.6 %** — **RP perd 2× moins**. **Recovery 2023-2025** : RP +47.9 % vs SPY +86.3 % (alpha -38.3 pp). **Conclusion stratégique** : RP = compromis défensif (protection downside vs upside), pas un outil de surperformance en bull.

<p align="center">
  <img src="assets/readme/rp-regime.png" alt="Bar chart mono-panel « Rendements par regime: Risk Parity vs SPY » (Y Rendement total %) sur 5 regimes : (1) Bull 2015-2019 RP ~30% / SPY ~76% (alpha -46 pp RP sous-performe massivement) ; (2) COVID 2020 RP ~10% / SPY ~17% (alpha -7 pp) ; (3) Recovery 2021 RP ~13% / SPY ~31% (alpha -18 pp) ; (4) Inflation 2022 RP ~-11% / SPY ~-19% (RP PERD 2× MOINS, avantage defensif) ; (5) Recovery 2023-2025 RP ~48% / SPY ~86% (alpha -38 pp). RP = compromis defensif (protection downside vs upside), PAS outil de surperformance en bull." width="840"/><br>
  <em>Régimes — mono-panel RP vs SPY ; Inflation 2022 RP perd 2× moins (-9.8 % vs -18.6 %), Bull 2015-19 RP -46.4 pp sous SPY (cell[16]·out[3]).</em>
</p>

## Pourquoi cette stratégie a atteint un plafond

### Cause racine : anti-pattern en marché haussier

La parité de risque alloue le capital de façon inversement proportionnelle à la volatilité :

- **Hypothèse** : contribution égale au risque = meilleurs rendements ajustés du risque
- **Réalité (2015-2026)** : sous-performe face à des approches plus simples (Sharpe 0.544 vs 60/40 0.571, vs 1/N 0.511) — le compromis est plus défensif que productif

### Ce qui a été testé (et a échoué)

| Itération | Modification | Résultat | Pourquoi l'échec |
|-----------|--------------|----------|------------------|
| H5 | Remplacer TLT par IEF | Sharpe 0.330 | TLT supérieur en marché haussier obligataire (2015-2020) |
| H6 | Ciblage de vol 10 % | Négatif | Cash drag en faible vol (anti-pattern en hausse) |
| H7 | Filtre VIX > 25 (sortie vers cash) | Négatif | Trop peu de temps en stress (<15 %) = cash drag |

### Pourquoi la parité de risque sous-performe (2015-2026)

**Le problème du marché haussier** :

1. **Le ciblage de vol réduit l'exposition** : quand la vol est faible, la stratégie réduit l'exposition (elle rate les gains)
2. **Les obligations ont sous-performé après 2020** : corrélation IEF/TLT avec les actions durant les hausses de taux
3. **Risque égal != rendement égal** : les actifs faible-vol (obligations) pèsent sur les rendements en marché haussier
4. **Complexité sans bénéfice** : l'équi-pondéré simple sous-performe marginalement (Sharpe 0.511 vs RP 0.544) mais capture davantage d'upside absolu

### Comparaison aux alternatives (research.ipynb cell[10]·out[0])

| Stratégie | Sharpe | CAGR | Vol | Max DD | Complexité |
|-----------|--------|------|-----|--------|------------|
| Risk Parity | 0.544 | 7.28 % | 9.71 % | -20.26 % | Élevée (pondération vol, rééquilibrage) |
| 1/N (équi-pondéré) | 0.511 | 7.04 % | 9.86 % | -20.29 % | Faible |
| 60/40 statique | 0.571 | 8.42 % | 11.24 % | -27.24 % | Faible |
| SPY (benchmark) | 0.655 | 13.65 % | 17.79 % | -33.72 % | Aucune |
| AdaptiveAssetAllocation* | 0.518 | 8.0 % | — | — | Élevée (momentum + min-var) |

> *AdaptiveAssetAllocation : valeur de référence projet, non issue du notebook RiskParity.

**Lecture stratégique** : RP **gagne en Sharpe** face au 1/N (0.544 > 0.511, +6.5 %) et **perd moins** que le 60/40 en drawdown (-20.26 % vs -27.24 %, -25 %), mais reste **derrière SPY** en absolu (Sharpe 0.544 < 0.655, CAGR 7.28 % < 13.65 %). Le 60/40 simple **surperforme RP en Sharpe** (0.571 > 0.544) sur la fenêtre 2015-2026 — le plafond structurel est confirmé par le verdict « MITIGÉ » du notebook lui-même.

### L'anti-pattern du « ciblage de vol »

La parité de risque utilise souvent un ciblage de vol (ex : cible 10 % de vol) :

- **En période de faible vol** : réduit l'exposition pour maintenir la cible -> rate les gains
- **En période de forte vol** : augmente l'exposition -> achète haut, vend bas
- **Résultat net** : alpha négatif en marché trenduel

**2015-2026 a été majoritairement un marché haussier** : le ciblage de vol a systématiquement réduit l'exposition durant les meilleures périodes.

### Leçons retenues

1. **Parité de risque != repas gratuit** : une contribution égale au risque ne garantit pas de meilleurs rendements
2. **Le ciblage de vol dépend du régime** : fonctionne en marché irrégulier, échoue en marché trenduel
3. **La complexité n'est pas toujours meilleure** : le 60/40 équi-pondéré surperforme en Sharpe sur 2015-2026 (0.571 vs 0.544)
4. **Les obligations ne sont pas toujours des diversificateurs** : les hausses de taux post-2020 ont cassé la corrélation obligations/actions
5. **Savoir quand s'arrêter** : après 3 itérations ratées (H5-H7), le plafond est confirmé

## Quand la parité de risque PEUT fonctionner

Cette approche peut fonctionner dans :

- **Marchés latéraux / irréguliers** : où le ciblage de vol ajoute de la valeur
- **Environnements à forte volatilité** : où l'égalisation du risque protège le capital
- **Cycles complets incluant 2000-2010** : où le downside protection pèse davantage (cf verdict cell[10]·out[0] : « RP brille davantage sur les cycles complets incluant 2000-2010 »)
- **Versions sensibles au régime** : qui ajustent l'approche selon l'état du marché

**Pour les actions US 2015-2026** : plafond structurel confirmé.

## Valeur pédagogique

Cette stratégie illustre :

- L'**anti-pattern du ciblage de vol** en marché haussier
- **Complexité != performance** : le 60/40 simple peut battre une parité de risque sophistiquée (Sharpe 0.571 vs 0.544 sur 2015-2026)
- **Dépendance au régime** : une stratégie optimisée pour un régime peut échouer dans un autre
- **Le compromis risque/rendement** : RP perd ~17 % en Sharpe face à SPY mais divise le MaxDD par ~1.7×
- **Quand déclarer un plafond** : après 3+ itérations ratées avec des hypothèses claires

## Comparaison avec de meilleures alternatives

```python
# RiskParity (pondéré par la volatilité)
weights = 1 / volatility
weights /= weights.sum()

# Équi-pondéré (plus simple, Sharpe 0.511 sur 2015-2026)
weights = np.array([1/n] * n)

# 60/40 statique (Sharpe 0.571 sur 2015-2026 — surperforme RP)
weights = np.array([0.6, 0.4])

# Adaptative (momentum + min-var)
# Voir le projet AdaptiveAssetAllocation
```

## Références

- **AdaptiveAssetAllocation** : combine momentum + min-var (Sharpe 0.518)
- **AllWeather** : portefeuille multi-actif plus simple (Sharpe 0.667)
- **OPTIMIZATION_BACKLOG.md** : historique complet des itérations (H5-H7)

---

**Note** : cette stratégie est conservée comme contre-exemple. Le verdict documenté du notebook `research.ipynb` cell[10]·out[0] (« MITIGÉ : SPY domine sur la période bull 2015-2026 ») reste valide — RP n'est pas l'outil de surperformance en bull market, mais offre une **protection downside réelle** (MaxDD -20.26 % vs SPY -33.72 %, **2× moins de perte en Inflation 2022**). Pour un usage en production, considérer des approches plus simples (équi-pondéré ou 60/40) ou des alternatives basées momentum (AdaptiveAssetAllocation).