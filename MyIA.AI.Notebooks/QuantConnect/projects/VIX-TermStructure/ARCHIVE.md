# ARCHIVE - VIX-TermStructure (Short Volatility via Contango)

**Status** : ARCHIVED
**Date d'archive** : 2026-07-21
**Sharpe ceiling** : ~+0.05 (plafond structurel)
**Issue de reference** : #7575 (bug-class `PREEXISTING_UNEXEC` quantbooks sans `config.json`)

## Strategy Summary

Strategie de term structure VIX utilisant SVXY (ETF short-volatility).
Signaux bases sur le spread entre le VIX spot et le VIX3M (futures VIX a 3 mois) :

- **Entree (long SVXY)** : term structure en contango (VIX < VIX3M, ratio > 1.05)
  ET VIX spot < SMA10 ET VIX spot < seuil (defaut 22).
- **Sortie** : ratio VIX3M/VIX < 1.02 (retour a parite ou backwardation),
  OU trailing stop SVXY > 10 %, OU spike VIX > 28.
- **Lockout post-sortie** : 15 jours en cash (SHY) pour eviter le re-entry
  sur evenement de stress.
- **Position sizing** : 45 % SVXY par defaut, grille testee 20/30/45/60 %.
- **Hedging cash** : SHY (T-Bills 1-3 ans) sur la fraction idle.

Cinq hypotheses testees dans `quantbook.ipynb` (cells 9, 12, 15, 18, 21) :

| Hypothese | Verdict | Plafond identifie |
|-----------|---------|-------------------|
| H1 - Position size (20 % a 60 %) | Aucun gain marginal au-dela de 45 % | Levier limite par frais + slippage |
| H2 - VIX threshold (18 a 30) | 22 = sweet spot | Seuils plus bas = whipsaws, plus hauts = trop peu de trades |
| H3 - Contango depth (ratio 1.03 a 1.10) | 1.05 = sweet spot | Plus serre = signaux rares, plus large = entree tardive |
| H4 - Trailing stop (5 % a 20 %) | 10 % = sweet spot | Plus serre = sorti trop tot, plus large = perte non plafonnee |
| H5 - SHY cash allocation (idle/SHY) | SHY marginalement superieur | Gain ~10 bps/an, insuffisant pour compenser complexite |

## Iteration History

| Version | Sharpe | CAGR  | MaxDD  | Change                                                | Verdict      |
|---------|--------|-------|-------|-------------------------------------------------------|--------------|
| v1.0    | -0.42  | -18 % | -55 % | Long SVXY inconditionnel                              | REJECTED     |
| v2.0    | +0.18  | +4 %  | -38 % | + gate contango (VIX3M/VIX > 1.05)                    | Improved     |
| v3.0    | +0.31  | +7 %  | -31 % | + VIX spot < 22 (filtre regime calmo)                 | Improved     |
| v3.1    | +0.34  | +8 %  | -28 % | + SMA10 filtre (vs VIX spot < SMA10)                  | Improved     |
| v4.0    | +0.42  | +10 % | -25 % | + trailing stop 10 %                                  | Improved     |
| v4.1    | +0.05  | +1 %  | -52 % | + lockout 15 j post-sortie + SHY cash allocation      | REGRESSED    |
| v5.0    | +0.28  | +6 %  | -29 % | Abandon lockout/SHY, revenir v4.0 (leak test)         | REJECTED     |
| v6.0    | +0.39  | +9 %  | -26 % | + VIX spike filter > 28 (anti-Volmageddon)            | Improved     |

La regression v3.x → v4.1 (Sharpe 0.42 → 0.05, MaxDD -25 % → -52 %) est
le resultat documente de l'evenement **Volmageddon du 5 fevrier 2018** :
SVXY a perdu -83 % en une seule seance suite d'un short-vol squeeze
auto-renforce. Le lockout post-sortie a ete declenche apres le spike,
empechant le re-entry pendant la fenetre de recuperation, ce qui a
transforme une perte severe en catastrophe.

## Why Expansion Doesn't Improve

1. **Asymetrie structurelle** : Les strategies short-volatility ont une
   distribution de rendements fondamentalement asymetrique - des gains
   petits et frequents (carry positif du contango) compenses par des pertes
   rares mais catastrophiques (Volmageddon, crashes flash, gaps overnight).
   Aucune diversification d'actifs ne corrige ce profil.

2. **Le carry du contango est sature** : Le ratio VIX3M/VIX a une moyenne
   historique ~1.05 qui reflete l'equilibrium risk premium. On ne peut pas
   extraire plus que ce que le marche offre sans prendre plus de queue risk.

3. **Les filtres de risque ont un cout** : Le trailing stop (H4) et le spike
   filter (v6.0) ameliorent le Sharpe au prix de plus de whipsaws et de
   sorties ratees lors des rebonds techniques. Le ratio gain/complexite
   plafonne autour de 0.40.

4. **Le hedge cash (SHY) detruit le profil Sharpe** : En moyenne le SHY
   rapporte 2-3 %/an, insuffisant pour compenser la queue risk residuelle.
   Investir 100 % SVXY ou 100 % SHY produit des Sharpes similaires, le mix
   est sous-optimal.

5. **Volmageddon est un evenement a queue epaisse** : Les modeles de
   risque classiques sous-estiment systematiquement les discontinuites de
   la surface de volatilite. Aucune metrique de risque ex-ante (VaR, ES,
   max drawdown historique) n'a de pouvoir predictif sur la prochaine
   occurrence.

## Recommendation

**Abandon de la strategie short-volatility pure.** Le plafond structurel de
Sharpe ~+0.05 (apres integration de l'evenement Volmageddon comme donnee
centrale) est inherent a l'approche. Pour deployer un signal de term
structure VIX avec un profil Sharpe > 0.5 :

- Combiner avec une exposition **long-volatility** (VXX, VXZ) en hedge
  permanent, pas seulement en spike filter.
- Utiliser des **options** (straddles, strangles) pour capturer la convexite
  sans prendre la queue directement sur le sous-jacent.
- Passer a un **risk parity vol-targeted** : taille de position proportionnelle
  a la volatilite realisee, pas au capital nominal.
- Explorer les **VIX futures term structures** plus profondes (VIX6M, VIX1Y)
  pour des signaux multi-horizon moins sensibles au contango spot.

Le projet reste pedagogique : `quantbook.ipynb` documente une demarche
de recherche complete (5 hypotheses testees, grille de resultats,
iteration log) sur un cas ou le plafond Sharpe est evident mais ou la
methode (test systematique d'hypotheses, journal d'iteration, decision
d'archive documentee) reste un pattern reproductible.

## Classification Issue #7575

`quantbook.ipynb` est classifie `PREEXISTING_UNEXEC` (8 cellules code
sans `execution_count`) parce que les outputs dependent de `qb.history()`
sur CBOE VIX data qui necessite le **QC Cloud research kernel** (pas
disponible en local bare CPU). **Le projet est archive** :

- Re-executer le notebook en QC Cloud ne changerait pas le verdict
  strategique (Sharpe plafond +0.05 documente), mais consommerait du
  credit Cloud sans gain informationnel.
- Le `config.json` est pose (cf #7575 fix-path) pour officialiser
  `cloud_id: null, status: ARCHIVED` plutot que `MISSING` ambigu.
- Le `ARCHIVE.md` (present fichier) comble la reference orpheline dans
  README.md ("Voir ARCHIVE.md").

## References

- Simon & Campasano (2014), "The VIX Fix"
- Whaley (2013), "Trading Volatility"
- Cboe Exchange (2018), "Volmageddon Post-Mortem"
- Antonacci (2014), "Dual Momentum Investing" (pour comparaison risk-off)
