# AllWeather Strategy Lessons

## Cloud ID: 28657833 | Issue: #23

## Historique des versions

| Version | Sharpe | CAGR | MaxDD | Changement clé |
|---------|--------|------|-------|----------------|
| v1.0 | 0.250 | 5.9% | 23.5% | Dalio static, DBC 7.5% |
| v2.0 | 0.264 | 5.8% | 17.6% | Gold Heavy + SMA overlay 50% |
| v2.1 | 0.365 | 7.2% | 24.1% | Gold Heavy, suppression SMA |
| v2.2 | 0.325 | 6.5% | 20.4% | SMA 25% — degradation |
| v3.0 | **0.482** | 8.2% | 20.7% | TLT 20%, IEF 20%, XLP 10%, drift 3% |
| v4.0 | TBD | ~8.5%? | ~19%? | TLT 0%, IEF 40% (research H5 confirme) |

## Leçons consolidées (iter 3 + iter 4 research)

### Ce qui fonctionne

1. **Réduire TLT**: TLT est monotonement négatif pour le Sharpe sur 2015-2026.
   Chaque +5pp TLT dégrade Sharpe de ~0.005-0.010. La cause : cycle hausse taux
   Fed 2020-2023, TLT -40%. Leçon: sur période de hausse taux, duration longue détruit la valeur.

2. **IEF > TLT pour 2015-2026**: IEF (7-10 ans) est bien moins sensible aux chocs
   de taux nominaux. Corrélation avec SPY quasi-nulle (~0.0 vs TLT légèrement négative).

3. **XLP comme remplacement TLT partial**: Consumer Staples ajoute un rendement dividende
   ~3%/an, un faible beta, et performe mieux que TLT en période de hausse de taux.
   L'amélioration est honnête (pas du beta loading): XLP n'est pas un proxy SPY.

4. **Drift rebalancing 3% > 5%**: Plus réactif, confirmé sur 2+ itérations.
   Combiné avec trimestriel fixe = bon compromis transactions/réactivité.

5. **GLD 20%**: Inflation hedge solide, maintenu à travers toutes les versions.
   Ne pas toucher sauf si régime déflationniste confirmé.

### Ce qui ne fonctionne pas

1. **SMA overlay**: v2.0 et v2.2 ont testé SMA avec réduction 50%. Le Sharpe standalone
   est bon (~0.858) mais en QC le slippage mensuel annule le gain. Verdict: ne pas implémenter.

2. **DBC (Commodités)**: Structurellement mauvais à cause du contango futures roll decay.
   Sharpe standalone avec DBC = 0.691 vs sans DBC = 0.817.

3. **Vol targeting sans levier**: Le portfolio AllWeather a une vol naturelle ~7-9%/an.
   Sans levier (scale max 1.0), le vol targeting n'a presque jamais d'effet (scale~1.0).
   Complexité QC non justifiée.

4. **TIPS (TIP) en masse**: TIP corrélé avec IEF (double exposition bonds intermédiaires).
   Substitution partielle TLT→TIP ok (améliore 2020-2023) mais gain marginal sur 11 ans.
   Seuil: n'inclure TIP que si gain standalone > +0.03 Sharpe.

### Findings notebook iter 4 (H5-H8)

- **H5 CONFIRMEE**: TLT sweep 0-40% montre relation monotone décroissante Sharpe/TLT%
- **H6 PARTIELLE**: TIP_replaces_TLT améliore 2020-2023 mais marginal sur ensemble période
- **H7 INFIRMEE**: Vol targeting inutile sans levier (scale=1.0 quasi-permanent)
- **H8 HONNETE**: AllWeather: MaxDD < SPY, Alpha > 0, Sharpe < SPY (pédagogiquement valide)

### Plafond structurel

Sharpe ~0.50-0.55 est le plafond réaliste pour AllWeather 2015-2026 sans levier.
- 2015-2026 = bull market quasi-continu, SPY Sharpe ~0.55
- AllWeather est une stratégie de GESTION DU RISQUE, pas une stratégie alpha
- MaxDD < 21% vs SPY ~34% : c'est la vraie valeur ajoutée

### Configuration v4.0 (implémentée 2026-03-08)

```python
target_allocations = {
    "SPY": 0.30,   # Actions US
    "IEF": 0.40,   # Obligations intermédiaires (was 20%, absorbe TLT)
    "GLD": 0.20,   # Or
    "XLP": 0.10,   # Consumer Staples défensif
}
rebalance_threshold = 0.03  # Drift 3%
# Rebalancement: trimestriel + drift
```

### Bug QC connu: update_file_contents requiert `name` pas `fileName`

```python
# CORRECT
model = {"projectId": 28657833, "name": "main.py", "content": "..."}
# INCORRECT (erreur Pydantic validation)
model = {"projectId": 28657833, "fileName": "main.py", "content": "..."}
```
