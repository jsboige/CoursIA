# L6 — Sizing régime-conditionnel par probabilité HMM (ladder #1409, rung 6)

> Script associé : [`scripts/s5_hmm_regime_sizing.py`](../scripts/s5_hmm_regime_sizing.py)
> (le préfixe `s5` = 5ᵉ script de la série *sizing* ; le rung *Curriculum* est
> **L6** — la 6ᵉ hypothèse falsifiable de la V3, distincte de la famille *trend*).
> Résultat brut : [`scripts/results/s5_hmm_regime_sizing/{verdict.md, results.json}`](../scripts/results/s5_hmm_regime_sizing/).

## Verdict : ROBUST NO BEATS

Utiliser la **probabilité de régime HMM continue** comme scalaire de sizing
(blend `(1-p_bear)·w_bull + p_bear·w_bear`) **ne bat pas** le switch dur de S4,
à **aucun** niveau de shrinkage Ridge testé. Le verdict est *robuste* au sweep
d'alpha {0.0, 0.1, 0.5, 1.0} : NO BEATS partout → l'éventuelle sous-performance
n'est pas un artefact de shrinkage (cf. finding 1).

## Hypothèse (décision coordination ai-01 2026-07-19, #1409)

L1-L5 (overlays *trend*) sont tous NO BEATS. L6 est définie comme l'**unique**
hypothèse falsifiable DISTINCTE de la famille trend : un **sizing régime-conditionnel
via l'ÉTAT de régime HMM (probabilité par jour)**, pas un nouvel overlay trend.
La barre de preuve est la même que chaque rung du Curriculum : walk-forward 5-fold,
≥4 seeds, edge ≥ 2σ cross-seed, coûts de transaction, verdict honnête
(ai-01 : « si L6 NO BEATS → l'Epic se parque honnêtement, pas de L7 inventé »).

Le delta architectural vs les keepers V2 (S3/S4) : **S3 et S4 fittent tous deux**
le modèle `MarkovRegime` 2-états, et `s3_hmm_regime.fit_markov_regime` renvoie
même les `smoothed_probs` par jour (col 0 = bull, col 1 = bear) — **mais les deux
prédécesseurs jettent la probabilité à l'étape OOS** et collapsent sur le label
dur argmax avant sizing (S3:256, S4:289). Le sizing de S4 est un tilt défensif
`if regime_label == 1`. La question « la probabilité *continue* de régime
utilisée comme scalaire de sizing bat-elle le switch dur ? » n'avait jamais été
posée dans le Curriculum. L6 la pose.

## Méthode

1. **Inférence de régime OOS réelle** (PAS in-sample-sur-le-bloc-test comme S3/S4) :
   re-fit du HMM sur la fenêtre d'entraînement expansive `[0, t-1[` tous les
   `REFIT_EVERY` (22) jours, lecture de la probabilité lissée du jour courant via
   la récursion de filtre du modèle sur la slice d'entraînement. **Aucune fuite
   d'information future** dans l'appel de régime (sémantique OOS honnête ;
   vérifié S3:248-256, S4:287-289 — ni l'un ni l'autre ne le fait).
2. **Sizing continu** : blend des vecteurs de poids inverse-vol bull/bear par
   `p_bear = smoothed_probs[-1, 1]` :
   `w = (1 - p_bear)·w_bull + p_bear·w_bear`, au lieu du `np.where` dur de S4.
   Avec shrinkage Ridge + projection simplexe.
3. **Coût de transaction turnover-aware** (`estimate_trade_cost`) mesuré sur
   (old, new) AVANT réassignation — le bug same-dict de `s7_composite` (PR #8591)
   est évité par construction ici.
4. **Sweep d'alpha** {0.0, 0.1, 0.5, 1.0} : alpha = shrinkage Ridge vers
   equal-weight (alpha=0.0 = inverse-vol bull/bear pur, amplitude de blend max ;
   alpha=1.0 = défaut S4). Robustesse au shrinkage = exclut l'artefact
   « shrinkage masque la sous-performance ».

**Baselines** : `equal` (equal-weight 11 actifs), `inv_vol` (inverse-vol statique),
`s4_hard` (switch dur de S4 reproduit — la baseline *directe* qui isole la question
continue-vs-dur). Si L6 ne bat pas `s4_hard`, la probabilité n'ajoute rien et
l'hypothèse est réfutée.

**Univers** : le panel 11-actifs de S4 (SPY, TLT, XLF, XLK, XLE, XLV, XLY, XLI,
XLB, XLU, XLP). Données via yfinance (data-source-to-convert, AUTORISÉ).

**Gate** : BEATS si `mean(delta_sharpe_vs_s4_hard) > GATE_SHARPE_DELTA`, t ≥ 2.0,
≥ 3/4 seeds positifs, p_sign < 0.05. Sinon NO BEATS.

## Résultats — sweep d'alpha (4 seeds × 5-fold, OOS)

| alpha | Continue | Dur (s4_hard) | Equal | Delta vs dur | t | seeds > 0 | Verdict |
|-------|----------|---------------|-------|--------------|---|-----------|---------|
| 0.0 | 0.3385 | 0.7393 | 0.7604 | **-0.4008** | -2125 | 0/4 | NO BEATS |
| 0.1 | 0.4174 | 0.7393 | 0.7604 | -0.3219 | -1638 | 0/4 | NO BEATS |
| 0.5 | 0.6330 | 0.7393 | 0.7604 | -0.1063 | -426 | 0/4 | NO BEATS |
| 1.0 | 0.7394 | 0.7393 | 0.7604 | +0.0001 | 0.33 | 2/4 | NO BEATS |

Détail par seed (alpha=1.0, défaut S4) :

| Seed | Continue | Dur | Delta | mean p_bear | frac jours bear |
|------|----------|-----|-------|-------------|-----------------|
| 0 | 0.7396 | 0.7396 | +0.0000 | 0.409 | 0.396 |
| 1 | 0.7397 | 0.7403 | -0.0005 | 0.305 | 0.263 |
| 7 | 0.7395 | 0.7396 | -0.0001 | 0.280 | 0.264 |
| 42 | 0.7389 | 0.7379 | +0.0010 | 0.319 | 0.341 |

## Findings clés

1. **Continue-vs-dur = bruit quand un régime domine.** Au défaut S4 (alpha=1.0),
   la probabilité continue n'apporte rien sur le switch dur : delta Sharpe
   **+0.0001** (t=0.33, non significatif, 2/4 seeds). L'amplitude du blend ne sert
   à rien parce que le régime est **rarement bear** (mean `p_bear` ~0.28-0.41,
   fraction de jours bear ~0.26-0.40) : le vecteur de poids bear est peu engagé,
   switch dur ou blend continu convergent.

2. **L'amplitude de blend maximale détruit la performance, elle ne l'améliore pas.**
   À alpha=0.0 (inverse-vol bull/bear pur, blend à pleine amplitude), la version
   continue s'effondre à **0.3385** vs **0.7393** pour le switch dur (delta -0.40).
   Plus on laisse le blend s'exprimer, plus on sous-performe — l'opposé de ce que
   l'hypothèse prédisait. Un sizing régime-conditionnel agressif dans un univers
   bull-dominé sur-alloue au vecteur bear.

3. **Le sizing régime-conditionnel (dur OU continu) ne bat pas le naive equal-weight.**
   Le switch dur (0.7393) ET le blend (≤0.7394) sont **sous** l'equal-weight (0.7604).
   L'inverse-vol statique (0.4214, déterministe) est encore sous. Le conditionnement
   par régime n'ajoute pas d'alpha au-delà de la pondération égale sur cet univers.

   **Réserve de comparabilité, à ne pas gommer** : cette comparaison-là n'est pas
   symétrique en coûts. Les stratégies régime-conditionnelles paient 5 bps sur leur
   turnover quotidien ; les baselines statiques (`equal`, `inv_vol`) n'en paient
   **aucun** — le script le dit lui-même (`walk_forward_sizing`, docstring : *« Static
   baselines (equal/inv_vol) pay no cost »* ; `strat["equal"]` n'a pas de terme de
   coût). L'écart de **0.021** Sharpe vs `equal` est donc un **majorant** du déficit
   réel : une part en revient au coût que la baseline ne supporte pas. Ce qui n'est
   **pas** affecté, c'est le verdict du gate — `continuous` vs `s4_hard` sont tous
   deux facturés au même barème, donc le ROBUST NO BEATS de l'hypothèse L6 tient
   sans réserve. La conclusion prudente est : le conditionnement par régime
   n'établit pas d'alpha au-delà de l'equal-weight sur cet univers ; il faudrait un
   run à coûts symétriques pour le réfuter au sens fort.

4. **Robustesse au shrinkage = l'artefact exclus.** NO BEATS à CHAQUE alpha
   (concern Hermes 1) : la sous-performance n'est pas un masquage par shrinkage.
   Mesures `p_bear`/frac-bear sur la fenêtre OOS **entière** (concern Hermes 2),
   cadence de rebalancement **quotidienne par design** (concern Hermes 3 :
   conservateur pour NO BEATS — plus de rebalancing = plus de coût de turnover).

5. **L'OOS HMM réelle (vs S3/S4 in-sample) ne sauve pas l'hypothèse.** L6 est
   méthodologiquement PLUS honnête que ses prédécesseurs (re-fit expanding tous
   les 22j, zéro fuite future), et réfute quand même. Le gain de rigueur OOS ne
   transforme pas un signal absent en signal présent.

## Implication pour la ladder (#1409)

L6 **clôt la branche regime-sizing** du Curriculum V3. Avec L1 (TSMOM), L2 (CS
momentum), L3 (trend long-horizon), L5 (vol-targeted composite) et L6 (HMM
regime-sizing) tous **NO BEATS**, et L4 (Decision Transformer, action-based) le
**seul** BEATS, l'évidence dit : **l'alpha sur cet univers provient de politiques
d'action apprises, pas d'overlays trend ni de sizing régime-conditionnel sur une
allocation risk-based.**

L'hypothèse centrale de l'Epic — que des signaux *long-horizon trend & regime*
ajoutent de la valeur au-delà de l'equal-weight après coûts — est **réfutée** sur
cet univers (11 ETF anti-FAANG, 2017-2026, yfinance daily), sous la réserve de
comparabilité posée au finding 3 (baselines statiques non facturées). Conformément à la
décision ai-01 2026-07-19 (« si L6 NO BEATS → Epic se parque honnêtement, pas de
L7 inventé »), l'Epic #1409 atteint son **point de parc honnête** : un résultat
négatif multi-axes documenté, sans invention d'un L7 ad hoc.

## Données

- 11 symboles (SPY, TLT, 9 ETF sectoriels), ~2373 lignes, 2017-01-03 → 2026-06-11
  (yfinance daily close, data-source-to-convert AUTORISÉ).
- Observations OOS : 1975 par seed, 5-fold expanding, re-fit HMM tous les 22j.
- Coûts : `TX_COST_BPS = 5` appliqué au turnover des stratégies actives
  (`continuous`, `hard`) ; baselines statiques (`equal`, `inv_vol`) non facturées
  — asymétrie assumée, portée du finding 3.
- Runtime : CPU (conda `coursia-ml-training`, statsmodels 0.14.6, regle F).

## Script

`scripts/s5_hmm_regime_sizing.py` — sorties vers
`scripts/results/s5_hmm_regime_sizing/{results.json, verdict.md}`. Réutilise les
briques `s3_hmm_regime.fit_markov_regime` (régime OOS) et
`s4_inverse_vol_ridge_v2` (poids régime-conditionnels) corrigées du bug turnover
#8591.

## Références

- Hamilton (1989) — regime-switching models.
- Corsi (2009) — HAR-RV (l'entrée de régime de vol).
- S3/S4 (keepers V2) : `scripts/s3_hmm_regime.py`, `s4_inverse_vol_ridge_v2.py`.
- L5 (rung précédent, NO BEATS) : [`L5_vol_targeted_composite.md`](L5_vol_targeted_composite.md).
- Correctif turnover S7 : PR #8591 (c.884).
- Robustesse alpha-sweep + concerns Hermes : PR #8592 (c.885/c.886).
