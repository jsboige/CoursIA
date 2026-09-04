# L1b — TSMOM-CF (Baltas & Kosowski 2017), ablation à quatre configurations

Distillation de l'article QC research [#15272](https://www.quantconnect.com/research/15272/)
*« Improved momentum strategy on commodities futures »*, sous l'EPIC #11698.
Lecture analytique et verdict de différenciation : issue #14462.

## Verdict

| Instrument | Verdict |
|---|---|
| **Stratégie** (gate Sharpe, règle C) | **NO BEATS** — les quatre configurations, aux deux fréquences |
| **Estimateur de volatilité** (Diebold-Mariano) | **NON CONCLUANT** — 0 / 0 / 26 symboles, p médiane 0,579 |

Aucune des trois corrections proposées par l'article ne fait passer le TSMOM
au-dessus du buy-and-hold sur notre panier. La correction qui change réellement
le résultat n'est **aucune des trois** : c'est la **fréquence de rebalancement**,
que l'article ne présente pas comme un levier parce qu'il rebalance mensuellement
depuis le départ.

## Ce que l'article corrige, et où ça tombe dans notre code

L'article nomme trois faiblesses du TSMOM de Moskowitz-Ooi-Pedersen (2012). Elles
tombent chacune sur une ligne de notre propre baseline `L1_tsmom.py` :

| axe | `L1_tsmom.py` (Moskowitz 2012) | TSMOM-CF (l'article) |
|---|---|---|
| signal | `np.sign(past_return)`, binaire | t-stat 12 mois, capée sur [−1, +1] |
| volatilité | close-to-close, écart-type glissant | Yang-Zhang (2000), OHLC |
| allocation | equal-weight 1/N | `CF(rho) = sqrt(N / (1 + (N−1) rho))` |

Un TSMOM-CF complet qui battrait la baseline ne dirait pas **lequel** des trois
leviers porte l'effet. D'où l'ablation :

    A  sign   + close-to-close + 1/N   (= L1, contrôle de reproduction)
    B  t-stat + close-to-close + 1/N   (levier 1 seul)
    C  t-stat + Yang-Zhang     + 1/N   (leviers 1+2)
    D  t-stat + Yang-Zhang     + CF    (TSMOM-CF complet)

## Résultats — rebalancement mensuel (la fréquence de l'article)

26 symboles à OHLC complet, 2015-01-02 → 2026-05-22, 5 graines (0/1/7/42/99),
walk-forward 5 folds, gap 21 j, coûts 5 bps actions / 10 bps crypto.

| config | Sharpe brut | Sharpe net | σ inter-graines | Δ vs B&H | edge | turnover/j | net (conv. L1) | verdict |
|---|---|---|---|---|---|---|---|---|
| A `sign` + c2c + 1/N | +0,3791 | **+0,3509** | 0,1028 | −0,7101 | −5,76σ | 0,126 | +0,1456 | NO BEATS |
| B `t-stat` + c2c + 1/N | +0,4748 | **+0,4467** | 0,0810 | −0,6143 | −5,80σ | 0,102 | +0,1324 | NO BEATS |
| C `t-stat` + YZ + 1/N | +0,4207 | **+0,3878** | 0,1477 | −0,6732 | −4,14σ | 0,116 | +0,0788 | NO BEATS |
| D `t-stat` + YZ + CF | +0,3995 | **+0,3678** | 0,1546 | −0,6932 | −4,10σ | 0,133 | +0,1593 | NO BEATS |

Baseline buy-and-hold equal-weight, mêmes vues, mêmes graines :
**Sharpe 1,0610** (écart-type inter-graines 0,0682).

`net (conv. L1)` est le **même résultat** facturé selon la convention de
`L1_tsmom.py` — un aller-retour plein notionnel par ligne touchée, chaque jour.
La colonne est là pour que l'écart entre les deux conventions reste **mesuré**
plutôt qu'affirmé (voir « Deux défauts de `L1_tsmom.py` » plus bas).

## Sensibilité — rebalancement journalier (la fréquence de `L1_tsmom.py`)

| config | Sharpe brut | Sharpe net | Δ vs B&H | edge | turnover/j | net (conv. L1) |
|---|---|---|---|---|---|---|
| A | +0,4948 | **−0,5620** | −1,6230 | −18,07σ | 4,606 | −5,4184 |
| B | +0,5263 | **−0,4508** | −1,5118 | −17,60σ | 3,533 | −7,4136 |
| C | +0,5813 | **−0,4368** | −1,4978 | −16,91σ | 3,579 | −7,5391 |
| D | +0,5400 | **−0,4286** | −1,4896 | −16,91σ | 4,129 | −5,4914 |

## Trois lectures

### 1. La fréquence de rebalancement domine les trois leviers de l'article

Le notionnel déplacé par jour passe de **3,5-4,6 en journalier à 0,10-0,13 en
mensuel** — un facteur 31 à 37. C'est assez pour retourner le **signe** du Sharpe
net : les mêmes quatre configurations rendent −0,43 à −0,56 en journalier et
+0,35 à +0,45 en mensuel.

Le mécanisme est mécanique et n'a rien de subtil : la position est
`signal × (vol_cible / vol_estimée)`. Les deux facteurs bougent tous les jours,
donc une position recalculée quotidiennement **dérive tous les jours** et se
refacture tous les jours, même quand le signal ne change pas de camp. Une
position tenue entre deux dates de rebalancement ne coûte rien.

Le TSMOM de Moskowitz (2012) comme celui de Baltas & Kosowski (2017) sont des
stratégies à rebalancement **mensuel**. Tester l'article à une fréquence qu'il
n'emploie pas ne serait pas un test de l'article.

### 2. Sous la bonne fréquence, seul le levier 1 travaille — et le classement s'inverse

| levier | effet sur le Sharpe brut (mensuel) | effet (journalier) |
|---|---|---|
| 1 — t-stat au lieu de `sign` (B−A) | **+0,096** | +0,032 |
| 2 — Yang-Zhang au lieu de c2c (C−B) | **−0,054** | +0,055 |
| 3 — CF au lieu de 1/N (D−C) | **−0,021** | −0,041 |

Le levier 2 **change de signe** entre les deux fréquences. Lu en journalier
seulement, on conclurait que Yang-Zhang améliore la performance brute ; lu à la
fréquence de l'article, il la dégrade. C'est le contrôle qui justifie de ne pas
publier une ablation sans avoir vérifié qu'elle est menée à la fréquence de la
stratégie testée.

Le levier 1 est le seul qui tienne aux deux fréquences, et c'est cohérent avec sa
nature : passer de `sign` (binaire) à une t-stat capée conserve l'information
d'**intensité** de la tendance, là où le signe la jette.

### 3. Yang-Zhang est moins biaisé, pas plus précis

Test de Diebold-Mariano sur une perte de **précision** (`loss_fn="mse"`),
Yang-Zhang contre close-to-close, cible = volatilité réalisée sur les 21 jours
**suivants**, HAC à `max_lag = 20` pour couvrir le recouvrement des fenêtres.

- **0 victoire Yang-Zhang, 0 victoire close-to-close, 26 non concluants** sur 26
  symboles ; p médiane **0,579**.
- Biais signé moyen — `mean(estimateur − réalisé)` : **YZ +0,002512**,
  **c2c +0,012828**. Yang-Zhang est ~5× moins biaisé.

Les deux mesures ne disent pas la même chose et ne se remplacent pas : le DM
mesure la **précision** (l'erreur quadratique), le biais mesure le **décalage
systématique**. Yang-Zhang gagne sur le second sans gagner sur le premier — un
écart qu'un rapport ne citant que le DM effacerait, et qu'un rapport ne citant
que le biais surinterpréterait (cf #10938 / #10956 : `loss_fn="linear"` est un
contrôle de biais, jamais la jambe de précision d'un verdict).

Le DM ne dit **rien** de la stratégie. Il tranche la claim (b) de l'article, et
rien d'autre : l'estimateur de volatilité est le seul des trois leviers qui soit
une **prévision** au sens propre, donc le seul auquel un DM s'applique
honnêtement.

## Portée — ce que ce module ne teste pas

L'article backteste des **futures de matières premières** sur **janvier 2018 →
septembre 2019**, soit 20 mois, et y rapporte Sharpe 0,198 pour TSMOM-CF contre
−0,746 pour le TSMOM de base et 0,46 pour SPY sur la même fenêtre. Notre panier
anti-biais est à dominante **actions + crypto** sur **11 ans**, et son
buy-and-hold rend 1,06 : la barre est incomparablement plus haute.

Un NO BEATS ici ne réfute donc pas l'article ; il dit que **les trois corrections
ne transportent pas leur effet** de son univers au nôtre. Le seul résultat qui se
transporte est le classement des leviers entre eux, et il est mesuré ci-dessus.

À noter que l'article, dans sa propre fenêtre, ne bat pas non plus son benchmark :
0,198 contre 0,46 pour SPY.

## Ce que les graines perturbent

Une graine tire une **vue du problème**, et la même vue sert au modèle et à sa
baseline (comparaison appariée) :

- un sous-panier de 80 % des symboles, sans remise ;
- un décalage d'origine de 0 à 40 jours ouvrés — qui décale aussi la **grille de
  rebalancement**, donc la date d'entrée.

C'est ce qui rend le σ inter-graines du gate mesurable. Voir le défaut symétrique
de `L1_tsmom.py` ci-dessous.

## Deux défauts de `L1_tsmom.py`, signalés et non corrigés ici

Suivis dans l'issue **#14470** (mesures reproduites, acceptance écrite).

Trouvés en construisant le contrôle de reproduction (config A). Ils ne sont
**pas** corrigés dans ce module — principe 3 du `CLAUDE.md` : signaler le mauvais
code découvert, le traiter en sujet séparé.

1. **Boucle de graines inerte.** `L1_tsmom.py:124` construit
   `rng = np.random.default_rng(seed)` et ne s'en sert jamais (le symbole
   n'apparaît qu'une fois dans le fichier) ; sa boucle buy-and-hold (l. 233) n'en
   construit même pas. Le splitter walk-forward étant déterministe, les quatre
   graines rendent des nombres **identiques** : l'écart-type inter-graines y vaut
   0, donc `t_stat = delta / 0 → 0`, donc la clause `t_stat >= 2.0` de son gate
   rend le verdict `BEATS` **structurellement inatteignable**. Son gate
   multi-graines ne mesure rien. Écrit comme test :
   `test_zero_dispersion_can_never_reach_beats`.

2. **Modèle de coûts sur-facturé.** `L1_tsmom.py:158-173` compte un ordre dès
   qu'une position bouge, puis facture un aller-retour **plein notionnel** :
   `trades_per_day * 2 * cost_per_trade / n_assets`. Comme la position dérive
   chaque jour avec la volatilité estimée, chaque ligne est facturée chaque jour.
   Mesuré sur notre panier en journalier : 13,5 « ordres » par jour pour 21
   lignes. L'écart est la colonne `net (conv. L1)` des deux tableaux ci-dessus.

Le second explique en partie le NO BEATS publié de L1 — mais **en partie
seulement** : sous facturation proportionnelle au turnover **et** rebalancement
mensuel, le Sharpe net redevient positif (+0,35 à +0,45) et le verdict reste
NO BEATS, cette fois pour la bonne raison — la stratégie est simplement
en dessous du buy-and-hold.

## Reproduction

```bash
cd MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/scripts

# tests (23, chacun avec son contrôle positif)
python -m pytest tests/test_l1b_tsmom_cf.py -q

# ablation à la fréquence de l'article (défaut)
python L1b_tsmom_cf.py --seeds 0 1 7 42 99

# sensibilité à la fréquence de L1_tsmom.py
python L1b_tsmom_cf.py --seeds 0 1 7 42 99 --rebalance 1 \
    --output ../checkpoints/l1b_tsmom_cf/l1b_results_daily.json
```

Sorties dans `checkpoints/l1b_tsmom_cf/` (répertoire gitignoré — les nombres de
cette page sont donc la trace committée de la mesure).

## Script

`scripts/L1b_tsmom_cf.py` · tests `scripts/tests/test_l1b_tsmom_cf.py`
