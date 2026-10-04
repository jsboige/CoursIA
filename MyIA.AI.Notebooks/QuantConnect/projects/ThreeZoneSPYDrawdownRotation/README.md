# Three-Zone SPY Drawdown Rotation

Évaluation sous frais IBKR de la stratégie publique **781** « Three-Zone SPY
Drawdown Rotation Strategy » du Strategy Explorer QuantConnect (auteur affiché :
Viliam Balara, v1.0.0 du 29/09/2026). Protocole complet : issue
[jsboige/CoursIA#18905](https://github.com/jsboige/CoursIA/issues/18905).

## Résumé

| Paramètre | Valeur |
|-----------|--------|
| **Type** | Rotation de régime (drawdown SPY) |
| **Signal** | Baisse du SPY depuis son plus haut 52 semaines |
| **Zones** | verte < 5 % ; jaune 5-10 % ; rouge ≥ 10 % (grille, voir ci-dessous) |
| **Portefeuille dividende** | ≤ 20 titres, rendement ≥ 3 %, payout 5-80 %, historique 10 ans |
| **Revue** | Hebdomadaire (lundi après l'ouverture) |
| **Frais** | Interactive Brokers (`InteractiveBrokersFeeModel`) |
| **Fenêtre** | 2018-01-01 → 2026-09-25 |

## Réimplémentation déclarée

Le projet source (37135744) n'est **pas lisible par le compte de la flotte**
(`read_project` : « You do not own this project ») et la fiche n'est pas
accessible anonymement. Cette implémentation suit la **description publique**
de la fiche ; les seuils exacts des zones vivent dans le code inaccessible de
l'auteur. La grille de robustesse (point 4 du protocole) balaie ces seuils :

| Paramètre | Défaut | Grille prévue |
|-----------|--------|---------------|
| `zone1_dd` | 0.05 | {0.04, 0.05, 0.07} |
| `zone2_dd` | 0.10 | {0.08, 0.10, 0.12} |
| `top_n` | 20 | {10, 20} |
| `min_yield` | 0.03 | {0.025, 0.03, 0.04} |

Mode de balayage (déclaré avant tout calcul, c.`59a808dd84`) : **un paramètre
à la fois (OAT)** — chaque variante ne change qu'un seul seuil, les autres
restant à leur défaut. Soit 7 backtests : `zone1_dd` ∈ {0.04, 0.07} ;
`zone2_dd` ∈ {0.08, 0.12} ; `top_n` ∈ {10} ; `min_yield` ∈ {0.025, 0.04}
(les défauts 0.05 / 0.10 / 20 / 0.03 sont portés par le run de base). Le
produit cartésien complet (3 × 3 × 2 × 3 = 54 points) n'est pas exécuté :
quota d'appels API QC partagé par la flotte (10/min). L'OAT couvre chaque
axe indépendamment ; la base `f41b0eed` sert de référence à chaque ligne.

Proxys déclarés (non spécifiés par la fiche) :

- **Taux de distribution** = rendement du dividende / rendement des bénéfices
  (le champ fondamental direct n'est pas stable d'une source à l'autre).
- **Historique de dividende 10 ans** = au moins 8 années distinctes avec
  paiement sur les 10 dernières (tolérance 2 années), vérifié une fois par
  mois et mis en cache.
- **Liquidité** : prix > 5 $, dollar volume > 20 M$, capitalisation > 2 Md$
  (écarte les micro-caps ; la fiche ne filtre pas explicitement).

## Allocations par zone

| Zone | Drawdown SPY | SPY | Dividendes |
|------|--------------|-----|------------|
| Verte | < `zone1_dd` | 100 % | — |
| Jaune | [`zone1_dd`, `zone2_dd`) | 50 % | 50 % |
| Rouge | ≥ `zone2_dd` | — | 100 % |

## Invalidation des résultats v2/v3 (mesurée, 2026-10-04)

Les runs `f41b0eed` (base v2), la grille OAT 7/7, le run corrélations et le
run `fee_mult=2` ci-dessous décrivent une implémentation **buguée** : l'appel
`self.history(self.dividends, ...)` lève une `AttributeError` sur Lean master
v18155 (« object has no attribute 'dividends' »), attrapée par le `except` du
filtre → **tout titre était rejeté, la jambe dividende n'a jamais investi**.
La stratégie effectivement mesurée est « SPY-ou-cash » (verte = SPY, jaune =
50 % SPY + 50 % cash, rouge = cash), pas la rotation de la fiche.

Preuve : logs du run `781-fee2-2018-2026` (projet 37317779) et du run
`781-corr-2018-2024` (projet 37320712) — centaines de lignes « dividend
history error … has no attribute 'dividends' » (qui ont de surcroît épuisé le
quota de 100 kb de logs) ; « Lowest Capacity Asset : SPY » (aucun titre
individuel tradé). Les axes « non-mordants » de la grille (`top_n`,
`min_yield`) s'expliquent par ce bug, pas par un goulot du filtre.

Fix : `self.history(Dividend, symbol, ...)` (la classe `Dividend`, pas
l'instance inexistante `self.dividends`). La base, la grille OAT, les
corrélations et le run à frais doublés doivent être **rejoués** sur le code
corrigé — les sections ci-dessous restent visibles comme comportement mesuré
de la version buguée, pour la traçabilité, jusqu'à remplacement.

## Résultat de base v4 (2018-2026, frais IBKR, code corrigé)

Backtest `781-base-2018-2026-ibkr-v4-fix-dividend` (`bf0655ac`, projet
37317779, compile `e855ce4a`, 2195 jours, **1961 ordres**) :

| Mesure | Valeur |
|--------|--------|
| Sharpe | 0,426 |
| CAGR | 11,48 % |
| Pire baisse | 27,7 % |
| Profit net total | +158,5 % |
| PSR | 1,69 % |

Preuve que la jambe dividende investit (vs la v2 buguée à 91 ordres) :
1961 ordres, et les logs du run montrent des `set_holdings` sur des titres
individuels nommés (WMB, DH, NWL, CCL, MET, FD, OXY…), sans aucune ligne
« dividend history error ». Les « Backtest Handled Error : … does not have
an accurate price » résiduelles sont bénines : premier ciblage d'un titre
admis avant sa première barre daily (l'ordre part à la revue suivante).

Comparaisons (même fenêtre, mêmes frais — projet
[ThreeZone781Benchmarks](../ThreeZone781Benchmarks/)) :

| Run | Sharpe | CAGR | Pire baisse | Total |
|-----|--------|------|-------------|-------|
| **781 réimplémentée v4** | **0,426** | **11,48 %** | **27,7 %** | **+158 %** |
| SPY détenu (`43fa2e07`) | 0,499 | 13,91 % | 33,6 % | +212 % |
| 60/40 SPY/IEF (`d4a2b089`) | 0,383 | 8,86 % | 21,2 % | +110 % |

Lecture mesurée : la 781 corrigée **bat le 60/40 en Sharpe et en CAGR**
mais **cède sur la pire baisse** (27,7 % vs 21,2 %) — la dominance sur les
trois axes mesurée en v2 était un artefact du cash (jambe dividende morte =
zone rouge 100 % cash, DD 16,4 %). La vraie 781 prend un portefeuille
d'actions à dividende en zone rouge : plus de rendement, plus de drawdown.
Elle réduit toujours le drawdown du SPY détenu (27,7 % vs 33,6 %) mais
beaucoup moins que la version buguée ne le laissait croire. Aucun dominant
du SPY en rendement absolu. Verdict différé aux rejeux (grille OAT, frais
doublés, corrélations, sous-périodes).

Rotation annuelle (proxy déclaré : ordres/an sur la fenêtre) : 781 v4 ≈
224,6 ordres/an (1961 ordres sur 8,73 ans — le rebalancement hebdo du
portefeuille dividende en zones jaune/rouge porte l'activité) ; 60/40 ≈
19,8/an (173 ordres) ; SPY détenu 1 ordre.

## Résultat v2 invalidé (traçabilité)

Backtest `781-base-2018-2026-ibkr-v2` (`f41b0eed`, 2195 jours, 91 ordres) :
Sharpe 0,404 · CAGR 9,22 % · pire baisse 16,4 % · +116,1 % · PSR 1,5 %.
Ce run décrivait la « SPY-ou-cash » (voir « Invalidation » ci-dessus) — la
lecture initiale de dominance défensive sur le 60/40 (trois axes) et de pire
baisse divisée par deux venait du cash, pas de la stratégie.

## Grille de robustesse v4 (OAT, 7 variantes, code corrigé)

Sept backtests sur le compile v4 (`e855ce4a`, source identique au run de
base v4), un paramètre à la fois (mode déclaré ci-dessus) :

| Variante | Sharpe | CAGR | Pire baisse | Ordres | Lecture |
|----------|--------|------|-------------|--------|---------|
| **base (défauts)** | **0,426** | **11,48 %** | **27,7 %** | **1961** | référence |
| `zone1_dd`=0.04 | 0,418 | 11,28 % | 27,7 % | 2193 | quasi-neutre, léger coût |
| `zone1_dd`=0.07 | **0,491** | **12,91 %** | 27,7 % | 1551 | meilleur point de la grille |
| `zone2_dd`=0.08 | 0,421 | 11,37 % | 27,7 % | 2001 | quasi-neutre |
| `zone2_dd`=0.12 | 0,424 | 11,46 % | 27,7 % | 1967 | quasi-neutre |
| `top_n`=10 | 0,406 | 11,31 % | **30,9 %** | 1296 | mord : panier moins diversifié |
| `min_yield`=0.025 | 0,434 | 11,64 % | 29,5 % | 2147 | mord : panier élargi, DD en hausse |
| `min_yield`=0.04 | 0,415 | 11,65 % | 30,4 % | 889 | mord : panier restreint, DD en hausse |

Lecture d'ensemble (v4) :

- **`zone1_dd` est l'axe vif** : monotone sur la fenêtre — rester investi
  SPY plus longtemps paie (0,418 → 0,426 → 0,491). Le seuil 5 % de la
  description n'est pas un optimum local.
- **`zone2_dd` est plat** (0,421-0,426) : la « sensibilité violente »
  mesurée en v2 (0,317-0,341) était un artefact du bug, pas une propriété
  de la stratégie.
- **`top_n` et `min_yield` mordent désormais** (bit-identiques à la base en
  v2) — via le drawdown surtout : le défaut 20 titres / 3 % est un point de
  diversification favorable (DD 27,7 % contre 29,5-30,9 % pour tout écart).
- **Toutes les variantes battent le 60/40 en Sharpe** (minimum 0,406 >
  0,383) et en CAGR (minimum 11,28 % > 8,86 %) ; **aucune ne le bat en
  pire baisse** (27,7-30,9 % contre 21,2 %).
- `zone1_dd`=0.07 (0,491) frôle SPY détenu (0,499) — aucune variante ne
  le bat.

### Grille v2 invalidée (traçabilité)

La table v2 d'origine (seuls z1/z2 « mordaient », `top_n`/`min_yield`
bit-identiques à la base, lu alors comme un « goulot du filtre dividende à
~10 titres ») décrivait la SPY-ou-cash : les axes « non-mordants » étaient
morts par construction (picks toujours vides) et la « sensibilité » de z2
mesurait le moment exact des bascules SPY/cash. Chiffres conservés dans
l'historique du fichier (commit `cd56c2512a`).

## Sensibilité aux frais (v4)

Run `781-fee2-2018-2026-v4` (`b9f133ba`, compile v4, frais IBKR ×2) :

| Mesure | base v4 | frais ×2 | Écart |
|--------|---------|----------|-------|
| Sharpe | 0,426 | 0,416 | −0,010 |
| CAGR | 11,48 % | 11,27 % | −0,21 pt |
| Pire baisse | 27,7 % | 27,7 % | — |
| Total | +158,5 % | +154,4 % | −4,1 pts |

Le doublement des frais coûte 0,010 de Sharpe : la stratégie est **peu
sensible aux frais** — l'activité (~225 ordres/an) porte sur des large caps
liquides dont les frais IBKR sont déjà très bas. Le run fee2 v2
(0,402 / 9,20 % / 89 ordres) décrivait la SPY-ou-cash (invalidé).

## Corrélations aux allocations du dépôt (v4)

Run `781-corr-2018-2024-v4-fix-dividend` (`28a33e39`, projet
[ThreeZone781Correlation](../ThreeZone781Correlation/), fenêtre commune
2018-2024, Pearson des retours hebdomadaires, statistiques custom du
rapport) :

| Panier | corr v4 | corr v2 (invalidée) |
|--------|---------|---------------------|
| VT2 (SPY/QQQ/IEF/GLD, poids égaux) | **0,8025** | 0,5989 |
| AW (AllWeather v5.0) | 0,7395 | 0,5006 |
| TW (sleeve AllWeather du TrendWeather) | 0,7395 | 0,5006 |

(TW ≡ AW par construction du proxy.) Le run v4 : Sharpe 0,42 / +110,0 % /
pire baisse 27,7 % / 1772 ordres sur 2018-2024.

Lecture : la vraie 781 est **nettement plus corrélée** aux allocations ETF
que la SPY-ou-cash mesurée en v2 ne le laissait croire — la jambe dividende
est un facteur equity long qui chute avec le marché en zones jaune/rouge.
À 0,80 avec VT2, la stratégie ne diversifie pas le dépôt : les ETF existants
sont entre eux à 0,8-0,9, la 781 s'y ajoute sans décorrélation.

## Sous-périodes (v4)

Découpage déclaré : split médian de la fenêtre (2018-01-01 → 2022-06-30 /
2022-07-01 → 2026-09-25), compile v4, défauts :

| Fenêtre | Sharpe | CAGR | Pire baisse | Ordres |
|---------|--------|------|-------------|--------|
| 2018-01 → 2022-06 (COVID inclus) | 0,332 | 7,87 % | 27,7 % | 1027 |
| 2022-07 → 2026-09 | 0,597 | 15,66 % | 17,4 % | 934 |

La performance est **portée par la seconde moitié** : 0,332 (A, COVID
inclus) contre 0,597 (B), pour 0,426 sur la fenêtre pleine — hétérogénéité
temporelle confirmée par les deux bouts. (La sous-période B, refusée cinq
fois par un node pool QC occupé par d'autres sièges de la flotte, a été
posée dès libération ; les deux lectures sous-jacentes du verdict ont été
écrites avant sa mesure et ne changent pas.)

## Verdict : NO BEATS (point 4 du protocole)

**La 781 réimplémentée ne remplace aucune allocation existante du dépôt.**

1. **Jamais SPY détenu** (0,499 / 13,91 % / +212 %) : le meilleur point de
   la grille (`zone1_dd`=0.07 : 0,491 / 12,91 %) reste dessous, et la base
   (0,426) nettement.
2. **60/40 battu en Sharpe et CAGR sur toute la grille** (Sharpe min 0,406
   vs 0,383 ; CAGR min 11,28 % vs 8,86 %) **mais jamais en pire baisse**
   (27,7-30,9 % vs 21,2 %) — un profil « rendement supérieur, queue de
   risque supérieure », pas une domination.
3. **Pas de diversification** : corrélations hebdo 0,74-0,80 avec les
   paniers existants — la motivation première de l'issue n'est pas servie.
4. **Hétérogénéité temporelle** : sous-période A à 0,332 contre 0,426 sur
   la fenêtre pleine.
5. PSR affiché par QC faible (1,69 % base v4) — valeur brute citée sans
   interprétation de convention.

Robustesse positive à retenir : peu sensible aux frais (×2 → −0,010
Sharpe) ; grille OAT sans effondrement (pire variante à 0,406) ; jambe
dividende vivante et vérifiée dans les logs (1961 ordres, titres nommés).
Pourquoi B ne renverse rien : le verdict tient à la non-domination sur la
fenêtre pleine et à la corrélation structurelle — une sous-fenêtre
favorable ne change ni l'une ni l'autre.

## Couverture des données fondamentales (point 5)

Sources utilisées par le code : fine fundamental US (Morningstar via QC) —
`valuation_ratios.trailing_dividend_yield`, `valuation_ratios.pe_ratio`,
`market_cap` — et historique de dividendes du provider via
`history(Dividend, …)`. Preuve empirique de couverture continue : ordres
individuels répartis de 2018 à 2026 (1961 ordres sur la fenêtre pleine,
titres nommés dans les logs dès 2018), sans période d'effondrement du
nombre de picks. Limite déclarée : aucune mesure directe de trous par champ
(NaN) n'a été faite — un run de diagnostic dédié reste possible si le
coordinateur le demande.

## Gel du code (point 6)

Code gelé au verdict : commit du dépôt + compile cloud **`e855ce4a`**
(BuildSuccess, Lean master v18155). Rejeu mensuel : `create_backtest` sur
ce compile avec `start_date` = dernier rejeu et `end_date` = dernier jour
ouvré, paramètres par défaut — toute divergence du Sharpe/CAGR/DD hors des
bandes habituelles de la fenêtre écoulée se signale sur l'issue.

## État du protocole (issue #18905)

| Point | État |
|-------|------|
| 1. Cloner le projet source | Non réalisable (accès refusé) → réimplémentation déclarée. Réponse coordinateur (04/10) : demande transmise à la lane QC qui a lu la fiche ; si le code source arrive, il servira **d'oracle de vérification** (écarts cités), jamais commité tel quel |
| 2. Backtest frais IBKR | **Rejoué sur code corrigé** (v4 `bf0655ac`, 2018-2026, 1961 ordres) ; grille OAT en cours de rejeu sur compile v4 |
| 3. Mesures + comparaisons | Benchmarks SPY/60-40 **valides** ; fee2 v4 mesuré (peu sensible) ; **corrélations v4 rejouées** : VT2 0,80 · AW/TW 0,74 — pas de diversification |
| 4. Verdict + robustesse | **Rendu : NO BEATS** — grille OAT 7/7 rejouée sur code corrigé (4 axes mordants dont top_n/min_yield révélés par le fix) ; **sous-périodes A (0,332) et B (0,597) mesurées** — hétérogénéité temporelle confirmée, verdict inchangé |
| 5. Couverture données fondamentales | Documenté : Morningstar fine fundamental + provider dividends ; preuve empirique = ordres répartis 2018→2026 ; limite déclarée (pas de mesure NaN par champ sans run dédié) |
| 6. Gel du code au verdict | **Gelé** : commit du dépôt + compile `e855ce4a` ; procédure de rejeu mensuel décrite dans la section dédiée |

Chiffres affichés par la fiche (non vérifiés) : CAGR 16,7 %, pire baisse
20,9 % — aucun historique hors échantillon (publication du 29/09/2026).
