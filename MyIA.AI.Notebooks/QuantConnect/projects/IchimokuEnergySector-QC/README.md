# IchimokuEnergySector-QC — Ichimoku Clouds In The Energy Sector

Portage QC Cloud de l'article de recherche QuantConnect **9031 — « Ichimoku Clouds In The
Energy Sector »** (Derek Melchin, draft/pending review) :
<https://www.quantconnect.com/research/9031/ichimoku-clouds-in-the-energy-sector/>.

- Grain : `DEEP/qc` — lane `myia-po-2023:CoursIA` — See #19678 (semis + acceptance), EPIC #11698
  (moissonnage QC-research).
- Projet QC Cloud : `IchimokuEnergySector-9031` (id 37468246), exécution via MCP
  `quantconnect/mcp-server` — jamais d'exécution locale fictive.

## Ce que fait la stratégie

L'article applique l'indicateur **Ichimoku Kinko Hyo** aux 10 plus grandes capitalisations
du secteur énergie (univers fine-fundamental mensuel, `MorningstarSectorCode.ENERGY`) :

- l'AlphaModel émet **long** quand la ligne **Chikou** croise le haut du nuage (Senkou A/B)
  par le bas, **short** quand elle croise le bas du nuage par le haut ;
- des insights quotidiens de durée 1 jour maintiennent la position entre deux croisements ;
- construction de portefeuille équipondère, exécution immédiate, données quotidiennes ajustées.

L'article confronte la stratégie au benchmark **XLE** (ETF secteur énergie) sur quatre
fenêtres, et conclut honnêtement que **la stratégie ne bat pas le benchmark** — c'est
précisément ce que ce portage mesure.

## Adaptations documentées (a1-a6)

| # | Écart | Mesure / motif |
|---|---|---|
| a1 | Fenêtre et capital paramétrées (`start`/`end` YYYYMMDD, défaut = fenêtre de l'article 20150101→20200816), cash 1 M, brokerage IBKR marge, `seed_initial_prices` | La prose de l'article ne livre ni code de setup ni frais ; convention du dépôt pour la vérification sous frais de courtier (campagne #1630) |
| a2 | Paramètre `mode` : `strategy` (portage) / `xle_hold` (XLE buy-and-hold) | La table de l'article compare Sharpe/ASD sur fenêtres identiques ; le comparateur vit dans le même projet pour garantir le **même harnais** (frais, calendrier, données) |
| a3 | `symbol_data_by_symbol` porté en attribut d'instance de l'AlphaModel | L'article le déclare attribut de **classe** — dictionnaire latent partagé entre instances |
| a4 | Retrait des SymbolData sortis d'univers (`on_securities_changed`) | L'article ne montre pas cette gestion ; sans elle les titres sortis continueraient d'émettre des insights sur données absentes |
| a5 | `set_benchmark("XLE")` explicite pour les deux modes | Benchmark ETF énergie, comme l'étude |
| a6 | Warm-up par énumération typée `algorithm.history[TradeBar](...)` | Le warm-up pandas de l'article (`row.volume`) lève `Runtime Error` sur LEAN courant (mesuré au premier run : la Series rendue par `.loc[symbol]` n'expose plus `volume`) — mêmes barres quotidiennes, même séquence `is_ready`/`update` |

## Métriques reproduites (frais IBKR, cash 1 M)

### Stratégie vs article — reproduction

L'article ne publie que deux statistiques par fenêtre (Sharpe et ASD, écart-type annualisé des
rendements) et ne définit **aucune** fenêtre hors temps : 2015-01-01 → 2020-08-16 est à la fois
sa période de réglage et son test. Les valeurs ci-dessous sont relevées à la source
(<https://www.quantconnect.com/research/9031/ichimoku-clouds-in-the-energy-sector/>, page servie
en HTML, sans JavaScript).

| Fenêtre | Article — strat (Sharpe / ASD) | Portage — strat (Sharpe / ASD) | Ordres |
|---|---|---|---|
| Backtest 2015-01-01 → 2020-08-16 | −0,31 / 0,223 | non exécutée | — |
| Fall 2015 2015-08-10 → 2015-10-10 | −0,31 / 0,294 | **−2,504 / 0,053** | 848 |
| 2020 Crash 2020-02-19 → 2020-03-23 | 176,524 / 0,949 | **aucune négociation** | **0** |
| 2020 Recovery 2020-03-23 → 2020-06-08 | −1,556 / 0,447 | non exécutée | — |

**Les niveaux ne sont pas comparables, et le README ne prétend pas le contraire.** L'article ne
publie ni son capital initial, ni son modèle de frais, ni la convention d'agrégation de son
Sharpe ; le portage tourne sous `BrokerageName.INTERACTIVE_BROKERS_BROKERAGE` (frais réels par
action, mesure : 6,69 bps du volume sur `fall2015`) et sous 1 M de capital. L'écart
`−2,504` contre `−0,31` est **rapporté, pas moyenné** — ces deux nombres ne mesurent pas la même
expérience.

**La ligne `2020 Crash` est un défaut de portage, pas un résultat.** L'article y annonce un
Sharpe de `176,524` ; le portage n'y négocie **rien** (0 ordre, equity plate à 1 000 000 $). Un
run qui ne trade pas ne valide ni n'infirme l'article. Voir la section « Extension out-of-sample »
ci-dessous : la même signature a depuis été reproduite sur quatre autres fenêtres **pré-correction**,
ce qui écarte l'explication initiale (« 23 séances, trop court pour armer l'univers ») — la cause
réelle (constructeur de base non chaîné) et son correctif y sont documentés.

### XLE buy-and-hold (même harnais)

Le comparateur est le mode `xle_hold` du **même projet** : mêmes bornes, mêmes frais, même
calendrier, même normalisation. C'est la seule comparaison que ce README tient pour valide — un
achat intégral unique (1 ordre), donc aucune dépendance au chemin.

| Fenêtre | Source | Sharpe | ASD | Net | Drawdown max | Ordres |
|---|---|---|---|---|---|---|
| Backtest 2015-01-01 → 2020-08-16 | article | −0,083 | 0,312 | — | — | — |
| Fall 2015 2015-08-10 → 2015-10-10 | article | 0,242 | 0,351 | — | — | — |
| 2020 Crash 2020-02-19 → 2020-03-23 | article | −0,902 | 1,108 | — | — | — |
| 2020 Recovery 2020-03-23 → 2020-06-08 | article | 46,068 | 0,703 | — | — | — |
| **Bloc gelé 2020-08-17 → 2026-09-30** | portage | **0,746** | — | **+310,517 %** | 26,000 % | 1 |
| **Sous-fenêtre 2020-08-17 → 2022-08-16** | portage | **1,276** | **0,290** | **+122,499 %** | 26,000 % | 1 |

Les quatre lignes « article » sont les valeurs du benchmark publiées par l'article, conservées
pour situer l'ordre de grandeur ; elles ne sont pas rejouées ici. Les deux lignes « portage » sont
mesurées sur ce dépôt (projet QC `37468246`), et le champ `Sharpe` y est celui du harnais, lu tel
quel — jamais substitué par le nôtre (voir le caveat de reproductibilité dans `verdict_stats.py`).

**La baseline n'a pas besoin d'être découpée** : elle complète sur le bloc gelé entier, en un run,
sans joint. La mesure du 08/10 le confirme — le run dédié sur la sous-fenêtre (1 000 000 $ →
2 224 992,87 $) et la restriction de la série du run complet donnent le même chemin de rendement
au centième, ce qui est attendu d'un achat intégral unique : il n'a aucune dépendance au futur.

### Extension out-of-sample (2020-08-17 → 2026-09-30)

**Défaut de portage trouvé puis corrigé (#19863) : l'univers fine n'était jamais armé.** Les runs
pré-correction (mesure du 08/10, projet `37468246`) présentaient des fenêtres **vides** — 0 ordre,
equity plate au centime, aucune erreur — et des fenêtres qui négocient :

| Fenêtre | Durée | Ordres | Statut (pré-correction) |
|---|---|---|---|
| 2015-08-10 → 2015-10-10 | 2 mois | **848** | négocie |
| 2020-02-19 → 2020-03-23 | 1 mois | 0 | **vide** |
| **2020-08-17 → 2022-08-16** | 24 mois | **839** | négocie |
| 2021-01-01 → 2022-01-01 | 12 mois | 0 | **vide** |
| 2021-08-17 → 2022-08-16 | 12 mois | 0 | **vide** |
| 2022-08-16 → 2023-08-16 | 12 mois | 0 | **vide** |
| **2020-08-17 → 2026-09-30 (bloc gelé, corrigé)** | 6,1 ans | **4 860** | complète et négocie |

Trois explications ont d'abord été testées et **réfutées par la mesure** (fenêtre trop courte /
fin de donnée fine / alignement du mois de départ). Une sonde instrumentée (issue #19863) puis la
lecture de la source publique LEAN ont nommé la cause exacte : `EnergyTopTenUniverseSelectionModel`
sous-classait `FineFundamentalUniverseSelectionModel` **sans chaîner de constructeur de base** —
le pattern canonique QC exige `super().__init__(self.select_coarse, self.select_fine)`. Sans lui,
l'univers fine n'est **jamais construit** : le compteur `fine_calls` de la sonde vaut **0 sur tous
les runs pré-correction** (y compris ceux qui négociaient), l'univers dégénère en le coarse brut
(~5 000 titres à données fondamentales), le verrou mensuel (`self.month`, posé dans
`select_fine`) ne s'arme jamais — re-sélection quotidienne de ~5 000 symboles, >1 M d'*insights* —
et la pondération égale sur ~5 000 titres (~200 $ par position) arrondit la plupart des tailles
d'ordre à 0 action : c'est l'origine des fenêtres « vides ». Une sélection qui ne rend aucun
ordre n'est pas une erreur pour LEAN ; le run conclut normalement.

**Correction** (commit `a745f2545d`, une ligne) : chaînage canonique au constructeur de base. Le
run conteneur corrigé **complète et négocie : 1 692 ordres** sur 2020-08-17 → 2022-08-16 (Sharpe
harnais 0,049, net −2,312 %, MaxDD 30,5 %). Et à l'échelle du bloc gelé entier : le run plein bloc
corrigé (`22fde01f1ad65`, 2020-08-17 → 2026-09-30) **complète et négocie : 4 860 ordres** — net
+12,6 %, CAGR 1,96 %, Sharpe harnais −0,041, contre +310,5 % / 25,93 %/an pour la baseline XLE du
même bloc (mesure du 08/10, consignée dans [#19867](https://github.com/jsboige/CoursIA/pull/19867)).
Les fenêtres 2021+, re-jouées avec la sonde corrigée, sont suivies sur #19863.

Un corollaire pratique, mesuré : **la durée du run trahit le vidage.** Une fenêtre de 12 mois vide
complète en ~90 s là où deux mois qui négocient prennent 6-8 min — la sélection d'univers domine le
coût, et un univers vide ne coûte rien. `progress` est un ratio temporel pur et ne dit rien ; la
seule lecture qui discrimine est la **courbe d'equity** (plate au centime = run vide).

## Verdict BEATS / NO BEATS

**Sur la fenêtre du conteneur corrigé (24 mois, la seule où le bootstrap pré-enregistré ait été
rejoué), le test rend `INCONCLUSIVE` — calculé sur le port corrigé.**

Le verdict porte sur **2020-08-17 → 2022-08-16**, la fenêtre du run conteneur corrigé (1 692
ordres, univers fine armé). Le test est celui du pré-enregistrement, inchangé : bootstrap par
blocs, **bloc = 21 séances, 10 000 rééchantillonnages, graine 42**, apparié séance par séance,
placebo à 21 séances.

| | Sharpe (instrument) | Cumul | Drawdown max |
|---|---|---|---|
| Stratégie (corrigée, `4cdcd965`) | 0,0788 | −2,513 % | −30,517 % |
| Baseline XLE (`xle_hold`) | 1,303 | +123,020 % | −25,983 % |

| Test | Écart de Sharpe | p (bat) | p (sous-performe) | Verdict |
|---|---|---|---|---|
| Principal (521 séances communes) | −1,2242 | 0,9132 | **0,0868** | **`INCONCLUSIVE`** |
| Placebo (baseline décalée de 21 séances) | −1,517 | 0,9241 | 0,0759 | `INCONCLUSIVE` |

**Ce que le verdict dit, exactement.** La stratégie **ne bat pas** le buy-and-hold XLE — l'écart de
Sharpe est négatif et le cumul de la stratégie (−2,513 %) est très loin de celui de la baseline
(+123,020 % — le rally énergie 2021-2022). Mais le seuil gelé exige p < 0,05 pour conclure un
`BEATS` **ou** un `UNDERPERFORMS` : à p = 0,0868, on ne peut **pas** non plus conclure à une
sous-performance significative sur cet échantillon. Le verdict est donc `INCONCLUSIVE`, et c'est
le verdict, pas un repli. La première version de ce verdict (écart −0,7252, p 0,1941), calculée
avant la correction de l'univers, mesurait le coarse brut dégénéré — elle est **supersédée** par
celle-ci ; les deux sont conservées dans le fil #19678 pour la traçabilité.

**Le placebo ne fabrique pas d'effet** : en décalant la baseline de 21 séances vers le futur,
l'écart de Sharpe reste négatif (−1,517) et le verdict reste `INCONCLUSIVE` — le test n'est pas un
dispositif à sens unique.

**Limite honnête, déjà gelée avant le premier calcul.** Un verdict sur une fenêtre unique reste un
verdict sur une fenêtre. Le port corrigé **produit** la jambe stratégie sur le bloc entier (4 860
ordres, run `22fde01f1ad65`) ; ce qui reste borné à 24 mois est le **test statistique pré-enregistré** :
son bootstrap par blocs n'a été rejoué que sur le conteneur 2020-08-17 → 2022-08-16 (1 692 ordres) —
tant qu'il n'est pas rejoué sur le bloc complet, la significativité est mesurée sur ces 24 mois
uniquement, le bloc complet n'ayant fait l'objet que de la comparaison brute (net +12,6 % contre
+310,5 % — lisible `NO BEATS`, sans significativité mesurée). Le résultat reste hors temps —
2020-08-17 → 2022-08-16 n'a servi à aucun réglage, le portage ayant été écrit et débogué sur
2015-01-01 → 2020-08-16.

**Ce que ce verdict ne dit pas.** Il ne dit rien de la fenêtre 2015-01-01 → 2020-08-16 (jambe
stratégie non exécutée sous le code courant), ni des fenêtres `2020 Recovery` et `2020 Crash`.
L'écart de niveau avec les valeurs publiées par l'article (`fall2015` : −2,504 contre −0,31) n'est
pas expliqué par ce verdict et reste ouvert : l'article ne publie ni capital ni modèle de frais, et
le portage tourne sous frais de courtage réels.

## Référence

Gurrib, I., Kamalov, F., & Elshareif, E. (2021). *Can the leading US energy stock prices be
predicted using the Ichimoku cloud?* International Journal of Energy Economics and Policy,
11(1), 41–51. https://doi.org/10.32479/ijeep.10260 (version SSRN 2020,
abstract 3520582). PDF archivé au gisement :
`G:\Mon Drive\MyIA\IA\Bibliographie IA\Trading\2021 - Gurrib Kamalov Elshareif - Can the
Leading US Energy Stock Prices be Predicted using the Ichimoku Cloud (IJEEP 11-1).pdf`
(sha256[:12] `CBEE9BFCBAEF`).

L'étude académique de référence utilise une **sélection fixe constituée sur les poids de fin
de période** (biais de look-ahead documenté par l'article QC lui-même) ; le portage conserve
l'univers fine-fundamental **mensuelle** de l'article QC, qui élimine ce biais — les niveaux
absolus de Sharpe ne sont donc pas directement comparables à Gurrib et al., c'est la
**confrontation stratégie vs XLE sous le même harnais** qui fait foi.
