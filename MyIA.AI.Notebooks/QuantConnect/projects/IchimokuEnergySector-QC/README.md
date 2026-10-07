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

<!-- TABLE_REPRO -->

### XLE buy-and-hold (même harnais)

<!-- TABLE_XLE -->

### Extension out-of-sample (2020-08-17 → 2026-09-30)

<!-- TABLE_OOS -->

## Verdict BEATS / NO BEATS

<!-- VERDICT -->

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
