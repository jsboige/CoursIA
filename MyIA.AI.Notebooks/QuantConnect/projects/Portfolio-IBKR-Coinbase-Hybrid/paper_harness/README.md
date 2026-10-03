# paper_harness — exécution paper-trading Phase 4

Harness local d'**exécution paper** du portefeuille hybride IBKR + Coinbase (MiCA) décrit
dans le [README parent](../README.md) (Phase 4). Distinct de `../main.py` (algorithme
de backtest QC Cloud) : ce package parle aux **venues paper réelles** (Coinbase Advanced
Trade API, IB Gateway paper) au lieu du backtester QC.

## Migration MiCA : sleeve crypto Binance → Coinbase (2026-06-28)

Le sleeve crypto ACTIF est désormais **Coinbase** (Binance France cesse le 2026-07-01,
pas de licence CASP MiCA ; Coinbase détient la CASP MiCA France + est nativement supporté
par QC, `Market.COINBASE` dans `../main.py`). Le `binance_sleeve.py` est conservé comme
**fallback legacy** mais n'est plus le chemin actif. Voir la section [Migration MiCA](../README.md#migration-mica-sleeve-crypto-binance--coinbase-2026-06-28)
du README parent.

Architecture conforme à la décision Phase 4 du README parent (leçon Phase 2 :
`set_brokerage_model(IBKR)` rejette le type Crypto → un backtest unifié 2-broker
n'est pas transposable en live unifié) : approche **crypto-first** — paper-trader
le sleeve crypto seul sur Coinbase, sleeve IBKR en backtest parallèle.

## État (2026-06-28)

| Composant | Statut |
|-----------|--------|
| `config.py` (loader `.env` typé) | livré (ajout `CoinbaseConfig`) |
| `risk.py` (circuit-breakers) | livré, dry-run validé ; état persistant (`save`/`load`) ajouté |
| `rebalance.py` (poids inverse-volatilité → ordres en parts entières) | livré, testé (`tests/`) |
| `orchestrator.py` (`run_cycle` : un cycle de rééquilibrage, dry-run par défaut) | cœur livré, testé contre un courtier factice |
| `ibkr_broker.py` (adaptateur IBKR de `Broker` : lignes UCITS, comptabilité de poche) | livré (2026-10-03), testé contre un faux client IB ; cycle à blanc validé en lecture seule sur IB Gateway paper |
| `ibkr_cycle.py` (un cycle en ligne de commande, à blanc par défaut) | livré (2026-10-03) |
| `coinbase_sleeve.py` (wrapper coinbase-advanced-py, **MiCA**) | livré, **SOTA-OK code** (API vérifiée firsthand) |
| `smoke_test_coinbase.py` (validation read-only) | livré, exit 2 = USER-HAND sans creds |
| `binance_sleeve.py` (wrapper python-binance testnet, **legacy**) | livré, SOTA-OK (pré-MiCA) |
| `smoke_test_binance.py` (validation read-only live) | livré (legacy) |
| `ibkr_sleeve.py` (wrapper ib_insync) | livré, **SOTA-OK** (validé live, surface read-only) |
| `smoke_test_ibkr.py` (validation read-only live) | livré |

## Sécurité

- **Sandbox / paper uniquement** tant que `COINBASE_SANDBOX=true`. Coinbase Advanced
  Trade n'a pas de testnet public distinct de Binance : le « sandbox » est un **compte
  Coinbase paper** dont la clé API frappe le même endpoint (documenté honnêtement, pas
  contourné). Les soldes d'un compte paper sont fictifs.
- Le smoke test est **read-only** (connexion, soldes, prix, dry-run breakers) — il ne
  place **aucun ordre**. Le chemin ordre (`market_buy`/`market_sell`) est implémenté
  mais activé uniquement par l'orchestrator, après relecture des circuit-breakers.
- Circuit-breakers (`risk.py`) : drawdown max (`RISK_MAX_DD_PCT`), perte journalière
  (`RISK_DAILY_VAR_PCT`), taille de position unitaire (`RISK_MAX_POSITION_PCT`),
  exposition brute (`RISK_MAX_GROSS_EXPOSURE`). Tout ordre passe par `RiskGate.check_order`.
- Aucun secret n'est imprimé ; les credentials vivent uniquement dans le `.env` gitigné.

## SOTA-OK (Prong A)

Les sleeves pilotent la **vraie lib** contre la **vraie venue paper** — aucune
sortie de substitution (ASCII, réimplémentation jouet, stub).

- **Coinbase (ACTIF, MiCA)** : `coinbase-advanced-py` contre l'Advanced Trade API (clé
  CDP Ed25519/ECDSA). API surface vérifiée firsthand sur la lib installée (1.8.4) :
  `RESTClient(api_key, api_secret)`, `get_accounts()`, `get_product()`,
  `market_order_buy(client_order_id, product_id, quote_size)`,
  `market_order_sell(client_order_id, product_id, base_size)`, `cancel_orders(order_ids=[...])`.
  Le code sleeve est SOTA-OK ; le **run live** est gated **USER-HAND** : ouverture de
  compte Coinbase + création de clé CDP côté user (#1027 Phase-B). Le smoke test
  rapporte `RECOVERABLE-USER-HAND` (exit 2) en attendant.
- **Binance (LEGACY)** : `python-binance` contre le Spot Testnet (pré-MiCA). Conservé
  comme fallback.
- **IBKR** : `ib_insync` contre IB Gateway en mode paper/simulated (port 4002). Validation
  live : compte paper connecté, `accountSummary()` lu (NetLiq, cash, buying power),
  `positions()` lu. Le chemin ordre est implémenté mais **gated** sur deux conditions :
  (1) "Read-Only API" OFF côté gateway (sinon IB rejette l'ordre, Error 321), (2) passage
  derrière l'orchestrator + circuit-breakers relus. Aucun ordre placé à ce stade.

## Installation

```bash
python -m pip install -r paper_harness/requirements.txt
```

## Smoke test (read-only, depuis la racine du projet)

```bash
# Coinbase (MiCA) — sans creds : exit 2 RECOVERABLE-USER-HAND (attendu)
python -m paper_harness.smoke_test_coinbase

# IB Gateway paper (doit tourner en mode simulated/paper sur IBKR_PORT)
python -m paper_harness.smoke_test_ibkr
```

Sortie attendue (IBKR) : `managed acct`, `net_liq`, `total_cash`, `buying_power`,
`positions: N`, puis dry-run des 3 cas breakers (sane → ALLOW, oversized → BLOCK,
gross → BLOCK). Exit code 0 = SOTA-OK.

## Rééquilibrage et état du disjoncteur

`rebalance.py` sépare le calcul de l'exécution, en deux fonctions pures que l'orchestrateur
appellera avant tout ordre :

- `inverse_vol_weights` calcule les poids cibles de la règle `Cloud-VolTargeting` v2 : chaque
  ligne reçoit `budget / volatilité réalisée` (21 rendements quotidiens), plafonné à 50 %, et le
  total est ramené à 100 % s'il le dépasse ; le reste demeure en liquidités. La convention
  (rendements simples, écart-type d'échantillon) est celle du backtest de recherche ; un test
  vérifie la parité avec le calcul pandas à `1e-10` près.
- `plan_orders` traduit ces poids en ordres signés en **parts entières** (arrondi inférieur),
  ventes avant achats. Une bande de tolérance (`band`, en fraction de l'équité) ignore les
  échanges trop petits pour justifier leur commission, un notionnel minimum (`min_notional`)
  écarte les ordres qu'un courtier facturerait au minimum, et une réserve (`cash_reserve`)
  garde de quoi payer les frais. Une cible nulle est une **sortie**, pas un rééquilibrage :
  la position est vendue en entier, quelle que soit sa taille, sans bande ni notionnel
  minimum. Sinon un retour au cash laisserait en place toute position plus petite que la
  bande.

`RiskGate.save` / `RiskGate.load` conservent le pic d'équité, l'équité d'ouverture et un
éventuel arrêt dans un fichier JSON, écrit de façon atomique. Sans cela, un redémarrage du
programme remettrait le disjoncteur à zéro. Un fichier illisible lève une erreur plutôt que
de repartir d'un état vierge.

`orchestrator.run_cycle` enchaîne ces briques autour d'un courtier (tout objet qui fournit
`equity`, `positions`, `prices` et `place`) : marquage de l'équité dans le `RiskGate`, poids
cibles éventuellement réduits (`exposure_scale`, par exemple 0,5 après un premier seuil de
perte, 0 pour revenir au cash), correspondance signal → ligne échangée (un signal sur un ETF
américain peut piloter une ligne UCITS européenne), plan d'ordres, contrôle de chaque ordre
par le `RiskGate`, puis journal JSONL et sauvegarde de l'état. Le mode **dry-run** est le
défaut : rien n'est envoyé tant que `dry_run=False` n'est pas passé explicitement.

Un ordre qui ne fait que réduire une position détenue (`reduces_exposure=True`) passe même
quand le disjoncteur est déclenché : un disjoncteur sert à couper le risque, il ne doit jamais
empêcher le retour au cash. Les achats restent bloqués. `run_cycle` refuse aussi de démarrer
si le plafond par ligne de la stratégie dépasse `RISK_MAX_POSITION_PCT`, sans quoi le
`RiskGate` bloquerait chaque achat de taille pleine.

```bash
python -m pytest paper_harness/tests -q
```

## Adaptateur IBKR et cycle en ligne de commande

`ibkr_broker.IBKRBroker` implémente `Broker` sur une connexion `ib_insync` à IB Gateway
**paper**, pour la version UCITS de la stratégie : des lignes européennes cotées en euros
sur Xetra, pilotées par des signaux calculés sur les ETF américains équivalents
(`SIGNAL_TO_LINE`, ou `SIGNAL_TO_LINE_SMALL` pour des lignes à petit prix de part qui
arrondissent mieux une petite poche). Quatre choix le structurent :

- **Contrats par identifiant IBKR (`conId`).** Un ticker Xetra n'est pas toujours le
  symbole IBKR : la ligne iShares $ Treasury 7-10 ans (distribuante) se traite sous
  `IUSM` sur Xetra, mais son symbole IBKR est `BTMA`, et une recherche par le symbole
  `IUSM` ne résout rien. `UCITS_LINES` désigne donc chaque ligne par son `conId`, vérifié
  sur une session paper.
- **Comptabilité de poche, jamais la valeur du compte.** Un compte paper porte un capital
  fictif bien plus grand que la poche, et plusieurs poches peuvent partager un compte. La
  valeur de la poche est celle de *ses* lignes plus *son* cash, tenus dans un
  `SleeveLedger` (fichier JSON écrit de façon atomique). Le registre se construit à partir
  des exécutions étiquetées par l'`orderRef` de la poche, comptées une seule fois par
  `execId`, commissions comprises, même quand leur rapport arrive après l'exécution. Il est
  confronté aux positions du compte : la poche peut détenir moins que le compte (une autre
  poche détient le reste), jamais plus (`LedgerDriftError`).
- **Prix.** Instantané différé (type 3) quand le temps réel n'est pas abonné, puis la
  clôture précédente, puis la dernière barre quotidienne. Sans aucun des trois, l'adaptateur
  lève une erreur plutôt que de planifier à l'aveugle ; `price_sources` dit lequel a servi.
- **Ordres.** Ordres limites avec un collier (`collar=0.005` : un achat au plus 0,5 %
  au-dessus du prix de référence), refusés si le compte n'est pas un compte paper (préfixe
  `D`) ou si la connexion est en lecture seule. `place` attend les exécutions et les
  enregistre avant de rendre la main, pour que les ventes d'un cycle financent ses achats.

`ibkr_cycle` enchaîne un cycle complet depuis la ligne de commande, **à blanc par défaut**
(connexion en lecture seule, rien n'est envoyé). Le registre et l'état du disjoncteur
vivent dans `--state-dir`, hors du dépôt par défaut (`~/.paper_harness`) :

```bash
# premier passage : attribuer à la poche une somme fictive du compte paper
python -m paper_harness.ibkr_cycle --initial-cash 100000 --small-lines --max-position-pct 0.5
# passages suivants : le registre est réutilisé
python -m paper_harness.ibkr_cycle --small-lines --max-position-pct 0.5
# envoyer les ordres paper (« Read-Only API » décoché sur la passerelle)
python -m paper_harness.ibkr_cycle --small-lines --max-position-pct 0.5 --send
```

Codes de sortie : 0 cycle fait, 2 refus (compte non paper, configuration incohérente),
3 échec de connexion. `--max-position-pct` doit couvrir le plafond par ligne de la
stratégie (50 %) : avec la valeur par défaut de `RISK_MAX_POSITION_PCT` (25 %), le cycle
refuse de démarrer plutôt que de laisser le `RiskGate` bloquer chaque achat de taille
pleine.

Validation du 2026-10-03, en lecture seule contre IB Gateway paper (samedi, marchés
fermés) : les quatre lignes se résolvent par `conId`, les prix différés sont lus, les
signaux américains (`ADJUSTED_LAST`) suffisent au calcul des poids, et le cycle planifie
un achat par ligne sur la poche fictive sans rien envoyer. Un second passage réutilise le
registre sans le réinitialiser.

## Suite (cycles suivants)

1. Premier cycle envoyé sur le compte paper (« Read-Only API » décoché côté
   passerelle), puis déclenchement mensuel et comparaison des exécutions au backtest.
2. Premier ordre paper (BTC spot sur Coinbase sandbox ; équity IBKR derrière
   "Read-Only API" OFF côté gateway) derrière circuit-breakers relus — **après**
   obtention des creds Coinbase USER-HAND.

## Liens

- [README parent](../README.md) — Phase 1-3 + roadmap 5 phases + migration MiCA
- Issue [#1027](https://github.com/jsboige/CoursIA/issues/1027)
- [`.env.template`](../.env.template) — clés de configuration (`.env` local gitigné)
