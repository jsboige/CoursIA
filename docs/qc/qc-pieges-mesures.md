# Pièges mesurés QuantConnect et Lean

Cette page sert aux agents qui backtestent, corrigent ou mesurent des stratégies QuantConnect et Lean du dépôt : chaque piège ci-dessous a d'abord coûté une mesure ou un cycle de diagnostic avant d'être compris. Chaque entrée a été mesurée sur ce dépôt ; l'issue ou la PR de la mesure est citée quand la source en donne une, sinon l'entrée porte la mention « mesure directe, sans issue dédiée ».

## Avant de conclure sur un backtest

- [ ] [Le run est `completed: true`, `progress: 1`, et les statistiques sont présentes (sinon, relire)](#ne-rien-conclure-avant-completed-true)
- [ ] [Les statistiques sont lues sous `statistics.*` / `runtimeStatistics.*` en camelCase, pas par libellé en clair](#statistiques-sous-statistics-et-runtimestatistics-en-camelcase)
- [ ] [La plus forte variation de séance de la trace a été vérifiée (un prix erroné d'un facteur 1000 a déjà été vu)](#vérifier-la-plus-forte-variation-de-séance-avant-tout-test)
- [ ] [Le journal des ordres a été relu avant la mesure : refus, ventes manquantes, positions négatives](#un-ordre-en-séance-est-exécuté-à-la-clôture-en-résolution-journalière)
- [ ] [Les compteurs `invalid_orders` / `refused` / `margin_calls` sont publiés, à 0 pour un run sain](#une-rotation-mono-ligne-ne-vend-pas-les-autres-lignes)
- [ ] [`history(n)` appelé depuis `on_data` un jour de demi-séance rend environ 0,83 n barres](#historyn-sur-une-demi-séance-rend-environ-083-n-barres)
- [ ] [Les classes `PythonData` ont été vérifiées : `Time = date` sans `EndTime` lit le futur](#pythondata-sans-endtime-lit-le-futur)
- [ ] [L'accès au dataset est sondé : un univers non licencié tourne vide sans erreur](#un-dataset-non-licencié-donne-un-univers-vide-sans-erreur)
- [ ] [Le témoin est un backtest du code d'origine relancé le même jour, jamais la table publiée](#un-même-code-ne-rejoue-pas-toujours-ses-propres-ordres)
- [ ] [Les insights FLAT portent `weight=0` et les jours d'expiration sont comptés dans les ordres](#un-flat-sans-poids-est-ignoré-par-insightweightingpcm)
- [ ] [Le backtest trace au plus 10 séries, tous graphiques confondus](#dix-séries-tracées-au-maximum-par-backtest)
- [ ] [Le Sharpe est recalculé depuis l'equity : celui de QC soustrait un taux sans risque](#le-sharpe-affiché-par-qc-soustrait-un-taux-sans-risque)

## Lire un backtest

### Ne rien conclure avant completed true

- **Symptôme :** `read_backtest` rend des `statistics` à `"-"` et `totalOrders: 0` tant que le run est en file ou en cours ; un cas mesuré voit aussi `completed: true` arriver avec des statistiques vides (fenêtre flottante de l'espace QC sponsorisé, voir l'entrée « Témoin sur fenêtre flottante »).
- **Cause :** les statistiques ne sont écrites qu'à la fin du run ; le cas d'un run vraiment vide ou planté, l'incident fondateur et la garde d'assertion obligatoire sont détaillés dans la section « Mesures post-backtest » de [quantconnect.md](quantconnect.md).
- **Geste :** n'interpréter les statistiques que si `completed: true` et `progress: 1`, et relire par `read_backtest` si elles restent vides.
- **Source :** mesure directe, sans issue dédiée.

### Statistiques sous statistics et runtimeStatistics en camelCase

- **Symptôme :** un script qui cherche les statistiques d'un backtest par leurs libellés en clair (« Sharpe Ratio », « Total Fees ») lit du vide.
- **Cause :** `read_backtest` de `qc-mcp-lite` range les statistiques sous `statistics.*` en camelCase, et les frais et l'équité sous `runtimeStatistics.*`.
- **Geste :** adresser les clés `statistics.*` et `runtimeStatistics.*` exactement telles que rendues par l'outil.
- **Source :** mesure directe, sans issue dédiée.

### Le MCP lite ne rend pas les analyses du rapport

- **Symptôme :** les analyses du rapport QC (`FlatEquityCurveAnalysis`, `SecurityPriceZeroOrderResponseErrorAnalysis` et consœurs) sont invisibles à travers `read_backtest` de `qc-mcp-lite`.
- **Cause :** la réponse de cet outil n'a pas de champ `analysis`, alors que l'API `/backtests/read` le rend.
- **Geste :** passer par le client REST du serveur `scripts/qc-mcp-lite/` (même jeton, même cadence que l'outil) et n'imprimer que `analysis[].name` et `sample` ; un `sample` peut lister plusieurs fenêtres, vérifier où elles tombent (début ou milieu de run) avant de dire l'analyse « présente pour le défaut ». La réponse de l'outil manque le champ `analysis` (vérifié dans `server.py::_extract_stats`).
- **Source :** #21585.

### netProfitAbsolute non fiable

- **Symptôme :** `netProfitAbsolute` a été relevé non fiable au cours d'une mesure, sans que le défaut observé ait été détaillé.
- **Cause :** constat de mesure uniquement, aucune cause n'est établie.
- **Geste :** utiliser `totalNetProfit` en pourcentage.
- **Source :** mesure directe, sans issue dédiée.

### Un même code ne rejoue pas toujours ses propres ordres

- **Symptôme :** le même code rejoué sur la même fenêtre ne reproduit pas une mesure de quelques mois plus tôt (Sharpe 0,752 et 2009 ordres en octobre contre 0,787 et 1994 ordres publiés en juillet, blob du `main.py` identique depuis juin) ; un même composite rend 9805 ou 9808 ordres entre deux runs.
- **Cause :** cause probable, non prouvée : mode de normalisation par défaut `ADJUSTED`, chaque nouveau dividende réécrit les prix historiques, donc les quantités et tout indicateur en unités de prix ; à cela s'ajoute une variance de quelques ordres entre deux runs du même code.
- **Geste :** rejouer le code d'avant le commit suspect le même jour (c'est le test qui tranche, il a réfuté une hypothèse en un backtest) ; comparer un témoin à un backtest du code d'origine lancé le même jour, jamais à la table publiée ; instrumenter l'ancien et le nouveau calcul au même instant avant d'imputer un écart à un correctif. Piste non testée : rejouer avec `data_normalization_mode` à `RAW` ou `SPLIT_ADJUSTED` à deux dates.
- **Source :** #21894, #21471.

### Un projet cloud cité par un README peut porter un autre code

- **Symptôme :** la mesure qu'on veut citer depuis un README ne correspond pas au comportement du code présent dans le dépôt.
- **Cause :** constat de mesure : le code du projet QC Cloud référencé par un README est parfois différent de la copie du dépôt ; la manière dont l'écart est survenu n'est pas établie.
- **Geste :** comparer le code du projet cloud au fichier du dépôt avant de citer une mesure qui en provient.
- **Source :** mesure directe, sans issue dédiée.

## Ordres et exécution

### Un ordre en séance est exécuté à la clôture en résolution journalière

- **Symptôme :** un `liquidate()` suivi de `set_holdings(cibles)` n'envoie que les écarts : le portefeuille reste sous-investi (exposition médiane mesurée à 0,71 fois la cible), sans aucune erreur ni ordre invalide.
- **Cause :** avec `Resolution.DAILY`, un ordre au marché passé en séance (ex. `after_market_open(+30)`) est rempli à la clôture ; le second appel calcule donc ses quantités contre des positions pas encore vendues.
- **Geste :** calculer les quantités absolues avant de liquider (`q = portfolio[s].quantity + calculate_order_quantity(s, w)`), puis appeler `liquidate()` puis `market_order(s, q)` ; en backtest les ventes passent d'abord à la même clôture, donc le pouvoir d'achat tient. Deux runs aux mêmes cibles mais aux pires baisses très différentes signalent ce défaut : relire le journal des ordres avant toute mesure.
- **Source :** #19174.

### set_holdings ignore les ordres encore en attente

- **Symptôme :** deux rééquilibrages le même jour (mensuel puis disjoncteur, tous deux remplis à la clôture) s'additionnent au lieu de se remplacer : SPY passé à découvert, DJP doublé.
- **Cause :** `set_holdings([PortfolioTarget(...)], liquidate_existing_holdings=True)` calcule bien les ordres sur la position finale, mais ignore les ordres pas encore remplis.
- **Geste :** appeler `self.transactions.cancel_open_orders()` juste avant le second train ; mesure après correctif : 0 position courte, 0 Invalid, 5 annulés par fenêtre. Détecter en rejouant les remplis jour par jour depuis le journal des ordres et en comptant les dates à position négative.
- **Source :** #23014.

### Prix zéro à la première séance planifiée

- **Symptôme :** `float division by zero` le premier jour d'une fenêtre, sur tout calcul qui divise par le prix (ex. plafond de marge `room / price`).
- **Cause :** aucun prix n'est connu à l'heure de la revue le jour 1 : `security.price == 0` à cette première séance, qui n'est donc jamais investie.
- **Geste :** garder `if security.price > 0` avant le calcul et reporter l'achat à la revue suivante.
- **Source :** #20388.

### Le contrôle de pouvoir d'achat ignore les ventes en attente

- **Symptôme :** `Insufficient buying power` à l'envoi des achats pendant une bascule ou une rotation ; après un refus, le portefeuille reste en liquidités jusqu'à la bascule suivante, sans erreur visible hors du journal des ordres. Cas mesurés : bascule à 100 % refusée d'un côté ou de l'autre de la limite selon la séance ; `set_holdings` à 1,0 sur deux titres au levier 2, un bras resté 56 mois sur 138 tout en liquidités ; rotation `MarketOnOpen` avec achat refusé environ un mois sur dix pendant que le drapeau de l'algorithme croit la ligne investie.
- **Cause :** la vente de la ligne détenue et l'achat de la nouvelle sont remplis à la même clôture (ou à l'ouverture suivante en `MarketOnOpen`), mais le contrôle de marge de l'achat ne déduit pas la vente encore en attente ; au levier 2, deux lignes à 1,0 dépassent d'un rien le pouvoir d'achat.
- **Geste :** compter `invalid_orders` dans tout algorithme à bascule ; préférer `liquidate` puis achat à la séance suivante, ou relever le levier en le déclarant.
- **Source :** #24069, #19680, #20388.

### set_leverage(4) saute les petits ordres de rééquilibrage

- **Symptôme :** après le correctif `set_leverage(4)`, des ordres de rééquilibrage disparaissent (60/40 : 38 ordres du code gelé sans pendant en fenêtre 1) ; le plus petit ordre passé monte de 0,17 % de la valeur au levier 2 à 0,37 % au levier 4, pour un écart de valeur maximum de 0,063 %.
- **Cause :** explication probable, non vérifiée dans le source Lean : seuil minimal d'ordre exprimé en marge, qui double en valeur quand le levier double.
- **Geste :** relever le levier en le déclarant, et ne pas annoncer qu'une référence « rendra la même série » après un changement de levier.
- **Source :** #24069 (PR #24086).

### Une rotation mono-ligne ne vend pas les autres lignes

- **Symptôme :** jusqu'à trois lignes détenues à la fois, des centaines d'achats refusés, et pour seules ventes des appels de marge, même en univers sans levier.
- **Cause :** `set_holdings(cible, 1.0)` sur un seul titre n'envoie pas les ventes des autres lignes ; sur le compte marge par défaut (levier 2), l'achat part à crédit.
- **Geste :** correctif mesuré (`_rotate_to`) : quantités calculées avant les ventes, ventes d'abord, cible 0,98, complément sous 0,97, ordres ouverts déduits, achat plafonné ; publier les compteurs `refused` et `margin_calls` en statistiques d'exécution, un run sain les a à 0.
- **Source :** #20388.

### Compte cash crypto : l'ordre planifié est rempli à la barre suivante

- **Symptôme :** sur un compte cash en résolution journalière, une tâche planifiée suivie de `set_holdings` produit un jour de décalage sur le rendement prédit et des ordres Invalid (190 achats sur 505 Invalid mesurés), car l'achat est contrôlé avant que la vente soit créditée.
- **Cause :** un ordre envoyé par une tâche planifiée est contrôlé et rempli à la barre suivante, au prix de cette barre ; un ordre INVALID n'est jamais renvoyé ; un ordre envoyé depuis `on_data` est rempli à l'instant, au prix vendeur courant.
- **Geste :** décider dans `on_data` à l'arrivée des barres ; la tâche planifiée n'envoie que les ventes, et les achats partent une fois les ventes remplies, bornés par les liquidités libres au prix vendeur. Compter `invalid_orders` (dans `on_order_event`) et `missing_bars` ; après correctif : 0 Invalid sur 8 runs. Ce défaut se voit au journal des ordres, pas aux statistiques : relire les ordres dès la première passe.
- **Source :** #23563, #20388.

### set_holdings sur un contrat à terme dimensionne à la marge initiale

- **Symptôme :** une cible de 2,5 % sur un contrat à terme ouvre une position 10 à 20 fois plus grosse en exposition (notionnel brut médian de 2,36 fois la valeur pour une cible de 0,2).
- **Cause :** `set_holdings` dimensionne par la marge initiale, pas par le notionnel.
- **Geste :** dimensionner au notionnel : `int(round(side * w * TPV / (price * symbol_properties.contract_multiplier)))`, puis `market_order` sur l'écart ; `holdings_value` donne le notionnel pour le contrôle.
- **Source :** #23594 (PR #23601).

### calculate_order_quantity divisé par le multiplicateur empile la jambe courte

- **Symptôme :** une jambe courte vaut toujours -1 contrat et s'empile à chaque reconduction (position nette mesurée à -3,36 fois la valeur), une jambe longue tombe à 0.
- **Cause :** sur un contrat à terme, `calculate_order_quantity` rend des contrats dimensionnés à la marge initiale ET l'écart à la cible ; un code qui divise encore ce résultat par `contract_multiplier` avec `//` arrondit vers moins l'infini.
- **Geste :** repérer le motif `calculate_order_quantity` ou `set_holdings` suivi d'une division par le multiplicateur ; réparer en cible au notionnel moins la position, report tel quel au rollover, et garder l'ancien code comme témoin.
- **Source :** #23689 (PR #23692).

### month_start sans symbole saute des mois

- **Symptôme :** des rééquilibrages mensuels planifiés n'ont pas lieu certains mois.
- **Cause :** `date_rules.month_start()` sans symbole saute les mois dont le premier jour n'est pas un jour de bourse.
- **Geste :** toujours écrire `month_start("SPY")`.
- **Source :** #18941.

## Données et univers

### PythonData sans EndTime lit le futur

- **Symptôme :** 2894 décisions sur 2894 d'un projet lisaient la valeur du jour même d'un indice chargé par CSV ; l'effet sur le Sharpe était nul, mais le chiffre publié devait venir du code corrigé.
- **Cause :** Lean livre une donnée personnalisée (`PythonData`) à son heure de début quand aucune `EndTime` n'est fixée ; avec `Time = date` (jour de la ligne), la clôture du jour D est visible dès D 00:00 et une décision intraday de D lit le futur.
- **Geste :** avant de mesurer un projet qui charge un CSV ou un indice personnalisé, chercher `Time =` dans les classes `PythonData` ; si la ligne est datée au jour sans décalage, ajouter un mode `lag` (`Time = jour + 1`, colonne `tradeday` pour le compteur) et un compteur « dernière ligne lue du jour même ».
- **Source :** #19825, #19837 (instances connues non corrigées).

### history(n) sur une demi-séance rend environ 0,83 n barres

- **Symptôme :** `history(symbol, n)` journalier rend 208 à 210 barres pour n = 252, et 104 à 105 pour n = 126.
- **Cause :** appelé depuis `on_data` à la clôture de 13:00 d'une demi-séance NYSE (03/07, lendemain de Thanksgiving, 24/12) ; appelé depuis un événement planifié (minuit, ouverture +30, ouverture +60), il rend toujours n barres, la dernière étant la clôture de 16:00 de la veille.
- **Geste :** demander 2n puis tronquer par `.iloc[-n:]`, qui rend n dans tous les cas ; vérifier d'où part l'appel, pas seulement le calendrier.
- **Source :** #21471 (correctif #21487 / #20330).

### Un dataset non licencié donne un univers vide sans erreur

- **Symptôme :** backtest `Completed`, aucune erreur, 0 appel du sélecteur d'univers, 0 date tradable, 0 ordre : indiscernable d'un univers vide ou d'un bug.
- **Cause :** `add_universe(QuiverQuantCongressUniverse, sel)` sans licence tourne vide silencieusement ; seul le flux par titre du même dataset (`add_data`, `history`) lève l'erreur explicite de licence, dès l'initialisation.
- **Geste :** pour tester l'accès à un dataset, souscrire SPY explicitement (contrôle positif : barres comptées), compter les appels du sélecteur et les constituants, et ajouter le flux par titre du même fournisseur pour obtenir le message de licence exact.
- **Source :** #16372.

### Trou d'historique des paires USDC sur Coinbase

- **Symptôme :** `BTCUSDC` / `ETHUSDC` sur `Market.COINBASE` en journalier : séries complètes du 28/10/2018 à mi-juillet 2022, zéro barre de mi-2022 à fin 2025, 83 barres en 2026 ; `USDCUSD` absent de la base de symboles. Un backtest en devise de compte USDC tourne donc sur des prix figés par fill-forward.
- **Cause :** trou de données dans l'historique des paires USDC ; quand les deux cotations existent, l'écart USDC contre USD a une médiane de 0,02 à 0,06 % et un p95 inférieur ou égal à 0,77 %.
- **Geste :** backtester sur `BTCUSD` / `ETHUSD` avec un compte en USD ; sonder l'historique par `raise RuntimeError("PROBE|...")` dans `initialize` plutôt que de re-sonder sans raison nouvelle.
- **Source :** mesure directe, sans issue dédiée.

### Vérifier la plus forte variation de séance avant tout test

- **Symptôme :** une trace de backtest peut contenir un prix erroné d'un facteur 1000.
- **Cause :** donnée de prix ponctuellement erronée à la source, constatée une fois.
- **Geste :** vérifier la plus forte variation de séance d'une trace avant tout test qui s'appuie sur ses prix.
- **Source :** #24228.

### Les prix d'ordre QC sont ajustés

- **Symptôme :** les prix de remplissage ne collent pas aux prix bruts : SPY rempli vers 0,915 fois le prix brut.
- **Cause :** QC sert des prix ajustés par défaut, la trace d'ordres est donc en prix ajustés.
- **Geste :** comparer les prix d'ordre aux clôtures yfinance obtenues avec `auto_adjust=True`.
- **Source :** mesure directe, sans issue dédiée.

## Framework (alpha, insights, portefeuille)

### Les attributs Python sont invisibles sur l'objet algorithm du framework

- **Symptôme :** `getattr(algorithm, 'fundamental_cache', {})` rend le défaut à chaque appel, sans erreur : 84 appels mensuels sur 84 mesurés.
- **Cause :** dans le framework Lean Python, l'objet `algorithm` passé à `AlphaModel.update` ne porte pas les attributs Python posés sur l'algorithme ; un alpha qui sort par `if not scores: return []` ne lève rien, le composite tourne avec moins de facteurs qu'annoncé.
- **Geste :** passer une référence explicite à la construction (`ValueAlpha(owner=self)`), initialiser l'attribut dans `initialize` et lire `self.owner.<attr>` ; avant toute mesure d'un composite, compter les insights émis par alpha (`set_runtime_statistic`) et les champs lus avec valeur : un `0/0` est le signal.
- **Source :** #21141, #21137.

### Champs fondamentaux : mauvais noms lus en silence

- **Symptôme :** `price_to_book`, `return_on_equity` lus par `getattr(..., None)` sous `try/except` rendent zéro valeur sur la totalité des lignes du run.
- **Cause :** ces noms de champs n'existent pas ; les bons noms sont `pb_ratio`, `pe_ratio` (nombres), `roe`, `total_debt_equity_ratio` (MultiPeriodField, lire `.value`).
- **Geste :** vérifier les noms de champs contre l'API avant toute mesure d'un composite factoriel.
- **Source :** #21141.

### Une période timedelta compte des barres, pas des jours calendaires

- **Symptôme :** un insight « mensuel » de 30 jours chevauche l'émission suivante.
- **Cause :** `Insight.ComputeCloseTime(..., TimeSpan)` convertit `timedelta(days=30)` en 30 barres journalières, soit environ 6 semaines calendaires (vérifié dans le source Lean, commit 80e7843f6456, `Insight.cs:544-556`).
- **Geste :** compter la période en jours de bourse avant de prédire le comportement d'une variante Framework.
- **Source :** #20264.

### Un FLAT sans poids est ignoré par InsightWeightingPCM

- **Symptôme :** la ligne reste figée après l'émission d'un FLAT ; un UP de poids 0, lui, crée une cible 0 (vente) à l'émission.
- **Cause :** `GetTargetInsights` filtre les insights sans `Weight` avant de retenir le dernier insight par symbole (`PortfolioConstructionModel.cs:163-177`) ; l'ancien UP garde sa cible jusqu'à expiration, et la cible zéro n'est créée que si aucun insight n'est actif.
- **Geste :** émettre le FLAT avec `weight=0`.
- **Source :** #20264, confirmé sur #20388 (PR #21022).

### L'expiration d'un insight déclenche un rééquilibrage

- **Symptôme :** des ordres tombent hors des dates d'émission : 10 ordres sur 6 dates, toutes à exactement 30 séances de l'avant-dernière émission ; sur une autre stratégie, 288 des 743 ordres partent les jours d'expiration, et une prédiction qui comptait 610 ordres a été fausse pour avoir omis ce fait.
- **Cause :** l'expiration d'un insight déclenche un rééquilibrage du PCM, même si celui-ci ne rééquilibre qu'aux changements (`InsightWeightingPortfolioConstructionModel(lambda time: None)`) ; changer la période (30 vers 45 barres) déplace ces ordres (46 ordres sur 51 différents) sans changer le résultat au millième.
- **Geste :** inclure les jours d'expiration dans tout compte d'ordres pré-enregistré.
- **Source :** #20264 (PR #21069), PR #21109.

### PCM sans modèle de courtier : compte marge par défaut

- **Symptôme :** cinq lignes détenues à la fois, exposition brute 1,71, 282 achats refusés ; le CAGR passe de 10,0 % à 16,9 % sur la même stratégie.
- **Cause :** le PCM sans argument rééquilibre chaque jour en `Resolution.Daily` et, sans modèle de courtier, le compte est marge par défaut : une sur-exposition est financée et les achats au-delà sont refusés.
- **Geste :** une variante Framework qui bat sa jumelle standalone se vérifie d'abord sur les positions détenues.
- **Source :** #20388 (PR #21022).

## Graphiques et statistiques

### Grille d'environ 1,32 jour sur les graphiques par défaut

- **Symptôme :** aucun rendement par séance ne sort des graphiques par défaut (`Strategy Equity`, `Exposure`, `Portfolio Turnover`) : 5433 points pour 4946 séances, week-ends compris.
- **Cause :** ces graphiques suivent une grille uniforme d'environ 1,32 jour, week-ends compris.
- **Geste :** pour une série par séance, tracer 5 séries entrelacées `e0` à `e4`, avec un point toutes les 5 séances pour chacune : cela restitue les 4946 clôtures, toutes à des dates de séance.
- **Source :** #18921.

### Portfolio Turnover en fraction, points à écarter le jour du rééquilibrage

- **Symptôme :** la valeur lue n'est pas un pourcentage (environ 0,41 au premier rééquilibrage) ; deux points non nuls entourent chaque rééquilibrage.
- **Cause :** la valeur tracée est une fraction du portefeuille ; le jour même d'un rééquilibrage, la valeur tracée montre tantôt l'ancienne, tantôt la nouvelle, selon l'ordre des événements.
- **Geste :** écarter le point du jour de rééquilibrage avant toute agrégation.
- **Source :** #18921.

### Le Sharpe affiché par QC soustrait un taux sans risque

- **Symptôme :** 0,55 affiché contre 1,09 à taux sans risque nul sur 2007-2026 (taux implicite d'environ 3,6 %) ; le classement des variantes peut changer.
- **Cause :** le Sharpe de QC soustrait un taux sans risque implicite.
- **Geste :** toujours recalculer le Sharpe depuis la série d'equity.
- **Source :** #18921.

### Graphique Equity d'un algorithme à terme : points toutes les 23 heures

- **Symptôme :** points de week-end (mouvement du dimanche soir), dernier point avant la dernière séance, heure qui dérive ; un Sharpe calculé jour calendaire par jour calendaire le sous-estime d'environ 15 %.
- **Cause :** grille d'environ 23 heures sur les graphiques d'un algorithme négociant des contrats à terme ; la corrélation avec une référence prise à la clôture est tirée vers zéro par ce désalignement.
- **Geste :** prendre la dernière valeur de chaque jour ouvré à l'heure de New York, intersecter avec la référence, racine de 252 ; garder CAGR, MaxDD et PSR de QC.
- **Source :** #23594 (PR #23601).

### Dix séries tracées au maximum par backtest

- **Symptôme :** les dernières séries créées n'apparaissent pas dans le backtest, sans aucune erreur.
- **Cause :** QC garde 10 séries tracées par backtest, tous graphiques confondus, et perd les suivantes.
- **Geste :** compter les séries tracées avant d'en ajouter ; regrouper ou entrelacer les séries au-delà de 10.
- **Source :** #24153.

## Outils (API, MCP, IDE, Lean CLI)

### L'éditeur web QC écrase un envoi fait par l'API

- **Symptôme :** un `main.py` revenu à son ancienne version après un envoi par l'API, signature de build différente de celle attendue ; l'éditeur refuse le nouveau code (« Latest code changes not compiled yet ») tant qu'il n'a pas compilé lui-même, même si une compilation API a réussi.
- **Cause :** un fichier ouvert dans un onglet de l'éditeur web QC est réécrit par l'éditeur par-dessus la version envoyée par `update_file_contents`.
- **Geste :** fermer l'onglet du fichier dans l'éditeur, envoyer par l'API, recharger la page de l'éditeur, vérifier l'empreinte du fichier sur QC (le suffixe d'un compile id après le tiret est la signature du code), puis lancer Cloud Build dans l'éditeur et vérifier la signature du build.
- **Source :** mesure directe, sans issue dédiée.

### Une compilation verte ne prouve pas qu'une bibliothèque est attachée

- **Symptôme :** `create_compile` rend `BuildSuccess` avec une liste d'erreurs vide ; `create_backtest` plante en `Runtime Error` dans `Initialize()` avec `No module named ...`, 0 ordre.
- **Cause :** la compilation Python de QC ne résout pas les imports de bibliothèque ; l'attachement d'une bibliothèque à un projet ne se fait que dans l'interface QC (« Add Library »), pas par l'API.
- **Geste :** prouver la consommation par `read_project` (le fichier de la bibliothèque doit être listé dans le projet) ou par un backtest court qui passe `Initialize()`.
- **Source :** #20188.

### Le lean du PATH peut être le prouveur Lean 4

- **Symptôme :** `qc_quantbook_execute.py` échoue avec `unknown option --detach` et le journal montre le texte d'usage de Lean 4.
- **Cause :** `shutil.which("lean")` peut résoudre le prouveur Lean 4 d'elan au lieu du CLI QuantConnect, qui vit dans les Scripts du Python qui l'a installé (un autre interpréteur que celui que le script sonde) ; avec `MSYS2_ARG_CONV_EXCL='*'` en préfixe, la forme `/c/...` du chemin n'est pas convertie, `Path(...).exists()` rend faux et le script retombe silencieusement sur le prouveur.
- **Geste :** épingler `LEAN_CLI` sur le binaire du CLI (forme Windows du chemin) en préfixe du run.
- **Source :** mesure directe, sans issue dédiée.

### read_backtest (MCP lite) ne rend pas les logs

- **Symptôme :** impossible de sortir une mesure intermédiaire d'un backtest à travers le MCP lite.
- **Cause :** `read_backtest` ne renvoie que les statistiques et le texte d'erreur, pas les journaux d'exécution.
- **Geste :** faire sortir la mesure dans le texte d'erreur par `raise RuntimeError("PROBE|...")` dans `initialize`.
- **Source :** mesure directe, sans issue dédiée.

### self.history rend un DataFrame MultiIndex

- **Symptôme :** du code qui attend des objets barre échoue ou lit vide sur le résultat de `self.history(...)`.
- **Cause :** en Python, `self.history(...)` rend un DataFrame MultiIndex, pas des objets barre.
- **Geste :** traiter le résultat comme un DataFrame et retirer le premier niveau d'index par `droplevel(0)`.
- **Source :** mesure directe, sans issue dédiée.

## Suivi en ombre

### fill_forward=False pour un suivi en ombre crypto

- **Symptôme :** un passage avant minuit UTC reçoit une barre recopiée à la date du passage, refusée par `ingest-qc`.
- **Cause :** sans `fill_forward=False`, le remplissage fabrique une barre recopiée datée du passage quand la journée n'est pas terminée ; en crypto, `tradeableDates` couvre tous les jours calendaires.
- **Geste :** demander les barres du suivi en ombre avec `fill_forward=False`.
- **Source :** mesure directe, sans issue dédiée.

### shadow_replay.py : options avant la sous-commande

- **Symptôme :** un appel qui place les chemins après la sous-commande ne les prend pas en compte.
- **Cause :** `shadow_replay.py` vit sous `MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/scripts/` et ses options `--registry .../registry.json` et `--csv .../passes.csv` se placent avant la sous-commande.
- **Geste :** ordonner l'appel : script complet, puis `--registry` et `--csv` avec leurs chemins, puis la sous-commande.
- **Source :** mesure directe, sans issue dédiée.

### Témoin sur fenêtre flottante : comparer sur le préfixe commun

- **Symptôme :** le témoin et la variante ne couvrent pas la même fin de fenêtre d'un run à l'autre ; `completed: true` peut arriver avec des statistiques vides.
- **Cause :** dans l'espace QC sponsorisé, la fin des données avance avec la date du run (la troncature de fin de backtest est détaillée dans la section « Organisations QC » de [quantconnect.md](quantconnect.md)).
- **Geste :** comparer le témoin sur son préfixe commun de dates, et relire par `read_backtest` si les statistiques sont vides.
- **Source :** mesure directe, sans issue dédiée.
