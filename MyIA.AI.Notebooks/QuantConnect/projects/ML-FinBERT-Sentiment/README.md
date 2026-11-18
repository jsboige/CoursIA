# ML-FinBERT-Sentiment (HandsOn Ex19)

**Classe d'actifs :** Actions US (la plus volatile des 10 plus liquides)
**ID projet Cloud :** 29936073 (HandsOn-Ex19-FinBERT-Sentiment)

## Description

Portage fidèle du modèle de base de l'exemple 19 du livre (*Hands-On AI Trading*, chapitre 06) : FinBERT (`ProsusAI/finbert`) classe les articles Tiingo des 10 derniers jours, le sentiment agrégé (poids exponentiels) décide long 100 % ou short 25 %, au rebalancement mensuel.

**Exécution sur QC Cloud** : même pipeline que le livre, sous **blindage par étape** (adaptation d'exécution, cf. §Historique) et sur une **fenêtre de 2 mois** — les deux conditions mesurées pour qu'un backtest complète.

**Le modèle tourne dans l'algorithme sur QC Cloud** (variante PyTorch, `local_files_only=True` comme le livre) — mesuré par les sondes `probe2-bitmask-finbert` et `probe3-tiingo-decode` du 2026-10-05 : `torch`, `transformers` et même `tensorflow` importent sur les nœuds, et l'inférence y rend ses probabilités.

## Modèle ré-entraîné (exemple 19/02)

L'exemple 19/02 du livre va plus loin : **ré-entraîner** FinBERT, à chaque rebalancement mensuel, sur les articles des 30 derniers jours étiquetés par la réaction du cours, avant de scorer le mois. Deux artefacts le portent :

- `main_finetuned.py` — portage fidèle du code du livre en PyTorch (écarts n1–n8 documentés en tête de fichier). Il **n'est pas exécutable en CI ni sur un nœud QC ordinaire** : le ré-entraînement tourne dans l'algorithme et demande un GPU.
- `finetune/run_finetune_finbert.py` — harnais **hors ligne** qui sort le ré-entraînement de l'algorithme pour l'exécuter sur un GPU local, et **compare modèle de base et modèle ré-entraîné hors échantillon**.

Le livre n'a **aucune séparation entraînement / hors échantillon** — il ré-entraîne et prédit sur les mêmes 100 échantillons du mois. Le harnais ajoute la séparation que l'issue demande : les six derniers mois sont retirés de l'entraînement.

### Corpus et étiquetage — deux écarts mesurés, pas supposés

**Source des articles.** Le livre lit Tiingo News sur QC Cloud ; hors ligne, le harnais lit **FNSPID** (`Stock_news/All_external.csv`, corpus public horodaté de même forme : date + ticker + titre). Le corpus est **CC BY-NC 4.0** et reste un **cache local hors dépôt** : seules les mesures sont committées. Sa couverture temporelle a été **mesurée** (échantillonnage de plages d'octets dans le fichier) avant de calibrer la fenêtre : ≈ 2004–2020, d'où le choix de 2015–2019.

**Fenêtre de réaction.** Le livre mesure la réaction du cours **entre deux parutions consécutives**, sur des clôtures à la seconde (`Resolution.SECOND`). À résolution quotidienne, cette règle s'effondre : deux parutions de la même séance n'ont aucune réaction résolvable et rendent un label exactement nul. Mesuré sur le corpus du harnais : **410 des 680 paires consécutives (60 %) tombent dans la même séance**, donc **429 labels (63 %) sont nuls exactement** — ce qui fabrique une classe neutre majoritaire à 75 %, que le livre ne connaît pas. Le harnais mesure donc la réaction **à la parution** (rendement de la première séance dont la clôture suit l'instant de parution). Sur le même corpus, la distribution des classes passe de **12 / 75 / 13** à **32 / 29 / 38**, contre les **37,5 / 25 / 37,5** que la règle du livre vise. L'intention du livre est préservée ; sa mécanique de mesure est adaptée à la résolution disponible, et l'écart est écrit en tête du harnais.

**Sélecteur d'actif et couverture du corpus.** Le livre retient le plus volatil des dix valeurs les plus liquides, sur un marché où la couverture d'actualité est **universelle** (Tiingo News sur QC Cloud). Hors ligne, la couverture de FNSPID est **très inégale** : le sélecteur du livre y désigne régulièrement un titre sans actualité observable. Mesure sur le corpus complet (13,06 M d'enregistrements parcourus, 22 496 articles retenus, 18 tickers) : la distribution va de HD 2 587 articles à **AMD 14**, et la tête de classement du livre *est* AMD — ce qui écartait **37 des 60 mois pour une raison de couverture, pas de stratégie**. Le harnais descend donc d'un rang quand le candidat n'est pas observable. Quand le premier choix du livre **est** couvert, il reste retenu à l'identique ; la même mesure passe alors à **1 948 échantillons sur 59 des 60 mois**.

### Résultat — 4 graines, et un verdict qui va contre le livre

Le harnais entraîne 1 680 échantillons sur 53 mois et évalue sur les **6 derniers mois tenus à l'écart** (268 échantillons, juillet-décembre 2019), quatre graines. Le modèle de base est le même pour toutes : exactitude hors échantillon **0,4515**.

| Graine | Exactitude ré-entraînée | Écart au modèle de base | McNemar p | Classes prédites [nég, neu, pos] |
| --- | --- | --- | --- | --- |
| 1 | 0,2948 | **−0,1567** | 0,0001 | [109, 14, 145] |
| 2 | 0,3694 | **−0,0821** | 0,0507 | [20, 6, 242] |
| 3 | 0,3731 | **−0,0784** | 0,0640 | [36, 0, 232] |
| 42 | 0,3470 | **−0,1045** | 0,0175 | [203, 4, 61] |
| *vérité* | — | — | — | [90, 75, 103] |

Écart moyen **−0,1054**, écart-type inter-graines 0,0361, soit **−2,92 σ**, et **aucune graine ne bat le modèle de base**. Verdict : **NO BEATS** — au sens strict, ce n'est pas « amélioration non démontrée » mais **dégradation démontrée**.

**Ce que la distribution des classes prédites ajoute à l'exactitude.** Le modèle de base prédit [70, 105, 93] : il sur-prédit le neutre, biais connu de FinBERT sur du texte court. Le modèle ré-entraîné prédit **0 à 14 neutres sur 268**, quelle que soit la graine — la classe neutre **disparaît**. Le signe du déséquilibre dépend en revanche de la graine (242 positifs pour la graine 2, 203 négatifs pour la graine 42) : ce n'est donc pas un effondrement sur une classe fixe, mais la perte du neutre **et** une instabilité de signe d'une graine à l'autre. Deux époques à 3e-5 sur 1 680 étiquettes bruitées suffisent à détruire la frontière du neutre d'un modèle pré-entraîné.

**Ce que ce verdict ne dit pas.** Il ne condamne pas la recette du livre, il condamne sa mesure **hors échantillon** dans ces conditions : le livre ré-entraîne et prédit sur les mêmes 100 échantillons du mois, donc sa mesure ne *peut pas* voir cette perte. C'est exactement l'écart que l'issue demande de mesurer.

**Portée.** Un univers de 24 grandes capitalisations, une fenêtre (2015-2019), un modèle de base, quatre graines. Le résultat est falsifiable via `finetune/measures/` (un fichier par graine plus l'agrégat) et reproductible par `finetune/run_finetune_finbert.py`.

## Historique du « 0 trade » (fermé le 2026-10-05)

Les portages v1/v2 appelaient `add_data(TiingoNews, "AAPL")` avec un **ticker en chaîne**. TiingoNews exige un `Symbol` d'action déjà mappé — l'appel lève `The custom data type TiingoNews requires mapping, but the provided ticker is not in the cache`, exception avalée par le `try/except` → zéro article → zéro trade. Le livre passe `security.symbol` (issu de l'univers) ; le portage fait de même désormais. Le diagnostic ancien « TF unavailable on QC Cloud » était faux sur les deux comptes.

**Deuxième couche (fermée le même jour)** : le portage fidèle crashait en `FATAL UNHANDLED EXCEPTION`. Douze exécutions (v1–v6, sondes probe4–probe10, projet 29936073) établissent une partition nette :

| Configuration | Effet mesuré |
| --- | --- |
| Portage non blindé, 100k, année complète — SPY jamais abonné (v1/v2) | FATAL en `initialize` (`hasInitializeError=true`, 2 reproductions) |
| Portage non blindé, 100k, année complète — SPY abonné (v3/v4) | FATAL natif **~12 s après le départ** (progress ~0,15) |
| Sondée blindée étape par étape, année complète (probe8, 1M) | **même FATAL natif** : blindage complet + cash 1M ne changent rien, `on_end_of_algorithm` jamais atteint, error = 100 % bruit TF → crash moteur, pas Python |
| Portage fidèle non blindé, 1M, **6 mois** (v5) | **même FATAL natif ~11 s après le départ** (progress 0,29) : un terme deux fois plus court ne repousse pas le mur |
| Portage fidèle non blindé, 1M, **2 mois** (v6) | **`Runtime Error`** — **aucune exécution non blindée n'a jamais complété (6/6)** |
| Sondée **blindée**, fenêtres courtes (probe5 janvier ; probe6/probe7 jan-fév ; probe9 jan-fév complet) | **toutes Completed** — probe9 traverse la transition du 1ᵉʳ février (re-sélection, `remove_security` TiingoNews, re-`add_data`, 2ᵉ `_trade`, vrais ordres ; Sharpe -1.137 sur jan-fév) |
| probe9 verbatim, année complète (probe10) | **`Runtime Error`** — le mur de l'année n'est pas une affaire de blindage |
| **Livrable** : portage fidèle **blindé**, 1M, **2 mois** (v7) | **`Completed.`** — 40 séances, **2 ordres** (les 2 rebalancements mensuels), Sharpe -1,137 : le livrable complète et trade |

Deux conditions sont nécessaires pour qu'un backtest complète, et aucune ne suffit seule : **une fenêtre ≤ 2 mois** (l'année et le semestre meurent nativement) **et le blindage par étape** (la seule exécution non blindée sur fenêtre courte échoue en `Runtime Error`, là où toutes les exécutions blindées de fenêtres courtes complètent — probe5, probe6, probe7, probe9 et le livrable v7). Le livrable réunit les deux.

## Comment exécuter

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/ML-FinBERT-Sentiment"` (le modèle doit être dans le cache HuggingFace local).
**QC Cloud :** projet 29936073, `create_compile` → `create_backtest`.

## Métriques de backtest

`ex19-portage-livre-2022-jan-fev-v7-blinde` — le livrable : portage fidèle blindé, cash 1 M, 2022-01-01 → 2022-03-01, **40 séances**, statut **`Completed.`** :

| Métrique | Livrable (v7, jan-fév 2022) | Sonde `probe9` (même fenêtre) | Référence livre |
| --- | --- | --- | --- |
| Sharpe | -1,137 | -1,137 | — |
| Rendement annualisé composé | -84,294 % | -84,294 % | — |
| Rendement net total | -26,230 % | -26,230 % | +123 % cumulé sur 2022 |
| Drawdown max | 37,800 % | 37,800 % | — |
| Probabilistic Sharpe Ratio | 8,371 % | 8,371 % | — |
| Profit net absolu | -20 375,04 $ | -20 375,04 $ | — |
| **Ordres** | **2** | 8193 | — |

Le livrable **complète et produit ses ordres** : 2 ordres = les 2 rebalancements mensuels (1ᵉʳ janvier, 1ᵉʳ février), exactement le comportement du livre. Le « 0 trade » de l'issue #18903 est fermé **par la mesure**, pas par un argument.

**Sur la sonde `probe9`** : elle porte 8191 ordres-marqueurs de plus (un `market_order` d'une action SPY par bit de son masque de diagnostic) et rend pourtant des statistiques **identiques à l'unité près** à celles de v7. Les marqueurs sont donc **neutres sur la mesure** — 8191 ordres d'écart ne déplacent ni le Sharpe, ni le rendement, ni le drawdown. Les deux exécutions se corroborent.

**Verdict du modèle de base : `INCONCLUSIVE`.** Sur 40 séances et **2 ordres** — les deux rebalancements mensuels, exactement le rythme du livre — l'échantillon est trop court pour conclure quoi que ce soit sur la stratégie. Le mot est exigé par le critère 4 de #18903, et le seul défendable ici est celui-ci : ni `BEATS` ni `NO BEATS`, parce que ce backtest n'est pas une mesure de performance — c'est la vérification qu'un portage fidèle **complète et trade**. Le verdict de l'autre bras, le ré-entraînement FinBERT évalué hors échantillon sur quatre graines, est **`NO BEATS`** et vit dans la section « Résultat » ci-dessus.

**Deux bornes de mesure, qui encadrent ce verdict.** (1) La comparaison au livre est **à fenêtre inégale** : le livre couvre 2022 entier, le livrable le premier sixième (mur natif, cf. §Historique) — aucun jugement de performance n'est tiré de l'écart. (2) Une seule configuration, déterministe, sans répétition multi-seed : le résultat est celui du portage fidèle, pas une évaluation du modèle.

## Fichiers

- `main.py` — Stratégie : portage PyTorch du `FinbertBaseModelAlgorithm` du livre (exemple 19/01)
- `main_finetuned.py` — Stratégie : portage du `FinbertFineTunedModelAlgorithm` du livre (exemple 19/02), ré-entraînement dans l'algorithme
- `finetune/run_finetune_finbert.py` — Harnais hors ligne : corpus, étiquetage, ré-entraînement GPU, évaluation hors échantillon base contre ré-entraîné
- `finetune/measures/` — Mesures committées (une par graine + agrégat)
- `research.ipynb` — Évaluation du modèle de sentiment

## Références

- *Hands-On AI Trading*, Section 06, Exemple 19 (01 Base Model, 02 Fine-Tuned Model)
- Repo du livre : `QuantConnect/HandsOnAITradingBook`, `06 Applied Machine Learning/19 FinBERT Model`
- `ProsusAI/finbert` — modèle de base (Hugging Face)
- FNSPID — corpus d'articles financiers horodatés, CC BY-NC 4.0 (cache local hors dépôt ; cf. `.claude/rules/bibliography-hygiene.md`)
