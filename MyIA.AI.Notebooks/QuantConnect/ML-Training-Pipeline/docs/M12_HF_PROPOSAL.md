# M12-HF — High-Frequency (Minute) Realized Volatility for HAR-RV-J

**Status :** PROPOSAL (PREP+PROPOSE). **Gated** sur (a) achat données minute crypto QC Cloud (QCC) + (b) greenlight user. Aucun achat, aucun run, aucun code exécuté tant que le greenlight n'est pas posé.

**Source de la mission :** directive ai-01 (dashboard workspace CoursIA, 2026-06-23T16:38Z) — rédiger spec + plan d'achat données minute crypto QCC + estimation coût, **sans acheter**. ai-01 escalade la décision d'achat vers le user une fois cette spec prête (signature données = user-blocker).

---

## 1. Contexte — pourquoi maintenant

Le pipeline ML/trading a consolidé un verdict net (cf [`docs/archive/ml-trading-state.md`](../../../../docs/archive/ml-trading-state.md) + `CURRICULUM.md` FINAL VERDICT) :

- **Direction / return forecasting = ÉPUISÉ** (0 BEATS / 14 FAILS POST-FIX : MTGNN, LSTM, Transformer, PatchTST, iTransformer, Mamba, STGAT sur SPY/BTC/multi). Ne pas ré-attempter.
- **Les seuls edges survivants = vol-forecasting + politique d'action apprise** : les 4 V2 KEEPERS (**M12 HAR-RV-J** p=7.9e-7, M15 LSTM h=32, S3 HMM, S4 v2 Ridge) + L4 Decision Transformer (24/26).
- **M12 HAR-RV-J = KEEPER le plus solide** : BEATS cluster-wide, p=7.9e-7, 64/84 (76.2 %), delta-Sharpe médian +0.0032 vs HAR Classic.

Le gate `ml-trading-state.md` §B est explicite (lignes 113-116) :

> « B. Après validation Phase B : acheter donnée minute crypto QC pour les 7 coins → lancer **M12-HF** (high-freq RV). **Seul achat signé.** »
> « Verdict : 0 QCCC maintenant (finir Phase B M12). Achat minute crypto QC **SEULEMENT** après verdict A/B M12 positif. »

**Phase B #83 (`HAR-RV-J-Kelly` QC production) = DONE** → le gate est franchi. M12-HF est donc le **prochain levier signé** — et le **seul achat de données autorisé** (point C : « Ne PAS acheter pour étendre l'univers d'actifs ni donnée alternative tant que le cœur vol n'est pas en prod »).

---

## 2. État courant (vérifié G.1 contre le code source)

Le module [`scripts/m12_har_rv_j.py`](../scripts/m12_har_rv_j.py) **utilise déjà des données intraday** pour estimer la RV et la bipower-variation journalières — M12-HF n'est **pas** « ajouter de l'intraday » (déjà présent), mais **monter en fréquence d'échantillonnage** :

- `daily_jump_component(intraday_log_returns, ...)` → `rv = daily_realized_variance(...)` + `bpv = daily_bipower_variation(...)`.
- Source actuelle : [`scripts/intraday_loader.py`](../scripts/intraday_loader.py) → **horly** (1h) : `load_bitstamp_btc` (`Bitstamp_BTCUSD_1h_2014-20240808.csv`), `load_binance_eth`, `load_yf_intraday(interval="1h")`. Crypto 24/7 → **24 observations / jour**.
- **Aucune donnée minute** dans le repo (`datasets/yfinance/crypto_panier/` = daily ; `stitch_crypto.py` Stage -1 = « BTC/USD 1h continuous »).

**Donc : M12-HF = remplacer la source horaire (24 obs/j) par une source minute (1440 obs/j) pour les mêmes estimateurs RV/BPV/J.** Le harnais walk-forward Kelly est inchangé.

---

## 3. Rationale scientifique

**Consistance de l'estimateur de realized volatility.** Andersen-Bollerslev-Diebold-Labys (2003, « Modeling and Forecasting Realized Volatility ») montrent que la RV (= somme des carrés des rendements intraday) converge vers la variance intégrée quand la fréquence d'échantillonnage augmente. À 24 obs/j (horaire crypto), la RV est un estimateur **bruité** ; la bipower-variation (BPV) et le Z-statistique de saut (Huang-Tauchen) le sont encore plus, car ils dépendent de produits de rendements adjacents — peu d'observations = forte variance d'estimation = détection de sauts peu fiable.

**Plancher de bruit de microstructure.** En dessous de ~1-5 min, le bruit de microstructure (bid-ask bounce, latence exchange) domine et **influe** artificiellement la RV (Hansen-Lunde 2006 ; Bandi-Russell 2008). La fréquence **minute est proche de l'optimum** pour le crypto liquid (BTC/ETH surtout) : assez fine pour réduire la variance de l'estimateur, assez coarse pour rester au-dessus du bruit. L'approche défensive = **sparse sampling** (sous-échantillonner à 1-min ou 5-min plutôt qu'utiliser tous les ticks) — standard en realized-vol econometrics.

**Hypothèse testable.** La RV/BPV minute étant plus précise, les composantes de saut `J_t = max(RV_t − μ·BPV_t, 0)` (μ = 0.6 Huang-Tauchen) deviennent plus nettes. Les régresseurs de saut de HAR-RV-J (`b_dj, b_wj, b_mj`) devraient gagner en signal. L'amélioration attendue se concentre donc sur **h=1** (où M12-horaire gagne déjà 24/28, 85.7 %) et sur le **terme de saut** — pas sur la RV continue (déjà bien captée).

**Risque réel à documenter.** Le bruit de microstructure minute **peut dégrader** la RV (inflation bid-ask) si l'échantillonnage est trop fin pour les coins moins liquides (DOT, ADA). Mitigation : sparse sampling 1-min/5-min + diagnostic per-coin de la « noise-to-signal ratio » (Hansen-Lunde). C'est précisément ce que la validation walk-forward tranchera.

---

## 4. Données requises + plan d'achat QCC

### 4.1 Signature des données

| Champ | Valeur |
|-------|--------|
| Univers | 7 coins anti-FAANG : BTC-USD, ETH-USD, SOL-USD, LTC-USD, XRP-USD, ADA-USD, DOT-USD |
| Résolution | **Minute** (1-min OHLCV) |
| Période | 2018-01 → 2025-12 (alignée fenêtre #1630, ~8 ans) |
| Source | QC Cloud — CoinAPI : **Binance** (principal, liquidité max) et/ou Coinbase |
| Format | LEAN (un fichier par ticker / jour / brokerage) |
| Acquisition | `lean data download` CLI (cf [QC Binance data](https://www.quantconnect.com/data/binance-crypto-price-data)) |

### 4.2 Volume estimé

~7 coins × 8 ans × 365 j × 1440 min/j ≈ **29.5 M barres / coin**, ~**207 M barres total**. Stockage LEAN compressé estimé ~5-15 GB.

### 4.3 Coût estimé (QCC) — **à confirmer au checkout**

- Conversion QC : **300 QCC = 3 USD** (source : [QC data pricing](https://www.quantconnect.com/data)).
- Les datasets CoinAPI/Binance minute sont vendus au téléchargement ; le coût exact **par symbole / par histoire complète** n'est pas publié sur la page publique (derrière le pricing page).
- **Bracket honnête** : datasets crypto minute QC historiquement de l'ordre de **~2-10 USD / symbole / histoire complète multi-années**. Pour les 7 coins : **~15-70 USD (~1.5k-7k QCC)**.
- **Caveat G.1** : ce bracket est une estimation basée sur le barème QCC et des datasets comparables, **pas** un prix vérifié.
- **Réalité du pricing vérifiée (G.1, 2026-06-23)** : `lean data download` n'a **pas** de flag `--dry-run` / d'aperçu de coût (seulement des credentials data-provider + des options de téléchargement) — il consomme les QCC à la confirmation. La [page pricing Binance CoinAPI](https://www.quantconnect.com/datasets/binance-crypto-price-data/pricing) est une SPA JS derrière login : un fetch statique ne retourne que le shell (« Algorithm Lab v3.0 »), **aucun prix public**. **Donc le prix ferme exact exige l'un des deux** : (a) login QC-web (Playwright sur le compte QC) pour consulter la grille tarifaire logged-in, OU (b) greenlight user pour un micro-achat mono-symbole qui révèle le coût au prompt de confirmation (`lean data download` l'affiche avant de débiter). Le bracket ~15-70 USD reste l'estimation courante en attendant le chiffre ferme.
- Note : les coins à listing tardif (SOL/DOT/AVAX 2020, cf `CURRICULUM.md` Stage 3a) limitent la profondeur historique réelle — ne pas payer pour des années pré-listing.

### 4.4 Décision requise (user-blocker)

L'achat est une **décision user** qu'**ai-01 escalade** (signature données = user-blocker, cf directive ai-01). Tant que le greenlight n'est pas posé : **0 QCC dépensé, 0 `lean data download`, 0 run**. Le présent doc sert de base à cette décision.

### 4.5 Convention de sauvegarde + vérification pré-achat (HARD, mandat user 2026-06-23)

**Sauvegarde durable (HARD).** Toute donnée achetée via `lean data download` est **sauvegardée** dans `G:\Mon Drive\MyIA\Dev\Trading\Data` (durable, réutilisable cross-projet, **ne JAMAIS re-payer** une donnée déjà acquise). Cette convention s'applique à **tous** les achats data futures du pipeline ML/trading, pas seulement M12-HF.

**Vérification pré-achat (G.1, faite 2026-06-23).** Le répertoire ci-dessus a été audité **avant** tout achat. Résultat :

| Élément | État |
|---------|------|
| `Minutes_246537_1216726_bundle_archive.zip` | **Déjà présent (gratuit)** — OHLCV minute **réel** (`time,open,close,high,low,volume`, timestamps unix-ms, incréments 60000 ms), couvrant **2013-04-01 → 2020-06-05**, pour **4 des 7 coins** : btcusd, ethusd, ltcusd, xrpusd (~2.8 M barres BTC seul) |
| SOL-USD / ADA-USD / DOT-USD | **Absents** du bundle (listings post-2020) → à acheter |
| Période **2020-06 → 2025** | **Absente** pour tous les coins → à acheter (c'est le segment le plus décisif : bear 2022 + momentum 2024-25) |
| Format | Le bundle GDrive est **CSV générique** (pas LEAN QC) → conversion vers LEAN requise avant ingestion |

**Conséquence sur le scope d'achat.** Le bracket ~15-70 USD (§4.3) est une **borne supérieure** : la fraction déjà couverte gratuitement (4 coins × 2018-2020) réduit le périmètre payant. Le script `minute_loader.py` du §5 devra **fusionner deux sources** : le CSV GDrive converti (2018-2020 × 4 coins) **et** le LEAN QC acheté (2020-2025 × 7 coins). Le prix ferme ne peut être isolé qu'après résolution du point §4.3 (login QC-web).

---

## 5. Changements pipeline (post-greenlight)

1. **Nouveau** `scripts/minute_loader.py` (parallèle à `intraday_loader.py`) : **fusionne deux sources** — (i) le bundle CSV minute GDrive converti au format LEAN (4 coins BTC/ETH/LTC/XRP × 2018-2020, cf §4.5, gratuit) **et** (ii) les archives LEAN minute QC Cloud achetées (7 coins × 2020-2025) — puis produit des `IntradayDataset` minute + `minute_log_returns`. Un adaptateur de format gère le CSV générique GDrive (normalisation pandas `time/open/high/low/close/volume` → LEAN) avant la fusion.
2. **Sparse-sampling option** : `minute_loader` expose `sample_freq ∈ {1min, 5min}` (défaut 5min = robuste microstructure ; 1min = test liquides BTC/ETH).
3. **Ré-utilisation** de `daily_realized_variance` / `daily_bipower_variation` / `daily_jump_component` (inchangés — ils prennent déjà une série intraday quelconque).
4. **Nouveau** `scripts/m12_hf_har_rv_j.py` : fork de `m12_har_rv_j.py`, source = minute_loader au lieu de intraday_loader. Même sortie (`results/m12_hf/`).
5. **Aucun changement** au harnais Kelly/walk-forward (`m11g_fee_aware_kelly`, `m11c_sharpe_test`, `ledoit_wolf_sharpe_diff_se`).

Pas de GPU requis (OLS + pandas). Compute CPU thermal-safe. Runtime estimé ~1-3 h pour les 84 combos (parité avec M12-horaire).

---

## 6. Cadre de validation

| Élément | Valeur |
|---------|--------|
| Walk-forward | 5-fold expanding OLS, refit every 22 j |
| Combos | 7 coins × 3 horizons (h=1, 5, 10) × 4 seeds (0,1,7,42) = 84 |
| Baselines | **(a) M12-horaire** (le comparatif décisif), (b) HAR Classic |
| Test | DM direction-aware + sign-test paired Sharpe-diff (HAC SE, Ledoit-Wolf) |
| Kelly | cap=1.0 (M11i a confirmé cap=3.0 tué par Calmar) |
| Frais | fee=50 bps (break-even HAR Kelly, cf M11f) |

**Critère d'acceptation** : M12-HF **BEATS_p005** M12-horaire sur **≥4/7 coins à h=1** (le front où M12 gagne déjà). Si M12-HF ne bat pas M12-horaire → verdict « HF n'apporte rien sur cette univers/période », documenté, pas d'itération forcée. Si le bruit de microstructure minute **dégrade** → fallback sparse 5-min ; si dégradation persiste → M12-horaire reste le KEEPER, M12-HF clos négatif.

Honnêteté des rapports (cf `verify-before-claiming`) : verdict **BEATS / NO BEATS / INCONCLUSIVE** par combo, pas de « promising ».

---

## 7. Résultats attendus (hypothèse, à falsifier)

- **Attendu** : amélioration modeste concentrée h=1 + terme de saut (les régresseurs `b_dj/b_wj/b_mj` gagnent en signal). Magnitude attendue ~+10-30 % du delta-Sharpe M12→M12-HF (donc faible — M12 lui-même ne bat HAR Classic que de +0.0032 médian).
- **Risque** : microstructure minute influe RV sur coins peu liquides (DOT/ADA) → M12-HF NO BEATS sur ces coins, BEATS seulement sur BTC/ETH/LTC. Ce serait **déjà un résultat utile** (cadre de validité de la fréquence d'échantillonnage).
- **Décisionnel** : même un NO BEATS clarifié vaut l'achat — c'est le **dernier levier non testé** du cœur vol, et il ferme la question « est-ce que la fréquence d'échantillonnage plafonne M12 ? ».

---

## 8. Pourquoi pas les alternatives

Toutes les pistes GARCH-family / regime-switching / bivariate / multi-asset Kelly = **NO BEATS** (M10 Realized GARCH 0/21, M13 MS-HAR 39/84, M14 HEAVY 48/84, M11j Multi-Asset Kelly 0/36 — cf [`M_NEXT_VOL_PROPOSAL.md`](M_NEXT_VOL_PROPOSAL.md) table comparative). M12-HF est le **seul levier non testé** sur l'axe « qualité de l'estimateur de realized measure » — orthogonal aux pistes déjà invalidées (qui jouaient sur la *forme du modèle*, pas sur la *qualité de l'input*). C'est précisément pourquoi le gate §B le réserve comme seul achat signé.

---

## 9. Gating récapitulatif

| Gate | État |
|------|------|
| Phase B #83 (`HAR-RV-J-Kelly` prod) | **DONE** → gate §B franchi |
| Direction-ML épuisé (0/14 BEATS) | **confirmé** → M12-HF est le bon axe (vol, pas direction) |
| Training G.1 HOLD | **maintenu** (M12-HF = CPU, pas de GPU) |
| **Achat données minute QCC** | **GATED user greenlight** (ai-01 escalade) |
| **Run M12-HF** | **après achat + greenlight** |

**Aucune action tant que le greenlight user n'est pas posé.** Ce document est la base de la décision.

---

## 10. Références

- Andersen, T.G., Bollerslev, T. & Diebold, F.X. (2007) « Roughing It Up: Including Jump Components in the Measurement, Modeling, and Forecasting of Return Volatility », *Review of Economics and Statistics* 89(4):701-720. (modèle HAR-RV-J de M12.)
- Andersen, T.G., Bollerslev, T., Diebold, F.X. & Labys, P. (2003) « Modeling and Forecasting Realized Volatility », *Econometrica* 71(2):579-625. (consistance RV / fréquence d'échantillonnage.)
- Hansen, P.R. & Lunde, A. (2006) « Realized Variance and Market Microstructure Noise », *Journal of Business & Economic Statistics* 24(2):127-161. (plancher de bruit / sparse sampling.)
- Bandi, F.M. & Russell, J.R. (2008) « Microstructure noise, realized variance, and optimal sampling », *Review of Economic Studies* 75(2):339-369.
- Huang, X. & Tauchen, G. (2005) « The Relative Contribution of Jumps to Total Price Variance », *Journal of Financial Econometrics* 3(4):456-499. (seuil μ ≈ 0.6.)

Docs internes : [`M12_HAR_RV_J.md`](M12_HAR_RV_J.md) (résultats M12-horaire), [`M_NEXT_VOL_PROPOSAL.md`](M_NEXT_VOL_PROPOSAL.md) (comparatif M10-M14), [`docs/archive/ml-trading-state.md`](../../../../docs/archive/ml-trading-state.md) §B (gate achat).
