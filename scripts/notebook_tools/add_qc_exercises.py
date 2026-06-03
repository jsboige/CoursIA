#!/usr/bin/env python3
"""Add exercises to QuantConnect Cloud notebooks for #2161 convention."""

import json
import uuid

def load_notebook(path):
    with open(path, 'r', encoding='utf-8') as f:
        return json.load(f)

def save_notebook(path, nb):
    with open(path, 'w', encoding='utf-8') as f:
        json.dump(nb, f, ensure_ascii=False, indent=1)

def make_cell(cell_type, source):
    cell = {
        "cell_type": cell_type,
        "id": uuid.uuid4().hex[:8],
        "metadata": {},
        "source": [source] if isinstance(source, str) else source
    }
    if cell_type == "code":
        cell["execution_count"] = None
        cell["outputs"] = []
    return cell

def find_cell_index(cells, cell_id):
    for i, c in enumerate(cells):
        if c.get("id") == cell_id:
            return i
    return None

def find_cell_after(cells, search_text, start=0):
    """Find first cell whose source contains search_text, return its index."""
    for i in range(start, len(cells)):
        src = cells[i].get("source", "")
        if isinstance(src, list):
            src = "".join(src)
        if search_text in src:
            return i
    return None

def insert_after(cells, idx, cells_to_insert):
    """Insert cells_to_insert after index idx."""
    for j, new_cell in enumerate(cells_to_insert):
        cells.insert(idx + 1 + j, new_cell)

def add_exercises(path, exercises):
    """
    exercises: list of (after_search_text, md_content, code_content)
    """
    nb = load_notebook(path)
    cells = nb["cells"]

    offset = 0
    for after_text, md_src, code_src in exercises:
        idx = find_cell_after(cells, after_text, offset)
        if idx is None:
            print(f"  WARNING: Could not find '{after_text[:50]}...' in {path}")
            continue

        md_cell = make_cell("markdown", md_src)
        code_cell = make_cell("code", code_src)

        cells.insert(idx + 1, md_cell)
        cells.insert(idx + 2, code_cell)
        offset = idx + 3

    save_notebook(path, nb)
    print(f"  Added {len(exercises)} exercises to {path}")

# ============================================================
# Exercise definitions for each notebook
# ============================================================

EXERCISES = {
    # Notebook 3: ML-Classification
    "QC-Py-Cloud-02-ML-Classification.ipynb": [
        (
            "Positive Words et Negative Words",
            '### Exercice 1 : Extension du vocabulaire financier\n\n'
            'Le vocabulaire utilise dans la demonstration couvre seulement 42 mots uniques. '
            'Pour ameliorer la precision du classifieur, il faut enrichir ce vocabulaire.\n\n'
            '**Objectif** : Ajoutez au moins 10 nouveaux mots financiers aux listes `positive_words` et `negative_words` '
            'de la cellule de scoring Naive Bayes. Testez le classifieur sur de nouveaux titres que vous inventez.\n\n'
            '**Indices** :\n'
            '- # Indice : Pensez aux termes utilises dans les rapports financiers : "dividend", "guidance", "outlook", "upgrade", "downgrade".\n'
            '- # Indice : Testez avec des titres ambigus contenant des mots des deux listes.',

            '# Exercice 1 : Extension du vocabulaire financier\n'
            '# TODO etudiant : ajouter au moins 10 mots positifs et 10 negatifs\n'
            '# Indice : pensez aux termes de rapports financiers, upgrades/downgrades\n'
            '\n'
            'extended_positive = set()  # TODO etudiant : ajouter vos mots ici\n'
            'extended_negative = set()  # TODO etudiant : ajouter vos mots ici\n'
            '\n'
            'def extended_sentiment_score(headline):\n'
            '    # TODO etudiant : implementer le scoring avec le vocabulaire etendu\n'
            '    return None  # TODO etudiant : retourner le score\n'
            '\n'
            'result_vocab = None  # TODO etudiant : tester sur de nouveaux titres\n'
            'print("Exercice a completer : extension du vocabulaire financier")\n'
        ),
        (
            "Score hybride",
            '### Exercice 2 : Score hybride sentiment + technique\n\n'
            "L'algorithme QC combine un signal textuel (50%) et un signal technique (50%) pour produire un score hybride. "
            "Le signal technique utilise le RSI, le ratio EMA et le momentum.\n\n"
            '**Objectif** : Implementez une fonction `hybrid_score(sentiment, rsi, ema_ratio, momentum)` '
            'qui combine les signaux avec des poids personnalisables. Testez differents poids (60/40, 40/60, 50/50) '
            'et observez comment le signal final change.\n\n'
            '**Indices** :\n'
            '- # Indice : Normalisez chaque signal entre 0 et 1 avant la combinaison.\n'
            '- # Indice : Un RSI < 30 est un signal d\'achat (contrarien), un RSI > 70 est un signal de vente.',

            '# Exercice 2 : Score hybride sentiment + technique\n'
            '# TODO etudiant : implementer hybrid_score(sentiment, rsi, ema_ratio, momentum, weights)\n'
            '# Indice : normaliser chaque input entre 0 et 1 avant combinaison\n'
            '\n'
            'def hybrid_score(sentiment, rsi, ema_ratio, momentum, weights=(0.5, 0.2, 0.15, 0.15)):\n'
            '    # TODO etudiant : normaliser le sentiment (deja entre -1 et 1)\n'
            '    # TODO etudiant : normaliser le RSI (0-100 -> 0-1, inverser car contrarien)\n'
            '    # TODO etudiant : calculer le score pondere\n'
            '    return None  # TODO etudiant : retourner le score hybride\n'
            '\n'
            'result_hybrid = None  # TODO etudiant : tester avec differents poids\n'
            'print("Exercice a completer : score hybride sentiment + technique")\n'
        ),
        (
            "Conclusion",
            '### Exercice 3 : Evaluation des performances du classifieur\n\n'
            'Un classifieur Naive Bayes produit des probabilites P(hausse) pour chaque headline. '
            'Pour evaluer sa qualite, on utilise la precision (fraction des predictions positives qui sont correctes) '
            'et le rappel (fraction des vrais positifs detectes).\n\n'
            '**Objectif** : Simulez 100 paires (prediction, verite terrain) avec un biais vers les bonnes predictions (55-60% de precision). '
            'Calculez la precision, le rappel et la F1-score. Affichez la matrice de confusion.\n\n'
            '**Indices** :\n'
            '- # Indice : Utilisez `np.random.choice([0, 1])` pour simuler les predictions.\n'
            '- # Indice : Precision = TP / (TP + FP), Rappel = TP / (TP + FN), F1 = 2 * P * R / (P + R).',

            '# Exercice 3 : Evaluation des performances du classifieur\n'
            '# TODO etudiant : simuler 100 paires (prediction, verite) avec biais\n'
            '# TODO etudiant : calculer precision, rappel et F1-score\n'
            '# Indice : Precision = TP/(TP+FP), Rappel = TP/(TP+FN)\n'
            '\n'
            'import numpy as np\n'
            'np.random.seed(42)\n'
            '\n'
            'def evaluate_classifier(n_samples=100, accuracy=0.57):\n'
            '    # TODO etudiant : generer les predictions et labels\n'
            '    # TODO etudiant : calculer TP, FP, TN, FN\n'
            '    # TODO etudiant : calculer precision, rappel, F1\n'
            '    return None  # TODO etudiant : retourner les metriques\n'
            '\n'
            'result_eval = None  # TODO etudiant : appeler evaluate_classifier\n'
            'print("Exercice a completer : evaluation du classifieur")\n'
        ),
    ],

    # Notebook 4: SectorRotation-Momentum
    "QC-Py-Cloud-02-SectorRotation-Momentum.ipynb": [
        (
            "Correlation elevee entre secteurs",
            '### Exercice 1 : Calcul du momentum relatif\n\n'
            'La rotation sectorielle selectionne les secteurs avec le meilleur momentum relatif. '
            'Le momentum 6 mois est calcule comme le rendement sur 126 jours de bourse.\n\n'
            '**Objectif** : Implementez une fonction `relative_momentum(prices, lookback=126)` qui prend un DataFrame de prix '
            '(lignes = dates, colonnes = tickers) et retourne le classement par momentum. Identifiez le top 3.\n\n'
            '**Indices** :\n'
            '- # Indice : Le momentum 6m = prix_actuel / prix_actuel_minus_126 - 1.\n'
            '- # Indice : Triez par momentum decroissant et prenez les 3 premiers.',

            '# Exercice 1 : Calcul du momentum relatif\n'
            '# TODO etudiant : implementer relative_momentum(prices, lookback=126) -> classement\n'
            '# Indice : momentum = prix[-1] / prix[-lookback] - 1\n'
            '\n'
            'import numpy as np\n'
            '\n'
            'def relative_momentum(prices_dict, lookback=126):\n'
            '    # prices_dict : {ticker: array_de_prix}\n'
            '    # TODO etudiant : calculer le momentum pour chaque ticker\n'
            '    # TODO etudiant : trier par momentum decroissant\n'
            '    return None  # TODO etudiant : retourner le classement\n'
            '\n'
            '# Test avec des donnees simulees\n'
            'np.random.seed(42)\n'
            'sim_prices = {t: 100 + np.cumsum(np.random.randn(300) * (0.3 + 0.1*i)) for i, t in enumerate(["XLK","XLY","XLF","XLE","XLV"])}\n'
            'result_mom = None  # TODO etudiant : appeler relative_momentum\n'
            'print("Exercice a completer : momentum relatif sectoriel")\n'
        ),
        (
            "Filtre tendance = protection drawdown",
            '### Exercice 2 : Double filtre tendance AQR\n\n'
            "L'approche AQR utilise un double filtre : prix > SMA200 ET momentum 6 mois > 0. "
            "Ce filtre elimine les actifs en bear market. La v3 atteint un Sharpe de 0.614 grace a ce filtre.\n\n"
            '**Objectif** : Implementez `aqr_filter(prices)` qui retourne la liste des actifs eligibles selon le double filtre. '
            'Testez avec des series simulees en bull, bear et sideways.\n\n'
            '**Indices** :\n'
            '- # Indice : Un actif en bull aura prix > SMA200 ET momentum_6m > 0.\n'
            '- # Indice : En bear market, la plupart des actifs seront exclus par le filtre.',

            '# Exercice 2 : Double filtre tendance AQR\n'
            '# TODO etudiant : implementer aqr_filter(prices_dict) -> list des tickers eligibles\n'
            '# Indice : eligible si prix[-1] > SMA(200) ET momentum_6m > 0\n'
            '\n'
            'def aqr_filter(prices_dict, sma_period=200, mom_period=126):\n'
            '    # TODO etudiant : pour chaque ticker, verifier les deux conditions\n'
            '    return None  # TODO etudiant : retourner la liste des eligibles\n'
            '\n'
            'result_aqr = None  # TODO etudiant : tester avec des series simulees\n'
            'print("Exercice a completer : double filtre AQR")\n'
        ),
        (
            "Lecon : L'equal-weight est plus robuste",
            '### Exercice 3 : Comparaison equal-weight vs momentum-weighted\n\n'
            "La v4 (momentum-weighted) sous-performe la v3 (equal-weight) avec un Sharpe de 0.276 vs 0.614 et un MaxDD de 38.8% vs 15.5%. "
            "La ponderation par momentum concentre trop le portefeuille sur l'actif le plus chaud.\n\n"
            '**Objectif** : Simulez les poids equal-weight et momentum-weighted pour 4 actifs avec des scores de momentum differents. '
            'Calculez la concentration (indice Herfindahl-Hirschman, somme des carres des poids) pour chaque methode. '
            'Un HHI plus eleve indique une plus grande concentration.\n\n'
            '**Indices** :\n'
            '- # Indice : HHI = sum(w_i^2). Pour equal-weight avec N actifs, HHI = 1/N.\n'
            '- # Indice : Momentum-weighting normalise les scores de momentum pour sommer a 1.',

            '# Exercice 3 : Comparaison equal-weight vs momentum-weighted\n'
            '# TODO etudiant : calculer les poids equal-weight et momentum-weighted\n'
            '# TODO etudiant : calculer la concentration HHI pour chaque methode\n'
            '# Indice : HHI = sum(w_i^2), plus HHI est haut, plus c est concentre\n'
            '\n'
            'def hhi(weights):\n'
            '    # TODO etudiant : calculer l indice Herfindahl-Hirschman\n'
            '    return None  # TODO etudiant : retourner la somme des carres\n'
            '\n'
            'mom_scores = {"QQQ": 0.15, "SPY": 0.08, "EFA": -0.02, "GLD": 0.05}\n'
            'result_alloc = None  # TODO etudiant : comparer HHI(equal) vs HHI(momentum-weighted)\n'
            'print("Exercice a completer : equal-weight vs momentum-weighted")\n'
        ),
    ],

    # Notebook 5: DualMomentum
    "QC-Py-Cloud-03-DualMomentum.ipynb": [
        (
            "Momentum absolu",
            '### Exercice 1 : Implementation du filtre de momentum absolu\n\n'
            "Le momentum absolu (time-series) verifie si un actif a un rendement positif sur une periode donnee. "
            "Si oui, l'actif est en tendance. Si non, on se refugie en defensif.\n\n"
            '**Objectif** : Implementez `absolute_momentum(prices, lookback=252)` qui retourne True si le rendement est positif, '
            'False sinon. Testez sur des series simulees en tendance haussiere et baissiere.\n\n'
            '**Indices** :\n'
            '- # Indice : Rendement = prix_actuel / prix_actuel_minus_lookback - 1.\n'
            '- # Indice : Un lookback de 252 jours correspond a environ 12 mois de bourse.',

            '# Exercice 1 : Implementation du filtre de momentum absolu\n'
            '# TODO etudiant : implementer absolute_momentum(prices, lookback=252) -> bool\n'
            '# Indice : retourne True si le rendement sur lookback jours est > 0\n'
            '\n'
            'import numpy as np\n'
            '\n'
            'def absolute_momentum(prices, lookback=252):\n'
            '    # TODO etudiant : calculer le rendement sur lookback jours\n'
            '    return None  # TODO etudiant : retourner True ou False\n'
            '\n'
            'np.random.seed(42)\n'
            'bull = 100 + np.cumsum(np.random.randn(300) * 0.5 + 0.03)\n'
            'bear = 100 + np.cumsum(np.random.randn(300) * 0.5 - 0.03)\n'
            'result_abs_mom = None  # TODO etudiant : tester sur bull et bear\n'
            'print("Exercice a completer : filtre de momentum absolu")\n'
        ),
        (
            "Selection de l'univers",
            '### Exercice 2 : Selection du top N par momentum relatif\n\n'
            "Le Dual Momentum combine le filtre absolu (rendement > 0) avec une selection par momentum relatif "
            "(top N par rendement). L'algorithme v2 selectionne le top 2 parmi 5 actifs.\n\n"
            '**Objectif** : Implementez `dual_momentum_select(returns_dict, top_n=2)` qui filtre les actifs avec momentum absolu > 0, '
            'puis selectionne le top N par momentum relatif.\n\n'
            '**Indices** :\n'
            '- # Indice : Premier filtre : ne garder que les actifs avec rendement > 0.\n'
            '- # Indice : Second filtre : trier par rendement decroissant et prendre les top_n.',

            '# Exercice 2 : Selection du top N par momentum relatif\n'
            '# TODO etudiant : implementer dual_momentum_select(returns_dict, top_n=2)\n'
            '# Indice : 1) filtrer rendement > 0, 2) trier et prendre top_n\n'
            '\n'
            'def dual_momentum_select(returns_dict, top_n=2):\n'
            '    # returns_dict : {ticker: rendement_12m}\n'
            '    # TODO etudiant : filtrer les actifs avec rendement > 0\n'
            '    # TODO etudiant : trier par rendement decroissant\n'
            '    return None  # TODO etudiant : retourner les top_n tickers\n'
            '\n'
            'returns = {"SPY": 0.12, "QQQ": 0.18, "IEF": 0.03, "GLD": -0.05, "XLP": 0.06}\n'
            'result_dual = None  # TODO etudiant : appeler dual_momentum_select\n'
            'print("Exercice a completer : selection Dual Momentum")\n'
        ),
        (
            "Impact de l'actif defensif",
            "### Exercice 3 : Impact de l'actif defensif sur le drawdown\n\n"
            "La v1 utilise BND comme defensif (Sharpe 0.340, MaxDD 33.6%). La v2 elimine le defensif separe "
            "et inclut des actifs defensifs dans l'univers (Sharpe 0.392, MaxDD 23.6%).\n\n"
            '**Objectif** : Simulez un scenario de bear market ou SPY et QQQ perdent 25% en 6 mois. '
            'Comparez la perte du portefeuille dans 3 cas : (a) 100% SPY, (b) 100% BND, (c) 50% IEF + 50% GLD. '
            'Calculez le drawdown maximal pour chaque cas.\n\n'
            '**Indices** :\n'
            '- # Indice : En bear market, BND peut aussi perdre (correlation non-nulle avec actions en 2022).\n'
            '- # Indice : GLD a historiquement une correlation negative avec les actions en periode de crise.',

            "# Exercice 3 : Impact de l'actif defensif sur le drawdown\n"
            '# TODO etudiant : simuler un bear market et comparer 3 allocations defensives\n'
            '# Indice : en bear, SPY/QQQ perdent 25%, BND perd 5-15%, GLD peut gagner\n'
            '\n'
            'import numpy as np\n'
            '\n'
            'def simulate_drawdown(allocation, scenarios):\n'
            '    # allocation : {ticker: weight}\n'
            '    # scenarios : {ticker: rendement_6m}\n'
            '    # TODO etudiant : calculer le rendement pondere du portefeuille\n'
            '    return None  # TODO etudiant : retourner le drawdown\n'
            '\n'
            'bear_scenario = {"SPY": -0.25, "QQQ": -0.30, "BND": -0.08, "IEF": -0.03, "GLD": 0.05}\n'
            'result_defense = None  # TODO etudiant : comparer les 3 allocations\n'
            'print("Exercice a completer : impact de lactif defensif")\n'
        ),
    ],

    # Notebook 6: Risk-Parity
    "QC-Py-Cloud-03-Risk-Parity.ipynb": [
        (
            "Volatilite 60j",
            '### Exercice 1 : Calcul de la volatilite realisee\n\n'
            "La volatilite realisee sur 60 jours est l'indicateur cle du Risk Parity. Elle est calculee comme "
            "l'ecart-type des rendements quotidiens sur une fenetre glissante, annualise par multiplication par sqrt(252).\n\n"
            '**Objectif** : Implementez `realized_vol(returns, window=60)` qui retourne la volatilite annuelle realisee. '
            'Testez avec des rendements simules et comparez differentes fenetres (21, 60, 126 jours).\n\n'
            '**Indices** :\n'
            '- # Indice : Vol_annualisee = std(rendements) * sqrt(252).\n'
            '- # Indice : Une fenetre plus courte reactit plus vite mais est plus bruitee.',

            '# Exercice 1 : Calcul de la volatilite realisee\n'
            '# TODO etudiant : implementer realized_vol(returns, window=60) -> float\n'
            '# Indice : vol_annualisee = std(rendements_fenetre) * sqrt(252)\n'
            '\n'
            'import numpy as np\n'
            '\n'
            'def realized_vol(returns, window=60):\n'
            '    # TODO etudiant : prendre les derniers window rendements\n'
            '    # TODO etudiant : calculer ecart-type et annualiser\n'
            '    return None  # TODO etudiant : retourner la vol annualisee\n'
            '\n'
            'np.random.seed(42)\n'
            'sim_returns = np.random.normal(0.0003, 0.01, 500)\n'
            'result_vol = None  # TODO etudiant : comparer window=21, 60, 126\n'
            'print("Exercice a completer : volatilite realisee")\n'
        ),
        (
            "Trigger de derive",
            '### Exercice 2 : Detection de derive des poids\n\n'
            "Le Risk Parity rebalance mensuellement mais verifie intra-mensuellement si les poids ont derive "
            "au-dela d'un seuil de 5%. Si oui, un rebalancement d'urgence est declenche.\n\n"
            '**Objectif** : Implementez `check_drift(target_weights, current_prices, initial_prices, threshold=0.05)` '
            'qui detecte si un actif a derive au-dela du seuil.\n\n'
            '**Indices** :\n'
            '- # Indice : Le poids actuel = (quantite * prix_actuel) / valeur_portefeuille.\n'
            '- # Indice : Si |poids_actuel - poids_cible| > seuil, il y a derive.',

            '# Exercice 2 : Detection de derive des poids\n'
            '# TODO etudiant : implementer check_drift(target, current, threshold=0.05) -> bool\n'
            '# Indice : derive si |poids_actuel - poids_cible| > threshold pour au moins un actif\n'
            '\n'
            'def check_drift(target_weights, current_weights, threshold=0.05):\n'
            '    # TODO etudiant : comparer chaque poids actuel au poids cible\n'
            '    return None  # TODO etudiant : retourner True si derive detectee\n'
            '\n'
            'target = {"SPY": 0.20, "EFA": 0.20, "GLD": 0.20, "DBC": 0.20, "TLT": 0.20}\n'
            'current = {"SPY": 0.24, "EFA": 0.18, "GLD": 0.19, "DBC": 0.21, "TLT": 0.18}\n'
            'result_drift = None  # TODO etudiant : appeler check_drift\n'
            'print("Exercice a completer : detection de derive")\n'
        ),
        (
            "Rebalancement mensuel",
            '### Exercice 3 : Simulation du rebalancement Risk Parity\n\n'
            "Un portefeuille Risk Parity rebalance mensuellement vers les poids cibles. Entre deux rebalancements, "
            "les prix bougent et les poids derivent. Le rebalancement vend les actifs surponderes et achete les sous-ponderes.\n\n"
            '**Objectif** : Simulez un portefeuille de 5 ETFs sur 12 mois. Recalculez les poids Risk Parity chaque mois '
            'en utilisant la volatilite realisee glissante. Affichez l\'evolution des poids au fil du temps.\n\n'
            '**Indices** :\n'
            '- # Indice : Chaque mois, calculez la vol sur 60j, puis les poids 1/vol.\n'
            '- # Indice : Les poids changeront legerement chaque mois car la vol change.',

            '# Exercice 3 : Simulation du rebalancement Risk Parity\n'
            '# TODO etudiant : simuler 12 mois de rebalancement Risk Parity\n'
            '# Indice : chaque mois, recalculer vol(60j) puis poids 1/vol\n'
            '\n'
            'import numpy as np\n'
            '\n'
            'def simulate_rp_rebalance(returns_dict, n_months=12, vol_window=60):\n'
            '    # returns_dict : {ticker: array de rendements quotidiens}\n'
            '    # TODO etudiant : boucler sur les mois\n'
            '    # TODO etudiant : recalculer poids Risk Parity chaque mois\n'
            '    return None  # TODO etudiant : retourner historique des poids\n'
            '\n'
            'result_rp_sim = None  # TODO etudiant : lancer la simulation\n'
            'print("Exercice a completer : simulation rebalancement Risk Parity")\n'
        ),
    ],

    # Notebook 7: MeanReversion
    "QC-Py-Cloud-04-MeanReversion.ipynb": [
        (
            "RSI d'un secteur tombe",
            '### Exercice 1 : Calcul du RSI sur une serie de prix\n\n'
            "Le RSI (Relative Strength Index) mesure la vitesse et l'amplitude des mouvements de prix. "
            "Un RSI < 35-40 indique une condition de survente (signal d'achat en mean reversion).\n\n"
            '**Objectif** : Implementez `compute_rsi(prices, period=14)` qui retourne le RSI actuel. '
            'Testez sur une serie simulee avec un mouvement de hausse puis de baisse brutale.\n\n'
            '**Indices** :\n'
            '- # Indice : RSI = 100 - 100/(1 + RS), ou RS = moyenne_gain / moyenne_perte.\n'
            '- # Indice : Un RSI < 30 est fortement surventu, < 40 est modrement surventu.',

            '# Exercice 1 : Calcul du RSI sur une serie de prix\n'
            '# TODO etudiant : implementer compute_rsi(prices, period=14) -> float\n'
            '# Indice : RSI = 100 - 100/(1 + RS), RS = avg_gain / avg_loss\n'
            '\n'
            'import numpy as np\n'
            '\n'
            'def compute_rsi(prices, period=14):\n'
            '    # TODO etudiant : calculer les differences quotidiennes\n'
            '    # TODO etudiant : separer gains et pertes\n'
            '    # TODO etudiant : calculer RS puis RSI\n'
            '    return None  # TODO etudiant : retourner le RSI\n'
            '\n'
            '# Test : serie avec hausse puis baisse\n'
            'np.random.seed(42)\n'
            'test_prices = np.concatenate([100 + np.cumsum(np.random.randn(50)*0.5+0.1),\n'
            '                               105 + np.cumsum(np.random.randn(30)*0.8-0.3)])\n'
            'result_rsi = None  # TODO etudiant : calculer le RSI\n'
            'print("Exercice a completer : calcul du RSI")\n'
        ),
        (
            "Regime filter (SMA200)",
            '### Exercice 2 : Filtre de regime SMA200\n\n'
            "Le regime filter est la difference entre le mean reversion dangereux (v1, MaxDD 42.4%) et le mean reversion "
            "viable (v2, MaxDD 14.6%). L'ajout d'un seul filtre -- ne pas acheter si prix < SMA200 -- divise le MaxDD par 3.\n\n"
            '**Objectif** : Implementez `regime_filter(prices, sma_period=200)` qui retourne True si le marche est en regime '
            'haussier (prix > SMA). Combinez avec le RSI pour ne generer des signaux d\'achat que quand RSI < 40 ET regime = haussier.\n\n'
            '**Indices** :\n'
            '- # Indice : Prix > SMA200 = regime haussier. Prix < SMA200 = bear market.\n'
            '- # Indice : En bear market, un RSI bas ne signifie pas "rebond imminent" mais "vente massive en cours".',

            '# Exercice 2 : Filtre de regime SMA200\n'
            '# TODO etudiant : implementer regime_filter(prices, sma_period=200)\n'
            '# TODO etudiant : combiner avec RSI pour generer des signaux filtres\n'
            '# Indice : acheter seulement si RSI < 40 ET prix > SMA200\n'
            '\n'
            'def mean_reversion_signal(prices, rsi_period=14, rsi_threshold=40, sma_period=200):\n'
            '    # TODO etudiant : calculer RSI et SMA\n'
            '    # TODO etudiant : retourner "ACHAT" si RSI < threshold ET prix > SMA\n'
            '    return None  # TODO etudiant : retourner le signal\n'
            '\n'
            'result_regime = None  # TODO etudiant : tester le signal\n'
            'print("Exercice a completer : filtre de regime SMA200")\n'
        ),
        (
            "Le stop-loss degrade",
            '### Exercice 3 : Impact du stop-loss sur le mean reversion\n\n'
            "Contre-intuitivement, le stop-loss a 8% degrade la performance en mean reversion (Sharpe 0.278 vs 0.307). "
            "Le mean reversion achete des actifs qui ont baisse ; un stop-loss declenche souvent avant le rebond.\n\n"
            '**Objectif** : Simulez 50 trades de mean reversion. Chaque trade achete apres une baisse de 5-15% et attend le rebond. '
            'Comparez deux strategies : (a) sans stop-loss, (b) avec stop-loss a 8%. Calculez le taux de trades coupes '
            'inutilement (rebond apres le stop).\n\n'
            '**Indices** :\n'
            '- # Indice : Simulez le prix post-achat comme un mouvement brownien avec un biais positif (mean reversion).\n'
            '- # Indice : Un stop a 8% sous l\'achat se declenche si le prix descend de 8% avant de remonter.',

            '# Exercice 3 : Impact du stop-loss sur le mean reversion\n'
            '# TODO etudiant : simuler 50 trades de mean reversion avec et sans stop-loss\n'
            '# Indice : comparer le nombre de trades coupes inutilement\n'
            '\n'
            'import numpy as np\n'
            '\n'
            'def simulate_mean_rev_trades(n_trades=50, stop_loss=0.08, seed=42):\n'
            '    np.random.seed(seed)\n'
            '    # TODO etudiant : pour chaque trade, simuler le chemin post-achat\n'
            '    # TODO etudiant : avec stop-loss, couper si prix tombe a -8%\n'
            '    return None  # TODO etudiant : retourner resultats avec/sans stop\n'
            '\n'
            'result_stop = None  # TODO etudiant : lancer la simulation\n'
            'print("Exercice a completer : impact du stop-loss")\n'
        ),
    ],

    # Notebook 8: RL-DQN-Trading
    "QC-Py-Cloud-04-RL-DQN-Trading.ipynb": [
        (
            "Epsilon-greedy",
            '### Exercice 1 : Politique epsilon-greedy\n\n'
            "L'agent DQN utilise une politique epsilon-greedy : avec probabilite epsilon, il choisit une action aleatoire "
            "(exploration), sinon il choisit la meilleure action selon Q(s,a) (exploitation). Epsilon decroit de 0.5 a 0.05.\n\n"
            '**Objectif** : Implementez `epsilon_greedy(q_values, epsilon)` qui retourne une action. Simulez 1000 decisions '
            'avec epsilon decroissant et affichez la frequence d\'exploration au fil du temps.\n\n'
            '**Indices** :\n'
            '- # Indice : Si random() < epsilon, choisir une action aleatoire, sinon argmax(Q).\n'
            '- # Indice : Epsilon decroit exponentiellement : eps(t+1) = eps(t) * decay.',

            '# Exercice 1 : Politique epsilon-greedy\n'
            '# TODO etudiant : implementer epsilon_greedy(q_values, epsilon) -> action\n'
            '# Indice : exploration si random() < epsilon, sinon argmax(Q)\n'
            '\n'
            'import numpy as np\n'
            '\n'
            'def epsilon_greedy(q_values, epsilon):\n'
            '    # TODO etudiant : implementer la politique\n'
            '    return None  # TODO etudiant : retourner l action choisie\n'
            '\n'
            'def epsilon_decay(eps_start=0.5, eps_min=0.05, decay=0.9978, n_steps=504):\n'
            '    # TODO etudiant : simuler la decroissance sur n_steps\n'
            '    return None  # TODO etudiant : retourner la liste des epsilon\n'
            '\n'
            'result_eps = None  # TODO etudiant : afficher la courbe de decroissance\n'
            'print("Exercice a completer : politique epsilon-greedy")\n'
        ),
        (
            "Recompense ajustee",
            '### Exercice 2 : Fonction de recompense ajustee au risque\n\n'
            "Le DQN utilise une recompense concave : `r - 0.5 * r^2`. Cette formulation penalise asymetriquement les pertes. "
            "Un rendement de +10% donne un reward de 0.05, un de -10% donne -0.15.\n\n"
            '**Objectif** : Implementez `risk_adjusted_reward(portfolio_return)` et comparez-la avec une recompense lineaire '
            "(r) sur une distribution de rendements simulee. Affichez les deux courbes et identifiez le point ou la penalite "
            "asymetrique commence.\n\n"
            '**Indices** :\n'
            '- # Indice : La fonction est concave : elle croit moins vite pour les grands rendements positifs.\n'
            '- # Indice : Pour r = 0, les deux fonctions coincident. Pour r < 0, la penalite est plus forte.',

            '# Exercice 2 : Fonction de recompense ajustee au risque\n'
            '# TODO etudiant : implementer risk_adjusted_reward(r) = r - 0.5*r^2\n'
            '# TODO etudiant : comparer avec la recompense lineaire sur un intervalle [-0.1, 0.1]\n'
            '# Indice : la fonction est concave, elle penalise les pertes plus fortement\n'
            '\n'
            'import numpy as np\n'
            '\n'
            'def risk_adjusted_reward(r):\n'
            '    # TODO etudiant : implementer r - 0.5*r^2\n'
            '    return None  # TODO etudiant : retourner le reward ajuste\n'
            '\n'
            'r_range = np.linspace(-0.10, 0.10, 100)\n'
            'result_reward = None  # TODO etudiant : tracer les deux courbes\n'
            'print("Exercice a completer : recompense ajustee au risque")\n'
        ),
        (
            "Experience replay",
            '### Exercice 3 : Experience replay buffer\n\n'
            "Le replay buffer stocke les experiences passees (s, a, r, s', done) et echantillonne des mini-batchs "
            "pour l'entrainement. Cela casse la correlation temporelle entre les experiences successives.\n\n"
            '**Objectif** : Implementez une classe `ReplayBuffer` avec les methodes `add(experience)` et `sample(batch_size)`. '
            'Remplissez le buffer avec 100 experiences simulees et echantillonnez un batch de 32.\n\n'
            '**Indices** :\n'
            '- # Indice : Utilisez `collections.deque(maxlen=capacity)` pour un buffer a taille fixe.\n'
            '- # Indice : `random.sample(buffer, batch_size)` echantillonne sans remplacement.',

            '# Exercice 3 : Experience replay buffer\n'
            '# TODO etudiant : implementer ReplayBuffer avec add() et sample()\n'
            '# Indice : utiliser deque(maxlen=capacity) et random.sample()\n'
            '\n'
            'import numpy as np\n'
            'import random\n'
            'from collections import deque\n'
            '\n'
            'class ReplayBuffer:\n'
            '    def __init__(self, capacity=5000):\n'
            '        # TODO etudiant : initialiser le deque\n'
            '        pass\n'
            '    \n'
            '    def add(self, state, action, reward, next_state, done):\n'
            '        # TODO etudiant : ajouter une experience\n'
            '        pass\n'
            '    \n'
            '    def sample(self, batch_size):\n'
            '        # TODO etudiant : echantillonner un batch\n'
            '        return None  # TODO etudiant : retourner le batch\n'
            '\n'
            'result_buffer = None  # TODO etudiant : tester le buffer\n'
            'print("Exercice a completer : experience replay buffer")\n'
        ),
    ],

    # Notebook 9: MLP-Forecasting
    "QC-Py-Cloud-05-MLP-Forecasting.ipynb": [
        (
            "Vecteur de features",
            '### Exercice 1 : Ingenierie de features temporelles\n\n'
            "Le MLP utilise 20 features pour predire la direction du prix. Ces features incluent des lag returns, "
            "volatilite glissante, RSI, momentum et autocorrelation.\n\n"
            '**Objectif** : Implementez une fonction `build_lag_features(returns, lags=[1,2,3,5,10,20])` qui extrait '
            "les rendements retardees. Verifiez que les 6 premieres features correspondent aux lag returns.\n\n"
            '**Indices** :\n'
            '- # Indice : lag_returns[i] = returns[-lag] pour chaque lag dans la liste.\n'
            '- # Indice : Attention a l\'indexation : returns[-1] est le dernier rendement, returns[-2] l\'avant-dernier, etc.',

            '# Exercice 1 : Ingenierie de features temporelles\n'
            '# TODO etudiant : implementer build_lag_features(returns, lags)\n'
            '# Indice : lag_returns[i] = returns[-lag]\n'
            '\n'
            'import numpy as np\n'
            '\n'
            'def build_lag_features(returns, lags=[1, 2, 3, 5, 10, 20]):\n'
            '    # TODO etudiant : extraire les rendements retardees\n'
            '    return None  # TODO etudiant : retourner le vecteur de features\n'
            '\n'
            'np.random.seed(42)\n'
            'test_returns = np.random.normal(0.0003, 0.01, 100)\n'
            'result_lags = None  # TODO etudiant : tester build_lag_features\n'
            'print("Exercice a completer : features temporelles")\n'
        ),
        (
            "Seuil de probabilite",
            '### Exercice 2 : Impact du seuil de probabilite\n\n'
            "L'algorithme utilise un seuil de P(hausse) > 0.52 pour decider de prendre une position. "
            "Ce seuil filtre les predictions incertaines. Un seuil plus bas genere plus de trades, "
            "un seuil plus haut est plus selectif.\n\n"
            '**Objectif** : Simulez 1000 predictions avec des probabilites entre 0.3 et 0.7. '
            "Pour differents seuils (0.50, 0.52, 0.55, 0.60), calculez le nombre de trades et le taux de reussite estime.\n\n"
            '**Indices** :\n'
            '- # Indice : Plus le seuil est eleve, moins de trades mais meilleur taux de reussite.\n'
            '- # Indice : Le seuil optimal depend du cout de transaction (plus de trades = plus de frais).',

            '# Exercice 2 : Impact du seuil de probabilite\n'
            '# TODO etudiant : simuler 1000 predictions et tester differents seuils\n'
            '# Indice : seuil plus haut = moins de trades mais meilleur taux de reussite\n'
            '\n'
            'import numpy as np\n'
            '\n'
            'np.random.seed(42)\n'
            'n_predictions = 1000\n'
            'probabilities = np.random.uniform(0.3, 0.7, n_predictions)\n'
            'true_directions = (np.random.random(n_predictions) < probabilities).astype(int)\n'
            '\n'
            'def evaluate_threshold(probs, truths, threshold):\n'
            '    # TODO etudiant : filtrer les predictions au-dessus du seuil\n'
            '    # TODO etudiant : calculer le nombre de trades et le taux de reussite\n'
            '    return None  # TODO etudiant : retourner (n_trades, win_rate)\n'
            '\n'
            'result_threshold = None  # TODO etudiant : tester seuils 0.50, 0.52, 0.55, 0.60\n'
            'print("Exercice a completer : seuil de probabilite")\n'
        ),
        (
            "MLP sklearn",
            '### Exercice 3 : Entrainement d\'un MLPClassifier\n\n'
            "Le MLPClassifier de sklearn avec couches cachees (64, 32) est l'architecture utilisee dans l'algorithme. "
            "Il est reentraine mensuellement sur une fenetre glissante de 252 jours.\n\n"
            '**Objectif** : Generez un jeu de donnees synthetiques (X: 20 features, y: binaire) avec un signal non-lineaire. '
            "Entrainez un MLPClassifier avec StandardScaler et evaluez la precision. Comparez avec un classifieur lineaire (LogisticRegression).\n\n"
            '**Indices** :\n'
            '- # Indice : Utilisez sklearn.pipeline.Pipeline pour combiner StandardScaler et MLPClassifier.\n'
            '- # Indice : Le MLP devrait surpasser la regression logistique sur des donnees non-lineaires.',

            "# Exercice 3 : Entrainement d'un MLPClassifier\n"
            '# TODO etudiant : generer des donnees synthetiques et entrainer un MLP\n'
            '# TODO etudiant : comparer avec une regression logistique\n'
            '# Indice : Pipeline(StandardScaler + MLPClassifier) pour normalisation\n'
            '\n'
            'import numpy as np\n'
            '\n'
            'def generate_synthetic_data(n_samples=500, n_features=20):\n'
            '    # TODO etudiant : generer X aleatoire et y avec un signal non-lineaire\n'
            '    return None, None  # TODO etudiant : retourner X, y\n'
            '\n'
            'result_mlp = None  # TODO etudiant : comparer MLP vs LogisticRegression\n'
            'print("Exercice a completer : entrainement MLP")\n'
        ),
    ],

    # Notebook 10: RegimeSwitching
    "QC-Py-Cloud-05-RegimeSwitching.ipynb": [
        (
            "SMA50/200 crossover",
            '### Exercice 1 : Detection de regime par SMA crossover\n\n'
            "Le regime switching detecte l'etat du marche avec un SMA crossover : prix > SMA200 ET SMA50 > SMA200 = Bull. "
            "Prix < SMA200 ET SMA50 < SMA200 = Bear. Autre = Sideways.\n\n"
            '**Objectif** : Implementez `detect_regime(prices)` qui retourne "BULL", "BEAR" ou "SIDEWAYS". '
            'Testez sur des series simulees avec des transitions de regime.\n\n'
            '**Indices** :\n'
            '- # Indice : Calculer SMA50 et SMA200, puis comparer au prix actuel.\n'
            '- # Indice : BULL = prix > SMA200 ET SMA50 > SMA200 (double confirmation).',

            '# Exercice 1 : Detection de regime par SMA crossover\n'
            '# TODO etudiant : implementer detect_regime(prices) -> str\n'
            '# Indice : BULL si prix > SMA200 ET SMA50 > SMA200\n'
            '\n'
            'import numpy as np\n'
            '\n'
            'def detect_regime(prices):\n'
            '    # TODO etudiant : calculer SMA50 et SMA200\n'
            '    # TODO etudiant : comparer au prix actuel\n'
            '    return None  # TODO etudiant : retourner "BULL", "BEAR" ou "SIDEWAYS"\n'
            '\n'
            '# Test avec une serie simulee\n'
            'np.random.seed(42)\n'
            'sim_prices = 100 + np.cumsum(np.random.randn(300) * 0.5)\n'
            'result_regime = None  # TODO etudiant : tester detect_regime\n'
            'print("Exercice a completer : detection de regime")\n'
        ),
        (
            "Regime + momentum selection",
            '### Exercice 2 : Allocation adaptive par regime\n\n'
            "La v2 adapte l'allocation au regime detecte : en Bull, momentum parmi SPY/QQQ ; "
            "en Bear, 50% IEF + 50% GLD ; en Sideways, 30% SPY + 35% IEF + 35% GLD.\n\n"
            '**Objectif** : Implementez `adaptive_allocation(regime, momentum_scores)` qui retourne un dictionnaire '
            "de poids. En Bull, selectionnez le meilleur actif par momentum avec un split 70/30.\n\n"
            '**Indices** :\n'
            '- # Indice : En Bull, donner 70% au meilleur momentum et 30% au second.\n'
            '- # Indice : En Bear, splitter equitablement entre IEF et GLD.',

            '# Exercice 2 : Allocation adaptive par regime\n'
            '# TODO etudiant : implementer adaptive_allocation(regime, momentum_scores)\n'
            '# Indice : BULL -> top momentum 70/30, BEAR -> IEF/GLD 50/50\n'
            '\n'
            'def adaptive_allocation(regime, momentum_scores=None):\n'
            '    # momentum_scores : {ticker: score}\n'
            '    # TODO etudiant : implementer la logique par regime\n'
            '    return None  # TODO etudiant : retourner {ticker: weight}\n'
            '\n'
            'scores = {"SPY": 0.08, "QQQ": 0.15, "IEF": 0.02, "GLD": 0.04}\n'
            'result_adaptive = None  # TODO etudiant : tester pour chaque regime\n'
            'print("Exercice a completer : allocation adaptive")\n'
        ),
        (
            "Meilleur Sharpe",
            '### Exercice 3 : Comparaison des strategies par ratio de Sharpe\n\n'
            "Le regime switching v2 atteint le meilleur Sharpe de la serie cloud (0.622). "
            "Pour comparer objectivement les strategies, le Sharpe ratio est la metrique standard.\n\n"
            '**Objectif** : Implementez `sharpe_ratio(returns, risk_free_rate=0.02)` qui calcule le Sharpe annualise. '
            "Comparez les strategies de la serie cloud a partir de leurs metriques.\n\n"
            '**Indices** :\n'
            '- # Indice : Sharpe = (rendement_moyen - taux_sans_risque) / ecart_type_rendements * sqrt(252).\n'
            '- # Indice : Annualiser en multipliant par sqrt(252) pour des rendements quotidiens.',

            '# Exercice 3 : Comparaison des strategies par ratio de Sharpe\n'
            '# TODO etudiant : implementer sharpe_ratio(returns, rf=0.02) -> float\n'
            '# Indice : Sharpe = (mean - rf) / std * sqrt(252)\n'
            '\n'
            'import numpy as np\n'
            '\n'
            'def sharpe_ratio(returns, risk_free_rate=0.02):\n'
            '    # returns : array de rendements quotidiens\n'
            '    # TODO etudiant : calculer le Sharpe annualise\n'
            '    return None  # TODO etudiant : retourner le Sharpe\n'
            '\n'
            '# Simuler des rendements pour 3 strategies\n'
            'np.random.seed(42)\n'
            'strategies = {\n'
            '    "Regime Switch": np.random.normal(0.0005, 0.008, 252),\n'
            '    "Risk Parity": np.random.normal(0.0003, 0.006, 252),\n'
            '    "Mean Reversion": np.random.normal(0.0002, 0.005, 252),\n'
            '}\n'
            'result_sharpe = None  # TODO etudiant : calculer et comparer les Sharpe\n'
            'print("Exercice a completer : ratio de Sharpe")\n'
        ),
    ],

    # Notebook 11: PCA-StatArb
    "QC-Py-Cloud-06-PCA-StatArb.ipynb": [
        (
            "Composantes principales",
            '### Exercice 1 : Application de la PCA sur des series de prix\n\n'
            "La PCA extrait les facteurs communs a partir de la matrice des log-prix de 100 actions. "
            "Les 3 premieres composantes expliquent plus de 90% de la variance.\n\n"
            '**Objectif** : Simulez 10 series de prix correlees (avec un facteur commun). '
            "Appliquez PCA et affichez la variance expliquee par chaque composante. Verifiez que les 3 premieres suffisent.\n\n"
            '**Indices** :\n'
            '- # Indice : Utilisez sklearn.decomposition.PCA sur les log-prix centres.\n'
            '- # Indice : pca.explained_variance_ratio_ donne le pourcentage de variance par composante.',

            '# Exercice 1 : Application de la PCA sur des series de prix\n'
            '# TODO etudiant : simuler 10 series correlees et appliquer PCA\n'
            '# Indice : sklearn.decomposition.PCA sur log-prix centres\n'
            '\n'
            'import numpy as np\n'
            '\n'
            'def simulate_correlated_prices(n_assets=10, n_days=200, seed=42):\n'
            '    # TODO etudiant : generer un facteur commun + bruit individuel\n'
            '    return None  # TODO etudiant : retourner la matrice de prix (n_days x n_assets)\n'
            '\n'
            'result_pca = None  # TODO etudiant : appliquer PCA et afficher variance expliquee\n'
            'print("Exercice a completer : PCA sur series de prix")\n'
        ),
        (
            "Z-scores",
            '### Exercice 2 : Calcul des z-scores de residus\n\n'
            "Les z-scores mesurent l'ecart entre le prix observe et le prix predit par le modele factoriel. "
            "Un z-score < -1.5 signale une sous-evaluation (opportunite d'achat).\n\n"
            '**Objectif** : Implementez `compute_zscores(residuals)` qui standardise les residus. '
            "Identifiez les actions avec un z-score inferieur a -1.5 dans un echantillon simule.\n\n"
            '**Indices** :\n'
            '- # Indice : Z-score = (residu - moyenne) / ecart-type.\n'
            '- # Indice : Un z-score de -2 signifie que le residu est 2 ecarts-types sous la moyenne.',

            '# Exercice 2 : Calcul des z-scores de residus\n'
            '# TODO etudiant : implementer compute_zscores(residuals) -> array\n'
            '# Indice : z = (x - mean) / std\n'
            '\n'
            'import numpy as np\n'
            '\n'
            'def compute_zscores(residuals):\n'
            '    # TODO etudiant : standardiser les residus\n'
            '    return None  # TODO etudiant : retourner les z-scores\n'
            '\n'
            '# Simuler des residus\n'
            'np.random.seed(42)\n'
            'sim_residuals = np.random.normal(0, 1, 50)\n'
            'sim_residuals[5] = -3.2  # outlier negatif\n'
            'sim_residuals[20] = -2.1  # autre outlier\n'
            'result_zscores = None  # TODO etudiant : identifier les z-scores < -1.5\n'
            'print("Exercice a completer : z-scores de residus")\n'
        ),
        (
            "Win rate de 48%",
            '### Exercice 3 : Profit factor et win rate\n\n'
            "La strategie PCA stat-arb a un win rate de 48% mais reste profitable grace a un profit-loss ratio de 1.30. "
            "Le profit factor (somme des gains / somme des pertes) est une metrique complementaire.\n\n"
            '**Objectif** : Simulez 200 trades avec un win rate de 48% et un gain moyen de 0.80% vs perte moyenne de 0.61%. '
            'Calculez le profit factor, le rendement cumule et le nombre de trades gagnants vs perdants.\n\n'
            '**Indices** :\n'
            '- # Indice : Profit factor = total_gains / total_pertes. Un PF > 1 est profitable.\n'
            '- # Indice : Le rendement cumule = produit des (1 + r_i) pour chaque trade.',

            '# Exercice 3 : Profit factor et win rate\n'
            '# TODO etudiant : simuler 200 trades et calculer profit factor\n'
            '# Indice : PF = sum(gains) / sum(pertes), un PF > 1 est profitable\n'
            '\n'
            'import numpy as np\n'
            '\n'
            'def simulate_trades(n_trades=200, win_rate=0.48, avg_win=0.008, avg_loss=0.0061, seed=42):\n'
            '    # TODO etudiant : generer les trades\n'
            '    # TODO etudiant : calculer PF, rendement cumule, win/loss counts\n'
            '    return None  # TODO etudiant : retourner les metriques\n'
            '\n'
            'result_pf = None  # TODO etudiant : lancer la simulation\n'
            'print("Exercice a completer : profit factor et win rate")\n'
        ),
    ],

    # Notebook 12: VolTargeting
    "QC-Py-Cloud-06-VolTargeting.ipynb": [
        (
            "weight = target_vol / realized_vol",
            '### Exercice 1 : Calcul du poids de volatilite targeting\n\n'
            "Le volatility targeting ajuste l'exposition selon la formule `weight = target_vol / realized_vol`. "
            "Quand la vol est haute, on reduit les positions ; quand elle est basse, on les augmente.\n\n"
            '**Objectif** : Implementez `vol_target_weight(realized_vol, target_vol=0.10, caps=(0.3, 1.5))` '
            "qui calcule le poids avec des bornes min/max. Testez avec differentes valeurs de vol realisee.\n\n"
            '**Indices** :\n'
            '- # Indice : Poids = 0.10 / vol_realisee. Si vol = 0.05, poids = 2.0 mais plafonne a 1.5.\n'
            '- # Indice : Les caps evitent un levier excessif en basse vol et une sous-exposition en haute vol.',

            '# Exercice 1 : Calcul du poids de volatilite targeting\n'
            '# TODO etudiant : implementer vol_target_weight(realized_vol, target_vol, caps)\n'
            '# Indice : weight = target_vol / realized_vol, clip entre caps\n'
            '\n'
            'import numpy as np\n'
            '\n'
            'def vol_target_weight(realized_vol, target_vol=0.10, caps=(0.3, 1.5)):\n'
            '    # TODO etudiant : calculer le poids et appliquer les bornes\n'
            '    return None  # TODO etudiant : retourner le poids borne\n'
            '\n'
            '# Test avec differentes valeurs de vol\n'
            'test_vols = [0.05, 0.08, 0.10, 0.15, 0.25, 0.40]\n'
            'result_vt = None  # TODO etudiant : calculer les poids pour chaque vol\n'
            'print("Exercice a completer : volatilite targeting poids")\n'
        ),
        (
            "Decorrelation veritable",
            '### Exercice 2 : Allocation inverse-volatilite multi-actifs\n\n'
            "La v2 alloue les poids proportionnellement a l'inverse de la volatilite (equal risk contribution). "
            "Chaque actif contribue equitablement au risque total du portefeuille.\n\n"
            '**Objectif** : Implementez `inverse_vol_allocation(volatilities, target_vol=0.10)` qui calcule les poids '
            "inverse-vol pour chaque actif, puis ajuste l'exposition totale pour cibler la vol souhaitee.\n\n"
            '**Indices** :\n'
            '- # Indice : Poids inverse-vol normalises doivent sommer a 1, puis multiplier par target_vol / vol_portefeuille.\n'
            '- # Indice : La volatilite du portefeuille est la somme ponderee des vols individuelles (approximation).',

            '# Exercice 2 : Allocation inverse-volatilite multi-actifs\n'
            '# TODO etudiant : implementer inverse_vol_allocation(volatilities, target_vol)\n'
            '# Indice : normaliser 1/vol pour sommer a 1, puis ajuster pour target_vol\n'
            '\n'
            'import numpy as np\n'
            '\n'
            'def inverse_vol_allocation(volatilities, target_vol=0.10):\n'
            '    # volatilities : {ticker: vol_annuelle}\n'
            '    # TODO etudiant : calculer poids 1/vol\n'
            '    # TODO etudiant : ajuster pour cibler target_vol\n'
            '    return None  # TODO etudiant : retourner {ticker: weight}\n'
            '\n'
            'vols = {"SPY": 0.15, "QQQ": 0.20, "IEF": 0.06, "GLD": 0.16}\n'
            'result_inv_vol = None  # TODO etudiant : tester\n'
            'print("Exercice a completer : allocation inverse-volatilite")\n'
        ),
        (
            "Le momentum aide",
            '### Exercice 3 : Combinaison vol targeting + momentum\n\n'
            "La v3 combine le vol targeting avec un filtre de momentum (6 mois > 0). Le momentum elimine les actifs "
            "en bear market que le vol targeting seul continuerait a devoir. Cette combinaison ameliore le Sharpe de 0.413 a 0.464.\n\n"
            '**Objectif** : Implementez `vol_momentum_strategy(volatilities, momentum_scores, target_vol=0.10)` qui '
            "filtre d'abord les actifs avec momentum > 0, puis alloue en inverse-vol parmi les eligibles.\n\n"
            '**Indices** :\n'
            '- # Indice : Premiere etape : ne garder que les actifs avec momentum positif.\n'
            '- # Indice : Si aucun actif ne qualifie, tout allouer en defensif (IEF).',

            '# Exercice 3 : Combinaison vol targeting + momentum\n'
            '# TODO etudiant : implementer vol_momentum_strategy\n'
            '# Indice : filtrer momentum > 0, puis allouer inverse-vol\n'
            '\n'
            'def vol_momentum_strategy(volatilities, momentum_scores, target_vol=0.10):\n'
            '    # TODO etudiant : filtrer les actifs avec momentum > 0\n'
            '    # TODO etudiant : allouer en inverse-vol parmi les eligibles\n'
            '    return None  # TODO etudiant : retourner {ticker: weight}\n'
            '\n'
            'vols = {"SPY": 0.15, "QQQ": 0.20, "IEF": 0.06, "GLD": 0.16}\n'
            'momentum = {"SPY": 0.08, "QQQ": -0.03, "IEF": 0.01, "GLD": 0.05}\n'
            'result_vol_mom = None  # TODO etudiant : tester\n'
            'print("Exercice a completer : vol targeting + momentum")\n'
        ),
    ],

    # Notebook 13: TemporalCNN
    "QC-Py-Cloud-07-TemporalCNN.ipynb": [
        (
            "OHLCV historiques",
            '### Exercice 1 : Preparation des donnees OHLCV pour un CNN\n\n'
            "Le Temporal CNN prend en entree des donnees OHLCV (Open, High, Low, Close, Volume) sur 15 jours. "
            "Les donnees doivent etre normalisees avant d'etre presentees au modele.\n\n"
            '**Objectif** : Implementez `normalize_ohlcv(ohlcv_window)` qui normalise chaque feature par le prix de cloture '
            "du premier jour de la fenetre. Verifiez que les valeurs sont dans une plage raisonnable.\n\n"
            '**Indices** :\n'
            '- # Indice : Normaliser par le close du jour 0 : feature / close[0].\n'
            '- # Indice : Le volume peut etre normalise par la moyenne du volume sur la fenetre.',

            '# Exercice 1 : Preparation des donnees OHLCV pour un CNN\n'
            '# TODO etudiant : implementer normalize_ohlcv(ohlcv_window)\n'
            '# Indice : normaliser par close[0] pour les prix, mean(volume) pour le volume\n'
            '\n'
            'import numpy as np\n'
            '\n'
            'def normalize_ohlcv(ohlcv_window):\n'
            '    # ohlcv_window : array (15, 5) [O, H, L, C, V]\n'
            '    # TODO etudiant : normaliser les prix par close[0]\n'
            '    # TODO etudiant : normaliser le volume par mean(volume)\n'
            '    return None  # TODO etudiant : retourner les donnees normalisees\n'
            '\n'
            '# Donnees simulees\n'
            'np.random.seed(42)\n'
            'close = 100 + np.cumsum(np.random.randn(15) * 0.5)\n'
            'sim_ohlcv = np.column_stack([\n'
            '    close + np.random.randn(15) * 0.2,  # Open\n'
            '    close + np.abs(np.random.randn(15)) * 0.5,  # High\n'
            '    close - np.abs(np.random.randn(15)) * 0.5,  # Low\n'
            '    close,  # Close\n'
            '    np.random.randint(1000000, 5000000, 15),  # Volume\n'
            '])\n'
            'result_norm = None  # TODO etudiant : normaliser les donnees\n'
            'print("Exercice a completer : normalisation OHLCV")\n'
        ),
        (
            "Classification 3 classes",
            '### Exercice 2 : Definition des labels de direction\n\n'
            "Le Temporal CNN predit 3 classes : hausse (UP), baisse (DOWN), stationnaire (STATIONARY). "
            "Le label depend du rendement sur les 5 jours suivants.\n\n"
            '**Objectif** : Implementez `direction_label(future_return, threshold=0.0001)` qui retourne 0 (DOWN), '
            "1 (STATIONARY) ou 2 (UP). Testez avec differents rendements et seuils.\n\n"
            '**Indices** :\n'
            '- # Indice : Si |return| < threshold, c\'est STATIONARY. Sinon UP si > 0, DOWN si < 0.\n'
            '- # Indice : Le seuil de 0.01% est tres faible, la plupart des jours seront UP ou DOWN.',

            '# Exercice 2 : Definition des labels de direction\n'
            '# TODO etudiant : implementer direction_label(future_return, threshold)\n'
            '# Indice : DOWN=0, STATIONARY=1, UP=2 selon le seuil\n'
            '\n'
            'def direction_label(future_return, threshold=0.0001):\n'
            '    # TODO etudiant : classifier le rendement\n'
            '    return None  # TODO etudiant : retourner 0, 1 ou 2\n'
            '\n'
            '# Test\n'
            'test_returns = [0.005, -0.003, 0.00005, -0.00005, 0.02, -0.01]\n'
            'result_labels = None  # TODO etudiant : calculer les labels\n'
            'print("Exercice a completer : labels de direction")\n'
        ),
        (
            "Meilleur Sharpe du catalogue",
            '### Exercice 3 : Probabilistic Sharpe Ratio (PSR)\n\n'
            "Le Temporal CNN a un PSR de 28.7, ce qui est exceptionnellement eleve. Le PSR mesure la probabilite "
            "que le Sharpe observe soit reellement superieur a un benchmark.\n\n"
            '**Objectif** : Implementez `probabilistic_sharpe_ratio(sharpe, n_observations, skew=0, kurtosis=3, benchmark=0)` '
            "en utilisant la formule de Bailey & Lopez de Prado. Testez avec les Sharpe des strategies cloud.\n\n"
            '**Indices** :\n'
            '- # Indice : PSR suit une distribution normale : z = (sharpe - benchmark) / SE, ou SE = sqrt((1 - skew*sharpe + (kurtosis-1)/4*sharpe^2) / (n-1)).\n'
            '- # Indice : Un PSR > 2.0 est considere comme statistiquement significatif.',

            '# Exercice 3 : Probabilistic Sharpe Ratio (PSR)\n'
            '# TODO etudiant : implementer probabilistic_sharpe_ratio(sharpe, n_obs)\n'
            '# Indice : PSR = Phi(z) ou z = (sharpe - benchmark) / SE\n'
            '\n'
            'import numpy as np\n'
            'from scipy import stats\n'
            '\n'
            'def probabilistic_sharpe_ratio(sharpe, n_observations, skewness=0, kurtosis=3, benchmark=0):\n'
            '    # TODO etudiant : calculer SE du Sharpe\n'
            '    # TODO etudiant : calculer z et PSR via stats.norm.cdf\n'
            '    return None  # TODO etudiant : retourner le PSR\n'
            '\n'
            '# Test avec les strategies cloud\n'
            'cloud_sharpes = {"Temporal CNN": 0.734, "Sector Rotation": 0.614, "Regime Switch": 0.622}\n'
            'result_psr = None  # TODO etudiant : calculer PSR pour chaque strategie\n'
            'print("Exercice a completer : Probabilistic Sharpe Ratio")\n'
        ),
    ],
}

# Process all remaining notebooks
base_dir = r"D:\dev\CoursIA-2\MyIA.AI.Notebooks\QuantConnect\Python"

for filename, exercises in EXERCISES.items():
    path = f"{base_dir}\\{filename}"
    print(f"\nProcessing {filename}...")
    add_exercises(path, exercises)

print("\n\nDone! All exercises added.")
