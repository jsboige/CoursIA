#!/usr/bin/env python3
"""Fix missing exercises in QC Cloud notebooks (pass 2)."""
import json, uuid

def load_nb(path):
    with open(path, 'r', encoding='utf-8') as f:
        return json.load(f)
def save_nb(path, nb):
    with open(path, 'w', encoding='utf-8') as f:
        json.dump(nb, f, ensure_ascii=False, indent=1)

def make_md(src):
    return {'cell_type':'markdown','id':uuid.uuid4().hex[:8],'metadata':{},'source':[src]}
def make_code(src):
    return {'cell_type':'code','id':uuid.uuid4().hex[:8],'metadata':{},'source':[src],'execution_count':None,'outputs':[]}

def find_idx(cells, search):
    for i,c in enumerate(cells):
        src = ''.join(c.get('source',[]))
        if search in src:
            return i
    return None

base = r"D:\dev\CoursIA-2\MyIA.AI.Notebooks\QuantConnect\Python"

# === MeanReversion: needs Ex2 ===
path = base + r"\QC-Py-Cloud-04-MeanReversion.ipynb"
nb = load_nb(path)
cells = nb['cells']
idx = find_idx(cells, "regime filter est la difference")
if idx is not None:
    md = (
        "### Exercice 2 : Filtre de regime SMA200\n\n"
        "Le regime filter est la difference entre le mean reversion dangereux (v1, MaxDD 42.4%) et le mean reversion "
        "viable (v2, MaxDD 14.6%). L'ajout d'un seul filtre -- ne pas acheter si prix < SMA200 -- divise le MaxDD par 3.\n\n"
        "**Objectif** : Implementez `regime_filter(prices, sma_period=200)` qui retourne True si le marche est en regime "
        "haussier (prix > SMA). Combinez avec le RSI pour ne generer des signaux d'achat que quand RSI < 40 ET regime = haussier.\n\n"
        "**Indices** :\n"
        "- # Indice : Prix > SMA200 = regime haussier. Prix < SMA200 = bear market.\n"
        "- # Indice : En bear market, un RSI bas ne signifie pas rebond imminent mais vente massive en cours."
    )
    code = (
        "# Exercice 2 : Filtre de regime SMA200\n"
        "# TODO etudiant : implementer regime_filter(prices, sma_period=200)\n"
        "# TODO etudiant : combiner avec RSI pour generer des signaux filtres\n"
        "# Indice : acheter seulement si RSI < 40 ET prix > SMA200\n\n"
        "def mean_reversion_signal(prices, rsi_period=14, rsi_threshold=40, sma_period=200):\n"
        "    # TODO etudiant : calculer RSI et SMA\n"
        "    # TODO etudiant : retourner ACHAT si RSI < threshold ET prix > SMA\n"
        "    return None  # TODO etudiant : retourner le signal\n\n"
        "result_regime = None  # TODO etudiant : tester le signal\n"
        'print("Exercice a completer : filtre de regime SMA200")\n'
    )
    cells.insert(idx+1, make_md(md))
    cells.insert(idx+2, make_code(code))
    print("MeanReversion: inserted Ex2")
save_nb(path, nb)

# === RL-DQN: needs Ex3 ===
path = base + r"\QC-Py-Cloud-04-RL-DQN-Trading.ipynb"
nb = load_nb(path)
cells = nb['cells']
idx = find_idx(cells, "DQN applique au trading")
if idx is not None:
    md = (
        "### Exercice 3 : Experience replay buffer\n\n"
        "Le replay buffer stocke les experiences passees (s, a, r, s', done) et echantillonne des mini-batchs "
        "pour l'entrainement. Cela casse la correlation temporelle entre les experiences successives.\n\n"
        "**Objectif** : Implementez une classe `ReplayBuffer` avec les methodes `add(experience)` et `sample(batch_size)`. "
        "Remplissez le buffer avec 100 experiences simulees et echantillonnez un batch de 32.\n\n"
        "**Indices** :\n"
        "- # Indice : Utilisez `collections.deque(maxlen=capacity)` pour un buffer a taille fixe.\n"
        "- # Indice : `random.sample(buffer, batch_size)` echantillonne sans remplacement."
    )
    code = (
        "# Exercice 3 : Experience replay buffer\n"
        "# TODO etudiant : implementer ReplayBuffer avec add() et sample()\n"
        "# Indice : utiliser deque(maxlen=capacity) et random.sample()\n\n"
        "import numpy as np\n"
        "import random\n"
        "from collections import deque\n\n"
        "class ReplayBuffer:\n"
        "    def __init__(self, capacity=5000):\n"
        "        # TODO etudiant : initialiser le deque\n"
        "        pass\n"
        "    \n"
        "    def add(self, state, action, reward, next_state, done):\n"
        "        # TODO etudiant : ajouter une experience\n"
        "        pass\n"
        "    \n"
        "    def sample(self, batch_size):\n"
        "        # TODO etudiant : echantillonner un batch\n"
        "        return None  # TODO etudiant : retourner le batch\n\n"
        "result_buffer = None  # TODO etudiant : tester le buffer\n"
        'print("Exercice a completer : experience replay buffer")\n'
    )
    cells.insert(idx+1, make_md(md))
    cells.insert(idx+2, make_code(code))
    print("RL-DQN: inserted Ex3")
save_nb(path, nb)

# === RegimeSwitching: needs Ex2+Ex3 ===
path = base + r"\QC-Py-Cloud-05-RegimeSwitching.ipynb"
nb = load_nb(path)
cells = nb['cells']
# Ex2 after resultats
idx = find_idx(cells, "Resultats QC Cloud")
if idx is not None:
    md = (
        "### Exercice 2 : Allocation adaptive par regime\n\n"
        "La v2 adapte l'allocation au regime detecte : en Bull, momentum parmi SPY/QQQ ; "
        "en Bear, 50% IEF + 50% GLD ; en Sideways, 30% SPY + 35% IEF + 35% GLD.\n\n"
        "**Objectif** : Implementez `adaptive_allocation(regime, momentum_scores)` qui retourne un dictionnaire de poids.\n\n"
        "**Indices** :\n"
        "- # Indice : En Bull, donner 70% au meilleur momentum et 30% au second.\n"
        "- # Indice : En Bear, splitter equitablement entre IEF et GLD."
    )
    code = (
        "# Exercice 2 : Allocation adaptive par regime\n"
        "# TODO etudiant : implementer adaptive_allocation(regime, momentum_scores)\n"
        "# Indice : BULL -> top momentum 70/30, BEAR -> IEF/GLD 50/50\n\n"
        "def adaptive_allocation(regime, momentum_scores=None):\n"
        "    # momentum_scores : {ticker: score}\n"
        "    # TODO etudiant : implementer la logique par regime\n"
        "    return None  # TODO etudiant : retourner {ticker: weight}\n\n"
        'scores = {"SPY": 0.08, "QQQ": 0.15, "IEF": 0.02, "GLD": 0.04}\n'
        "result_adaptive = None  # TODO etudiant : tester pour chaque regime\n"
        'print("Exercice a completer : allocation adaptive")\n'
    )
    cells.insert(idx+1, make_md(md))
    cells.insert(idx+2, make_code(code))
    print("RegimeSwitching: inserted Ex2")

    # After inserting 2 cells, indices shifted by 2
    idx2 = find_idx(cells, "detection de regime est l")
    if idx2 is not None:
        md3 = (
            "### Exercice 3 : Comparaison des strategies par ratio de Sharpe\n\n"
            "Le regime switching v2 atteint le meilleur Sharpe de la serie cloud (0.622). "
            "Pour comparer objectivement les strategies, le Sharpe ratio est la metrique standard.\n\n"
            "**Objectif** : Implementez `sharpe_ratio(returns, risk_free_rate=0.02)` qui calcule le Sharpe annualise.\n\n"
            "**Indices** :\n"
            "- # Indice : Sharpe = (rendement_moyen - taux_sans_risque) / ecart_type_rendements * sqrt(252).\n"
            "- # Indice : Annualiser en multipliant par sqrt(252) pour des rendements quotidiens."
        )
        code3 = (
            "# Exercice 3 : Comparaison des strategies par ratio de Sharpe\n"
            "# TODO etudiant : implementer sharpe_ratio(returns, rf=0.02) -> float\n"
            "# Indice : Sharpe = (mean - rf) / std * sqrt(252)\n\n"
            "import numpy as np\n\n"
            "def sharpe_ratio(returns, risk_free_rate=0.02):\n"
            "    # returns : array de rendements quotidiens\n"
            "    # TODO etudiant : calculer le Sharpe annualise\n"
            "    return None  # TODO etudiant : retourner le Sharpe\n\n"
            "np.random.seed(42)\n"
            "strategies = {\n"
            '    "Regime Switch": np.random.normal(0.0005, 0.008, 252),\n'
            '    "Risk Parity": np.random.normal(0.0003, 0.006, 252),\n'
            '    "Mean Reversion": np.random.normal(0.0002, 0.005, 252),\n'
            "}\n"
            "result_sharpe = None  # TODO etudiant : calculer et comparer les Sharpe\n"
            'print("Exercice a completer : ratio de Sharpe")\n'
        )
        cells.insert(idx2+1, make_md(md3))
        cells.insert(idx2+2, make_code(code3))
        print("RegimeSwitching: inserted Ex3")
save_nb(path, nb)

# === PCA-StatArb: needs Ex1 + Ex3 ===
path = base + r"\QC-Py-Cloud-06-PCA-StatArb.ipynb"
nb = load_nb(path)
cells = nb['cells']
idx = find_idx(cells, "PCA Statistical Arbitrage")
if idx is not None:
    md = (
        "### Exercice 1 : Application de la PCA sur des series de prix\n\n"
        "La PCA extrait les facteurs communs a partir de la matrice des log-prix. "
        "Les 3 premieres composantes expliquent plus de 90% de la variance.\n\n"
        "**Objectif** : Simulez 10 series de prix correlees (avec un facteur commun). "
        "Appliquez PCA et affichez la variance expliquee par chaque composante.\n\n"
        "**Indices** :\n"
        "- # Indice : Utilisez sklearn.decomposition.PCA sur les log-prix centres.\n"
        "- # Indice : pca.explained_variance_ratio_ donne le pourcentage de variance par composante."
    )
    code = (
        "# Exercice 1 : Application de la PCA sur des series de prix\n"
        "# TODO etudiant : simuler 10 series correlees et appliquer PCA\n"
        "# Indice : sklearn.decomposition.PCA sur log-prix centres\n\n"
        "import numpy as np\n\n"
        "def simulate_correlated_prices(n_assets=10, n_days=200, seed=42):\n"
        "    # TODO etudiant : generer un facteur commun + bruit individuel\n"
        "    return None  # TODO etudiant : retourner la matrice de prix (n_days x n_assets)\n\n"
        "result_pca = None  # TODO etudiant : appliquer PCA et afficher variance expliquee\n"
        'print("Exercice a completer : PCA sur series de prix")\n'
    )
    cells.insert(idx+1, make_md(md))
    cells.insert(idx+2, make_code(code))
    print("PCA-StatArb: inserted Ex1")

# Ex3 after lecons (search again after insertion shifted indices)
idx = find_idx(cells, "Lecons principales")
if idx is not None:
    md3 = (
        "### Exercice 3 : Profit factor et win rate\n\n"
        "La strategie PCA stat-arb a un win rate de 48% mais reste profitable grace a un profit-loss ratio de 1.30. "
        "Le profit factor (somme des gains / somme des pertes) est une metrique complementaire.\n\n"
        "**Objectif** : Simulez 200 trades avec un win rate de 48% et un gain moyen de 0.80% vs perte moyenne de 0.61%. "
        "Calculez le profit factor, le rendement cumule et le nombre de trades gagnants vs perdants.\n\n"
        "**Indices** :\n"
        "- # Indice : Profit factor = total_gains / total_pertes. Un PF > 1 est profitable.\n"
        "- # Indice : Le rendement cumule = produit des (1 + r_i) pour chaque trade."
    )
    code3 = (
        "# Exercice 3 : Profit factor et win rate\n"
        "# TODO etudiant : simuler 200 trades et calculer profit factor\n"
        "# Indice : PF = sum(gains) / sum(pertes), un PF > 1 est profitable\n\n"
        "import numpy as np\n\n"
        "def simulate_trades(n_trades=200, win_rate=0.48, avg_win=0.008, avg_loss=0.0061, seed=42):\n"
        "    # TODO etudiant : generer les trades\n"
        "    # TODO etudiant : calculer PF, rendement cumule, win/loss counts\n"
        "    return None  # TODO etudiant : retourner les metriques\n\n"
        "result_pf = None  # TODO etudiant : lancer la simulation\n"
        'print("Exercice a completer : profit factor et win rate")\n'
    )
    cells.insert(idx+1, make_md(md3))
    cells.insert(idx+2, make_code(code3))
    print("PCA-StatArb: inserted Ex3")
save_nb(path, nb)

# === VolTargeting: needs Ex2+Ex3 ===
path = base + r"\QC-Py-Cloud-06-VolTargeting.ipynb"
nb = load_nb(path)
cells = nb['cells']
idx = find_idx(cells, "Resultats QC Cloud")
if idx is not None:
    md = (
        "### Exercice 2 : Allocation inverse-volatilite multi-actifs\n\n"
        "La v2 alloue les poids proportionnellement a l'inverse de la volatilite (equal risk contribution). "
        "Chaque actif contribue equitablement au risque total du portefeuille.\n\n"
        "**Objectif** : Implementez `inverse_vol_allocation(volatilities, target_vol=0.10)` qui calcule les poids "
        "inverse-vol pour chaque actif, puis ajuste l'exposition totale pour cibler la vol souhaitee.\n\n"
        "**Indices** :\n"
        "- # Indice : Poids inverse-vol normalises doivent sommer a 1, puis multiplier par target_vol / vol_portefeuille.\n"
        "- # Indice : La volatilite du portefeuille est la somme ponderee des vols individuelles (approximation)."
    )
    code = (
        "# Exercice 2 : Allocation inverse-volatilite multi-actifs\n"
        "# TODO etudiant : implementer inverse_vol_allocation(volatilities, target_vol)\n"
        "# Indice : normaliser 1/vol pour sommer a 1, puis ajuster pour target_vol\n\n"
        "import numpy as np\n\n"
        "def inverse_vol_allocation(volatilities, target_vol=0.10):\n"
        "    # volatilities : {ticker: vol_annuelle}\n"
        "    # TODO etudiant : calculer poids 1/vol\n"
        "    # TODO etudiant : ajuster pour cibler target_vol\n"
        "    return None  # TODO etudiant : retourner {ticker: weight}\n\n"
        'vols = {"SPY": 0.15, "QQQ": 0.20, "IEF": 0.06, "GLD": 0.16}\n'
        "result_inv_vol = None  # TODO etudiant : tester\n"
        'print("Exercice a completer : allocation inverse-volatilite")\n'
    )
    cells.insert(idx+1, make_md(md))
    cells.insert(idx+2, make_code(code))
    print("VolTargeting: inserted Ex2")

idx2 = find_idx(cells, "vol targeting ameliore")
if idx2 is not None:
    md3 = (
        "### Exercice 3 : Combinaison vol targeting + momentum\n\n"
        "La v3 combine le vol targeting avec un filtre de momentum (6 mois > 0). "
        "Le momentum elimine les actifs en bear market que le vol targeting seul continuerait a devoir.\n\n"
        "**Objectif** : Implementez `vol_momentum_strategy(volatilities, momentum_scores, target_vol=0.10)` qui "
        "filtre d'abord les actifs avec momentum > 0, puis alloue en inverse-vol parmi les eligibles.\n\n"
        "**Indices** :\n"
        "- # Indice : Premiere etape : ne garder que les actifs avec momentum positif.\n"
        "- # Indice : Si aucun actif ne qualifie, tout allouer en defensif (IEF)."
    )
    code3 = (
        "# Exercice 3 : Combinaison vol targeting + momentum\n"
        "# TODO etudiant : implementer vol_momentum_strategy\n"
        "# Indice : filtrer momentum > 0, puis allouer inverse-vol\n\n"
        "def vol_momentum_strategy(volatilities, momentum_scores, target_vol=0.10):\n"
        "    # TODO etudiant : filtrer les actifs avec momentum > 0\n"
        "    # TODO etudiant : allouer en inverse-vol parmi les eligibles\n"
        "    return None  # TODO etudiant : retourner {ticker: weight}\n\n"
        'vols = {"SPY": 0.15, "QQQ": 0.20, "IEF": 0.06, "GLD": 0.16}\n'
        'momentum = {"SPY": 0.08, "QQQ": -0.03, "IEF": 0.01, "GLD": 0.05}\n'
        "result_vol_mom = None  # TODO etudiant : tester\n"
        'print("Exercice a completer : vol targeting + momentum")\n'
    )
    cells.insert(idx2+1, make_md(md3))
    cells.insert(idx2+2, make_code(code3))
    print("VolTargeting: inserted Ex3")
save_nb(path, nb)

# === TemporalCNN: needs Ex2+Ex3 ===
path = base + r"\QC-Py-Cloud-07-TemporalCNN.ipynb"
nb = load_nb(path)
cells = nb['cells']
idx = find_idx(cells, "Decisions de conception")
if idx is not None:
    md = (
        "### Exercice 2 : Definition des labels de direction\n\n"
        "Le Temporal CNN predit 3 classes : hausse (UP), baisse (DOWN), stationnaire (STATIONARY). "
        "Le label depend du rendement sur les 5 jours suivants.\n\n"
        "**Objectif** : Implementez `direction_label(future_return, threshold=0.0001)` qui retourne 0 (DOWN), "
        "1 (STATIONARY) ou 2 (UP). Testez avec differents rendements et seuils.\n\n"
        "**Indices** :\n"
        "- # Indice : Si |return| < threshold, c'est STATIONARY. Sinon UP si > 0, DOWN si < 0.\n"
        "- # Indice : Le seuil de 0.01% est tres faible, la plupart des jours seront UP ou DOWN."
    )
    code = (
        "# Exercice 2 : Definition des labels de direction\n"
        "# TODO etudiant : implementer direction_label(future_return, threshold)\n"
        "# Indice : DOWN=0, STATIONARY=1, UP=2 selon le seuil\n\n"
        "def direction_label(future_return, threshold=0.0001):\n"
        "    # TODO etudiant : classifier le rendement\n"
        "    return None  # TODO etudiant : retourner 0, 1 ou 2\n\n"
        "test_returns = [0.005, -0.003, 0.00005, -0.00005, 0.02, -0.01]\n"
        "result_labels = None  # TODO etudiant : calculer les labels\n"
        'print("Exercice a completer : labels de direction")\n'
    )
    cells.insert(idx+1, make_md(md))
    cells.insert(idx+2, make_code(code))
    print("TemporalCNN: inserted Ex2")

idx2 = find_idx(cells, "Lecons principales")
if idx2 is not None:
    md3 = (
        "### Exercice 3 : Probabilistic Sharpe Ratio (PSR)\n\n"
        "Le Temporal CNN a un PSR de 28.7, ce qui est exceptionnellement eleve. "
        "Le PSR mesure la probabilite que le Sharpe observe soit reellement superieur a un benchmark.\n\n"
        "**Objectif** : Implementez `probabilistic_sharpe_ratio(sharpe, n_observations)` en utilisant la formule "
        "de Bailey & Lopez de Prado. Testez avec les Sharpe des strategies cloud.\n\n"
        "**Indices** :\n"
        "- # Indice : PSR suit une distribution normale : z = (sharpe - benchmark) / SE.\n"
        "- # Indice : Un PSR > 2.0 est considere comme statistiquement significatif."
    )
    code3 = (
        "# Exercice 3 : Probabilistic Sharpe Ratio (PSR)\n"
        "# TODO etudiant : implementer probabilistic_sharpe_ratio(sharpe, n_obs)\n"
        "# Indice : PSR = Phi(z) ou z = (sharpe - benchmark) / SE\n\n"
        "import numpy as np\n"
        "from scipy import stats\n\n"
        "def probabilistic_sharpe_ratio(sharpe, n_observations, skewness=0, kurtosis=3, benchmark=0):\n"
        "    # TODO etudiant : calculer SE du Sharpe\n"
        "    # TODO etudiant : calculer z et PSR via stats.norm.cdf\n"
        "    return None  # TODO etudiant : retourner le PSR\n\n"
        'cloud_sharpes = {"Temporal CNN": 0.734, "Sector Rotation": 0.614, "Regime Switch": 0.622}\n'
        "result_psr = None  # TODO etudiant : calculer PSR pour chaque strategie\n"
        'print("Exercice a completer : Probabilistic Sharpe Ratio")\n'
    )
    cells.insert(idx2+1, make_md(md3))
    cells.insert(idx2+2, make_code(code3))
    print("TemporalCNN: inserted Ex3")
save_nb(path, nb)

print("\nAll remaining exercises inserted successfully.")
