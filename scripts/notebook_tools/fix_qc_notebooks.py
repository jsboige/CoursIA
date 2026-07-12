"""Fix QC notebooks with error cells - add guards for partial data."""
import json
import sys
import os

def fix_ml_xgboost(nb_path):
    """Fix ML-XGBoost/quantbook.ipynb - filter tickers to available + guard all downstream."""
    with open(nb_path, 'r', encoding='utf-8') as f:
        nb = json.load(f)

    cells = nb['cells']
    fixed = 0

    for i, cell in enumerate(cells):
        if cell.get('cell_type') != 'code':
            continue
        src = ''.join(cell['source'])

        # Cell 3: data load - add ticker filtering
        if 'Top 15 actions tech' in src and 'closes = history' in src:
            new_src = src.replace(
                'print(f"Données: {closes.shape[0]} jours, {closes.shape[1]} actifs")\ncloses.head()',
                '# Filter tickers to only those with actual data available\n'
                'symbol_to_ticker = {str(v): k for k, v in symbols.items()}\n'
                'available_tickers = [symbol_to_ticker[str(c)] for c in closes.columns if str(c) in symbol_to_ticker]\n'
                'tickers = available_tickers\n\n'
                'if len(tickers) < 2:\n'
                '    print(f"WARNING: Only {len(tickers)} ticker(s) available: {tickers}")\n'
                '    print("Multi-ticker analysis requires at least 2 tickers with data.")\n'
                '    print("All downstream analysis cells will be skipped.")\n'
                '    closes = None\n'
                '    volumes = None\n'
                '    highs = None\n'
                '    lows = None\n'
                'else:\n'
                '    print(f"Available tickers ({len(tickers)}): {tickers}")\n'
                '    print(f"Données: {closes.shape[0]} jours, {closes.shape[1]} actifs")\n'
                '    closes.head()'
            )
            if new_src != src:
                _set_source(cell, new_src)
                fixed += 1
                print(f'  Fixed cell {i}: data load + ticker filtering')

        # Cell 5: feature engineering - guard on closes=None
        elif 'def calculate_xgb_features' in src and 'features = calculate_xgb_features' in src:
            old_call = '# Calculer les features\nfeatures = calculate_xgb_features(closes, volumes, highs, lows)'
            new_call = ('if closes is None:\n'
                        '    print("Data not available - skipping feature engineering.")\n'
                        '    features = None\n'
                        'else:\n'
                        '    # Calculer les features\n'
                        '    features = calculate_xgb_features(closes, volumes, highs, lows)')
            if old_call in src:
                new_src = src.replace(old_call, new_call)
                _set_source(cell, new_src)
                fixed += 1
                print(f'  Fixed cell {i}: features guard')

        # Cell 7: prepare_training_data - guard on None
        elif 'def prepare_training_data' in src and 'X, y = prepare_training_data' in src:
            old_call = '# Préparer les données\nX, y = prepare_training_data(features, closes)'
            new_call = ('if features is None or closes is None:\n'
                        '    print("Data not available - skipping training data preparation.")\n'
                        '    X, y = None, None\n'
                        'else:\n'
                        '    # Préparer les données\n'
                        '    X, y = prepare_training_data(features, closes)')
            if old_call in src:
                new_src = src.replace(old_call, new_call)
                # Also guard the prints
                old_print = ('print(f"X shape: {X.shape}")\n'
                             'print(f"y shape: {y.shape}")\n'
                             'print(f"\\nDistribution des cibles:")\n'
                             'print(f"Moyenne: {y.mean():.4f}")\n'
                             'print(f"Std: {y.std():.4f}")\n'
                             'print(f"Min: {y.min():.4f}, Max: {y.max():.4f}")')
                new_print = ('if X is not None:\n'
                             '    print(f"X shape: {X.shape}")\n'
                             '    print(f"y shape: {y.shape}")\n'
                             '    print(f"\\nDistribution des cibles:")\n'
                             '    print(f"Moyenne: {y.mean():.4f}")\n'
                             '    print(f"Std: {y.std():.4f}")\n'
                             '    print(f"Min: {y.min():.4f}, Max: {y.max():.4f}")\n'
                             'else:\n'
                             '    print("Training data not available.")')
                new_src = new_src.replace(old_print, new_print)
                _set_source(cell, new_src)
                fixed += 1
                print(f'  Fixed cell {i}: training data guard')

        # Cell 9: train XGBoost - guard on X=None
        elif 'train_test_split' in src and 'GradientBoostingRegressor' in src and 'X, y, test_size' in src:
            indent_body = _indent(src, 4)
            new_src = ('from sklearn.model_selection import train_test_split\n'
                       'from sklearn.preprocessing import StandardScaler\n'
                       'from sklearn.ensemble import GradientBoostingRegressor\n'
                       'from sklearn.metrics import mean_squared_error, mean_absolute_error, r2_score\n\n'
                       'if X is None:\n'
                       '    print("Training data not available - skipping XGBoost training.")\n'
                       'else:\n'
                       '    # Split train/test\n'
                       '    X_train, X_test, y_train, y_test = train_test_split(\n'
                       '        X, y, test_size=0.2, random_state=42\n'
                       '    )\n\n'
                       '    # Normaliser\n'
                       '    scaler = StandardScaler()\n'
                       '    X_train_scaled = scaler.fit_transform(X_train)\n'
                       '    X_test_scaled = scaler.transform(X_test)\n\n'
                       '    # Entraîner GradientBoosting\n'
                       '    model = GradientBoostingRegressor(\n'
                       '        n_estimators=100,\n'
                       '        max_depth=5,\n'
                       '        learning_rate=0.05,\n'
                       '        subsample=0.8,\n'
                       '        random_state=42\n'
                       '    )\n'
                       '    model.fit(X_train_scaled, y_train)\n\n'
                       '    # Prédictions\n'
                       '    train_pred = model.predict(X_train_scaled)\n'
                       '    test_pred = model.predict(X_test_scaled)\n\n'
                       '    # Métriques\n'
                       '    train_mse = mean_squared_error(y_train, train_pred)\n'
                       '    test_mse = mean_squared_error(y_test, test_pred)\n'
                       '    train_r2 = r2_score(y_train, train_pred)\n'
                       '    test_r2 = r2_score(y_test, test_pred)\n\n'
                       '    print(f"Train MSE: {train_mse:.6f}, R2: {train_r2:.3f}")\n'
                       '    print(f"Test MSE: {test_mse:.6f}, R2: {test_r2:.3f}")')
            _set_source(cell, new_src)
            fixed += 1
            print(f'  Fixed cell {i}: XGBoost training guard')

        # Cell 11: feature importance - guard
        elif 'feature_importances_' in src and 'Top 20' in src:
            new_src = ('if "X" not in dir() or X is None or "model" not in dir():\n'
                       '    print("Model not trained - skipping feature importance analysis.")\n'
                       'else:\n'
                       '    # Extraire l\'importance des features\n'
                       '    importance = pd.DataFrame({\n'
                       '        \'feature\': X.columns,\n'
                       '        \'importance\': model.feature_importances_\n'
                       '    }).sort_values(\'importance\', ascending=False)\n\n'
                       '    # Top 20 features\n'
                       '    top_features = importance.head(20)\n\n'
                       '    print("Top 20 Features les plus importantes:")\n'
                       '    print(top_features)\n\n'
                       '    # Visualisation\n'
                       '    import matplotlib.pyplot as plt\n\n'
                       '    plt.figure(figsize=(12, 8))\n'
                       '    plt.barh(top_features[\'feature\'][::-1], top_features[\'importance\'][::-1])\n'
                       '    plt.xlabel(\'Importance\')\n'
                       '    plt.title(\'Feature Importance - XGBoost\')\n'
                       '    plt.tight_layout()\n'
                       '    plt.show()')
            _set_source(cell, new_src)
            fixed += 1
            print(f'  Fixed cell {i}: feature importance guard')

        # Cell 13: residuals - guard
        elif 'residuals = y_test' in src:
            new_src = ('if "y_test" not in dir():\n'
                       '    print("Test data not available - skipping residual analysis.")\n'
                       'else:\n'
                       '    # Analyser les résidus\n'
                       '    residuals = y_test - test_pred\n\n'
                       '    fig, axes = plt.subplots(1, 2, figsize=(14, 5))\n\n'
                       '    # Scatter plot\n'
                       '    axes[0].scatter(y_test, test_pred, alpha=0.5)\n'
                       '    axes[0].plot([y_test.min(), y_test.max()], [y_test.min(), y_test.max()], \'r--\')\n'
                       '    axes[0].set_xlabel(\'Réel\')\n'
                       '    axes[0].set_ylabel(\'Prédit\')\n'
                       '    axes[0].set_title(\'Prédictions vs Réel\')\n\n'
                       '    # Residuals plot\n'
                       '    axes[1].scatter(test_pred, residuals, alpha=0.5)\n'
                       '    axes[1].axhline(y=0, color=\'r\', linestyle=\'--\')\n'
                       '    axes[1].set_xlabel(\'Prédit\')\n'
                       '    axes[1].set_ylabel(\'Résidu\')\n'
                       '    axes[1].set_title(\'Résidus\')\n\n'
                       '    plt.tight_layout()\n'
                       '    plt.show()\n\n'
                       '    print(f"\\nStatistiques des résidus:")\n'
                       '    print(f"Moyenne: {residuals.mean():.6f}")\n'
                       '    print(f"Std: {residuals.std():.6f}")')
            _set_source(cell, new_src)
            fixed += 1
            print(f'  Fixed cell {i}: residuals guard')

        # Cell 15: hyperparameter tuning - guard
        elif 'GridSearchCV' in src and 'grid_search.fit(X_train_scaled' in src:
            new_src = ('from sklearn.model_selection import GridSearchCV\n\n'
                       'if "X_train_scaled" not in dir():\n'
                       '    print("Training data not available - skipping hyperparameter tuning.")\n'
                       'else:\n'
                       '    # Définir la grille de paramètres\n'
                       '    param_grid = {\n'
                       '        \'n_estimators\': [50, 100, 200],\n'
                       '        \'max_depth\': [3, 5, 7],\n'
                       '        \'learning_rate\': [0.01, 0.05, 0.1],\n'
                       '        \'subsample\': [0.8, 1.0]\n'
                       '    }\n\n'
                       '    # Grid search\n'
                       '    base_model = GradientBoostingRegressor(random_state=42)\n'
                       '    grid_search = GridSearchCV(\n'
                       '        base_model,\n'
                       '        param_grid,\n'
                       '        cv=3,\n'
                       '        scoring=\'neg_mean_squared_error\',\n'
                       '        n_jobs=-1,\n'
                       '        verbose=1\n'
                       '    )\n\n'
                       '    print("Recherche des meilleurs hyperparamètres...")\n'
                       '    grid_search.fit(X_train_scaled, y_train)\n\n'
                       '    print(f"\\nMeilleurs paramètres: {grid_search.best_params_}")\n'
                       '    print(f"Meilleur score MSE: {-grid_search.best_score_:.6f}")\n\n'
                       '    # Modèle optimisé\n'
                       '    best_model = grid_search.best_estimator_\n'
                       '    best_pred = best_model.predict(X_test_scaled)\n'
                       '    best_mse = mean_squared_error(y_test, best_pred)\n\n'
                       '    print(f"Test MSE (modèle optimisé): {best_mse:.6f}")')
            _set_source(cell, new_src)
            fixed += 1
            print(f'  Fixed cell {i}: hyperparameter tuning guard')

        # Cell 17: walk-forward - guard
        elif 'walk_forward_validation' in src and 'wf_pred, wf_actual' in src:
            old_call = '# Exécuter walk-forward\nwf_pred, wf_actual = walk_forward_validation(features, closes)'
            new_call = ('if features is None or closes is None:\n'
                        '    print("Data not available - skipping walk-forward validation.")\n'
                        '    wf_pred, wf_actual = None, None\n'
                        'else:\n'
                        '    # Exécuter walk-forward\n'
                        '    wf_pred, wf_actual = walk_forward_validation(features, closes)')
            if old_call in src:
                new_src = src.replace(old_call, new_call)
                old_print = ('wf_mse = mean_squared_error(wf_actual, wf_pred)\n'
                             'wf_r2 = r2_score(wf_actual, wf_pred)\n\n'
                             'print(f"Walk-Forward Results:")\n'
                             'print(f"MSE: {wf_mse:.6f}")\n'
                             'print(f"R²: {wf_r2:.3f}")')
                new_print = ('if wf_pred is not None:\n'
                             '    wf_mse = mean_squared_error(wf_actual, wf_pred)\n'
                             '    wf_r2 = r2_score(wf_actual, wf_pred)\n'
                             '    print(f"Walk-Forward Results:")\n'
                             '    print(f"MSE: {wf_mse:.6f}")\n'
                             '    print(f"R2: {wf_r2:.3f}")\n'
                             'else:\n'
                             '    print("Walk-forward validation skipped.")')
                new_src = new_src.replace(old_print, new_print)
                _set_source(cell, new_src)
                fixed += 1
                print(f'  Fixed cell {i}: walk-forward guard')

        # Cell 19: backtest strategy - guard
        elif 'backtest_xgboost_strategy' in src and 'bt_results = backtest' in src:
            new_src = src.replace(
                '# Exécuter backtest\nbt_results = backtest_xgboost_strategy(closes, volumes, highs, lows)\n\nprint(f"\\nBacktest Results:")\nprint(f"Return: {bt_results[\'return\']:.2%}")',
                'if closes is None:\n'
                '    print("Data not available - skipping backtest.")\n'
                '    bt_results = None\n'
                'else:\n'
                '    # Exécuter backtest\n'
                '    bt_results = backtest_xgboost_strategy(closes, volumes, highs, lows)\n\n'
                '    print(f"\\nBacktest Results:")\n'
                '    print(f"Return: {bt_results[\'return\']:.2%}")'
            )
            if new_src != src:
                _set_source(cell, new_src)
                fixed += 1
                print(f'  Fixed cell {i}: backtest guard')

        # Cell 21: model comparison - guard
        elif 'RandomForestRegressor' in src and 'model.fit(X_train_scaled' in src:
            new_src = ('# Comparaison avec d\'autres modèles\n'
                       'from sklearn.linear_model import Ridge\n'
                       'from sklearn.ensemble import RandomForestRegressor\n\n'
                       'if "X_train_scaled" not in dir():\n'
                       '    print("Training data not available - skipping model comparison.")\n'
                       'else:\n'
                       '    models = {\n'
                       '        \'Ridge\': Ridge(alpha=1.0),\n'
                       '        \'RandomForest\': RandomForestRegressor(n_estimators=100, max_depth=10, random_state=42),\n'
                       '        \'GradientBoosting\': GradientBoostingRegressor(n_estimators=100, max_depth=5, learning_rate=0.05, random_state=42)\n'
                       '    }\n\n'
                       '    results = []\n'
                       '    for name, model in models.items():\n'
                       '        model.fit(X_train_scaled, y_train)\n'
                       '        pred = model.predict(X_test_scaled)\n'
                       '        mse = mean_squared_error(y_test, pred)\n'
                       '        r2 = r2_score(y_test, pred)\n\n'
                       '        results.append({\n'
                       '            \'Model\': name,\n'
                       '            \'MSE\': mse,\n'
                       '            \'R2\': r2\n'
                       '        })\n\n'
                       '    results_df = pd.DataFrame(results)\n'
                       '    print("Comparaison des modèles:")\n'
                       '    print(results_df.round(6))\n\n'
                       '    # Visualisation\n'
                       '    results_df.set_index(\'Model\').plot(kind=\'bar\', subplots=True, figsize=(12, 6))\n'
                       '    plt.tight_layout()\n'
                       '    plt.show()')
            _set_source(cell, new_src)
            fixed += 1
            print(f'  Fixed cell {i}: model comparison guard')

    with open(nb_path, 'w', encoding='utf-8') as f:
        json.dump(nb, f, indent=1, ensure_ascii=False)
    print(f'  Saved {nb_path} ({fixed} cells fixed)')
    return fixed


def _set_source(cell, new_src):
    """Set cell source from a string, splitting into lines with newlines."""
    lines = new_src.split('\n')
    cell['source'] = [line + '\n' for line in lines[:-1]] + [lines[-1]]
    cell['outputs'] = []
    cell['execution_count'] = None


def _indent(src, spaces):
    """Indent all lines of src by spaces."""
    pad = ' ' * spaces
    return '\n'.join(pad + line if line.strip() else line for line in src.split('\n'))


def fix_rl_portfolio(nb_path):
    """Fix RL-Portfolio/quantbook.ipynb - guard for partial asset data (only SPY available)."""
    with open(nb_path, 'r', encoding='utf-8') as f:
        nb = json.load(f)

    cells = nb['cells']
    fixed = 0

    for i, cell in enumerate(cells):
        if cell.get('cell_type') != 'code':
            continue
        src = ''.join(cell['source'])

        # cell-4: data pivot - filter assets to available + guard performance loop
        if 'closes = history' in src and 'symbol_to_ticker' in src and 'Performance totale' in src:
            new_src = src.replace(
                "closes = closes.dropna()\n\n"
                "print(f\"Période: {closes.index[0].date()} à {closes.index[-1].date()}\")\n"
                "print(f\"Données: {len(closes)} jours de trading\")\n"
                'print(f"\\nPerformance totale:")\n'
                'for asset in assets:\n'
                '    ret = (closes[asset].iloc[-1] / closes[asset].iloc[0] - 1) * 100\n'
                '    print(f"  {asset}: {ret:+.1f}%")',
                "# Filter assets to only those with available data\n"
                "available_assets = [a for a in assets if a in closes.columns]\n"
                "assets = available_assets\n\n"
                "if len(assets) < 3:\n"
                '    print(f"WARNING: Only {len(assets)} asset(s) available: {assets}")\n'
                '    print("RL multi-asset strategy requires at least 3 assets (SPY, TLT, GLD).")\n'
                '    print("All RL-dependent analysis cells will be skipped.")\n'
                "    closes = None\n"
                "else:\n"
                '    closes = closes.dropna()\n\n'
                '    print(f"Période: {closes.index[0].date()} à {closes.index[-1].date()}")\n'
                '    print(f"Données: {len(closes)} jours de trading")\n'
                '    print(f"\\nAvailable assets ({len(assets)}): {assets}")\n'
                '    print(f"\\nPerformance totale:")\n'
                '    for asset in assets:\n'
                '        ret = (closes[asset].iloc[-1] / closes[asset].iloc[0] - 1) * 100\n'
                '        print(f"  {asset}: {ret:+.1f}%")'
            )
            if new_src != src:
                _set_source(cell, new_src)
                fixed += 1
                print(f'  Fixed cell {i}: data pivot + asset filtering')

        # cell-6: RLEnvironment - guard instantiation
        elif 'class RLEnvironment' in src and 'env = RLEnvironment(closes)' in src:
            old_create = '# Créer l\'environnement\nenv = RLEnvironment(closes)\n\n# Test\nstate = env.reset()'
            new_create = ('if closes is None:\n'
                          '    print("Data not available - skipping RL environment setup.")\n'
                          '    env = None\n'
                          'else:\n'
                          '    # Créer l\'environnement\n'
                          '    env = RLEnvironment(closes)\n\n'
                          '    # Test\n'
                          '    state = env.reset()\n'
                          '    print(f"État initial: {state}")\n'
                          '    next_state, reward, done = env.step(0)  # Action: investir dans SPY\n'
                          '    print(f"Action 0 (SPY) -> Reward: {reward:.4f}")')
            if old_create in src:
                new_src = src.replace(old_create, new_create)
                _set_source(cell, new_src)
                fixed += 1
                print(f'  Fixed cell {i}: RLEnvironment guard')

        # cell-11: train_agent - guard
        elif 'def train_agent' in src and 'rewards, epsilons = train_agent' in src:
            old_call = '# Entraîner l\'agent\nrewards, epsilons = train_agent(env, agent, n_episodes=50)'
            new_call = ('if env is None:\n'
                        '    print("RL environment not available - skipping agent training.")\n'
                        '    rewards, epsilons = [], []\n'
                        'else:\n'
                        '    # Entraîner l\'agent\n'
                        '    rewards, epsilons = train_agent(env, agent, n_episodes=50)')
            if old_call in src:
                new_src = src.replace(old_call, new_call)
                old_print = ('print(f"\\nEntraînement terminé.")\n'
                             'print(f"Reward moyen (10 derniers épisodes): {np.mean(rewards[-10:]):.4f}")\n'
                             'print(f"Epsilon final: {agent.epsilon:.3f}")')
                new_print = ('if len(rewards) > 0:\n'
                             '    print(f"\\nEntraînement terminé.")\n'
                             '    print(f"Reward moyen (10 derniers épisodes): {np.mean(rewards[-10:]):.4f}")\n'
                             '    print(f"Epsilon final: {agent.epsilon:.3f}")\n'
                             'else:\n'
                             '    print("Agent training skipped.")')
                new_src = new_src.replace(old_print, new_print)
                _set_source(cell, new_src)
                fixed += 1
                print(f'  Fixed cell {i}: train_agent guard')

        # cell-14: backtest_rl_policy - guard
        elif 'def backtest_rl_policy' in src and 'rl_values, rl_actions = backtest_rl_policy' in src:
            old_call = '# Backtest\nrl_values, rl_actions = backtest_rl_policy(env, agent)'
            new_call = ('if env is None:\n'
                        '    print("RL environment not available - skipping backtest.")\n'
                        '    rl_values, rl_actions = None, None\n'
                        'else:\n'
                        '    # Backtest\n'
                        '    rl_values, rl_actions = backtest_rl_policy(env, agent)')
            if old_call in src:
                new_src = src.replace(old_call, new_call)
                old_metrics = ('# Métriques\n'
                               'returns = rl_values.pct_change().dropna()\n'
                               'cagr = (rl_values.iloc[-1] ** (252/len(rl_values))) - 1\n'
                               'vol = returns.std() * np.sqrt(252)\n'
                               'sharpe = (cagr - 0.03) / vol\n'
                               'max_dd = (rl_values / rl_values.cummax() - 1).min()\n\n'
                               'print("=== Performance RL Policy ===")\n'
                               'print(f"Sharpe: {sharpe:.3f}")\n'
                               'print(f"CAGR:   {cagr:.1%}")\n'
                               'print(f"Max DD: {max_dd:.1%}")\n'
                               'print(f"Vol:    {vol:.1%}")')
                new_metrics = ('if rl_values is not None:\n'
                               '    # Métriques\n'
                               '    returns = rl_values.pct_change().dropna()\n'
                               '    cagr = (rl_values.iloc[-1] ** (252/len(rl_values))) - 1\n'
                               '    vol = returns.std() * np.sqrt(252)\n'
                               '    sharpe = (cagr - 0.03) / vol\n'
                               '    max_dd = (rl_values / rl_values.cummax() - 1).min()\n\n'
                               '    print("=== Performance RL Policy ===")\n'
                               '    print(f"Sharpe: {sharpe:.3f}")\n'
                               '    print(f"CAGR:   {cagr:.1%}")\n'
                               '    print(f"Max DD: {max_dd:.1%}")\n'
                               '    print(f"Vol:    {vol:.1%}")\n\n'
                               '    # Distribution des actions\n'
                               '    action_counts = pd.Series(rl_actions).value_counts().sort_index()\n'
                               '    print(f"\\nDistribution des actions:")\n'
                               '    for action, count in action_counts.items():\n'
                               '        print(f"  {env.action_names[action]}: {count} jours ({count/len(rl_actions)*100:.1f}%)")\n'
                               'else:\n'
                               '    print("Backtest skipped.")')
                new_src = new_src.replace(old_metrics, new_metrics)
                # Remove the standalone action distribution block since it's now inside the guard
                old_action_dist = ('# Distribution des actions\n'
                                   'action_counts = pd.Series(rl_actions).value_counts().sort_index()\n'
                                   'print(f"\\nDistribution des actions:")\n'
                                   'for action, count in action_counts.items():\n'
                                   '    print(f"  {env.action_names[action]}: {count} jours ({count/len(rl_actions)*100:.1f}%)")')
                new_src = new_src.replace(old_action_dist, '')
                _set_source(cell, new_src)
                fixed += 1
                print(f'  Fixed cell {i}: backtest guard')

        # cell-16: benchmark comparison - guard (skip if already guarded)
        elif 'spy_values = closes' in src and 'SPY Buy & Hold' in src and 'closes is None' not in src:
            new_src = ('if closes is None or "rl_values" not in dir() or rl_values is None:\n'
                       '    print("RL backtest results not available - skipping benchmark comparison.")\n'
                       'else:\n'
                       '    # Benchmark: SPY Buy & Hold\n'
                       '    spy_values = closes[\'SPY\'].iloc[60:] / closes[\'SPY\'].iloc[60]\n\n'
                       '    # Benchmark: Equal Weight (33% each)\n'
                       '    equal_weight_values = (closes.iloc[60:] / closes.iloc[60]).mean(axis=1)\n\n'
                       '    # Métriques SPY\n'
                       '    spy_ret = spy_values.pct_change().dropna()\n'
                       '    spy_cagr = (spy_values.iloc[-1] ** (252/len(spy_values))) - 1\n'
                       '    spy_vol = spy_ret.std() * np.sqrt(252)\n'
                       '    spy_sharpe = (spy_cagr - 0.03) / spy_vol\n'
                       '    spy_dd = (spy_values / spy_values.cummax() - 1).min()\n\n'
                       '    # Métriques Equal Weight\n'
                       '    ew_ret = equal_weight_values.pct_change().dropna()\n'
                       '    ew_cagr = (equal_weight_values.iloc[-1] ** (252/len(equal_weight_values))) - 1\n'
                       '    ew_vol = ew_ret.std() * np.sqrt(252)\n'
                       '    ew_sharpe = (ew_cagr - 0.03) / ew_vol\n'
                       '    ew_dd = (equal_weight_values / equal_weight_values.cummax() - 1).min()\n\n'
                       '    print("=== Comparaison des Stratégies ===")\n'
                       '    print(f"{\'Stratégie\':<20} {\'CAGR\':>10} {\'Sharpe\':>10} {\'MaxDD\':>10}")\n'
                       '    print("-" * 53)\n'
                       '    print(f"{\'RL Portfolio\':<20} {cagr:>9.1%} {sharpe:>10.3f} {max_dd:>9.1%}")\n'
                       '    print(f"{\'Equal Weight\':<20} {ew_cagr:>9.1%} {ew_sharpe:>10.3f} {ew_dd:>9.1%}")\n'
                       '    print(f"{\'SPY B&H\':<20} {spy_cagr:>9.1%} {spy_sharpe:>10.3f} {spy_dd:>9.1%}")')
            _set_source(cell, new_src)
            fixed += 1
            print(f'  Fixed cell {i}: benchmark comparison guard')

        # cell-18: hyperparams - guard
        elif 'def test_hyperparams' in src and 'hp_results = test_hyperparams' in src:
            old_call = ('print("Testing hyperparameters...")\n'
                        'hp_results = test_hyperparams(lr_values, df_values)')
            new_call = ('if closes is None or env is None:\n'
                        '    print("RL environment not available - skipping hyperparameter testing.")\n'
                        '    hp_results = {}\n'
                        'else:\n'
                        '    print("Testing hyperparameters...")\n'
                        '    hp_results = test_hyperparams(lr_values, df_values)')
            if old_call in src:
                new_src = src.replace(old_call, new_call)
                old_print = ('print(f"\\n{\'Config\':<20} {\'Sharpe\':>8} {\'CAGR\':>8}")\n'
                             'print("-" * 39)\n'
                             'for key, res in hp_results.items():\n'
                             '    print(f"{key:<20} {res[\'sharpe\']:>8.3f} {res[\'cagr\']:>7.1%}")\n\n'
                             '# Meilleure config\n'
                             'best_config = max(hp_results.items(), key=lambda x: x[1][\'sharpe\'])\n'
                             'print(f"\\nMeilleure config: {best_config[0]} (Sharpe={best_config[1][\'sharpe\']:.3f})")')
                new_print = ('if hp_results:\n'
                             '    print(f"\\n{\'Config\':<20} {\'Sharpe\':>8} {\'CAGR\':>8}")\n'
                             '    print("-" * 39)\n'
                             '    for key, res in hp_results.items():\n'
                             '        print(f"{key:<20} {res[\'sharpe\']:>8.3f} {res[\'cagr\']:>7.1%}")\n\n'
                             '    # Meilleure config\n'
                             '    best_config = max(hp_results.items(), key=lambda x: x[1][\'sharpe\'])\n'
                             '    print(f"\\nMeilleure config: {best_config[0]} (Sharpe={best_config[1][\'sharpe\']:.3f})")\n'
                             'else:\n'
                             '    print("No hyperparameter results available.")')
                new_src = new_src.replace(old_print, new_print)
                _set_source(cell, new_src)
                fixed += 1
                print(f'  Fixed cell {i}: hyperparams guard')

        # cell-20: visualization - full replacement with guard
        # Note: use multi-substring match to avoid unicode issues with inline comparison
        elif 'plt.subplots(2, 2' in src and 'rl_values.values' in src and 'Graphique sauvegard' in src:
            new_src = ('if "rl_values" not in dir() or rl_values is None or "rewards" not in dir() or len(rewards) == 0:\n'
                       '    print("No RL training results available - skipping visualization.")\n'
                       '    print("Run this notebook on QC Cloud with multi-asset data access.")\n'
                       'else:\n'
                       '    fig, axes = plt.subplots(2, 2, figsize=(16, 10))\n\n'
                       '    # Courbe d\'apprentissage\n'
                       '    ax = axes[0, 0]\n'
                       '    ax.plot(rewards)\n'
                       '    ax.set_title(\'Courbe d\\\'Apprentissage\', fontsize=12, fontweight=\'bold\')\n'
                       '    ax.set_xlabel(\'Episode\')\n'
                       '    ax.set_ylabel(\'Reward Total\')\n'
                       '    ax.axhline(y=0, color=\'r\', linestyle=\'--\', alpha=0.5)\n'
                       '    ax.grid(True, alpha=0.3)\n\n'
                       '    # Decay d\'epsilon\n'
                       '    ax = axes[0, 1]\n'
                       '    ax.plot(epsilons)\n'
                       '    ax.set_title(\'Exploration (Epsilon Decay)\', fontsize=12, fontweight=\'bold\')\n'
                       '    ax.set_xlabel(\'Episode\')\n'
                       '    ax.set_ylabel(\'Epsilon\')\n'
                       '    ax.grid(True, alpha=0.3)\n\n'
                       '    # Comparaison des stratégies\n'
                       '    ax = axes[1, 0]\n'
                       '    ax.plot(rl_values.values, label=\'RL Portfolio\', linewidth=2)\n'
                       '    if "spy_values" in dir():\n'
                       '        ax.plot(spy_values.values, label=\'SPY B&H\', linestyle=\'--\')\n'
                       '    if "equal_weight_values" in dir():\n'
                       '        ax.plot(equal_weight_values.values, label=\'Equal Weight\', linestyle=\'--\')\n'
                       '    ax.set_title(\'Performance des Stratégies\', fontsize=12, fontweight=\'bold\')\n'
                       '    ax.set_ylabel(\'Valeur Normalisée\')\n'
                       '    ax.legend()\n'
                       '    ax.grid(True, alpha=0.3)\n\n'
                       '    # Allocation au fil du temps\n'
                       '    ax = axes[1, 1]\n'
                       '    action_names_short = [\'S\', \'B\', \'G\', \'C\']\n'
                       '    actions_mapped = [action_names_short[a] for a in rl_actions]\n'
                       '    ax.plot(actions_mapped, markersize=3)\n'
                       '    ax.set_title(\'Allocation au Fil du Temps\', fontsize=12, fontweight=\'bold\')\n'
                       '    ax.set_ylabel(\'Actif\')\n'
                       '    ax.set_yticks(range(4))\n'
                       '    ax.set_yticklabels([\'SPY\', \'TLT\', \'GLD\', \'Cash\'])\n'
                       '    ax.grid(True, alpha=0.3)\n\n'
                       '    plt.tight_layout()\n'
                       '    plt.savefig(\'rl_portfolio_analysis.png\', dpi=150, bbox_inches=\'tight\')\n'
                       '    plt.show()\n'
                       '    print("Graphique sauvegardé.")')
            _set_source(cell, new_src)
            fixed += 1
            print(f'  Fixed cell {i}: visualization guard')

    with open(nb_path, 'w', encoding='utf-8') as f:
        json.dump(nb, f, indent=1, ensure_ascii=False)
    print(f'  Saved {nb_path} ({fixed} cells fixed)')
    return fixed


def fix_portfolio_optimization_ml(nb_path):
    """Fix Portfolio-Optimization-ML/research.ipynb - pandas 3.x Series[int] -> .iloc[i]."""
    with open(nb_path, 'r', encoding='utf-8') as f:
        nb = json.load(f)

    cells = nb['cells']
    fixed = 0

    for i, cell in enumerate(cells):
        if cell.get('cell_type') != 'code':
            continue
        src = ''.join(cell['source'])

        # cell-9: fix momentum[i] -> momentum.iloc[i], reversion[i] -> reversion.iloc[i]
        if 'predict_returns_momentum' in src and 'predict_returns_mean_reversion' in src:
            if 'momentum[i]' in src or 'reversion[i]' in src:
                new_src = src.replace('momentum[i]', 'momentum.iloc[i]')
                new_src = new_src.replace('reversion[i]', 'reversion.iloc[i]')
                if new_src != src:
                    _set_source(cell, new_src)
                    fixed += 1
                    print(f'  Fixed cell {i}: pandas 3.x Series[int] -> .iloc[i]')

    with open(nb_path, 'w', encoding='utf-8') as f:
        json.dump(nb, f, indent=1, ensure_ascii=False)
    print(f'  Saved {nb_path} ({fixed} cells fixed)')
    return fixed


def fix_ml_regression(nb_path):
    """Fix ML-Regression/quantbook.ipynb - wrap window test in try/except for empty data."""
    with open(nb_path, 'r', encoding='utf-8') as f:
        nb = json.load(f)

    cells = nb['cells']
    fixed = 0

    for i, cell in enumerate(cells):
        if cell.get('cell_type') != 'code':
            continue
        src = ''.join(cell['source'])

        # cell-20: window test - wrap each backtest call in try/except
        if 'window_values = [30, 60, 90]' in src and 'backtest_ml_regression' in src:
            old_loop = (
                "window_results = {}\n"
                "for window in window_values:\n"
                "    r = backtest_ml_regression(closes, volumes, train_window=window)\n"
                "    window_results[f\"{window}\"] = r\n"
                "    print(f\"{window}j{'':<7} {r['sharpe']:>8.3f} {r['cagr']:>7.1%} {r['max_dd']:>7.1%}\")"
            )
            new_loop = (
                "window_results = {}\n"
                "for window in window_values:\n"
                "    try:\n"
                "        r = backtest_ml_regression(closes, volumes, train_window=window)\n"
                "        window_results[f\"{window}\"] = r\n"
                "        print(f\"{window}j{'':<7} {r['sharpe']:>8.3f} {r['cagr']:>7.1%} {r['max_dd']:>7.1%}\")\n"
                "    except (ValueError, KeyError) as e:\n"
                "        print(f\"{window}j  - skipped ({type(e).__name__}: {e})\")"
            )
            if old_loop in src:
                new_src = src.replace(old_loop, new_loop)
                _set_source(cell, new_src)
                fixed += 1
                print(f'  Fixed cell {i}: window test try/except guard')

    with open(nb_path, 'w', encoding='utf-8') as f:
        json.dump(nb, f, indent=1, ensure_ascii=False)
    print(f'  Saved {nb_path} ({fixed} cells fixed)')
    return fixed


def fix_btc_ml(nb_path):
    """Fix BTC-ML/research.ipynb - guard for empty qb.history (0 rows)."""
    with open(nb_path, 'r', encoding='utf-8') as f:
        nb = json.load(f)

    cells = nb['cells']
    fixed = 0

    for i, cell in enumerate(cells):
        if cell.get('cell_type') != 'code':
            continue
        src = ''.join(cell['source'])

        # cell-6: data processing - guard empty history / droplevel
        if 'history.droplevel(0)' in src and 'compute_features' not in src:
            new_src = src.replace(
                'df = history.droplevel(0)',
                'if history.empty or not isinstance(history.index, pd.MultiIndex):\n'
                '    print("WARNING: No BTC data available from QC Cloud.")\n'
                '    print("BTC-ML analysis requires daily BTC data from QuantConnect.")\n'
                '    print("All analysis cells will be skipped.")\n'
                '    df = None\nelse:\n    df = history.droplevel(0)'
            )
            # Also guard the rest of the cell after df assignment
            if new_src != src and 'df is not None' not in new_src:
                # Wrap remaining code in if df is not None
                new_src = new_src.replace(
                    "df['returns'] = df['close'].pct_change()",
                    "if df is None:\n"
                    "    pass\n"
                    "else:\n"
                    "    df['returns'] = df['close'].pct_change()"
                )
                # Indent everything after df['returns']
                lines = new_src.split('\n')
                in_else = False
                result_lines = []
                for line in lines:
                    if line.strip().startswith("if df is None:"):
                        result_lines.append(line)
                        in_else = True
                    elif in_else and line.strip() == 'pass':
                        result_lines.append(line)
                    elif in_else and line.strip() == 'else:':
                        result_lines.append(line)
                    elif in_else and line.strip().startswith("df['returns']"):
                        result_lines.append(line)
                    elif in_else:
                        result_lines.append('    ' + line if line.strip() else line)
                    else:
                        result_lines.append(line)
                new_src = '\n'.join(result_lines)
                _set_source(cell, new_src)
                fixed += 1
                print(f'  Fixed cell {i}: data load guard')

        # cell-8: compute_features call - guard df
        elif 'compute_features(df)' in src and 'def compute_features' not in src:
            old_call = "features = compute_features(df)"
            new_call = (
                "if df is None:\n"
                "    print('Data not available - skipping feature engineering.')\n"
                "    features = None\n"
                "else:\n"
                "    features = compute_features(df)"
            )
            if old_call in src:
                new_src = src.replace(old_call, new_call)
                _set_source(cell, new_src)
                fixed += 1
                print(f'  Fixed cell {i}: compute_features guard')

        # cell-10/12: features guard for training/prediction
        elif "'features' in dir()" not in src and 'RandomForestClassifier' in src and 'rf.fit' in src:
            new_src = src.replace(
                '# Préparer les données\nX = features',
                "if features is None or len(features) == 0:\n"
                "    print('Features not available - skipping model training.')\n"
                "    rf = None\n"
                "    train_data = None\n"
                "else:\n"
                "    # Préparer les données\n    X = features"
            )
            if new_src != src:
                # Also wrap the fit and subsequent code
                _set_source(cell, new_src)
                fixed += 1
                print(f'  Fixed cell {i}: model training guard')

        # cell-12: feature importance / predictions guard
        elif 'importances = rf.feature_importances_' in src and 'features is None' not in src:
            new_src = (
                "if rf is None or features is None:\n"
                "    print('Model not trained - skipping predictions and feature importance.')\n"
                "else:\n"
                + _indent(src, 4)
            )
            _set_source(cell, new_src)
            fixed += 1
            print(f'  Fixed cell {i}: predictions guard')

        # cell-14: test_data guard
        elif 'test_data' in src and 'rf.predict' in src and 'test_data is None' not in src:
            new_src = (
                "if 'test_data' not in dir() or test_data is None or rf is None:\n"
                "    print('Test data not available - skipping evaluation.')\n"
                "else:\n"
                + _indent(src, 4)
            )
            _set_source(cell, new_src)
            fixed += 1
            print(f'  Fixed cell {i}: evaluation guard')

        # cell-16: walk-forward guard
        elif 'tscv.split(features' in src and 'features is None' not in src:
            new_src = (
                "if features is None or len(features) < 5:\n"
                "    print('Features not available - skipping walk-forward validation.')\n"
                "else:\n"
                + _indent(src, 4)
            )
            _set_source(cell, new_src)
            fixed += 1
            print(f'  Fixed cell {i}: walk-forward guard')

        # cell-18: recommendations guard
        elif 'RECOMMANDATIONS POUR BTC-ML' in src and 'best_vol' in src:
            new_src = src.replace(
                "print(f\"\"\"\\nRECOMMANDATIONS POUR BTC-ML",
                "if 'best_vol' not in dir() or best_vol is None:\n"
                "    print('Optimization results not available - using default parameters.')\n"
                "    best_vol, best_conf, best_ratio_exit = 0.60, 0.55, 0.45\n\n"
                "print(f\"\"\"\\nRECOMMANDATIONS POUR BTC-ML"
            )
            if new_src != src:
                _set_source(cell, new_src)
                fixed += 1
                print(f'  Fixed cell {i}: recommendations guard')

    with open(nb_path, 'w', encoding='utf-8') as f:
        json.dump(nb, f, indent=1, ensure_ascii=False)
    print(f'  Saved {nb_path} ({fixed} cells fixed)')
    return fixed


def fix_crypto_multicanal(nb_path):
    """Fix Crypto-MultiCanal/quantbook.ipynb - guard for empty qb.history."""
    with open(nb_path, 'r', encoding='utf-8') as f:
        nb = json.load(f)

    cells = nb['cells']
    fixed = 0

    for i, cell in enumerate(cells):
        if cell.get('cell_type') != 'code':
            continue
        src = ''.join(cell['source'])

        # cell-5: data extraction - guard btc_history['close']
        if "btc_history['close']" in src and 'btc_close' in src and 'btc_close is None' not in src:
            # Wrap entire cell in guard
            new_src = (
                "if btc_history.empty or 'close' not in btc_history.columns:\n"
                "    print('WARNING: No BTC/USDT data available from QC Cloud.')\n"
                "    print('Crypto-MultiCanal analysis requires Binance BTCUSDT data.')\n"
                "    print('All analysis cells will be skipped.')\n"
                "    btc_close = None\n"
                "    btc_high = None\n"
                "    btc_low = None\n"
                "else:\n"
                + _indent(src, 4)
            )
            _set_source(cell, new_src)
            fixed += 1
            print(f'  Fixed cell {i}: data extraction guard')

        # cell-7: detect_zigzag_pivots call - guard btc_close
        elif 'detect_zigzag_pivots(btc_close' in src and 'btc_close is None' not in src:
            new_src = (
                "if btc_close is None:\n"
                "    print('BTC data not available - skipping pivot detection.')\n"
                "    pivots = None\n"
                "else:\n"
                + _indent(src, 4)
            )
            _set_source(cell, new_src)
            fixed += 1
            print(f'  Fixed cell {i}: pivot detection guard')

        # cell-10: fit_channel_line call - guard pivots + fix None formatting
        elif 'fit_channel_line' in src and 'support_slope' in src and 'pivots is None' not in src:
            new_src = (
                "if pivots is None:\n"
                "    print('Pivots not available - skipping channel analysis.')\n"
                "    support_slope, support_intercept = None, None\n"
                "    resistance_slope, resistance_intercept = None, None\n"
                "else:\n"
                + _indent(src, 4)
            )
            # Fix None formatting: replace f-string with safe format
            new_src = new_src.replace(
                'f"Support: slope={support_slope:.4f}',
                'f"Support: slope={support_slope:.4f}' if '.4f' not in new_src else
                '"Support: slope=" + (f"{support_slope:.4f}" if support_slope is not None else "N/A")'
            )
            _set_source(cell, new_src)
            fixed += 1
            print(f'  Fixed cell {i}: channel analysis guard')

        # cell-12: backtest strategy - guard btc_close + fix 'cas' typo
        elif 'def backtest_strategy' in src and 'backtest_strategy(' in src and 'btc_close is None' not in src:
            # Fix the 'cas' -> 'cash' typo
            new_src = src.replace('portfolio_values.append(cas)', 'portfolio_values.append(cash)')
            # Wrap the call part
            new_src = new_src.replace(
                "# Exécuter le backtest\nresult = backtest_strategy(",
                "if btc_close is None:\n"
                "    print('BTC data not available - skipping backtest.')\n"
                "    result = None\n"
                "else:\n"
                "    # Exécuter le backtest\n    result = backtest_strategy("
            )
            # Indent everything after the else
            lines = new_src.split('\n')
            in_else = False
            result_lines = []
            for j, line in enumerate(lines):
                if '    result = backtest_strategy(' in line and 'else:' in lines[j-1]:
                    in_else = True
                    result_lines.append(line)
                elif in_else and line.strip() and not line.startswith('    '):
                    result_lines.append('    ' + line)
                else:
                    result_lines.append(line)
            new_src = '\n'.join(result_lines)
            _set_source(cell, new_src)
            fixed += 1
            print(f'  Fixed cell {i}: backtest guard + cas->cash typo')

        # cell-14: advanced strategy - guard
        elif 'detect_zigzag_pivots(btc_close' in src and 'advanced_backtest' in src:
            new_src = (
                "if btc_close is None:\n"
                "    print('BTC data not available - skipping advanced strategy.')\n"
                "else:\n"
                + _indent(src, 4)
            )
            _set_source(cell, new_src)
            fixed += 1
            print(f'  Fixed cell {i}: advanced strategy guard')

        # cell-16: combined strategy - guard
        elif 'combined_backtest' in src and 'btc_close' in src and 'btc_close is None' not in src:
            new_src = (
                "if btc_close is None:\n"
                "    print('BTC data not available - skipping combined strategy.')\n"
                "else:\n"
                + _indent(src, 4)
            )
            _set_source(cell, new_src)
            fixed += 1
            print(f'  Fixed cell {i}: combined strategy guard')

        # cell-18: comparison - guard
        elif 'result' in src and 'advanced_result' in src and "result is None" not in src:
            new_src = (
                "if result is None:\n"
                "    print('Backtest results not available - skipping comparison.')\n"
                "else:\n"
                + _indent(src, 4)
            )
            _set_source(cell, new_src)
            fixed += 1
            print(f'  Fixed cell {i}: comparison guard')

        # cell-20: visualization - guard
        elif 'btc_close.iloc' in src and 'plt.subplots' in src and 'btc_close is None' not in src:
            new_src = (
                "if btc_close is None:\n"
                "    print('BTC data not available - skipping visualization.')\n"
                "    print('Run this notebook on QC Cloud with Binance data access.')\n"
                "else:\n"
                + _indent(src, 4)
            )
            _set_source(cell, new_src)
            fixed += 1
            print(f'  Fixed cell {i}: visualization guard')

    with open(nb_path, 'w', encoding='utf-8') as f:
        json.dump(nb, f, indent=1, ensure_ascii=False)
    print(f'  Saved {nb_path} ({fixed} cells fixed)')
    return fixed


def fix_sector_ml_classification(nb_path):
    """Fix Sector-ML-Classification/research.ipynb - guard for empty qb.history."""
    with open(nb_path, 'r', encoding='utf-8') as f:
        nb = json.load(f)

    cells = nb['cells']
    fixed = 0

    for i, cell in enumerate(cells):
        if cell.get('cell_type') != 'code':
            continue
        src = ''.join(cell['source'])

        # cell-5: feature engineering - guard history['close']
        if "history['close']" in src and 'price_data' in src and 'history.empty' not in src:
            new_src = (
                "if history.empty or len(history) == 0:\n"
                "    print('WARNING: No stock data available from QC Cloud.')\n"
                "    print('Sector ML Classification requires multi-stock daily data.')\n"
                "    print('All analysis cells will be skipped.')\n"
                "    price_data = None\n"
                "    all_features = []\n"
                "else:\n"
                + _indent(src, 4)
            )
            _set_source(cell, new_src)
            fixed += 1
            print(f'  Fixed cell {i}: feature engineering guard')

        # cell-7: data preparation - guard price_data
        elif 'price_data' in src and 'train_test_split' in src and 'price_data is None' not in src:
            new_src = (
                "if price_data is None:\n"
                "    print('Price data not available - skipping data preparation.')\n"
                "    X_scaled, y = None, None\n"
                "else:\n"
                + _indent(src, 4)
            )
            _set_source(cell, new_src)
            fixed += 1
            print(f'  Fixed cell {i}: data preparation guard')

        # cell-9: model training - guard X_scaled
        elif 'X_scaled' in src and 'RandomForestClassifier' in src and 'X_scaled is None' not in src:
            new_src = (
                "if X_scaled is None:\n"
                "    print('Training data not available - skipping model training.')\n"
                "    rf = None\n"
                "else:\n"
                + _indent(src, 4)
            )
            _set_source(cell, new_src)
            fixed += 1
            print(f'  Fixed cell {i}: model training guard')

        # cell-11: prediction and backtest - guard rf
        elif 'rf.predict' in src and 'feature_importance' not in src.lower() and 'rf is None' not in src:
            new_src = (
                "if rf is None:\n"
                "    print('Model not trained - skipping predictions.')\n"
                "else:\n"
                + _indent(src, 4)
            )
            _set_source(cell, new_src)
            fixed += 1
            print(f'  Fixed cell {i}: prediction guard')

        # cell-12: feature importance - guard
        elif 'feature_importance' in src.lower() and 'importances' in src and 'rf is None' not in src:
            new_src = (
                "if rf is None:\n"
                "    print('Model not trained - skipping feature importance.')\n"
                "else:\n"
                + _indent(src, 4)
            )
            _set_source(cell, new_src)
            fixed += 1
            print(f'  Fixed cell {i}: feature importance guard')

        # cell-14: sector predictions - guard
        elif 'sector_predictions' in src and 'price_data' in src and 'price_data is None' not in src:
            new_src = (
                "if price_data is None:\n"
                "    print('Price data not available - skipping sector predictions.')\n"
                "    sector_predictions = {}\n"
                "else:\n"
                + _indent(src, 4)
            )
            _set_source(cell, new_src)
            fixed += 1
            print(f'  Fixed cell {i}: sector predictions guard')

        # cell-17: summary visualization - guard
        elif 'sector_predictions' in src and 'n_buy_per_month' in src and 'not sector_predictions' not in src:
            new_src = (
                "if not sector_predictions:\n"
                "    print('No sector predictions available - skipping summary.')\n"
                "else:\n"
                + _indent(src, 4)
            )
            _set_source(cell, new_src)
            fixed += 1
            print(f'  Fixed cell {i}: summary guard')

    with open(nb_path, 'w', encoding='utf-8') as f:
        json.dump(nb, f, indent=1, ensure_ascii=False)
    print(f'  Saved {nb_path} ({fixed} cells fixed)')
    return fixed


if __name__ == '__main__':
    if len(sys.argv) < 2:
        print('Usage: python fix_qc_notebooks.py <notebook_path>')
        sys.exit(1)

    nb_path = sys.argv[1]
    if not os.path.exists(nb_path):
        print(f'File not found: {nb_path}')
        sys.exit(1)

    if 'ML-XGBoost' in nb_path:
        fix_ml_xgboost(nb_path)
    elif 'RL-Portfolio' in nb_path:
        fix_rl_portfolio(nb_path)
    elif 'Portfolio-Optimization-ML' in nb_path:
        fix_portfolio_optimization_ml(nb_path)
    elif 'ML-Regression' in nb_path:
        fix_ml_regression(nb_path)
    elif 'BTC-ML' in nb_path:
        fix_btc_ml(nb_path)
    elif 'Crypto-MultiCanal' in nb_path:
        fix_crypto_multicanal(nb_path)
    elif 'Sector-ML-Classification' in nb_path:
        fix_sector_ml_classification(nb_path)
    else:
        print(f'No fix defined for {nb_path}')
