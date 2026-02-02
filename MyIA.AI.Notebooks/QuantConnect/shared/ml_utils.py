"""
Machine Learning Utilities pour QuantConnect

Utilitaires pour entraîner, évaluer et persister des modèles ML dans QuantConnect.
Utilisé principalement dans les notebooks 19-27 (ML/DL/AI).

Fonctions principales:
    - train_classifier: Entraîne un modèle de classification
    - train_regressor: Entraîne un modèle de régression
    - evaluate_model: Calcule métriques de performance
    - save_to_objectstore: Sauvegarde modèle dans ObjectStore QuantConnect
    - load_from_objectstore: Charge modèle depuis ObjectStore

Usage:
    from shared.ml_utils import train_classifier, save_to_objectstore

    model = train_classifier(X_train, y_train, model_type='xgboost')
    save_to_objectstore(model, 'my_model', qc_algorithm)
"""

import pandas as pd
import numpy as np
from typing import Dict, Any, Optional, Tuple
import pickle
import joblib
from pathlib import Path


def train_classifier(X_train: np.ndarray,
                    y_train: np.ndarray,
                    model_type: str = 'random_forest',
                    **kwargs) -> Any:
    """
    Entraîne un modèle de classification

    Args:
        X_train: Features d'entraînement (n_samples, n_features)
        y_train: Labels d'entraînement (n_samples,)
        model_type: 'random_forest', 'xgboost', 'lightgbm', 'logistic'
        **kwargs: Paramètres spécifiques au modèle

    Returns:
        Modèle entraîné

    Example:
        >>> import numpy as np
        >>> X = np.random.rand(100, 5)
        >>> y = np.random.randint(0, 2, 100)
        >>> model = train_classifier(X, y, model_type='random_forest', n_estimators=50)
        >>> predictions = model.predict(X[:10])
        >>> len(predictions)
        10
    """
    if model_type == 'random_forest':
        from sklearn.ensemble import RandomForestClassifier
        default_params = {'n_estimators': 100, 'max_depth': 10, 'random_state': 42}
        default_params.update(kwargs)
        model = RandomForestClassifier(**default_params)

    elif model_type == 'xgboost':
        try:
            import xgboost as xgb
        except ImportError:
            raise ImportError("XGBoost not installed. pip install xgboost")
        default_params = {'n_estimators': 100, 'max_depth': 6, 'random_state': 42}
        default_params.update(kwargs)
        model = xgb.XGBClassifier(**default_params)

    elif model_type == 'lightgbm':
        try:
            import lightgbm as lgb
        except ImportError:
            raise ImportError("LightGBM not installed. pip install lightgbm")
        default_params = {'n_estimators': 100, 'max_depth': 6, 'random_state': 42}
        default_params.update(kwargs)
        model = lgb.LGBMClassifier(**default_params)

    elif model_type == 'logistic':
        from sklearn.linear_model import LogisticRegression
        default_params = {'max_iter': 1000, 'random_state': 42}
        default_params.update(kwargs)
        model = LogisticRegression(**default_params)

    else:
        raise ValueError(f"Unknown model_type: {model_type}")

    # Entraîner
    model.fit(X_train, y_train)
    return model


def train_regressor(X_train: np.ndarray,
                   y_train: np.ndarray,
                   model_type: str = 'random_forest',
                   **kwargs) -> Any:
    """
    Entraîne un modèle de régression

    Args:
        X_train: Features d'entraînement
        y_train: Targets d'entraînement
        model_type: 'random_forest', 'xgboost', 'svr', 'linear'
        **kwargs: Paramètres spécifiques au modèle

    Returns:
        Modèle entraîné

    Example:
        >>> import numpy as np
        >>> X = np.random.rand(100, 5)
        >>> y = np.random.rand(100)
        >>> model = train_regressor(X, y, model_type='linear')
        >>> predictions = model.predict(X[:10])
        >>> len(predictions)
        10
    """
    if model_type == 'random_forest':
        from sklearn.ensemble import RandomForestRegressor
        default_params = {'n_estimators': 100, 'max_depth': 10, 'random_state': 42}
        default_params.update(kwargs)
        model = RandomForestRegressor(**default_params)

    elif model_type == 'xgboost':
        try:
            import xgboost as xgb
        except ImportError:
            raise ImportError("XGBoost not installed. pip install xgboost")
        default_params = {'n_estimators': 100, 'max_depth': 6, 'random_state': 42}
        default_params.update(kwargs)
        model = xgb.XGBRegressor(**default_params)

    elif model_type == 'svr':
        from sklearn.svm import SVR
        default_params = {'kernel': 'rbf', 'C': 1.0}
        default_params.update(kwargs)
        model = SVR(**default_params)

    elif model_type == 'linear':
        from sklearn.linear_model import LinearRegression
        model = LinearRegression(**kwargs)

    else:
        raise ValueError(f"Unknown model_type: {model_type}")

    # Entraîner
    model.fit(X_train, y_train)
    return model


def evaluate_model(model: Any,
                  X_test: np.ndarray,
                  y_test: np.ndarray,
                  task: str = 'classification') -> Dict[str, float]:
    """
    Évalue un modèle ML

    Args:
        model: Modèle entraîné
        X_test: Features de test
        y_test: Labels/targets de test
        task: 'classification' ou 'regression'

    Returns:
        Dict de métriques

    Example:
        >>> import numpy as np
        >>> from sklearn.ensemble import RandomForestClassifier
        >>> X_train = np.random.rand(100, 5)
        >>> y_train = np.random.randint(0, 2, 100)
        >>> X_test = np.random.rand(20, 5)
        >>> y_test = np.random.randint(0, 2, 20)
        >>> model = RandomForestClassifier(n_estimators=10, random_state=42)
        >>> model.fit(X_train, y_train)
        >>> metrics = evaluate_model(model, X_test, y_test, task='classification')
        >>> 'accuracy' in metrics
        True
    """
    predictions = model.predict(X_test)

    if task == 'classification':
        from sklearn.metrics import accuracy_score, precision_score, recall_score, f1_score

        metrics = {
            'accuracy': accuracy_score(y_test, predictions),
            'precision': precision_score(y_test, predictions, average='weighted', zero_division=0),
            'recall': recall_score(y_test, predictions, average='weighted', zero_division=0),
            'f1_score': f1_score(y_test, predictions, average='weighted', zero_division=0)
        }

        # Sharpe ratio basé sur predictions (si applicable)
        try:
            if hasattr(model, 'predict_proba'):
                proba = model.predict_proba(X_test)[:, 1]
                returns = (proba - 0.5) * 2  # Scale to [-1, 1]
                if len(returns) > 1 and np.std(returns) > 0:
                    sharpe = np.mean(returns) / np.std(returns) * np.sqrt(252)
                    metrics['sharpe_ratio'] = sharpe
        except:
            pass

    elif task == 'regression':
        from sklearn.metrics import mean_absolute_error, mean_squared_error, r2_score

        metrics = {
            'mae': mean_absolute_error(y_test, predictions),
            'mse': mean_squared_error(y_test, predictions),
            'rmse': np.sqrt(mean_squared_error(y_test, predictions)),
            'r2': r2_score(y_test, predictions)
        }

    else:
        raise ValueError(f"Unknown task: {task}")

    return metrics


def save_to_objectstore(model: Any,
                       name: str,
                       qc_algorithm: Optional[Any] = None,
                       local_path: Optional[str] = None) -> str:
    """
    Sauvegarde modèle dans QuantConnect ObjectStore (ou localement)

    Args:
        model: Modèle à sauvegarder
        name: Nom du modèle (ex: 'my_rf_model')
        qc_algorithm: Instance QCAlgorithm (si dans QuantConnect)
        local_path: Chemin local (si hors QuantConnect)

    Returns:
        Path où le modèle est sauvegardé

    Example:
        >>> import numpy as np
        >>> from sklearn.ensemble import RandomForestClassifier
        >>> X = np.random.rand(50, 3)
        >>> y = np.random.randint(0, 2, 50)
        >>> model = RandomForestClassifier(n_estimators=5, random_state=42)
        >>> model.fit(X, y)
        >>> path = save_to_objectstore(model, 'test_model', local_path='./test_model.pkl')
        >>> Path(path).exists()
        True
    """
    # Sérialiser modèle
    model_bytes = pickle.dumps(model)

    if qc_algorithm is not None:
        # QuantConnect ObjectStore
        key = f'{name}.pkl'
        qc_algorithm.ObjectStore.Save(key, model_bytes)
        return f'ObjectStore:{key}'

    elif local_path is not None:
        # Sauvegarde locale
        path = Path(local_path)
        path.parent.mkdir(parents=True, exist_ok=True)

        with open(path, 'wb') as f:
            f.write(model_bytes)

        return str(path)

    else:
        raise ValueError("Provide either qc_algorithm or local_path")


def load_from_objectstore(name: str,
                         qc_algorithm: Optional[Any] = None,
                         local_path: Optional[str] = None) -> Any:
    """
    Charge modèle depuis ObjectStore ou local

    Args:
        name: Nom du modèle
        qc_algorithm: Instance QCAlgorithm (si dans QuantConnect)
        local_path: Chemin local (si hors QuantConnect)

    Returns:
        Modèle chargé

    Example:
        >>> import numpy as np
        >>> from sklearn.ensemble import RandomForestClassifier
        >>> X = np.random.rand(50, 3)
        >>> y = np.random.randint(0, 2, 50)
        >>> model = RandomForestClassifier(n_estimators=5, random_state=42)
        >>> model.fit(X, y)
        >>> save_to_objectstore(model, 'test_load', local_path='./test_load.pkl')
        './test_load.pkl'
        >>> loaded = load_from_objectstore('test_load', local_path='./test_load.pkl')
        >>> loaded.n_estimators
        5
    """
    if qc_algorithm is not None:
        # QuantConnect ObjectStore
        key = f'{name}.pkl'
        if not qc_algorithm.ObjectStore.ContainsKey(key):
            raise FileNotFoundError(f"Model not found in ObjectStore: {key}")

        model_bytes = qc_algorithm.ObjectStore.ReadBytes(key)
        model = pickle.loads(model_bytes)
        return model

    elif local_path is not None:
        # Local
        path = Path(local_path)
        if not path.exists():
            raise FileNotFoundError(f"Model file not found: {path}")

        with open(path, 'rb') as f:
            model = pickle.load(f)

        return model

    else:
        raise ValueError("Provide either qc_algorithm or local_path")


def cross_validate_walk_forward(model_factory,
                                X: np.ndarray,
                                y: np.ndarray,
                                n_splits: int = 5,
                                train_size_ratio: float = 0.7) -> Dict[str, float]:
    """
    Cross-validation avec walk-forward pour time series

    Args:
        model_factory: Fonction qui retourne un nouveau modèle
        X: Features (n_samples, n_features)
        y: Labels (n_samples,)
        n_splits: Nombre de splits
        train_size_ratio: Ratio train

    Returns:
        Dict de métriques moyennes

    Example:
        >>> import numpy as np
        >>> from sklearn.ensemble import RandomForestClassifier
        >>> X = np.random.rand(100, 5)
        >>> y = np.random.randint(0, 2, 100)
        >>> def factory():
        ...     return RandomForestClassifier(n_estimators=5, random_state=42)
        >>> results = cross_validate_walk_forward(factory, X, y, n_splits=3)
        >>> 'mean_accuracy' in results
        True
    """
    from sklearn.metrics import accuracy_score

    scores = []
    total_size = len(X)
    test_size = int(total_size * (1 - train_size_ratio))
    train_initial_size = int(total_size * train_size_ratio)

    for i in range(n_splits):
        if i == 0:
            train_end = train_initial_size
        else:
            train_end = train_initial_size + (i * test_size)

        test_start = train_end
        test_end = test_start + test_size

        if test_end > total_size:
            break

        X_train = X[:train_end]
        y_train = y[:train_end]
        X_test = X[test_start:test_end]
        y_test = y[test_start:test_end]

        # Créer et entraîner modèle
        model = model_factory()
        model.fit(X_train, y_train)

        # Évaluer
        predictions = model.predict(X_test)
        score = accuracy_score(y_test, predictions)
        scores.append(score)

    return {
        'mean_accuracy': np.mean(scores),
        'std_accuracy': np.std(scores),
        'n_splits_completed': len(scores)
    }


if __name__ == '__main__':
    # Tests rapides
    print("Testing ml_utils.py...")
    import tempfile
    import shutil

    # Test train_classifier
    X_train = np.random.rand(100, 5)
    y_train = np.random.randint(0, 2, 100)
    model = train_classifier(X_train, y_train, model_type='random_forest', n_estimators=10)
    print(f"✓ train_classifier: model trained")

    # Test evaluate_model
    X_test = np.random.rand(20, 5)
    y_test = np.random.randint(0, 2, 20)
    metrics = evaluate_model(model, X_test, y_test, task='classification')
    print(f"✓ evaluate_model: accuracy={metrics['accuracy']:.2f}")

    # Test save/load
    temp_dir = tempfile.mkdtemp()
    try:
        model_path = Path(temp_dir) / 'test_model.pkl'
        save_to_objectstore(model, 'test', local_path=str(model_path))
        loaded_model = load_from_objectstore('test', local_path=str(model_path))
        print(f"✓ save/load: model saved and loaded")
    finally:
        shutil.rmtree(temp_dir)

    print("\nAll tests passed! ✓")
