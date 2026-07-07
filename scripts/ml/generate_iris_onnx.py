#!/usr/bin/env python3
"""
Régénère le modèle ONNX Iris avec options propres pour Microsoft.ML.OnnxTransformer 5.0.0.

Usage:
    python scripts/ml/regen_iris_onnx.py

Sortie:
    MyIA.AI.Notebooks/ML/ML.Net/iris_model.onnx

Note:
    Version 2 du script — corrige trois bugs du premier jet :
    - target_opset=12 (stabilité ML.NET 5.0.0)
    - zipmap=False (sinon output_probability sort en UNDEFINED tensor,
      bug skl2onnx RandomForest)
    - initial_type ('input', FloatTensorType([None, 4])) pour input column
      conforme au code C# ML.NET
"""
import sys
from pathlib import Path

import numpy as np
from sklearn.datasets import load_iris
from sklearn.ensemble import RandomForestClassifier
from sklearn.model_selection import train_test_split
from sklearn.metrics import accuracy_score
from skl2onnx import convert_sklearn
from skl2onnx.common.data_types import FloatTensorType


def main() -> int:
    repo_root = Path(__file__).resolve().parents[2]
    output_path = repo_root / "MyIA.AI.Notebooks" / "ML" / "ML.Net" / "iris_model.onnx"

    iris = load_iris()
    X, y = iris.data.astype(np.float32), iris.target
    feature_names = iris.feature_names
    class_names = iris.target_names.tolist()

    X_train, X_test, y_train, y_test = train_test_split(
        X, y, test_size=0.2, random_state=42, stratify=y
    )
    clf = RandomForestClassifier(n_estimators=20, random_state=42, n_jobs=1)
    clf.fit(X_train, y_train)

    y_pred = clf.predict(X_test)
    accuracy = accuracy_score(y_test, y_pred)
    print(f"RandomForestClassifier entraîné sur {len(X_train)} échantillons.")
    print(f"Test set accuracy: {accuracy:.4f} ({len(y_test)} échantillons)")
    print(f"Classes: {class_names}")
    print(f"Features: {feature_names}")

    # Conversion ONNX :
    # - input column 'input' (le nom est utilisé par le code C# ML.NET)
    # - zipmap=False : sans zipmap, output_probabilities sort en float[0,3]
    #   (sinon c'est un map<string,float> non-typé qui pose problème à ML.NET)
    # - target_opset=12 (compat ML.NET 5.0.0)
    initial_type = [("input", FloatTensorType([None, 4]))]
    options = {id(clf): {"zipmap": False}}
    onnx_model = convert_sklearn(
        clf,
        initial_types=initial_type,
        target_opset=12,
        options=options,
    )

    output_path.parent.mkdir(parents=True, exist_ok=True)
    with open(output_path, "wb") as f:
        f.write(onnx_model.SerializeToString())

    size_bytes = output_path.stat().st_size
    print(f"\nModèle ONNX écrit: {output_path.relative_to(repo_root)}")
    print(f"Taille: {size_bytes} octets ({size_bytes / 1024:.1f} KiB)")
    print(f"OpSets: {[(o.domain or 'ai.onnx', o.version) for o in onnx_model.opset_import]}")

    # Vérification : inputs / outputs / types
    print("\nSignature du modèle:")
    for i in onnx_model.graph.input:
        shape = []
        for d in i.type.tensor_type.shape.dim:
            shape.append(d.dim_param or d.dim_value)
        print(f"  INPUT  {i.name}: elem_type={i.type.tensor_type.elem_type} shape={shape}")
    for o in onnx_model.graph.output:
        shape = []
        for d in o.type.tensor_type.shape.dim:
            shape.append(d.dim_param or d.dim_value)
        print(f"  OUTPUT {o.name}: elem_type={o.type.tensor_type.elem_type} shape={shape}")

    return 0


if __name__ == "__main__":
    sys.exit(main())