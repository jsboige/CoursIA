"""Tests de la source et du rapport d'environnement des sondes WS."""

import importlib.util
import sys
from pathlib import Path
from types import SimpleNamespace

import numpy as np
import pytest


spec = importlib.util.spec_from_file_location(
    "ws_probes_repro", Path(__file__).resolve().parents[1] / "repro/ws_probes_repro.py"
)
repro = importlib.util.module_from_spec(spec)
spec.loader.exec_module(repro)


def test_default_source_failure_does_not_fall_back(monkeypatch, capsys):
    def fail(*args, **kwargs):
        raise OSError("cache absent")

    monkeypatch.setitem(sys.modules, "torchvision", SimpleNamespace())
    monkeypatch.setitem(sys.modules, "torchvision.datasets", SimpleNamespace(FashionMNIST=fail))
    monkeypatch.setattr("sklearn.datasets.fetch_openml", lambda *a, **kw: pytest.fail("repli OpenML"))
    for source in (None, "auto"):
        with pytest.raises(RuntimeError, match="Chargement torchvision impossible"):
            if source is None:
                repro.load_fashion_mnist("/cache")
            else:
                repro.load_fashion_mnist("/cache", source)
    with pytest.raises(SystemExit) as result:
        repro.main(["--cache", "/cache"])
    assert result.value.code == 2
    assert "--source openml" in capsys.readouterr().err


def test_explicit_openml_is_noncanonical(monkeypatch, capsys):
    data = SimpleNamespace(data=np.zeros((2, 784)), target=np.array(["1", "2"]))
    calls = []
    monkeypatch.setattr("sklearn.datasets.fetch_openml", lambda *a, **kw: calls.append((a, kw)) or data)
    _, labels, _, _, source = repro.load_fashion_mnist("/cache", "openml")
    assert labels.tolist() == [1, 2]
    assert source == "openml" and calls[0][0] == ("Fashion-MNIST",)
    monkeypatch.setattr(repro, "probe_ws00c", lambda *a: repro.CITED["WS-00c"])
    monkeypatch.setattr(repro, "probe_ws03", lambda *a: repro.CITED["WS-03"])
    assert repro.main(["--source", "openml"]) == 1
    assert "NON_CANONICAL" in capsys.readouterr().out


def test_runtime_blas_reports_each_loaded_library(monkeypatch):
    monkeypatch.setattr(repro, "threadpool_info", lambda: [
        {"user_api": "blas", "internal_api": "openblas", "version": "0.3.30",
         "num_threads": 4, "filepath": "/one"},
        {"user_api": "blas", "internal_api": "mkl", "version": None,
         "num_threads": 2, "filepath": "/two"},
        {"user_api": "openmp", "internal_api": "openmp", "num_threads": 8},
    ])
    assert repro.blas_chain() == [
        {"user_api": "blas", "internal_api": "openblas", "version": "0.3.30",
         "num_threads": 4, "filepath": "/one"},
        {"user_api": "blas", "internal_api": "mkl", "version": None,
         "num_threads": 2, "filepath": "/two"},
    ]


def test_auto_alias_reports_torchvision(monkeypatch):
    class Tensor:
        def __init__(self, values):
            self.values = np.array(values)

        def numpy(self):
            return self.values

    def fashion_mnist(root, train, download):
        return SimpleNamespace(data=Tensor([[[255]]]), targets=Tensor([int(train)]))

    monkeypatch.setitem(sys.modules, "torchvision", SimpleNamespace())
    monkeypatch.setitem(sys.modules, "torchvision.datasets",
                        SimpleNamespace(FashionMNIST=fashion_mnist))
    images, labels, _, _, source = repro.load_fashion_mnist("/cache", "auto")
    assert images.tolist() == [[[1.0]]]
    assert labels.tolist() == [1]
    assert source == "torchvision"


def test_unknown_source_rejected():
    with pytest.raises(ValueError, match="Source inconnue"):
        repro.load_fashion_mnist("/cache", "unknown")


def test_margin_default_cli_reaches_prepare_with_torchvision(monkeypatch):
    class Tensor:
        def __init__(self, values):
            self.values = np.array(values)

        def numpy(self):
            return self.values

    calls = []

    def fashion_mnist(root, train, download):
        calls.append((train, download))
        return SimpleNamespace(data=Tensor([[[255]]]), targets=Tensor([int(train)]))

    class PrepareReached(Exception):
        pass

    def prepare(images, labels):
        assert images.tolist() == [[[1.0]]]
        assert labels.tolist() == [1]
        raise PrepareReached

    monkeypatch.setitem(sys.modules, "torchvision", SimpleNamespace())
    monkeypatch.setitem(sys.modules, "torchvision.datasets",
                        SimpleNamespace(FashionMNIST=fashion_mnist))
    monkeypatch.setitem(sys.modules, "ws_probes_repro", repro)
    margin_spec = importlib.util.spec_from_file_location(
        "ws_probes_margin_test", Path(__file__).resolve().parents[1] / "repro/ws_probes_margin.py"
    )
    margin = importlib.util.module_from_spec(margin_spec)
    margin_spec.loader.exec_module(margin)
    monkeypatch.setattr(margin, "prepare", prepare)
    # Interdire tout appel OpenML dans ce chemin CLI où torchvision réussit.
    # Le cas d'échec est couvert par test_default_source_failure_does_not_fall_back.
    monkeypatch.setattr("sklearn.datasets.fetch_openml", lambda *a, **kw: pytest.fail("repli OpenML"))
    with pytest.raises(PrepareReached):
        margin.main([])
    assert calls == [(True, True), (False, True)]
