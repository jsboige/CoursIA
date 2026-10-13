#!/usr/bin/env python3
"""`decision_index_report.py` classe par palier et ne devine pas les licences.

Ce que ce fichier garde
-----------------------
Le Pli 1 de #18204 reclasse les modeles de decision par **palier de taille
servie**. Deux proprietes portent la valeur du releve, et toutes deux se
cassent en silence :

1. **Un modele tombe dans un seul palier.** Les bornes de `TIERS` se touchent ;
   une borne ecrite en `<=` au lieu de `<` ferait compter deux fois une entree
   a 1,2 B ou 5,0 B, et le classement publierait un doublon sans rien signaler.
2. **La licence n'est jamais inventee.** L'index ne la publie pas. Le script
   doit donc rendre `-` quand il ne l'a pas relevee, et jamais une valeur
   plausible deduite du nom.

Les tests portent sur les fonctions pures : aucun acces reseau. `fetch_hf` est
remplace la ou il serait appele.
"""

import importlib.util
import json
from pathlib import Path

import pytest

_MOD_PATH = Path(__file__).resolve().parent.parent / "genai-stack" / "decision_index_report.py"
_spec = importlib.util.spec_from_file_location("decision_index_report", _MOD_PATH)
report = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(report)


def _model(name, params_b, skill, *, repo=None, url=None, note=None, latency=None):
    meta = {"served_params": int(params_b * 1e9)}
    if repo:
        meta["weights_repo"] = repo
    if url:
        meta["model_url"] = url
    if note:
        meta["weights_note"] = note
    return {
        "name": name,
        "meta": meta,
        "scores": {"balanced_skill": skill},
        "coverage": 1,
        "latency": {"median": latency},
    }


def _index(models):
    return {"suite": {"label": "Decision Index 0.3.1", "headline": "balanced_skill"},
            "models": models}


def test_each_model_falls_in_exactly_one_tier():
    """Les bornes se touchent sans se recouvrir : aucun doublon, aucun trou."""
    index = _index([
        _model("a", 0.5, 10), _model("b", 1.2, 20), _model("c", 4.99, 30),
        _model("d", 5.0, 40), _model("e", 14.99, 50), _model("f", 15.0, 60),
        _model("g", 39.99, 70),
    ])
    tiers = report.build_rows(index, with_license=False, top=50)

    placed = [name for rows in tiers.values() for name in (r["name"] for r in rows)]
    assert sorted(placed) == ["a", "b", "c", "d", "e", "f", "g"]
    assert len(placed) == len(set(placed)), "une entree a ete comptee dans deux paliers"

    # Dans chaque palier, le tri est par score decroissant.
    assert [r["name"] for r in tiers["<=1B"]] == ["a"]
    assert [r["name"] for r in tiers["2-4B"]] == ["c", "b"]
    assert [r["name"] for r in tiers["9-12B"]] == ["e", "d"]
    assert [r["name"] for r in tiers["26-35B"]] == ["g", "f"]


def test_tiers_are_sorted_by_score_and_capped():
    index = _index([_model("low", 3.0, 10), _model("high", 3.0, 90), _model("mid", 3.0, 50)])
    tiers = report.build_rows(index, with_license=False, top=2)

    assert [r["name"] for r in tiers["2-4B"]] == ["high", "mid"], "tri par score decroissant"


def test_license_is_not_invented_without_the_lookup():
    """Sans `--licenses`, la colonne reste vide : l'index ne porte pas la licence."""
    tiers = report.build_rows(_index([_model("m", 3.0, 50, repo="o/r")]),
                              with_license=False, top=5)
    assert tiers["2-4B"][0]["license"] is None


def test_license_lookup_is_called_once_per_repo(monkeypatch):
    """Deux modeles partageant un depot ne declenchent qu'une requete."""
    calls = []

    def fake_fetch(repo):
        calls.append(repo)
        return {"cardData": {"license": "apache-2.0"}, "tags": []}

    monkeypatch.setattr(report, "fetch_hf", fake_fetch)
    index = _index([_model("a", 3.0, 50, repo="o/r"), _model("b", 3.5, 40, repo="o/r")])
    tiers = report.build_rows(index, with_license=True, top=5)

    assert calls == ["o/r"], "le cache par depot n'a pas joue"
    assert all(r["license"] == "apache-2.0" for r in tiers["2-4B"])


def test_failed_lookup_is_reported_not_hidden(monkeypatch):
    """Un echec reseau remonte son code : il ne se lit pas comme « sans licence »."""
    monkeypatch.setattr(report, "fetch_hf", lambda repo: {"_error": "HTTP 401"})
    tiers = report.build_rows(_index([_model("jet", 4.6, 42, repo="m/jet")]),
                              with_license=True, top=5)
    assert tiers["2-4B"][0]["license"] == "HTTP 401"


@pytest.mark.parametrize("params,gguf,expected", [
    (0.87, False, "vLLM, llama.cpp (quantifie)"),
    (11.96, True, "llama.cpp (GGUF), vLLM"),
    (11.96, False, "vLLM (quantifie 4 bits obligatoire en 24 Go)"),
    (27.8, False, "vLLM (quantifie 4 bits obligatoire en 24 Go)"),
])
def test_service_path_follows_size_and_published_format(params, gguf, expected):
    assert report.service_paths(params, gguf) == expected


@pytest.mark.parametrize("meta,expected", [
    ({"weights_repo": "o/r"}, True),
    ({"model_url": "https://huggingface.co/o/r"}, True),
    ({"weights_note": "Open weights coming soon"}, False),
    ({"weights_note": "closed"}, False),
    ({}, False),
])
def test_open_weights(meta, expected):
    assert report.has_open_weights(meta) is expected


def test_repo_from_url():
    assert report.repo_from_url("https://huggingface.co/eljiwo/jiwo-0.8b") == "eljiwo/jiwo-0.8b"
    assert report.repo_from_url("https://huggingface.co/eljiwo/jiwo-0.8b/tree/main") == "eljiwo/jiwo-0.8b"
    assert report.repo_from_url("https://example.com/x") is None
    assert report.repo_from_url(None) is None


def test_render_markdown_carries_the_requested_columns():
    tiers = report.build_rows(
        _index([_model("m", 3.0, 50, repo="o/r", url="https://huggingface.co/o/r")]),
        with_license=False, top=5)
    text = report.render_markdown(tiers, with_license=True)

    for column in ("Modele", "Taille servie", "`balanced_skill`", "Depot des poids",
                   "Base", "Licence", "Poids ouverts", "Voie de service"):
        assert column in text
    assert "### Palier 2-4B" in text


def test_json_dump_is_serialisable():
    tiers = report.build_rows(_index([_model("m", 3.0, 50)]), with_license=False, top=5)
    json.dumps(tiers)  # ne doit pas lever
