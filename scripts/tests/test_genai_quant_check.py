"""Tests du branchement `genai.py quant check` sur l'organe doc <-> quant (#23252).

La commande ne mesure rien elle-même : elle délègue. Ces tests vérifient donc la
**délégation** (code de sortie repris, argv transmis) et non le verdict, qui est
couvert par `test_check_quant_doc_divergence.py`.

Enjeu réel : `genai-config.md` renvoie à `genai.py quant summary` comme geste de
vérification, alors que `summary` décrit la configuration DÉCLARÉE. Sans ce
branchement, le harnais pointe vers un geste qui ne mesure pas — le défaut relevé
par la relecture Hermes de #23238.
"""
from __future__ import annotations

import argparse
import sys
import types
from pathlib import Path

_SRC = Path(__file__).resolve().parents[1] / "genai-stack"
if str(_SRC) not in sys.path:
    sys.path.insert(0, str(_SRC))

from commands import quant  # noqa: E402  (apres l'insertion du chemin)


def _fake_organ(monkeypatch, rc: int) -> list[list[str] | None]:
    calls: list[list[str] | None] = []
    fake = types.ModuleType("check_quant_doc_divergence")

    def _main(argv=None):
        calls.append(argv)
        return rc

    fake.main = _main
    monkeypatch.setitem(sys.modules, "check_quant_doc_divergence", fake)
    return calls


def test_check_reprend_le_code_de_sortie_de_l_organe(monkeypatch) -> None:
    calls = _fake_organ(monkeypatch, rc=1)
    args = argparse.Namespace(quant_action="check", json=False, as_of=None)
    assert quant.execute(args) == 1
    assert calls == [[]]


def test_check_transmet_json_et_as_of(monkeypatch) -> None:
    calls = _fake_organ(monkeypatch, rc=0)
    args = argparse.Namespace(quant_action="check", json=True, as_of="c7b94f43bda")
    assert quant.execute(args) == 0
    assert calls == [["--json", "--as-of", "c7b94f43bda"]]


def test_check_est_une_sous_commande_distincte_de_summary(monkeypatch) -> None:
    """`summary` décrit la configuration déclarée : il ne doit pas appeler l'organe."""
    calls = _fake_organ(monkeypatch, rc=1)
    monkeypatch.setattr(quant, "show_summary", lambda: None)
    assert quant.execute(argparse.Namespace(quant_action="summary")) == 0
    assert calls == []


def test_register_expose_check() -> None:
    parser = argparse.ArgumentParser()
    quant.register(parser.add_subparsers(dest="cmd"))
    args = parser.parse_args(["quant", "check", "--json"])
    assert args.quant_action == "check"
    assert args.json is True
    assert args.as_of is None
