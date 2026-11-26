"""Tests de `changed_notebooks` (#22468 tranche 2).

Contrat verifie ici, dans cet ordre :

1. **controle positif** : un diff de PR qui touche 2 carnets (parmi du
   Python et un carnet supprime) rend une portee restreinte aux 2 carnets
   presents dans l'arbre ;
2. **workflow_dispatch reste pleine arbre** (#13861) — le declencheur
   manuel existe pour revalider l'arbre final d'un batch, le restreindre
   casserait sa raison d'etre, et le lecteur de diff ne doit meme pas
   tourner ;
3. **fail-open** : lecteurs en echec -> pleine arbre avec les raisons
   nommees ; portee restreinte vide -> pleine arbre (ce qui preserve la
   garde #14799 en aval : un workspace casse rend zero .ipynb) ;
4. **push** : diff HEAD~1, chaine d'un seul maillon ;
5. **CLI** : le JSON sort sur stdout, la raison sur stderr.
"""
import importlib.util
import json
import sys
from pathlib import Path

_SPEC = importlib.util.spec_from_file_location(
    "changed_notebooks",
    Path(__file__).resolve().parents[1] / "changed_notebooks.py",
)
mod = importlib.util.module_from_spec(_SPEC)
_SPEC.loader.exec_module(mod)


def _tree(tmp_path):
    """Arbre minimal : 2 carnets valides + 1 checkpoint + 1 carnet racine."""
    (tmp_path / "serie" / "sub").mkdir(parents=True, exist_ok=True)
    (tmp_path / "serie" / ".ipynb_checkpoints").mkdir(parents=True, exist_ok=True)
    (tmp_path / "serie" / "a.ipynb").write_text("{}", encoding="utf-8")
    (tmp_path / "serie" / "sub" / "b.ipynb").write_text("{}", encoding="utf-8")
    (tmp_path / "serie" / ".ipynb_checkpoints" / "a-checkpoint.ipynb").write_text(
        "{}", encoding="utf-8")
    (tmp_path / "autre.py").write_text("x = 1", encoding="utf-8")


def test_positive_control_two_modified_notebooks(tmp_path):
    _tree(tmp_path)
    mode, nbs, reason = mod.scope(
        "pull_request", tree_root=str(tmp_path),
        readers=[("diff", lambda _b: [
            "serie/a.ipynb",
            "serie/sub/b.ipynb",
            "autre.py",
            "serie/supprime.ipynb",  # absent de l'arbre : carnet supprime
            "serie/.ipynb_checkpoints/a-checkpoint.ipynb",
        ])],
    )
    assert mode == "restricted"
    assert nbs == ["serie/a.ipynb", "serie/sub/b.ipynb"]
    assert "source diff" in reason and "2 carnet(s)" in reason


def test_workflow_dispatch_stays_full_tree(tmp_path):
    _tree(tmp_path)
    called = []

    def _reader(_base):
        called.append(1)
        return ["serie/a.ipynb"]

    mode, nbs, reason = mod.scope(
        "workflow_dispatch", tree_root=str(tmp_path),
        readers=[("diff", _reader)],
    )
    assert mode == "full"
    assert sorted(nbs) == ["serie/a.ipynb", "serie/sub/b.ipynb"]
    assert called == []  # le lecteur ne tourne meme pas
    assert "#13861" in reason


def test_unknown_event_falls_back_to_full(tmp_path):
    _tree(tmp_path)
    mode, nbs, reason = mod.scope("", tree_root=str(tmp_path))
    assert mode == "full"
    assert "non restreint" in reason


def test_reader_failure_chain_named_then_api(tmp_path):
    _tree(tmp_path)
    mode, nbs, reason = mod.scope(
        "pull_request", tree_root=str(tmp_path),
        readers=[
            ("diff HEAD^1", lambda _b: (_ for _ in ()).throw(
                RuntimeError("HEAD^1 inexistant"))),
            ("api", lambda _b: ["serie/a.ipynb"]),
        ],
    )
    assert mode == "restricted"
    assert nbs == ["serie/a.ipynb"]
    assert "source api" in reason


def test_all_readers_fail_full_tree_with_named_reasons(tmp_path):
    _tree(tmp_path)
    mode, nbs, reason = mod.scope(
        "pull_request", tree_root=str(tmp_path),
        readers=[
            ("diff HEAD^1", lambda _b: (_ for _ in ()).throw(
                RuntimeError("sha invalide"))),
            ("api", lambda _b: (_ for _ in ()).throw(
                OSError("HTTP 403 quota"))),
        ],
    )
    assert mode == "full"
    assert sorted(nbs) == ["serie/a.ipynb", "serie/sub/b.ipynb"]
    assert "sha invalide" in reason and "HTTP 403 quota" in reason


def test_empty_restricted_scope_falls_back_to_full(tmp_path):
    _tree(tmp_path)
    mode, nbs, reason = mod.scope(
        "pull_request", tree_root=str(tmp_path),
        readers=[("diff", lambda _b: ["autre.py"])],
    )
    assert mode == "full"
    assert "aucun carnet modifie" in reason


def test_push_uses_head1_diff(tmp_path):
    _tree(tmp_path)
    seen = {}

    def _reader(base):
        seen["base"] = base
        return ["serie/sub/b.ipynb"]

    mode, nbs, _reason = mod.scope(
        "push", tree_root=str(tmp_path), readers=[("diff HEAD~1", _reader)],
    )
    assert mode == "restricted"
    assert nbs == ["serie/sub/b.ipynb"]
    assert seen["base"] == "HEAD~1"


def test_cli_json_on_stdout_reason_on_stderr(tmp_path, capsys, monkeypatch):
    monkeypatch.chdir(tmp_path)
    _tree(tmp_path)
    rc = mod.main(["--event", "workflow_dispatch"])
    assert rc == 0
    captured = capsys.readouterr()
    payload = json.loads(captured.out)
    assert payload["mode"] == "full"
    assert sorted(payload["notebooks"]) == [
        "serie/a.ipynb", "serie/sub/b.ipynb"]
    assert "#13861" in captured.err
