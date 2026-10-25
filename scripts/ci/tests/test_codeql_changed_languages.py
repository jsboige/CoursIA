"""Tests de `codeql_changed_languages` (issue #22548).

Contrat verifie ici, dans cet ordre :

1. **controle positif** : un diff qui ne touche qu'un fichier Python donne une
   matrice a UNE entree, pas quatre — c'est tout le gain de la derivation ;
2. **controle negatif** : un diff de carnet / markdown / Lean ne donne aucun
   langage, et la derivation rend alors la matrice complete (fail-open), pas
   une matrice vide qui ferait echouer `fromJSON` ;
3. **fail-open** : un `git fetch` en echec ou un diff illisible rend les quatre
   langages et le DIT dans la raison ;
4. **hors PR** (`push`, `schedule`) : matrice complete sans meme lire un diff —
   le lecteur injecte ne doit pas etre appele ;
5. l'entree `csharp` porte `build_mode: none` (arbitrage de cout de #22548),
   et l'ordre de la matrice est stable.
"""
import importlib.util
import json
from pathlib import Path

_SPEC = importlib.util.spec_from_file_location(
    "codeql_changed_languages",
    Path(__file__).resolve().parents[1] / "codeql_changed_languages.py",
)
mod = importlib.util.module_from_spec(_SPEC)
_SPEC.loader.exec_module(mod)


def test_positive_control_python_only():
    matrix, reason = mod.derive(
        "pull_request", "main", diff_paths=lambda _ref: ["scripts/ci/foo.py"]
    )
    assert [item["language"] for item in matrix] == ["python"]
    assert reason.startswith("langages touches :")


def test_negative_control_notebook_only_falls_back_to_full_matrix():
    paths = ["MyIA.AI.Notebooks/Sudoku/Sudoku-01.ipynb", "README.md",
             "MyIA.AI.Notebooks/Lean/Foo.lean"]
    matrix, reason = mod.derive("pull_request", "main", diff_paths=lambda _ref: paths)
    assert [item["language"] for item in matrix] == [
        "actions", "csharp", "javascript-typescript", "python"
    ]
    assert "aucun langage reconnu" in reason


def test_workflows_paths_select_the_actions_language():
    matrix, _ = mod.derive(
        "pull_request", "main",
        diff_paths=lambda _ref: [".github/workflows/foo.yml"],
    )
    assert [item["language"] for item in matrix] == ["actions"]


def test_csharp_variants_and_the_no_build_decision():
    for path in ("./a/b.cs", "Proj/App.csproj", "Proj/App.sln", "Web/View.cshtml"):
        matrix, _ = mod.derive("pull_request", "main", diff_paths=lambda _ref, p=path: [p])
        assert matrix == [{"language": "csharp", "build_mode": "none"}], path


def test_javascript_family_is_one_language():
    matrix, _ = mod.derive(
        "pull_request", "main",
        diff_paths=lambda _ref: ["a.js", "b.mjs", "c.ts", "d.tsx"],
    )
    assert [item["language"] for item in matrix] == ["javascript-typescript"]


def test_matrix_keeps_the_declared_order():
    matrix, _ = mod.derive(
        "pull_request", "main",
        diff_paths=lambda _ref: ["z.py", ".github/workflows/x.yml", "y.cs"],
    )
    assert [item["language"] for item in matrix] == ["actions", "csharp", "python"]


def test_fail_open_on_unreadable_diff():
    def boom(_ref):
        raise RuntimeError("fetch refuse")

    matrix, reason = mod.derive("pull_request", "main", diff_paths=boom)
    assert len(matrix) == 4
    assert "diff illisible" in reason


def test_non_pr_event_never_reads_a_diff():
    calls = []

    def reader(ref):
        calls.append(ref)
        return ["only.py"]

    matrix, reason = mod.derive("push", "main", diff_paths=reader)
    assert len(matrix) == 4
    assert calls == []
    assert "push" in reason


def test_github_output_receives_the_matrix(tmp_path, monkeypatch, capsys):
    out = tmp_path / "gh_output"
    monkeypatch.setenv("GITHUB_OUTPUT", str(out))
    monkeypatch.setenv("EVENT_NAME", "schedule")
    monkeypatch.setenv("BASE_REF", "main")
    rc = mod.main(["--event", "schedule"])
    assert rc == 0
    written = out.read_text(encoding="utf-8").strip()
    assert written.startswith("languages=")
    payload = json.loads(written.split("=", 1)[1])
    assert [item["language"] for item in payload] == [
        "actions", "csharp", "javascript-typescript", "python"
    ]
    assert "matrix:" in capsys.readouterr().out


def test_unwritable_output_is_named_not_silent(tmp_path):
    blocker = tmp_path / "dir"
    blocker.mkdir()
    rc = mod.main(["--event", "schedule", "--github-output", str(blocker)])
    assert rc == mod.EXIT_BROKEN


def test_output_is_absent_when_no_github_output(monkeypatch, capsys):
    monkeypatch.delenv("GITHUB_OUTPUT", raising=False)
    rc = mod.main(["--event", "push", "--json"])
    assert rc == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["languages"] and payload["reason"]


def test_empty_path_list_is_not_an_error():
    matrix, reason = mod.derive("pull_request", "main", diff_paths=lambda _ref: [])
    assert len(matrix) == 4
    assert "aucun langage reconnu" in reason


def test_languages_for_ignores_blank_entries():
    assert mod.languages_for(["", "  ", "a.py"]) == {"python"}


class _FakeResponse:
    """Reponse HTTP minimale : `with ... as r: r.read()`."""

    def __init__(self, payload):
        self._body = json.dumps(payload).encode("utf-8")

    def read(self):
        return self._body

    def __enter__(self):
        return self

    def __exit__(self, *exc):
        return False


def _opener(pages):
    """Rend un faux `urlopen` qui sert `pages` dans l'ordre, une par appel."""
    state = {"i": 0}

    def open_url(_request, timeout=None):
        page = pages[state["i"]] if state["i"] < len(pages) else []
        state["i"] += 1
        return _FakeResponse(page)

    return open_url


def test_api_reads_the_pr_file_list():
    opener = _opener([[{"filename": "a.py"}, {"filename": "README.md"}]])
    assert mod._api_pr_paths("jsboige/CoursIA", 7, None, opener=opener) == [
        "a.py", "README.md"
    ]


def test_api_paginates_until_a_short_page():
    pages = [[{"filename": "a.py"}], [{"filename": "b.cs"}], []]
    got = mod._api_pr_paths("o/r", 7, None, opener=_opener(pages), per_page=1)
    assert got == ["a.py", "b.cs"]


def test_api_truncation_raises_so_the_caller_fails_open(monkeypatch):
    monkeypatch.setattr(mod, "API_FILE_CAP", 2)
    pages = [[{"filename": "a.py"}], [{"filename": "b.py"}]]
    try:
        mod._api_pr_paths("o/r", 7, None, opener=_opener(pages), per_page=1)
    except ValueError as exc:
        assert "tronquee" in str(exc)
    else:  # pragma: no cover - le test doit echouer si la garde disparait
        raise AssertionError("un plafond atteint doit lever, pas rendre une liste partielle")


def test_api_failure_falls_back_to_the_full_matrix():
    def boom(_repo, _number, _token):
        raise OSError("API injoignable")

    matrix, reason = mod.derive("pull_request", "main", diff_paths=lambda _ref: boom("", 0, None))
    assert len(matrix) == 4
    assert "diff illisible" in reason
