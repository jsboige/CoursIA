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
import io
import json
import urllib.error
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


def _http_error(code, body=b'{"message":"Resource not accessible by integration"}'):
    return urllib.error.HTTPError(
        "https://api.github.com/x", code, "err", {}, io.BytesIO(body)
    )


def test_describe_names_the_status_not_just_the_type():
    """Premiere mesure en CI : « diff illisible (HTTPError) » ne disait ni 403
    ni 404, et ces deux causes n'ont pas le meme remede."""
    text = mod._describe(_http_error(403))
    assert "HTTP 403" in text
    assert "Resource not accessible" in text


def test_describe_of_a_non_http_error_keeps_the_message():
    assert "git casse" in mod._describe(RuntimeError("git casse"))


def test_retry_gives_a_second_chance_on_secondary_rate_limit(monkeypatch):
    monkeypatch.setattr(mod.time, "sleep", lambda _s: None)
    calls = {"n": 0}

    def flaky(_request, timeout=None):
        calls["n"] += 1
        if calls["n"] == 1:
            raise _http_error(403, b'{"message":"You have exceeded a secondary rate limit"}')
        return "reponse"

    assert mod._fetch_with_retry(flaky, "req") == "reponse"
    assert calls["n"] == 2


def test_retry_does_not_retry_a_not_found(monkeypatch):
    monkeypatch.setattr(mod.time, "sleep", lambda _s: None)
    calls = {"n": 0}

    def opener(_request, timeout=None):
        calls["n"] += 1
        raise _http_error(404, b'{"message":"Not Found"}')

    try:
        mod._fetch_with_retry(opener, "req")
    except urllib.error.HTTPError as exc:
        assert exc.code == 404
    else:  # pragma: no cover
        raise AssertionError("un 404 doit remonter tout de suite")
    assert calls["n"] == 1


def test_retry_gives_up_after_the_budget(monkeypatch):
    monkeypatch.setattr(mod.time, "sleep", lambda _s: None)
    calls = {"n": 0}

    def always_503(_request, timeout=None):
        calls["n"] += 1
        raise _http_error(503, b"{}")

    try:
        mod._fetch_with_retry(always_503, "req", attempts=3)
    except urllib.error.HTTPError as exc:
        assert exc.code == 503
    else:  # pragma: no cover
        raise AssertionError("un 503 permanent doit lever")
    assert calls["n"] == 3


# --- Chaine de sources : git local d'abord, API en repli -------------------
#
# Mesure du 2026-10-25 sur la PR #22553, job `CodeQL changed languages` :
# `HTTP 403 {"message": "API rate limit exceeded for installation"}`. Le quota
# est partage par toute la flotte, donc l'API ne peut pas etre la source
# primaire — sinon la derivation retombe sur la matrice complete des que le
# trafic des autres lanes monte, et le gain de #22548 disparait sans un mot.


def test_chain_uses_git_first_and_never_calls_the_api():
    calls = []

    def git_reader(_ref):
        calls.append("git")
        return ["a.py"]

    def api_reader(_ref):
        calls.append("API")
        return ["a.py", "b.cs", "c.ts", ".github/workflows/x.yml"]

    matrix, reason = mod.derive(
        "pull_request", "main",
        readers=[("git HEAD^1", git_reader), ("API", api_reader)],
    )
    assert [item["language"] for item in matrix] == ["python"]
    assert calls == ["git"], "l'API ne doit pas etre appelee quand git repond"
    assert "[source git HEAD^1]" in reason


def test_chain_falls_back_to_the_api_when_git_cannot_resolve():
    def git_reader(_ref):
        raise RuntimeError("fatal: ambiguous argument 'HEAD^1'")

    def api_reader(_ref):
        return ["b.cs"]

    matrix, reason = mod.derive(
        "pull_request", "main",
        readers=[("git HEAD^1", git_reader), ("API", api_reader)],
    )
    assert matrix == [{"language": "csharp", "build_mode": "none"}]
    assert "[source API]" in reason


def test_chain_names_every_failure_before_failing_open():
    """Une chaine qui echoue doit nommer ses deux maillons, pas le dernier."""
    def git_reader(_ref):
        raise RuntimeError("fatal: ambiguous argument 'HEAD^1'")

    def api_reader(_ref):
        raise _http_error(403, b'{"message":"API rate limit exceeded for installation"}')

    matrix, reason = mod.derive(
        "pull_request", "main",
        readers=[("git HEAD^1", git_reader), ("API", api_reader)],
    )
    assert len(matrix) == 4
    assert "git HEAD^1: RuntimeError" in reason
    assert "API: HTTPError: HTTP 403" in reason
    assert "rate limit exceeded for installation" in reason


def test_main_prefers_git_over_the_api_when_both_are_configured(monkeypatch, tmp_path,
                                                                 capsys):
    """Le cablage de `main`, pas seulement `derive` : c'est lui qui decide."""
    seen = []

    def fake_local(rev):
        seen.append(("git", rev))
        return [".github/workflows/foo.yml"]

    def fake_api(_repo, _number, _token, **_kw):
        seen.append(("api", _number))
        return ["a.py"]

    monkeypatch.setattr(mod, "_local_diff_paths", fake_local)
    monkeypatch.setattr(mod, "_api_pr_paths", fake_api)
    out = tmp_path / "gh_output"
    rc = mod.main([
        "--event", "pull_request", "--git-base", "HEAD^1",
        "--repo", "jsboige/CoursIA", "--pr", "22553",
        "--github-output", str(out), "--json",
    ])
    assert rc == 0
    assert seen == [("git", "HEAD^1")]
    payload = json.loads(capsys.readouterr().out)
    assert payload["languages"] == [{"language": "actions"}]
    assert "[source git HEAD^1]" in payload["reason"]


def test_local_diff_paths_reads_a_real_two_commit_history(tmp_path, monkeypatch):
    """Controle positif de la commande elle-meme, dans un depot jetable.

    Le test ne touche jamais le clone du projet : un `git diff` lance dans le
    depot de travail mesurerait sa fraicheur, pas le code (lecon
    `test-that-shells-out-to-git-measures-the-clone`).
    """
    import subprocess

    def git(*args):
        subprocess.run(
            ["git", "-c", "user.email=t@example.invalid", "-c", "user.name=t",
             "-c", "init.defaultBranch=main", *args],
            cwd=tmp_path, check=True,
            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
        )

    git("init", "-q")
    (tmp_path / "base.py").write_text("x = 1\n", encoding="utf-8")
    git("add", ".")
    git("commit", "-q", "-m", "base")
    (tmp_path / "added.cs").write_text("class A {}\n", encoding="utf-8")
    git("add", ".")
    git("commit", "-q", "-m", "change")

    monkeypatch.chdir(tmp_path)
    assert mod._local_diff_paths("HEAD^1") == ["added.cs"]

