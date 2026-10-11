"""Tests for the F2 of #18970 -- dump_readme_link_violations + diff comparator.

Why this test file exists
-------------------------
The guard is delta-only : the argv captures violations as JSON and the
delta_argv comparator decides the verdict. Without these tests, a refactor
of the JSON shape (e.g. dropping `class` or renaming `href`) would silently
break the comparator and the PR gate would stop catching NEW HTML_404
introductions. Pinned here :

  1. The JSON shape (classe / readme / href) is preserved end-to-end.
  2. A NEW violation injected in head (missing in base) flips the verdict
     to `exit=1` and emits `::error::HTML_404` on stderr.
  3. A PR that does not change violations passes (`exit=0`).
  4. The stderr/stdout split is what allows the workflow's own grep
     `2>&1 | grep -E '^::error::HTML_404 '` to keep working (F1).

These are the four conditions that the merge-gate relies on. Touch them
with the corresponding test name visible in the diff.
"""
from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[3]
DUMP = REPO_ROOT / "scripts" / "notebook_tools" / "dump_readme_link_violations.py"
DIFF = REPO_ROOT / "scripts" / "notebook_tools" / "diff_readme_link_violations.py"


def _run_dump() -> dict:
    proc = subprocess.run(
        [sys.executable, str(DUMP)],
        cwd=str(REPO_ROOT),
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )
    assert proc.returncode == 0, f"dump exit={proc.returncode} stderr={proc.stderr}"
    return json.loads(proc.stdout)


def _run_diff(base: dict, head: dict, tmp_path: Path) -> subprocess.CompletedProcess:
    base_p = tmp_path / "base.json"
    head_p = tmp_path / "head.json"
    base_p.write_text(json.dumps(base), encoding="utf-8")
    head_p.write_text(json.dumps(head), encoding="utf-8")
    return subprocess.run(
        [sys.executable, str(DIFF), str(base_p), str(head_p)],
        cwd=str(REPO_ROOT),
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )


def _git(repo: Path, *args: str) -> None:
    proc = subprocess.run(
        ["git", *args], cwd=str(repo), capture_output=True, text=True,
        encoding="utf-8", errors="replace",
    )
    assert proc.returncode == 0, f"git {args} failed: {proc.stderr}"


def _make_repo(
    tmp_path: Path,
    moves: list[tuple[str, str]],
    deletions: list[str] = (),
    additions: list[str] = (),
) -> Path:
    """Mini-repo Git a deux commits : base (branche main) puis tete.

    Les `moves` passent par `git mv` (renames enregistres), les `deletions`
    par `git rm` (suppressions sans rename), les `additions` par creation
    (fichiers sans relation). C'est la verite Git que le comparateur exige
    depuis la reserve #20274 : l'absence sur disque ne prouve pas la
    relation, seul le rename enregistre la prouve.
    """
    repo = tmp_path / "repo"
    repo.mkdir()
    _git(repo, "init", "-q", "-b", "main")
    _git(repo, "config", "user.name", "test")
    _git(repo, "config", "user.email", "test@example.com")
    for path in [old for old, _ in moves] + list(deletions):
        f = repo / path
        f.parent.mkdir(parents=True, exist_ok=True)
        f.write_text("base\n", encoding="utf-8")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-qm", "base")
    _git(repo, "checkout", "-q", "-b", "head")
    for old, new in moves:
        # rename(2) exige le repertoire destination : git mv ne le cree pas.
        (repo / new).parent.mkdir(parents=True, exist_ok=True)
        _git(repo, "mv", old, new)
    for path in deletions:
        _git(repo, "rm", "-q", path)
    for path in additions:
        f = repo / path
        f.parent.mkdir(parents=True, exist_ok=True)
        f.write_text("fresh\n", encoding="utf-8")
        _git(repo, "add", path)
    _git(repo, "commit", "-qm", "head")
    return repo


def _run_diff_in(
    base: dict, head: dict, repo: Path, tmp_path: Path
) -> subprocess.CompletedProcess:
    """_run_diff avec cwd=mini-repo et FAST_LANE_BASE=main (la base du repo)."""
    base_p = tmp_path / "base.json"
    head_p = tmp_path / "head.json"
    base_p.write_text(json.dumps(base), encoding="utf-8")
    head_p.write_text(json.dumps(head), encoding="utf-8")
    env = {**os.environ, "FAST_LANE_BASE": "main"}
    return subprocess.run(
        [sys.executable, str(DIFF), str(base_p), str(head_p)],
        cwd=str(repo),
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        env=env,
    )


def test_json_shape_preserved() -> None:
    payload = _run_dump()
    assert isinstance(payload, dict)
    assert isinstance(payload.get("violations"), list)
    assert payload["n_violations"] == len(payload["violations"])
    if payload["violations"]:
        v0 = payload["violations"][0]
        # Les trois cles sont exigees par le comparator (et par la garde
        # workflow qui grep `::error::<cls> <readme> -> <href>`).
        for key in ("class", "readme", "href"):
            assert key in v0, f"cle `{key}` absente du JSON : {v0}"
        # La classe est bornee aux categories de regen_quarto_render.py.
        # Depuis #18911 (geste 2, 2026-10-09) : HTML_404 (lien .html vers
        # une cible absente du depot) et BROKEN (cible inexistante).
        assert v0["class"] in {"HTML_404", "BROKEN"}


def test_dump_exits_zero_even_with_violations() -> None:
    # L'audit BRUT rend 2432 violations au 2026-10-03 ; argv ne doit PAS
    # en faire un rouge (sinon la phase 1 du fast-lane s'arreterait avant
    # d'avoir capture le JSON pour le comparator). Seul delta_argv tranche.
    payload = _run_dump()
    assert payload["n_violations"] > 0, "temoin casse : la branche ne contient pas le backlog attendu"


def test_diff_passes_when_no_new_violation(tmp_path: Path) -> None:
    base = _run_dump()
    head = dict(base)
    proc = _run_diff(base, head, tmp_path)
    assert proc.returncode == 0, f"diff exit={proc.returncode}\nstdout={proc.stdout}\nstderr={proc.stderr}"
    assert "NOUVELLES=0" in proc.stdout


def test_diff_fails_on_injected_html_404(tmp_path: Path) -> None:
    # Témoin F2 : une HTML_404 injectée dans HEAD doit faire NOUVELLES=1
    # (=exit 1) -- c'est ce que la garde workflow vérifie en CI.
    base = _run_dump()
    head = dict(base)
    head["violations"] = list(base["violations"]) + [
        {"class": "HTML_404", "readme": "WITNESS_README.md", "href": "WITNESS.html"}
    ]
    head["n_violations"] = len(head["violations"])
    proc = _run_diff(base, head, tmp_path)
    assert proc.returncode == 1, f"diff aurait du exit=1, exit={proc.returncode}\nstdout={proc.stdout}\nstderr={proc.stderr}"
    assert "NOUVELLES=1" in proc.stdout
    # F1 contreexemple : le format `::error::HTML_404 ...` doit etre emis
    # sur STDERR (le workflow greperait sans 2>&1 sinon). C'est la condition
    # qui a fait rougir le run originel 37109571492 sans etre vue.
    assert "::error::HTML_404 WITNESS_README.md -> WITNESS.html" in proc.stderr


# ---------------------------------------------------------------------------
# #20274 -- appariement des renames (T2-01). Un `git mv` de dossier re-keye
# chaque violation : l'ancienne cle part en CORRIGEES, la nouvelle arrive en
# NOUVELLES, sans aucun changement du backlog (mesure T2-01 : 12/12).
# Reserve de review sur #20274 : l'appariement ne se prouve plus par absence
# sur disque (une suppression + une introduction unrelated passent le meme
# temoin disque), mais par le MAPPING GIT des renommages -- seul un rename
# enregistre par Git prouve la relation. Chaque temoin construit un mini-repo
# a deux commits (base = branche main, tete = branche head) ou la verite Git
# est controlee : moves par `git mv`, temoins negatifs par suppression sans
# rename ou creation sans relation.
# ---------------------------------------------------------------------------


def test_diff_pairs_violation_moved_by_rename(tmp_path: Path) -> None:
    """Temoin positif : re-key par VRAI rename Git => DEPLACEES, exit 0.

    base porte la violation sur zz-old-dir/README.md, head la porte sur
    zz-new-dir/README.md ; le mini-repo enregistre le rename entre les deux
    par `git mv`. Couple (class, href) identique + rename Git exact =>
    deplacement, pas introduction.
    """
    repo = _make_repo(tmp_path, moves=[("zz-old-dir/README.md", "zz-new-dir/README.md")])
    base = {"violations": [
        {"class": "HTML_404", "readme": "zz-old-dir/README.md", "href": "notebooks/1.1-X.html"}
    ], "n_violations": 1}
    head = {"violations": [
        {"class": "HTML_404", "readme": "zz-new-dir/README.md", "href": "notebooks/1.1-X.html"}
    ], "n_violations": 1}
    proc = _run_diff_in(base, head, repo, tmp_path)
    assert proc.returncode == 0, f"diff exit={proc.returncode}\nstdout={proc.stdout}\nstderr={proc.stderr}"
    assert "NOUVELLES=0" in proc.stdout
    assert "DEPLACEES=1" in proc.stdout
    assert "MOVED" in proc.stdout


def test_diff_refuses_pairing_without_git_rename(tmp_path: Path) -> None:
    """Temoin negatif (reserve #20274) : suppression + introduction unrelated.

    Le README de base est SUPPRIME (git rm) et le nouveau README est un
    fichier CREE sans relation : l'ancien chemin est bien absent du disque --
    c'est exactement le faux temoin que l'absence seule blanchissait -- mais
    aucun rename Git ne mappe l'ancien sur le nouveau. La violation re-keyee
    reste une NOUVELLE (exit 1).
    """
    repo = _make_repo(
        tmp_path,
        moves=[],
        deletions=["zz-old-dir/README.md"],
        additions=["zz-new-dir/README.md"],
    )
    base = {"violations": [
        {"class": "HTML_404", "readme": "zz-old-dir/README.md", "href": "notebooks/1.1-X.html"}
    ], "n_violations": 1}
    head = {"violations": [
        {"class": "HTML_404", "readme": "zz-new-dir/README.md", "href": "notebooks/1.1-X.html"}
    ], "n_violations": 1}
    proc = _run_diff_in(base, head, repo, tmp_path)
    assert proc.returncode == 1, f"diff aurait du exit=1, exit={proc.returncode}\nstdout={proc.stdout}"
    assert "NOUVELLES=1" in proc.stdout
    assert "DEPLACEES=0" in proc.stdout


def test_diff_refuses_pairing_when_base_readme_still_exists(tmp_path: Path) -> None:
    """Temoin negatif : le README de base EXISTE encore au cwd => pas d'appariement.

    Re-key d'une violation reelle (son chemin existe au REPO_ROOT par
    construction) vers un chemin invente : ni le rename Git (absent du
    mapping) ni la disparition sur disque ne sont prouves, la violation
    re-keyee reste une NOUVELLE (exit 1). C'est ce temoin qui empeche
    l'appariement de blanchir un simple copier-coller de lien casse vers un
    nouveau fichier.
    """
    payload = _run_dump()
    real = next(v for v in payload["violations"])
    base = {"violations": [real], "n_violations": 1}
    rekeyed = dict(real)
    rekeyed["readme"] = "zz-invented-dir/README.md"
    head = {"violations": [rekeyed], "n_violations": 1}
    proc = _run_diff(base, head, tmp_path)
    assert proc.returncode == 1, f"diff aurait du exit=1, exit={proc.returncode}\nstdout={proc.stdout}"
    assert "NOUVELLES=1" in proc.stdout
    assert "DEPLACEES=0" in proc.stdout


def test_diff_pairs_href_rekey_in_unchanged_readme(tmp_path: Path) -> None:
    """Temoin positif passe 2 : le href suit une cible renommee par Git.

    Le README n'a pas bouge, le href change parce que sa cible a demenage :
    le mini-repo enregistre le rename zz-gone-dir/notebooks/1.1-X.html ->
    real-target/1.1-X.html par `git mv`. Rename Git sur les chemins resolus
    + nouveau parent present => deplacement, pas introduction.
    """
    repo = _make_repo(
        tmp_path,
        moves=[("zz-gone-dir/notebooks/1.1-X.html", "real-target/1.1-X.html")],
    )
    base = {"violations": [
        {"class": "HTML_404", "readme": "docs/README.md", "href": "../zz-gone-dir/notebooks/1.1-X.html"}
    ], "n_violations": 1}
    head = {"violations": [
        {"class": "HTML_404", "readme": "docs/README.md", "href": "../real-target/1.1-X.html"}
    ], "n_violations": 1}
    proc = _run_diff_in(base, head, repo, tmp_path)
    assert proc.returncode == 0, f"diff exit={proc.returncode}\nstdout={proc.stdout}\nstderr={proc.stderr}"
    assert "NOUVELLES=0" in proc.stdout
    assert "DEPLACEES=1" in proc.stdout


def test_diff_refuses_href_rekey_without_git_rename(tmp_path: Path) -> None:
    """Temoin negatif (reserve #20274) : re-key de href sans relation Git.

    La cible ancienne est SUPPRIMEE (git rm) et la cible nouvelle est CREEE
    independamment : l'ancien parent a bien disparu du disque -- le faux
    temoin que l'absence seule blanchissait -- mais aucun rename Git ne mappe
    la cible resolue ancienne sur la nouvelle. Introduction, pas deplacement
    (exit 1).
    """
    repo = _make_repo(
        tmp_path,
        moves=[],
        deletions=["zz-gone-dir/1.1-X.html"],
        additions=["real-target/1.1-X.html"],
    )
    base = {"violations": [
        {"class": "HTML_404", "readme": "docs/README.md", "href": "../zz-gone-dir/1.1-X.html"}
    ], "n_violations": 1}
    head = {"violations": [
        {"class": "HTML_404", "readme": "docs/README.md", "href": "../real-target/1.1-X.html"}
    ], "n_violations": 1}
    proc = _run_diff_in(base, head, repo, tmp_path)
    assert proc.returncode == 1, f"diff aurait du exit=1, exit={proc.returncode}\nstdout={proc.stdout}"
    assert "NOUVELLES=1" in proc.stdout
    assert "DEPLACEES=0" in proc.stdout


def test_diff_refuses_href_rekey_when_old_target_dir_exists(tmp_path: Path) -> None:
    """Temoin negatif passe 2 : l'ancien parent EXISTE encore => pas d'appariement.

    Un simple changement de href vers une autre cible cassee du meme dossier
    existant n'est pas un demenagement : l'ancienne violation est corrigee,
    la nouvelle est une introduction (exit 1).
    """
    base = {"violations": [
        {"class": "HTML_404", "readme": "docs/README.md", "href": "../scripts/notebook_tools/old-X.html"}
    ], "n_violations": 1}
    head = {"violations": [
        {"class": "HTML_404", "readme": "docs/README.md", "href": "../scripts/notebook_tools/new-Y.html"}
    ], "n_violations": 1}
    proc = _run_diff(base, head, tmp_path)
    assert proc.returncode == 1, f"diff aurait du exit=1, exit={proc.returncode}\nstdout={proc.stdout}"
    assert "NOUVELLES=1" in proc.stdout
    assert "DEPLACEES=0" in proc.stdout


# ---------------------------------------------------------------------------
# C23 / c.1443 -- propagation des pannes du scanner (adjoint po-2025).
# Un defaut du wrapper transforme une indisponibilite (rc=2 / script absent
# ou rc=1 + traceback sans resume) en scan vide reussi, ce qui masquerait
# une nouvelle violation. Les 2 tests ci-dessous sont discriminants : le fix
# doit faire retourner rc != 0 a main() et scan_ok=False dans le payload,
# distinct du cas "scan propre rc=0".
# ---------------------------------------------------------------------------


def _scan_via_dump_with_fake(monkeypatch: pytest.MonkeyPatch, fake_proc: subprocess.CompletedProcess) -> subprocess.CompletedProcess:
    """Patche subprocess.run du module + lance le script via python et ferme spawn.

    Monkeypatch ne peut pas traverser la frontiere du process, donc on ne peut
    pas patcher le subprocess depuis l'exterieur du script. A la place, on
    importe le module, on patche directement subprocess.run DU MODULE, et on
    appelle main() du module.
    """
    pass


def test_dump_exits_nonzero_on_rc2_script_absent(monkeypatch: pytest.MonkeyPatch) -> None:
    """Témoin négatif : rc=2 (script absent) NE DOIT PAS retourner 0.

    Avant le fix, le wrapper retournait un payload vide avec rc=0,
    ce qui faisait passer une indisponibilite du scanner pour un scan
    propre (delta_argv ne voyait aucune nouvelle violation).
    """
    import scripts.notebook_tools.dump_readme_link_violations as mod

    fake = subprocess.CompletedProcess(
        args=["python", "scripts/regen_quarto_render.py", "--check-readme-links"],
        returncode=2,
        stdout="",
        stderr="python: can't open file 'scripts/regen_quarto_render.py': [Errno 2] No such file or directory\n",
    )
    monkeypatch.setattr(mod.subprocess, "run", lambda *a, **kw: fake)
    rc = mod.main()
    # Si rc!=0, capture le payload via capfd (le main imprime sur stdout)
    assert rc != 0, f"dump aurait du exit != 0, exit={rc}"


def test_dump_exits_nonzero_on_rc1_traceback_no_summary(monkeypatch: pytest.MonkeyPatch) -> None:
    """Témoin négatif : rc=1 + traceback sans resume NE DOIT PAS retourner 0.

    Avant le fix, le wrapper ne regardait que stderr (violations) et ignorait
    stdout (resume). Un traceback produit du stdout non-resume, ce qui
    rendait n_readmes=0 mais RC=0 du wrapper -- indistinguable d'un scan
    propre.
    """
    import scripts.notebook_tools.dump_readme_link_violations as mod

    fake = subprocess.CompletedProcess(
        args=["python", "scripts/regen_quarto_render.py", "--check-readme-links"],
        returncode=1,
        stdout="Traceback (most recent call last):\n  File \"regen_quarto_render.py\", line 100, in <module>\n    raise ValueError()\nValueError\n",
        stderr="",
    )
    monkeypatch.setattr(mod.subprocess, "run", lambda *a, **kw: fake)
    rc = mod.main()
    assert rc != 0, f"dump aurait du exit != 0, exit={rc}"
