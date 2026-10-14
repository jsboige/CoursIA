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


def _run_diff(base: dict, head: dict, tmp_path: Path,
              cwd: Path | None = None,
              shas: tuple[str, str] | None = None) -> subprocess.CompletedProcess:
    base_p = tmp_path / "base.json"
    head_p = tmp_path / "head.json"
    base_p.write_text(json.dumps(base), encoding="utf-8")
    head_p.write_text(json.dumps(head), encoding="utf-8")
    cmd = [sys.executable, str(DIFF), str(base_p), str(head_p)]
    if shas is not None:
        cmd += ["--base-sha", shas[0], "--head-sha", shas[1]]
    return subprocess.run(
        cmd,
        cwd=str(cwd or REPO_ROOT),
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )


def _tmp_repo_with_rename(tmp_path: Path) -> tuple[Path, str, str]:
    """Depot git ephemere portant le discriminant complet du pairing.

    base : zz-old-dir (sera RENOMME via git mv -- preuve reelle),
    zz-deleted-dir (sera SUPPRIME -- pas un renommage), zz-other/README.md
    (sera SUPPRIME -- pas un renommage), zz-part-old (sera PARTIELLEMENT
    demenage : seul a.txt bouge, le README est supprime et un README au
    contenu radical different est cree -- FN 3), docs/README.md referent.
    head : git mv zz-old-dir zz-new-dir ; zz-deleted-dir parti et
    zz-unrelated-dir cree sans lien ; zz-other parti et zz-unrelated/
    README.md cree sans lien ; git mv zz-part-old/a.txt zz-part-new/a.txt
    puis zz-part-old supprime, zz-part-new/README.md (contenu different)
    et zz-part-new/deep/y.html crees. Rend (repo_cwd, base_sha, head_sha).
    """
    repo = tmp_path / "repo"
    repo.mkdir()

    def g(*args: str) -> None:
        subprocess.run(["git", "-c", "user.name=t", "-c", "user.email=t@t",
                        *args], cwd=repo, check=True, capture_output=True,
                       text=True, encoding="utf-8", errors="replace")

    def sha() -> str:
        return subprocess.run(["git", "rev-parse", "HEAD"], cwd=repo,
                              check=True, capture_output=True, text=True,
                              encoding="utf-8",
                              errors="replace").stdout.strip()

    g("init", "-q")
    (repo / "zz-old-dir" / "notebooks").mkdir(parents=True)
    (repo / "zz-old-dir" / "README.md").write_text("moved", encoding="utf-8")
    (repo / "zz-old-dir" / "notebooks" / "1.1-X.html").write_text("x",
                                                                 encoding="utf-8")
    (repo / "zz-deleted-dir").mkdir()
    (repo / "zz-deleted-dir" / "old-broken.html").write_text("y",
                                                             encoding="utf-8")
    (repo / "zz-other").mkdir()
    (repo / "zz-other" / "README.md").write_text("z", encoding="utf-8")
    (repo / "zz-part-old").mkdir()
    (repo / "zz-part-old" / "a.txt").write_text("pa", encoding="utf-8")
    (repo / "zz-part-old" / "README.md").write_text("part-base", encoding="utf-8")
    (repo / "zz-part-old" / "deep").mkdir()
    (repo / "zz-part-old" / "deep" / "b.txt").write_text(
        "contenu long et clairement distinct de la cible", encoding="utf-8")
    (repo / "docs").mkdir()
    (repo / "docs" / "README.md").write_text("ref", encoding="utf-8")
    g("add", "-A")
    g("commit", "-qm", "base")
    base_sha = sha()

    g("mv", "zz-old-dir", "zz-new-dir")
    g("rm", "-r", "-q", "zz-deleted-dir")
    (repo / "zz-unrelated-dir").mkdir()
    (repo / "zz-unrelated-dir" / "new-broken.html").write_text("u",
                                                               encoding="utf-8")
    g("rm", "-r", "-q", "zz-other")
    (repo / "zz-unrelated").mkdir()
    (repo / "zz-unrelated" / "README.md").write_text("v", encoding="utf-8")
    (repo / "zz-part-new").mkdir()
    g("mv", "zz-part-old/a.txt", "zz-part-new/a.txt")
    g("rm", "-r", "-q", "zz-part-old")
    (repo / "zz-part-new" / "README.md").write_text(
        "README radicalement different du precedant : sections et liens sans rapport",
        encoding="utf-8")
    (repo / "zz-part-new" / "deep").mkdir()
    (repo / "zz-part-new" / "deep" / "y.html").write_text("py",
                                                          encoding="utf-8")
    g("add", "-A")
    g("commit", "-qm", "head")
    head_sha = sha()
    return repo, base_sha, head_sha


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
# Depuis la revue adjointe du 2026-10-11 : un couple ne se classe MOVED que
# contre une PREUVE DE RENOMMAGE GIT (git diff --name-status -M base->head,
# passee par le fast-lane). Deux faux negatifs reproduits motivaient le
# durcissement : une suppression n'est pas un renommage. Les temoins
# ci-dessous tournent sur un depot git ephemere reel (_tmp_repo_with_rename)
# qui porte les deux cotes de CHAQUE discriminant.
# ---------------------------------------------------------------------------


def test_diff_pairs_violation_moved_by_git_rename(tmp_path: Path) -> None:
    """Temoin positif shape 1 : re-key par `git mv` PROUVE => DEPLACEES.

    Le README demenage (zz-old-dir -> zz-new-dir via git mv), href inchange :
    renommage de fichier exact dans la preuve git + README de base disparu
    du disque => deplacement, pas introduction (exit 0).
    """
    repo, base_sha, head_sha = _tmp_repo_with_rename(tmp_path)
    base = {"violations": [
        {"class": "HTML_404", "readme": "zz-old-dir/README.md", "href": "notebooks/1.1-X.html"}
    ], "n_violations": 1}
    head = {"violations": [
        {"class": "HTML_404", "readme": "zz-new-dir/README.md", "href": "notebooks/1.1-X.html"}
    ], "n_violations": 1}
    proc = _run_diff(base, head, tmp_path, cwd=repo, shas=(base_sha, head_sha))
    assert proc.returncode == 0, f"diff exit={proc.returncode}\nstdout={proc.stdout}\nstderr={proc.stderr}"
    assert "NOUVELLES=0" in proc.stdout
    assert "DEPLACEES=1" in proc.stdout
    assert "MOVED" in proc.stdout


def test_diff_pairs_href_rekey_by_git_dir_rename(tmp_path: Path) -> None:
    """Temoin positif shape 2 : le href suit un dossier que git prouve deplace.

    README referent inchange, la cible resolue ne differe que par le dossier
    renomme (zz-old-dir -> zz-new-dir) : deplacement (exit 0).
    """
    repo, base_sha, head_sha = _tmp_repo_with_rename(tmp_path)
    base = {"violations": [
        {"class": "HTML_404", "readme": "docs/README.md", "href": "../zz-old-dir/notebooks/1.1-X.html"}
    ], "n_violations": 1}
    head = {"violations": [
        {"class": "HTML_404", "readme": "docs/README.md", "href": "../zz-new-dir/notebooks/1.1-X.html"}
    ], "n_violations": 1}
    proc = _run_diff(base, head, tmp_path, cwd=repo, shas=(base_sha, head_sha))
    assert proc.returncode == 0, f"diff exit={proc.returncode}\nstdout={proc.stdout}\nstderr={proc.stderr}"
    assert "NOUVELLES=0" in proc.stdout
    assert "DEPLACEES=1" in proc.stdout


def test_diff_no_pairing_without_rename_evidence(tmp_path: Path) -> None:
    """Fail-closed : sans --base-sha/--head-sha, RIEN ne se classe MOVED.

    Les cles du temoin positif shape 1 sont presentes, mais aucune preuve
    de renommage n'est fournie : la re-key reste une NOUVELLE (exit 1).
    """
    repo, _base_sha, _head_sha = _tmp_repo_with_rename(tmp_path)
    base = {"violations": [
        {"class": "HTML_404", "readme": "zz-old-dir/README.md", "href": "notebooks/1.1-X.html"}
    ], "n_violations": 1}
    head = {"violations": [
        {"class": "HTML_404", "readme": "zz-new-dir/README.md", "href": "notebooks/1.1-X.html"}
    ], "n_violations": 1}
    proc = _run_diff(base, head, tmp_path, cwd=repo)
    assert proc.returncode == 1, f"diff exit={proc.returncode}\nstdout={proc.stdout}"
    assert "NOUVELLES=1" in proc.stdout
    assert "DEPLACEES=0" in proc.stdout
    assert "fail-closed" in proc.stdout


def test_diff_refuses_deleted_dir_vs_unrelated_dir(tmp_path: Path) -> None:
    """Faux negatif 1 reproduit (revue adjointe 2026-10-11) : supprimer un
    dossier et en creer un autre sans lien n'est pas un renommage.

    docs/README.md inchange : ancien href vers ../zz-deleted-dir/old-broken.html
    (dossier SUPPRIME), nouveau href vers ../zz-unrelated-dir/new-broken.html
    (dossier EXISTANT). L'ancienne heuristique (ancien parent parti + nouveau
    parent present) blanchissait ce cas ; sans renommage git zz-deleted-dir ->
    zz-unrelated-dir, la nouvelle violation reste NOUVELLE (exit 1).
    """
    repo, base_sha, head_sha = _tmp_repo_with_rename(tmp_path)
    base = {"violations": [
        {"class": "HTML_404", "readme": "docs/README.md", "href": "../zz-deleted-dir/old-broken.html"}
    ], "n_violations": 1}
    head = {"violations": [
        {"class": "HTML_404", "readme": "docs/README.md", "href": "../zz-unrelated-dir/new-broken.html"}
    ], "n_violations": 1}
    proc = _run_diff(base, head, tmp_path, cwd=repo, shas=(base_sha, head_sha))
    assert proc.returncode == 1, f"diff exit={proc.returncode}\nstdout={proc.stdout}"
    assert "NOUVELLES=1" in proc.stdout
    assert "DEPLACEES=0" in proc.stdout


def test_diff_refuses_deleted_readme_vs_unrelated_readme(tmp_path: Path) -> None:
    """Faux negatif 2 reproduit (revue adjointe 2026-10-11) : un README
    supprime et un README sans rapport qui partagent le meme href ne font
    pas un demenagement.

    zz-other/README.md est SUPPRIME, zz-unrelated/README.md est CREE, href
    identique missing.html. L'ancienne heuristique (README de base disparu)
    blanchissait ce cas ; sans renommage git zz-other -> zz-unrelated, la
    nouvelle violation reste NOUVELLE (exit 1).
    """
    repo, base_sha, head_sha = _tmp_repo_with_rename(tmp_path)
    base = {"violations": [
        {"class": "HTML_404", "readme": "zz-other/README.md", "href": "missing.html"}
    ], "n_violations": 1}
    head = {"violations": [
        {"class": "HTML_404", "readme": "zz-unrelated/README.md", "href": "missing.html"}
    ], "n_violations": 1}
    proc = _run_diff(base, head, tmp_path, cwd=repo, shas=(base_sha, head_sha))
    assert proc.returncode == 1, f"diff exit={proc.returncode}\nstdout={proc.stdout}"
    assert "NOUVELLES=1" in proc.stdout
    assert "DEPLACEES=0" in proc.stdout


def test_diff_refuses_sibling_rename_acquitting_new_readme(tmp_path: Path) -> None:
    """Faux negatif 3 reproduit (revue adjointe 14:00, #20357) : le
    renommage d'un fichier VOISIN ne prouve pas celui du README.

    git rapporte R100 zz-part-old/a.txt -> zz-part-new/a.txt (d'ou un
    mapping de dossier) mais le README lui-meme en delete+add : contenu
    radicalement different, aucun statut R. L'ancienne branche
    « dossier prouve renomme + meme basename » acquittait ce couple en
    MOVED ; sans entree R portant sur CE README, la violation re-keyee
    reste NOUVELLE (exit 1).
    """
    repo, base_sha, head_sha = _tmp_repo_with_rename(tmp_path)
    base = {"violations": [
        {"class": "HTML_404", "readme": "zz-part-old/README.md", "href": "missing.html"}
    ], "n_violations": 1}
    head = {"violations": [
        {"class": "HTML_404", "readme": "zz-part-new/README.md", "href": "missing.html"}
    ], "n_violations": 1}
    proc = _run_diff(base, head, tmp_path, cwd=repo, shas=(base_sha, head_sha))
    assert proc.returncode == 1, f"diff aurait du exit=1, exit={proc.returncode}\nstdout={proc.stdout}\nstderr={proc.stderr}"
    assert "NOUVELLES=1" in proc.stdout
    assert "DEPLACEES=0" in proc.stdout


def test_diff_shape2_partial_dir_mapping_pairs_rekeyed_link(tmp_path: Path) -> None:
    """Frontiere mesuree (revue adjointe 14:00 : « verifier shape 2 contre
    un mapping partiel ») : un SEUL fichier demenage (a.txt) suffit a
    prouver le renommage du dossier zz-part-old -> zz-part-new, et le lien
    casse preexistant, re-adresse vers le nouveau dossier, reste le MEME
    lien casse => MOVED (exit 0).

    Pourquoi ce n'est pas le FN de la shape 1 : le document (docs/README.md)
    est inchange, seul le prefixe du lien suit un renommage reel prouve par
    git ; et une cible HTML_404 est absente du depot par definition, donc
    son propre renommage ne peut JAMAIS etre prouve -- l'exiger
    fabriquerait un faux positif sur chaque rename reel.
    """
    repo, base_sha, head_sha = _tmp_repo_with_rename(tmp_path)
    base = {"violations": [
        {"class": "HTML_404", "readme": "docs/README.md", "href": "../zz-part-old/deep/x.html"}
    ], "n_violations": 1}
    head = {"violations": [
        {"class": "HTML_404", "readme": "docs/README.md", "href": "../zz-part-new/deep/x.html"}
    ], "n_violations": 1}
    proc = _run_diff(base, head, tmp_path, cwd=repo, shas=(base_sha, head_sha))
    assert proc.returncode == 0, f"diff exit={proc.returncode}\nstdout={proc.stdout}\nstderr={proc.stderr}"
    assert "NOUVELLES=0" in proc.stdout
    assert "DEPLACEES=1" in proc.stdout


def test_diff_refuses_pairing_when_base_readme_still_exists(tmp_path: Path) -> None:
    """Temoin negatif (depot reel) : le README de base EXISTE encore au cwd
    => pas d'appariement, meme avec preuve de renommage ailleurs.

    Re-key d'une violation reelle (son chemin existe au REPO_ROOT par
    construction) vers un chemin invente : la disparition n'est pas prouvee,
    la violation re-keyee reste une NOUVELLE (exit 1). C'est ce temoin qui
    empeche l'appariement de blanchir un simple copier-coller de lien casse
    vers un nouveau fichier.
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
