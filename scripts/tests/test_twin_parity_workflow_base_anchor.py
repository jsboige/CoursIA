"""La base du gate twin-parity est ancree sur l'EVENEMENT, pas sur le checkout.

`check_twin_parity.py --per-pair --base <commit>` compare le registre a la base
de la PR. Cette base doit etre **la base sur laquelle GitHub a construit le
merge**, pas `origin/main` (refetch au demarrage du job, donc plus recent que
le merge ref apres une attente en file) ni une deduction depuis la forme du
checkout.

Le re-cadrage du 2026-10-27 (#22419, apres #22293) fixe l'ancrage sur
`github.sha` -- le commit de fusion du merge ref, fourni par l'evenement --
puis en prend le premier parent (`github.sha^1`). Le mode `--base auto` de
l'outil, lui, deduit `HEAD^1` de la forme du checkout : c'est exactement ce que
ce workflow ne doit PAS faire.

Ce fichier fige l'invariant sur le FICHIER de workflow (le test du mode `auto`
vaut pour l'usage local, pas pour la CI) :

  1. le workflow ne lit plus `github.event.pull_request.base.sha` ;
  2. l'ancrage est `github.sha`, resolu en `^1` ;
  3. aucune ligne EXECUTABLE ne derive la base de `HEAD` ;
  4. la ligne de succes nomme la base REELLEMENT utilisee (le rapport porte
     `base_ref` ; une ligne qui annonce une base en dur ment, cf Hermes sur
     #22419, point (a)).

Le detecteur a un controle negatif : un workflow qui derive de `HEAD^1` DOIT
etre signale. Un garde jamais vu rouge n'est pas un garde.
"""

from __future__ import annotations

import re
import shutil
import subprocess
from pathlib import Path

import pytest

WORKFLOW = Path(".github/workflows/twin-parity.yml")


def _repo_root() -> Path:
    """scripts/tests/ -> scripts/ -> racine du depot."""
    return Path(__file__).resolve().parents[2]


def _text() -> str:
    return (WORKFLOW if WORKFLOW.is_absolute() else _repo_root() / WORKFLOW).read_text(
        encoding="utf-8"
    )


def _code_lines(text: str) -> list[str]:
    """Les lignes du fichier SANS les commentaires (bloc `#` ou ` #`).

    Un commentaire peut nommer `HEAD^1` pour expliquer pourquoi on ne l'utilise
    pas ; seule une ligne executable qui le lit est une faute.
    """
    out: list[str] = []
    for raw in text.splitlines():
        stripped = raw.strip()
        if not stripped or stripped.startswith("#"):
            continue
        # Un `run: |` porte un bloc shell : ses lignes sont du code meme si
        # elles commencent par `#` (elles seraient des commentaires shell).
        out.append(raw)
    return out


def _violations(text: str) -> list[str]:
    """Les manquements du workflow a la regle d'ancrage. Liste vide = conforme."""
    out: list[str] = []
    if "github.event.pull_request.base.sha" in text:
        out.append("base lue depuis `github.event.pull_request.base.sha`")
    if "PR_SHA: ${{ github.sha }}" not in text:
        out.append("ancrage `github.sha` absent")
    code = "\n".join(_code_lines(text))
    if "${PR_SHA}^1^{commit}" not in code:
        out.append("resolution `github.sha^1` absente du code executable")
    if re.search(r"(?<![\w^])\bHEAD\^1", code):
        out.append("base deduite de `HEAD^1` (forme du checkout)")
    if "rev-list --parents" not in code:
        out.append("garde de commit de fusion absente")
    if "(base=$BASE_SHA)" not in code:
        out.append("la ligne de succes ne nomme pas la base reellement utilisee")
    return out


def test_workflow_anchor_sur_evenement():
    """Le workflow reel est conforme a la regle d'ancrage."""
    assert _violations(_text()) == []


def test_un_ancrage_sur_head_est_signale():
    """CONTROLE NEGATIF : un workflow qui derive de `HEAD^1` doit etre rouge.

    Sans ce cas, le detecteur pourrait ne rien detecter du tout -- et un garde
    jamais vu rouge n'est pas un garde.
    """
    mutant = _text().replace(
        'CANDIDATE="$(git rev-parse -q --verify "${PR_SHA}^1^{commit}" 2>/dev/null || true)"',
        'CANDIDATE="$(git rev-parse -q --verify "HEAD^1^{commit}" 2>/dev/null || true)"',
    )
    assert mutant != _text(), "le mutant n'a pas ete applique : le test ne prouve rien"
    violations = _violations(mutant)
    assert violations, "le mutant n'a pas ete detecte"
    assert any("HEAD^1" in v for v in violations), violations


def test_une_base_en_dur_dans_la_ligne_de_succes_est_signalee():
    """CONTROLE NEGATIF (point (a) de Hermes) : une base en dur ment.

    La ligne de succes annoncait `origin/main` alors que le rapport portait la
    base reellement utilisee. Le lecteur du log se renseignait sur une base
    qui n'avait pas servi.
    """
    mutant = _text().replace("(base=$BASE_SHA)", "(base=origin/main)")
    assert mutant != _text(), "le mutant n'a pas ete applique : le test ne prouve rien"
    violations = _violations(mutant)
    assert violations, "le mutant n'a pas ete detecte"
    assert any("ligne de succes" in v for v in violations), violations


def test_une_base_lue_dans_le_payload_evenement_est_signalee():
    """CONTROLE NEGATIF : revenir a `github.event.pull_request.base.sha` doit rougir."""
    mutant = _text().replace(
        "PR_SHA: ${{ github.sha }}", "PR_SHA: ${{ github.event.pull_request.base.sha }}"
    )
    assert mutant != _text(), "le mutant n'a pas ete applique : le test ne prouve rien"
    violations = _violations(mutant)
    assert violations, "le mutant n'a pas ete detecte"
    assert any("base.sha" in v for v in violations), violations


def test_la_garde_de_fusion_absente_est_signalee():
    """CONTROLE NEGATIF : sans le controle du nombre de parents, un `github.sha`
    qui ne serait pas un commit de fusion donnerait une base FAUSSE
    silencieusement. La garde doit rester dans le fichier."""
    mutant = _text().replace(
        'PARENTS="$(git rev-list --parents -n 1 "$PR_SHA" 2>/dev/null || true)"',
        'PARENTS="$(echo x)"',
    )
    assert mutant != _text(), "le mutant n'a pas ete applique : le test ne prouve rien"
    violations = _violations(mutant)
    assert violations, "le mutant n'a pas ete detecte"
    assert any("garde de commit de fusion" in v for v in violations), violations


# --- le shell livre, execute tel quel -----------------------------------------
#
# Les tests ci-dessus portent sur la FORME du fichier. Celui-ci execute le
# BLOC REEL de resolution -- extrait du workflow, pas recopie -- dans un
# mini-depot git, et verifie la base reellement choisie.

def _resolution_snippet(text: str) -> str:
    """Le bloc `BASE=...` du workflow, extrait tel quel (indentation retiree).

    L'extraction passe par le parseur YAML (le `run:` de l'etape `check`) et
    compte l'imbrication des `if`/`fi` : le bloc contient des `fi` imbriques,
    et le premier `fi` rencontre ne le ferme pas.
    """
    import yaml

    doc = yaml.safe_load(text)
    step = next(
        s for s in doc["jobs"]["twin-parity"]["steps"] if s.get("id") == "check"
    )
    lines = step["run"].splitlines()
    start = next(i for i, l in enumerate(lines) if l.strip() == "BASE=origin/main")
    depth = 0
    for i in range(start, len(lines)):
        s = lines[i].strip()
        if s.startswith("if "):
            depth += 1
        elif s == "fi":
            depth -= 1
            if depth == 0:
                return "\n".join(l.strip() for l in lines[start : i + 1])
    raise AssertionError("bloc de resolution non trouve dans le workflow")


def _git(repo: Path, *args: str) -> str:
    r = subprocess.run(
        ["git", *args], cwd=repo, check=True, capture_output=True,
        text=True, encoding="utf-8", errors="replace",
    )
    return r.stdout.strip()


def _mini_repo(tmp_path: Path) -> Path:
    repo = tmp_path / "repo"
    repo.mkdir()
    _git(repo, "init", "-q", "-b", "main")
    _git(repo, "config", "user.email", "t@t")
    _git(repo, "config", "user.name", "t")
    (repo / "a.txt").write_text("a\n", encoding="utf-8")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-qm", "base")
    return repo


def _resolve(repo: Path, event: str, pr_sha: str) -> str:
    """Execute le bloc de resolution du workflow et rend la base choisie.

    Le script passe par un FICHIER, pas par `bash -c` : sur Windows,
    `subprocess` collapse les retours a la ligne de l'argument, ce qui
    transformerait le bloc en une seule ligne -- et une seule ligne
    commencee par `#` est un commentaire : le test passerait a vide.
    """
    snippet = _resolution_snippet(_text())
    script = f'EVENT="{event}"\nPR_SHA="{pr_sha}"\n{snippet}\necho "BASE=$BASE"\n'
    script_file = repo / "_resolution_probe.sh"
    script_file.write_text(script, encoding="utf-8", newline="\n")
    r = subprocess.run(
        ["bash", str(script_file.name)], cwd=repo, capture_output=True,
        text=True, encoding="utf-8", errors="replace",
    )
    assert r.returncode == 0, f"le bloc a echoue: {r.stderr!r}"
    out = r.stdout.strip().splitlines()[-1]
    assert out.startswith("BASE="), out
    return out[len("BASE=") :]


@pytest.mark.skipif(shutil.which("bash") is None, reason="bash absent")
def test_le_bloc_live_resout_le_premier_parent_du_merge_ref(tmp_path):
    repo = _mini_repo(tmp_path)
    _git(repo, "checkout", "-q", "-b", "feature")
    (repo / "b.txt").write_text("b\n", encoding="utf-8")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-qm", "PR")
    feature = _git(repo, "rev-parse", "HEAD")
    _git(repo, "checkout", "-q", "main")
    base = _git(repo, "rev-parse", "HEAD")
    _git(repo, "merge", "-q", "--no-ff", "feature", "-m", f"Merge {feature[:10]} into {base[:10]}")
    merge = _git(repo, "rev-parse", "HEAD")

    assert _resolve(repo, "pull_request", merge) == base


@pytest.mark.skipif(shutil.which("bash") is None, reason="bash absent")
def test_le_bloc_live_replique_sur_une_base_non_fusion(tmp_path):
    """Un `github.sha` qui n'est PAS un commit de fusion ne doit pas donner son
    parent ordinaire comme base : le repli d'origine (`origin/main`) est
    meilleure qu'une base fausse."""
    repo = _mini_repo(tmp_path)
    (repo / "b.txt").write_text("b\n", encoding="utf-8")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-qm", "commit ordinaire")
    head = _git(repo, "rev-parse", "HEAD")

    assert _resolve(repo, "pull_request", head) == "origin/main"


@pytest.mark.skipif(shutil.which("bash") is None, reason="bash absent")
def test_le_bloc_live_replique_hors_evenement_pull_request(tmp_path):
    repo = _mini_repo(tmp_path)
    head = _git(repo, "rev-parse", "HEAD")
    assert _resolve(repo, "workflow_dispatch", head) == "origin/main"
