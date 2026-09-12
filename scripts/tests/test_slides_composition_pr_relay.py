"""Non-regression #15359: le relais de composition doit voir les decks.

Le relais `slides-composition-pr-relay.yml` n'avait aucune etape
`actions/checkout` : sur un runner self-hosted le workspace est vide,
`git diff "${BASE}...${HEAD}" -- slides/` echoue, et le `|| true`
transformait la panne en `Touched decks: 0` vert — faux negatif
silencieux (run 34315275538 sur #15334, qui touchait pourtant
`slides/08-ia-generative/slides.md` +126/−14).

Controle negatif (#15359) : un detecteur se valide par ses faux
negatifs, pas par ses hits — une PR connue pour toucher un deck doit
rendre N >= 1. Deux volets :

1. Structurel — le workflow contient un checkout `fetch-depth: 0` sur
   le head de la PR, et le `git diff` du step `resolve` n'est plus
   avale (`|| true` absent) ;
2. Comportemental — la pipeline de decouverte (diff + grep + dedup +
   existence du fichier) rend N >= 1 sur un depot git minimal qui
   touche un deck, et 0 sur un depot qui ne touche rien.

Run:
    python -m pytest scripts/tests/test_slides_composition_pr_relay.py
"""
from __future__ import annotations

import re
import subprocess
from pathlib import Path

import pytest

WORKFLOW = (
    Path(__file__).resolve().parents[2]
    / ".github"
    / "workflows"
    / "slides-composition-pr-relay.yml"
)


def _workflow_text() -> str:
    return WORKFLOW.read_text(encoding="utf-8")


def _git_run(repo: Path, *args: str) -> subprocess.CompletedProcess:
    return subprocess.run(
        ["git", "-C", str(repo), *args],
        capture_output=True,
        text=True,
        encoding="utf-8", errors="replace",
    )


@pytest.fixture
def tiny_repo(tmp_path: Path):
    """Depot git minimal : un deck `slides/demo/slides.md` + un autre fichier."""
    repo = tmp_path / "repo"
    repo.mkdir()
    _git_run(repo, "init", "-q", "-b", "main")
    _git_run(repo, "config", "user.email", "test@local")
    _git_run(repo, "config", "user.name", "test")
    deck = repo / "slides" / "demo"
    deck.mkdir(parents=True)
    other = repo / "docs"
    other.mkdir()
    (deck / "slides.md").write_text("# Deck\nbody\n", encoding="utf-8")
    (other / "readme.md").write_text("docs\n", encoding="utf-8")
    _git_run(repo, "add", ".")
    _git_run(repo, "commit", "-q", "-m", "base")
    return repo


def _discovery(
    repo: Path, base: str, head: str, changed: str
) -> tuple[int, list[str]]:
    """Rejoue le step `resolve` du relais (decouverte des decks touches).

    La pipeline exacte du workflow (grep + dedup + existence locale du
    `slides.md`) — parametree par la sortie de `git diff` pour rester
    hermétique aux SHAs reels.
    """
    decks = []
    if re.search(r"slides/(theme-ia101|package(-lock)?\.json)", changed):
        # infra partagee : tous les decks — branche non couverte ici,
        # le comportement hermetique vise la decouverte par diff.
        return 0, decks
    for path in sorted(
        {m.group(1) for m in re.finditer(r"^slides/([^/]+)/", changed, re.M)}
    ):
        if (repo / "slides" / path / "slides.md").is_file():
            decks.append(f"slides/{path}/slides.md")
    return len(decks), decks


# --- volet 1 : structure du workflow -----------------------------------------

def test_workflow_has_checkout_before_resolve():
    """Un `uses: actions/checkout@v4` doit preceder le step `resolve`."""
    text = _workflow_text()
    checkout = text.index("uses: actions/checkout@v4")
    resolve = text.index("id: resolve")
    assert checkout < resolve


def test_checkout_fetches_head_and_full_history():
    """`ref: head.sha` + `fetch-depth: 0` : les deux SHAs du diff existent."""
    m = re.search(
        r"uses: actions/checkout@v4(.*?)-\s+name:\s+Resolve",
        _workflow_text(),
        re.S,
    )
    assert m, "bloc checkout manquant avant le step Resolve"
    block = m.group(1)
    assert "ref: ${{ github.event.pull_request.head.sha }}" in block
    assert "fetch-depth: 0" in block


def test_git_diff_not_swallowed():
    """Le `|| true` sur le `git diff` est retire : une panne doit rougir."""
    m = re.search(r"CHANGED=\$\(git diff[^\n]*\)", _workflow_text())
    assert m, "ligne CHANGED=$(git diff ...) introuvable"
    line = m.group(0)
    assert "|| true" not in line
    assert "slides/" in line


# --- volet 2 : comportement (controle negatif) --------------------------------

def test_discovery_renders_at_least_one_on_deck_touching_diff(
    tiny_repo: Path,
):
    """Une PR connue pour toucher un deck doit rendre N >= 1."""
    (tiny_repo / "slides" / "demo" / "slides.md").write_text(
        "# Deck\nbody modifie\n", encoding="utf-8"
    )
    changed = _git_run(
        tiny_repo, "diff", "--name-only", "HEAD", "--", "slides/"
    ).stdout
    assert "slides/demo/slides.md" in changed
    n, _ = _discovery(tiny_repo, "HEAD", "HEAD", changed)
    assert n >= 1


def test_discovery_renders_zero_on_untouched_slides(tiny_repo: Path):
    """Un diff qui ne touche que docs/ ne revele aucun deck."""
    (tiny_repo / "docs" / "readme.md").write_text("docs modifie\n", encoding="utf-8")
    changed = _git_run(
        tiny_repo, "diff", "--name-only", "HEAD", "--", "slides/"
    ).stdout
    n, _ = _discovery(tiny_repo, "HEAD", "HEAD", changed)
    assert n == 0