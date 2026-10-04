"""Temoins automatises du chemin WORKFLOW readme-ipynb-links-guard (#18970).

Les tests Python existants (test_fix_ipynb_links.py, test_readme_link_violations.py)
couvrent les SCRIPTS ; aucun ne couvre le bloc shell du workflow lui-meme, ou vivent
les fixes F1/F3/F4/F6/F7 (stderr fusionnee, rc captures sans `|| true`, PIPESTATUS,
resume-vs-traceback, grep rc>=2 refuse). Cette suite extrait le bloc `run:` de
l'etape "Compute delta" VERBATIM depuis le YAML et le rejoue dans un depot git
temporaire avec de VRAIS git/python/grep/sort/comm -- seul le scanner
`regen_quarto_render.py` est remplace par un stub encode par commit.

Toute regression du bloc (perte du `2>&1`, retour d'un `|| true`, indice
PIPESTATUS decale...) fait rougir le temoin correspondant. Rejeu manuel de
reference (adjoint c26, 2026-10-04 09:05Z) : propre rc0, backlog 2/2/0 rc0,
nouvelle STALE_LINK stderr 2/3/1 rc1, traceback rc1, scanner rc2, checkout refuse.
"""

import os
import shutil
import subprocess
import sys

import pytest

REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", ".."))
WORKFLOW = os.path.join(REPO_ROOT, ".github", "workflows", "readme-ipynb-links-guard.yml")
STEP_NAME = "- name: Compute delta (new STALE_LINK on this PR vs base)"

# Lignes de violation dans le style du vrai scanner : ::error::STALE_LINK sur STDERR.
SHARED_VIOLATIONS = [
    "::error::STALE_LINK MyIA.AI.Notebooks/Search/README.md link1 target1.ipynb",
    "::error::STALE_LINK MyIA.AI.Notebooks/Probas/README.md link2 target2.ipynb",
]
NEW_VIOLATION = (
    "::error::STALE_LINK MyIA.AI.Notebooks/New/README.md link3 target3.ipynb"
)

STUB_TEMPLATE = '''\
"""Stub sandbox -- simule le scanner selon STUB_MODE (encode par commit)."""
import sys

STUB_MODE = "{mode}"
SHARED = {shared!r}
EXTRA = {extra!r}

if STUB_MODE == "rc2":
    sys.stderr.write("stub: panne scanner franche\\n")
    sys.exit(2)
if STUB_MODE == "traceback":
    sys.stderr.write("Traceback (most recent call last):\\n")
    sys.stderr.write("  boom\\n")
    sys.exit(1)
violations = SHARED + (EXTRA if STUB_MODE == "extra" else [])
for line in violations:
    print(line, file=sys.stderr)
print("README-link audit: {{}} violations".format(len(violations)))
sys.exit(1 if violations else 0)
'''


def scanner_stub(mode):
    return STUB_TEMPLATE.format(
        mode=mode, shared=SHARED_VIOLATIONS, extra=[NEW_VIOLATION]
    )


def extract_delta_block():
    """Extrait verbatim le bloc run: de l'etape Compute delta du workflow."""
    with open(WORKFLOW, encoding="utf-8") as f:
        lines = f.read().splitlines()
    heads = [i for i, l in enumerate(lines) if l.strip() == STEP_NAME.strip()]
    assert len(heads) == 1, f"etape Compute delta: {len(heads)} occurrences"
    i = heads[0]
    while not lines[i].strip().startswith("run:"):
        i += 1
        assert i < len(lines), "pas de run: dans l'etape Compute delta"
    indent = len(lines[i]) - len(lines[i].lstrip())
    block = []
    for line in lines[i + 1:]:
        if line.strip() == "":
            block.append("")
            continue
        if len(line) - len(line.lstrip()) > indent:
            block.append(line[indent + 2:])
        else:
            break
    text = "\n".join(block).strip("\n") + "\n"
    # Gardes anti-extraction-fausse : le bloc doit porter les marqueurs V10.
    for marker in ("set -euo pipefail", "merge-base", "PIPESTATUS"):
        assert marker in text, f"marqueur {marker!r} absent du bloc extrait"
    return text


def run_git(cwd, *args):
    subprocess.run(
        ["git", *args], cwd=cwd, check=True, capture_output=True, text=True
    )


def build_sandbox(tmp_path, pr_mode, base_mode, empty_base=False):
    """Depot temporaire : root vide -> commit base -> origin/main -> commit PR.

    Le stub scanner est encode PAR COMMIT : le `git checkout BASE -- ...` du bloc
    restaure le stub base pour la passe base, puis `git checkout HEAD -- ...`
    restaure le stub PR -- exactement la mecanique du workflow reel.
    """
    sandbox = tmp_path / f"sb_{pr_mode}_{base_mode}"
    sandbox.mkdir()
    run_git(sandbox, "init", "-q")
    run_git(sandbox, "config", "user.email", "sandbox@example.invalid")
    run_git(sandbox, "config", "user.name", "sandbox")
    run_git(sandbox, "commit", "--allow-empty", "-q", "-m", "root")
    if not empty_base:
        readme_dir = sandbox / "MyIA.AI.Notebooks" / "Search"
        readme_dir.mkdir(parents=True)
        (readme_dir / "README.md").write_text("# readme\n", encoding="utf-8")
        (sandbox / "scripts").mkdir()
        (sandbox / "scripts" / "regen_quarto_render.py").write_text(
            scanner_stub(base_mode), encoding="utf-8"
        )
        (sandbox / "_quarto.yml").write_text("website: {}\n", encoding="utf-8")
        run_git(sandbox, "add", "-A")
        run_git(sandbox, "commit", "-q", "-m", "base")
    run_git(sandbox, "update-ref", "refs/remotes/origin/main", "HEAD")
    scripts = sandbox / "scripts"
    scripts.mkdir(parents=True, exist_ok=True)
    (scripts / "regen_quarto_render.py").write_text(
        scanner_stub(pr_mode), encoding="utf-8"
    )
    # Le commit PR porte toujours un contenu distinct de la base (sinon git
    # refuse un commit vide quand pr_mode == base_mode).
    pr_readme = sandbox / "MyIA.AI.Notebooks" / "Search" / "README.md"
    pr_readme.parent.mkdir(parents=True, exist_ok=True)
    pr_readme.write_text("# readme (PR head)\n", encoding="utf-8")
    run_git(sandbox, "add", "-A")
    run_git(sandbox, "commit", "-q", "-m", "pr")
    return sandbox


def replay_block(tmp_path, pr_mode, base_mode, empty_base=False):
    """Rejoue le bloc shell exact du workflow dans le sandbox, rend (rc, stdout).

    GITHUB_EVENT_NAME est exporte DANS le shell wrapper : sur certains hotes
    Windows, git-bash filtre les variables d'environnement ajoutees par le
    processus parent -- l'export prefixe reproduit exactement ce que fait le
    runner Actions (injection de l'env du step dans le shell avant le bloc).
    """
    sandbox = build_sandbox(tmp_path, pr_mode, base_mode, empty_base=empty_base)
    script = sandbox / "run_block.sh"
    script.write_text(extract_delta_block(), encoding="utf-8", newline="\n")
    # Idem PATH : un bash spawn depuis un parent natif Windows peut reconstruire
    # un PATH MSYS sans les entrees Windows -- on y reinsere le dossier de
    # l'interpreteur courant (no-op sur Linux CI).
    exe_dir = os.path.dirname(sys.executable)
    if ":" in exe_dir:
        drive, rest = exe_dir.split(":", 1)
        exe_dir = "/" + drive.lower() + rest.replace("\\", "/")
    proc = subprocess.run(
        [_bash_executable(), "-c",
         f'export GITHUB_EVENT_NAME=pull_request; export PATH="$PATH:{exe_dir}"; '
         "bash run_block.sh"],
        cwd=str(sandbox),
        capture_output=True,
        text=True,
        timeout=120,
    )
    return proc.returncode, proc.stdout


def _bash_executable():
    """Sur Windows, `bash` peut resoudre vers WSL (System32) : env filtree et
    chemins /c/ invisibles. On remonte depuis git.exe jusqu'au bash de git."""
    if os.name != "nt":
        return "bash"
    git = shutil.which("git")
    if not git:
        return "bash"
    d = os.path.dirname(os.path.abspath(git))
    while d and os.path.dirname(d) != d:
        for sub in ("bin", os.path.join("usr", "bin")):
            cand = os.path.join(d, sub, "bash.exe")
            if os.path.isfile(cand):
                return cand
        d = os.path.dirname(d)
    return "bash"


pytestmark = pytest.mark.skipif(
    shutil.which("bash") is None or shutil.which("git") is None,
    reason="bash/git requis pour rejouer le bloc workflow",
)


def test_temoin_propre_rc0(tmp_path):
    """Base et head sans violation : rc0, message nominal."""
    rc, out = replay_block(tmp_path, "clean", "clean")
    assert rc == 0, out
    assert "Aucune nouvelle violation STALE_LINK sur cette PR." in out
    assert "STALE_LINK NOUVELLES sur cette PR: 0" in out


def test_temoin_backlog_2_2_0_rc0(tmp_path):
    """Backlog historique identique base/head : 2/2/0, rc0 (le backlog ne rougit pas)."""
    rc, out = replay_block(tmp_path, "shared", "shared")
    assert rc == 0, out
    assert "STALE_LINK base" in out and ": 2" in out
    assert "STALE_LINK head (PR): 2" in out
    assert "STALE_LINK NOUVELLES sur cette PR: 0" in out


def test_temoin_nouvelle_violation_stderr_2_3_1_rc1(tmp_path):
    """F1 : violation NOUVELLE emise sur STDERR seulement -> 2/3/1, rc1.

    C'est le temoin discriminant du faux vert fondateur (run 37109571492) :
    si le `2>&1` disparait du pipe, les violations stderr echappent au grep,
    le delta rend 2/2/0 rc0 et CE test rougit.
    """
    rc, out = replay_block(tmp_path, "extra", "shared")
    assert rc == 1, out
    assert "STALE_LINK head (PR): 3" in out
    assert "STALE_LINK base" in out and ": 2" in out
    assert "STALE_LINK NOUVELLES sur cette PR: 1" in out
    assert "::error::Nouvelle violation STALE_LINK sur cette PR" in out
    assert "target3.ipynb" in out


def test_temoin_traceback_sans_resume_rc1(tmp_path):
    """F6 : scanner rc=1 SANS resume stdout (traceback) = crash refuse, pas un vert."""
    rc, out = replay_block(tmp_path, "traceback", "shared")
    assert rc == 1, out
    assert "Scanner en crash sur PR (rc=1" in out


def test_temoin_scanner_rc2_refuse(tmp_path):
    """F4 : rc>=2 = panne franche du scanner, refuse meme avec delta vide."""
    rc, out = replay_block(tmp_path, "rc2", "shared")
    assert rc == 1, out
    assert "Scanner en panne sur PR (rc=2)" in out


def test_temoin_checkout_base_refuse(tmp_path):
    """F3 : echec du checkout base = delta invalide, refuse (pas de faux vert).

    Base = commit root vide : `git checkout BASE -- <paths>` ne matche aucun
    pathspec et echoue ; l'ancien `|| true` aurait continue sur le working
    tree PR et rendu un delta vide rc0.
    """
    rc, out = replay_block(tmp_path, "shared", "none", empty_base=True)
    assert rc == 1, out
    assert "git checkout base en panne" in out


def test_extraction_bloc_unique_et_f1_present():
    """Meta-temoin : capture stderr sur les 2 passes, aucun || true actif."""
    import re

    block = extract_delta_block()
    assert block.count("2>&1") >= 2, "la fusion stderr doit couvrir les DEUX passes"
    # Le commentaire F3 documente les anciens `|| true` : on ne regarde que
    # les lignes de code, pas les commentaires.
    code_lines = [l for l in block.splitlines() if not l.lstrip().startswith("#")]
    actifs = [l for l in code_lines if re.search(r"\|\| true\s*$", l)]
    assert not actifs, f"|| true actif en fin de commande : {actifs}"
