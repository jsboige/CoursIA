"""#15697 -- les organes du corps de PR lisent le corps A L'EXECUTION.

Le defaut mesure : ``always-on-guards.yml`` fixait ``PR_BODY`` depuis
``github.event.pull_request.body`` -- une photographie au moment du
declenchement. Un corps amende SANS commit (typiquement par un organe sous
``github-actions``, dont les evenements sont avales par l'anti-recursion)
laissait le verdict du dernier run affiche sur un corps qui n'existe plus :
72 h sur #15303, 15 h sur #15587.

Le correctif : une etape de bootstrap lit le corps COURANT par l'API et
l'exporte dans ``PR_BODY`` via ``GITHUB_ENV`` ; repli sur le payload si
l'appel echoue. Ce fichier pince la structure ET execute le bloc livree
avec un ``gh`` factice (acceptance 1 + controle negatif de repli).
"""

import os
import re
import stat
import subprocess
import textwrap

import pytest
import yaml

REPO_ROOT = os.path.abspath(
    os.path.join(os.path.dirname(__file__), os.path.pardir, os.path.pardir)
)
WORKFLOW = os.path.join(
    REPO_ROOT, ".github", "workflows", "always-on-guards.yml"
)

# Sites ecrivant le litteral canonique dans always-on-guards.yml (job unique
# `always-on-guards`, 20 etapes, consommateurs aux indices 5-7 et 9-14).
# Valeur IDENTIQUE a la base de #15697 : c'est l'invariant que le corps
# revendique (« point unique de changement, les sites sont inchanges »).
PR_BODY_WRITE_SITES = 9


def _doc():
    with open(WORKFLOW, encoding="utf-8") as f:
        return yaml.safe_load(f)


def _steps(doc):
    return doc["jobs"]["always-on-guards"]["steps"]


def _bootstrap(steps):
    return next(
        (s for s in steps if "#15697" in s.get("name", "")), None
    )


def test_job_env_no_longer_pins_payload_body():
    """L'env de job ne fixe PLUS PR_BODY : un env statique primerait sur le
    GITHUB_ENV exporte par le bootstrap (precedence job-env > GITHUB_ENV),
    lui coupant la parole -- le defaut masque en pleine vue."""
    env = _doc()["jobs"]["always-on-guards"]["env"]
    assert "PR_BODY" not in env


def test_bootstrap_step_exists_before_first_consumer():
    """Le bootstrap existe et precede le premier organe qui consomme le corps
    -- un bootstrap place apres un consommateur jugerait la photographie."""
    steps = _steps(_doc())
    boot = _bootstrap(steps)
    assert boot is not None, "etape body-live #15697 absente"
    boot_idx = steps.index(boot)
    consumers = [
        i for i, s in enumerate(steps)
        if "pr_body.txt" in str(s.get("run", ""))
    ]
    assert consumers, "aucun consommateur de /tmp/pr_body.txt ?!"
    assert boot_idx < min(consumers)


def test_bootstrap_null_guard_and_fallback():
    """Le jq porte le null-guard (``// empty`` : un corps null rendrait le
    literal \"null\"), et le repli payload existe -- la lecture fraiche ne
    doit pouvoir bloquer aucune PR sur une panne d'API."""
    boot = _bootstrap(_steps(_doc()))
    run = boot["run"]
    assert "// empty" in run
    assert "PAYLOAD_BODY" in boot["env"]
    assert "PAYLOAD_BODY" in run


def test_consumer_sites_unchanged():
    """Les organes restent inchanges : NEUF sites ecrivent /tmp/pr_body.txt
    depuis ``${PR_BODY:-}`` -- le point unique de changement tient. Le pin
    est EXACT, pas un plancher : c'est l'invariant que le corps revendique,
    et un ``>= N`` laisserait passer la suppression de sites consommateurs."""
    run_all = "\n".join(
        str(s.get("run", "")) for s in _steps(_doc())
    )
    literal = 'printf \'%s\' "${PR_BODY:-}" > /tmp/pr_body.txt'
    assert run_all.count(literal) == PR_BODY_WRITE_SITES


FAKE_GH = textwrap.dedent(
    """
    #!/usr/bin/env bash
    # gh factice : la sous-commande api rend le corps fixe par GH_FAKE_BODY,
    # ou echoue (exit 1) si GH_FAKE_FAIL=1. Le jq est en $3, l'expression
    # en $4 : gh api <url> --jq <expr>.
    if [ "${GH_FAKE_FAIL:-}" = "1" ]; then exit 1; fi
    if [ "$1" = "api" ] && [ "$3" = "--jq" ]; then
      printf '%s' "${GH_FAKE_BODY:-}"
      exit 0
    fi
    exit 64
    """
)


def _bash_exe():
    """Sur Linux/CI : ``bash``. Sur Windows : le bash de Git for Windows --
    le ``bash.exe`` de System32 est le lanceur WSL, qui ne lit PAS les
    chemins Windows (``C:/...`` -> ``No such file or directory``)."""
    if os.name != "nt":
        return "bash"
    pf = os.environ.get("ProgramFiles", r"C:\Program Files")
    for cand in (
        os.path.join(pf, "Git", "bin", "bash.exe"),
        os.path.join(pf, "Git", "usr", "bin", "bash.exe"),
    ):
        if os.path.exists(cand):
            return cand
    pytest.skip("Git Bash introuvable -- le bash System32 (WSL) ne lit pas les chemins Windows")


def _run_bootstrap(tmp_path, fake_body, fail=False):
    """Extrait le bloc `run:` du bootstrap et l'execute avec le gh factice."""
    boot = _bootstrap(_steps(_doc()))
    bindir = tmp_path / "bin"
    bindir.mkdir()
    gh = bindir / "gh"
    gh.write_text(FAKE_GH, encoding="utf-8")
    gh.chmod(gh.stat().st_mode | stat.S_IEXEC)
    envfile = tmp_path / "github_env"
    script = tmp_path / "boot.sh"
    script.write_text(boot["run"], encoding="utf-8")
    env = dict(
        os.environ,
        GITHUB_ENV=str(envfile),
        GH_REPO="jsboige/CoursIA",
        PR_NUMBER="15587",
        PAYLOAD_BODY="Grain: PAYLOAD/photographie",
        GH_FAKE_BODY=fake_body,
    )
    if fail:
        env["GH_FAKE_FAIL"] = "1"
    # bash (Git Bash / runner Linux) n'accepte ni les separateurs Windows ni
    # un PATH mixte : un PATH ':'-sepague d'entrees ';'-separees est
    # re-parse par MSYS et le bin/ du gh factice se perd -- le gh REEL
    # repond alors (mesure : le test a lu le vrai corps de #15587 au lieu
    # du fixture). On convertit TOUT le PATH en entrees POSIX ':'-separees.
    path_entries = [
        p.replace("\\", "/")
        for p in os.environ.get("PATH", "").split(os.pathsep)
        if p
    ]
    env["PATH"] = ":".join(
        [str(bindir).replace("\\", "/")] + path_entries
    )
    out = subprocess.run(
        [_bash_exe(), str(script).replace("\\", "/")],
        capture_output=True, text=True, encoding="utf-8", env=env,
    )
    assert out.returncode == 0, out.stderr
    return out.stdout, envfile.read_text(encoding="utf-8")


def test_bootstrap_writes_live_body(tmp_path):
    """Acceptance 1, execution reelle du bloc livre : l'API rend le corps
    courant -> PR_BODY vaut le corps LIVE, pas le payload."""
    live = "Grain: LIVE/lu-a-l-execution -- corrige sans commit"
    stdout, genv = _run_bootstrap(tmp_path, live)
    assert "photographie" not in genv
    m = re.search(r"PR_BODY<<(\S+)\n(.*?)\n\1\n", genv, re.S)
    assert m, f"export GITHUB_ENV mal forme :\n{genv}"
    assert m.group(2) == live


def test_bootstrap_falls_back_to_payload_on_api_failure(tmp_path):
    """Controle negatif : API injoignable -> repli sur le payload, jamais de
    verdict vert par absence de corps (la lecture fraiche n'est pas une
    dispense)."""
    stdout, genv = _run_bootstrap(tmp_path, "", fail=True)
    m = re.search(r"PR_BODY<<(\S+)\n(.*?)\n\1\n", genv, re.S)
    assert m, f"export GITHUB_ENV mal forme :\n{genv}"
    assert m.group(2) == "Grain: PAYLOAD/photographie"
    assert "::warning::" in stdout


def test_bootstrap_multiline_body_survives_heredoc(tmp_path):
    """Un corps multiline (le cas reel : sections, tableaux) traverse
    l'export GITHUB_ENV sans troncature ni pollution du delimiteur."""
    live = "Grain: MED/tooling\n\n## Summary\n\n| a | b |\n|---|---|\n| 1 | 2 |"
    _, genv = _run_bootstrap(tmp_path, live)
    m = re.search(r"PR_BODY<<(\S+)\n(.*?)\n\1\n", genv, re.S)
    assert m and m.group(2) == live
