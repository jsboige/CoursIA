"""#17265 -- un document d'erreur de `gh` n'est pas un identifiant de commentaire.

Contexte. Quatre sites du harnais ecrivaient :

    EXISTING_ID=$(gh pr view "$PR_NUMBER" --json comments --jq '...' 2>/dev/null | head -1 || echo "")

Le `||` porte sur le rc du DERNIER maillon du pipeline. Mais meme sous
`-o pipefail` -- et le shell des workflows est bien `bash -eo pipefail` -- ce
repli ne corrige rien : `gh` ecrit son **document d'erreur sur stdout** en rc=1,
et un repli place DANS la substitution ne peut pas **effacer un stdout deja
ecrit**. Mesure a deux bras (gh factice qui echoue en ecrivant sur stdout) :

    avant : api -X PATCH repos/.../comments/{"message":"API rate limit exceeded..."}
    apres : le canal partage decide sur le rc (commentaire unique, une
            section par organe)

Consequence avant correctif : sur une panne de quota, le commentaire advisory
n'etait **jamais poste** (la branche `else` qui l'aurait poste etait sautee) et
un marqueur perime n'etait **pas retire** -- les deux echecs avales par
`2>/dev/null || true`, pendant que le `::notice:` affirmait le contraire.

#15511 a supprime les quatre sites : le canal consultatif est desormais
**l'organe partage** `scripts/ci/advisory_sticky.py`, qui decide sur le rc et
dont l'echec est remonte (le workflow imprime alors `::warning::`, jamais
`::notice::`). Ce fichier verifie donc deux choses :

1. **la forme fautive a disparu de TOUS les workflows** (plus aucun site
   `EXISTING_ID`, plus aucun `head -1 || echo ""`) ;
2. **le canal partage decide sur le code de sortie** : un `gh` en echec
   remonte (rc non nul, document d'erreur non promu identifiant), un `gh`
   qui repond fait un succes *constate*.

Le controle positif de l'instrument est explicite : la forme ANCIENNE est
rejouee et doit **reproduire** le defaut. Sans lui, un harnais incapable de
distinguer les deux formes passerait vert sur les deux -- et ne prouverait
rien.

Le resolveur `_bash_exe` est une copie assumee de celui de
`test_always_on_guards_live_body.py` : ce dernier est modifie par une PR
ouverte (#17260, meme famille de defaut), et importer un helper prive d'un
fichier en vol ferait rougir ce test pour une raison sans rapport.
"""

import contextlib
import io
import json
import os
import pathlib
import re
import stat
import subprocess
import sys
import textwrap

import pytest

REPO_ROOT = pathlib.Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "scripts" / "ci"))
import advisory_sticky as a_s  # noqa: E402
WORKFLOWS = (
    REPO_ROOT / ".github" / "workflows" / "always-on-guards.yml",
    REPO_ROOT / ".github" / "workflows" / "variation-light-genre.yml",
    REPO_ROOT / ".github" / "workflows" / "variation-tag-guard.yml",
)
# Les workflows qui publient des sections du commentaire unique (#15511).
LIVE_WORKFLOWS = (
    REPO_ROOT / ".github" / "workflows" / "always-on-guards.yml",
    REPO_ROOT / ".github" / "workflows" / "variation-light-genre.yml",
    REPO_ROOT / ".github" / "workflows" / "variation-tag-guard.yml",
    REPO_ROOT / ".github" / "workflows" / "markdown-claims-output-advisory.yml",
    REPO_ROOT / ".github" / "workflows" / "notebook-outputs-required.yml",
    REPO_ROOT / ".github" / "workflows" / "organ-duplication-advisory.yml",
)
SITE_HEAD = 'EXISTING_ID=$(gh pr view "$PR_NUMBER" --json comments'
FORM_FAUTIVE = 'head -1 || echo ""'
ORGAN = REPO_ROOT / "scripts" / "ci" / "advisory_sticky.py"

FAKE_GH = textwrap.dedent(
    """\
    #!/usr/bin/env bash
    # gh factice. Journalise chaque appel dans $GH_LOG, puis repond selon le mode.
    echo "$*" >> "$GH_LOG"
    if [ "$1" = "pr" ] && [ "$2" = "view" ]; then
      if [ "${GH_FAKE_API_FAIL:-}" = "1" ]; then
        printf '%s\\n' '{"message":"API rate limit exceeded for installation.","status":"403"}'
        exit 1
      fi
      [ -n "${GH_FAKE_ID:-}" ] && printf '%s\\n' "${GH_FAKE_ID}"
      exit 0
    fi
    if [ "$1" = "pr" ] && [ "$2" = "comment" ]; then
      [ "${GH_FAKE_WRITE_FAIL:-}" = "1" ] && exit 1
      echo "COMMENT_POSTED"
      exit 0
    fi
    if [ "$1" = "api" ]; then
      case "$*" in
        *"--method POST"*)
          if [ "${GH_FAKE_WRITE_FAIL:-}" = "1" ]; then
            # `gh` ecrit son document d'erreur sur STDOUT en rc=1 : c'est
            # precisement le piege -- un identifiant de commentaire ne doit
            # JAMAIS en etre extrait.
            printf '%s\\n' '{"message":"API rate limit exceeded for installation.","status":"403"}'
            exit 1
          fi
          printf '%s\\n' '{"id": 4242}'
          exit 0
          ;;
        *"--method PATCH"*)
          [ "${GH_FAKE_WRITE_FAIL:-}" = "1" ] && exit 1
          printf '%s\\n' '{"id": 4242}'
          exit 0
          ;;
        *)
          # lecture des commentaires : forme `--slurp` (liste de pages)
          if [ "${GH_FAKE_API_FAIL:-}" = "1" ]; then
            printf '%s\\n' '{"message":"API rate limit exceeded for installation.","status":"403"}'
            exit 1
          fi
          printf '%s\\n' '[[]]'
          exit 0
          ;;
      esac
    fi
    exit 64
    """
)


def _bash_exe() -> str:
    """CI/Linux : ``bash``. Windows : le bash de Git for Windows.

    Le ``bash.exe`` de System32 est le lanceur WSL, qui ne lit PAS les chemins
    Windows (``C:/...`` -> ``No such file or directory``).
    """
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


def _python_exe() -> str:
    return "python" if os.name != "nt" else "python"


def _block_at(lines: list[str], start: int) -> str:
    """Bloc shell commencant a ``lines[start]`` (le site), jusqu'a sa fermeture.

    On descend en profondeur sur les ``if``/``fi`` et on continue tant qu'une
    autre instruction ``if`` ouvre au meme niveau : le site « upsert » enchaine
    deux `if` (l'upsert lui-meme, puis l'emission du verdict), le site
    « delete » un seul.
    """
    indent = len(lines[start]) - len(lines[start].lstrip())
    depth = 0
    out: list[str] = []
    i = start
    while i < len(lines):
        line = lines[i]
        out.append(line)
        stripped = line.strip()
        if re.match(r"^if\b", stripped):
            depth += 1
        elif stripped == "fi":
            depth -= 1
            if depth == 0:
                nxt = lines[i + 1] if i + 1 < len(lines) else ""
                same_level_if = (
                    re.match(r"^\s*if\b", nxt)
                    and (len(nxt) - len(nxt.lstrip())) == indent
                )
                if not same_level_if:
                    break
        i += 1
    return "".join(out)


def _sites() -> list[tuple[str, int, str, str]]:
    """Les sites ``EXISTING_ID`` encore presents, avec leur NATURE.

    Deux natures, aux consequences OPPOSEES quand la lecture echoue :

    - ``upsert`` : le signal doit etre POSE -- sur echec de lecture, il faut
      poster (un commentaire en double vaut mieux qu'un silence) ;
    - ``delete`` : un marqueur est RETIRE -- sur echec de lecture, il ne faut
      SURTOUT rien supprimer (on ne connait pas l'identifiant).
    """
    found: list[tuple[str, int, str, str]] = []
    for wf in WORKFLOWS:
        lines = wf.read_text(encoding="utf-8").splitlines(keepends=True)
        for i, line in enumerate(lines):
            if SITE_HEAD in line:
                block = _block_at(lines, i)
                kind = "delete" if "api -X DELETE" in block else "upsert"
                found.append((wf.name, i + 1, block, kind))
    return found


SITES = _sites()
IDS = [f"{name}:L{line}-{kind}" for name, line, _, kind in SITES]


class _Proc:
    def __init__(self, stdout="", returncode=0, stderr=""):
        self.stdout = stdout
        self.returncode = returncode
        self.stderr = stderr


def _fake_runner(calls, api_fail=False, write_fail=False):
    """Remplace `gh` : meme forme de reponse que l'API, succes et echec.

    L'echec d'ecriture rend le **document d'erreur sur stdout** en rc=1 --
    c'est le piege de #17265 : un identifiant de commentaire ne doit jamais
    en etre extrait.
    """

    # Le faux `gh` tient un **etat** : un commentaire cree est relu par la
    # lecture suivante. L'organe verifie l'ecriture apres coup (concurrence
    # des workflows, review ai-01 5752268155) : sans etat, un succes ne
    # serait jamais constate.
    comments = []
    next_id = 4242

    def runner(cmd, **kwargs):
        calls.append(" ".join(cmd))
        method = ""
        if "--method" in cmd:
            method = cmd[cmd.index("--method") + 1]
        if method == "POST":
            if write_fail:
                return _Proc(
                    '{"message":"API rate limit exceeded for installation.","status":"403"}',
                    1, "boom")
            body = ""
            if "-f" in cmd:
                body = cmd[cmd.index("-f") + 1].split("=", 1)[1]
            comments.append({
                "id": next_id, "body": body,
                "user": {"login": "github-actions[bot]"},
            })
            return _Proc(json.dumps({"id": next_id}), 0)
        if method == "PATCH":
            if write_fail:
                return _Proc("", 1, "boom")
            body = cmd[cmd.index("-f") + 1].split("=", 1)[1]
            target = next(e for e in cmd if "/comments/" in e).split("/")[-1]
            for c in comments:
                if c["id"] == int(target):
                    c["body"] = body
            return _Proc(json.dumps({"id": int(target)}), 0)
        if api_fail:
            return _Proc(
                '{"message":"API rate limit exceeded for installation.","status":"403"}',
                1, "boom")
        # lecture des commentaires : forme `--slurp` (liste de pages)
        return _Proc(json.dumps([comments]), 0)

    return runner


def _run_organ(tmp_path, args, monkeypatch, api_fail=False, write_fail=False):
    """Execute l'organe partage (CLI) avec un `gh` factice.

    Rend (rc, stdout, stderr, appels `gh`).
    """
    body = tmp_path / "advisory.md"
    body.write_text("**Un avertissement consultatif.**\n", encoding="utf-8")
    calls: list[str] = []
    monkeypatch.setattr(
        a_s, "_default_runner", _fake_runner(calls, api_fail, write_fail))
    argv = ["--pr", "17265", "--organ", "organe-test", *args]
    if "--clear" not in args:
        argv += ["--body-file", str(body)]
    out, err = io.StringIO(), io.StringIO()
    with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
        rc = a_s.main(argv)
    return rc, out.getvalue(), err.getvalue(), calls


# --------------------------------------------------------------------------
# 1. La forme fautive a disparu de TOUS les workflows
# --------------------------------------------------------------------------

def test_la_forme_fautive_a_disparu_de_tous_les_workflows():
    """Plus aucun site `EXISTING_ID` : le canal partage l'a remplace partout.

    Le compte est EXACT : un `>= 1` laisserait passer la reintroduction de
    la forme fautive sur un site ajoute plus tard.
    """
    assert len(SITES) == 0, (
        f"sites `EXISTING_ID` encore presents : {IDS} -- la forme fautive "
        "de #17265 ne doit plus exister dans aucun workflow (#15511)"
    )
    for wf in WORKFLOWS:
        text = wf.read_text(encoding="utf-8")
        assert text.count(FORM_FAUTIVE) == 0, (
            f"{wf.name} : {text.count(FORM_FAUTIVE)} occurrence(s) de "
            f"`{FORM_FAUTIVE}` -- le repli dans la substitution ne peut pas "
            f"effacer un stdout deja ecrit (#17265)"
        )
        assert text.count('|| EXISTING_ID=""') == 0, wf.name


def test_le_canal_partage_est_cable_dans_les_workflows_vivants():
    """Les workflows qui publient des advisory passent par l'organe partage."""
    for wf in LIVE_WORKFLOWS:
        text = wf.read_text(encoding="utf-8")
        assert "scripts/ci/advisory_sticky.py" in text, (
            f"{wf.name} : n'appelle pas l'organe partage -- la section "
            "serait ecrite dans un canal propre, ce que #15511 supprime"
        )


# --------------------------------------------------------------------------
# 2. Le canal partage decide sur le code de sortie
# --------------------------------------------------------------------------

def test_la_forme_ancienne_reproduit_le_defaut(tmp_path):
    """CONTROLE POSITIF de l'instrument -- sans lui, ce fichier ne prouve rien.

    On rejoue la forme d'AVANT sur le meme `gh` factice : EXISTING_ID recoit le
    document d'erreur, la branche PATCH est prise, et l'URL porte le document.
    Si ce test passait (defaut non reproduit), alors les tests d'execution
    ci-dessous seraient verts pour une raison inconnue.
    """
    ancienne = textwrap.dedent(
        """\
        EXISTING_ID=$(gh pr view "$PR_NUMBER" --json comments --jq '.comments[] | .id' 2>/dev/null | head -1 || echo "")
        if [ -n "$EXISTING_ID" ]; then
          gh api -X PATCH "repos/${GH_REPO}/issues/comments/${EXISTING_ID}" -f body="$BODY" 2>/dev/null || true
        else
          gh pr comment "$PR_NUMBER" --body "$BODY" 2>/dev/null || true
        fi
        """
    )
    bindir = tmp_path / "bin"
    bindir.mkdir(exist_ok=True)
    gh = bindir / "gh"
    gh.write_text(FAKE_GH, encoding="utf-8")
    gh.chmod(gh.stat().st_mode | stat.S_IEXEC)
    log = tmp_path / "gh_calls.log"
    log.write_text("", encoding="utf-8")
    script = tmp_path / "bloc.sh"
    script.write_text(ancienne, encoding="utf-8")

    entries = [p.replace("\\", "/") for p in os.environ.get("PATH", "").split(os.pathsep) if p]
    env = dict(
        os.environ,
        PATH=":".join([str(bindir).replace("\\", "/"), *entries]),
        GH_LOG=str(log).replace("\\", "/"),
        GH_REPO="jsboige/CoursIA",
        PR_NUMBER="17265",
        BODY="corps du commentaire advisory",
        GH_FAKE_API_FAIL="1",
    )
    proc = subprocess.run(
        [_bash_exe(), "-eo", "pipefail", str(script).replace("\\", "/")],
        capture_output=True, text=True, encoding="utf-8", env=env,
    )
    calls = log.read_text(encoding="utf-8")
    assert proc.returncode == 0
    assert "api -X PATCH" in calls, f"le defaut n'est pas reproduit : {calls}"
    assert "rate limit exceeded" in calls, (
        "le document d'erreur doit se retrouver DANS l'identifiant de commentaire "
        f"(c'est le defaut) -- appels : {calls}"
    )
    assert "pr comment" not in calls


def test_le_canal_partage_remonte_l_echec_d_ecriture(tmp_path, monkeypatch):
    """`gh` en echec => rc non nul et aucun succes declare.

    C'est la traduction directe de #17265 sur le canal partage : le verdict
    suit l'ECRITURE, pas l'intention. Le workflow voit un rc non nul et
    imprime `::warning::` -- jamais `::notice::`.
    """
    rc, out, err, calls = _run_organ(tmp_path, [], monkeypatch, write_fail=True)
    assert rc != 0, f"l'echec d'ecriture ne doit pas rendre 0 (stdout={out!r})"
    assert "advisory_sticky:" in err, f"l'echec doit etre nomme : {err!r}"
    assert "4242" not in " ".join(calls), (
        "le document d'erreur de `gh` ne doit jamais etre promu identifiant"
    )


def test_le_canal_partage_echoue_si_la_lecture_echoue(tmp_path, monkeypatch):
    """Une lecture en echec est un echec, pas un « rien a signaler »."""
    rc, out, err, calls = _run_organ(tmp_path, [], monkeypatch, api_fail=True)
    assert rc != 0, f"une lecture en echec ne doit pas rendre 0 (stdout={out!r})"
    assert "advisory_sticky:" in err, f"l'echec doit etre nomme : {err!r}"


def test_le_canal_partage_requete_un_commentaire_puis_succes(tmp_path, monkeypatch):
    """Cas nominal : une lecture, une ecriture, un succes *constate*.

    L'identifiant renvoye par l'API est ce que l'organe rapporte : un succes
    sans identifiant n'est pas un succes (#22758).
    """
    rc, out, err, calls = _run_organ(tmp_path, [], monkeypatch)
    assert rc == 0, f"rc={rc} stderr={err!r}"
    assert '"comment_id": 4242' in out, out
    assert any("--method POST" in c for c in calls), calls


def test_le_succes_ne_poste_aucun_commentaire(tmp_path, monkeypatch):
    """Le retrait d'une section absente n'ecrit RIEN (le succes ne parle pas)."""
    rc, out, err, calls = _run_organ(tmp_path, ["--clear"], monkeypatch)
    assert rc == 0, f"rc={rc} stderr={err!r}"
    assert '"action": "silent"' in out, out
    assert not any("--method POST" in c for c in calls), (
        f"le succes ne doit creer aucun commentaire : {calls}"
    )
    assert not any("--method PATCH" in c for c in calls), calls
