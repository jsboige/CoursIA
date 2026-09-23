"""#17265 -- un document d'erreur de `gh` n'est pas un identifiant de commentaire.

Contexte. Quatre sites du harnais ecrivaient :

    EXISTING_ID=$(gh pr view "$PR_NUMBER" --json comments --jq '...' 2>/dev/null | head -1 || echo "")

Le `||` porte sur le rc du DERNIER maillon du pipeline. Mais meme sous
`-o pipefail` -- et le shell des workflows est bien `bash -eo pipefail` -- ce
repli ne corrige rien : `gh` ecrit son **document d'erreur sur stdout** en rc=1,
et un repli place DANS la substitution ne peut pas **effacer un stdout deja
ecrit**. Mesure a deux bras (gh factice qui echoue en ecrivant sur stdout),
reprise ici par `test_la_forme_ancienne_reproduit_le_defaut` :

    avant : api -X PATCH repos/.../comments/{"message":"API rate limit exceeded..."}
    apres : pr comment <n> --body ...

Consequence avant correctif : sur une panne de quota, le commentaire advisory
n'etait **jamais poste** (la branche `else` qui l'aurait poste etait sautee) et
un marqueur perime n'etait **pas retire** -- les deux echecs avales par
`2>/dev/null || true`, pendant que le `::notice::` affirmait le contraire.

Ce fichier execute les 4 blocs **reellement presents** dans les workflows
(extraits du TEXTE, pas du YAML : c'est le texte qui tourne) avec un `gh`
factice, dans les trois modes -- API en echec / marqueur present / marqueur
absent -- et sous les deux jeux de flags du shell.

Le controle positif de l'instrument est explicite : la forme ANCIENNE est
rejouee et doit **reproduire** le defaut. Sans lui, un harnais incapable de
distinguer les deux formes passerait vert sur les deux -- et ne prouverait rien.

Hors scope, mesure et non corrige ici : les sites `if ! gh pr view ... | grep -qF`
(always-on-guards.yml L402/L654) prennent, eux, la branche « poster » quand `gh`
echoue -- direction benigne (un doublon au lieu d'un silence). Ils ne sont pas
la meme classe et ne sont pas dans l'issue.

Le resolveur `_bash_exe` est une copie assumee de celui de
`test_always_on_guards_live_body.py` : ce dernier est modifie par une PR
ouverte (#17260, meme famille de defaut), et importer un helper prive d'un
fichier en vol ferait rougir ce test pour une raison sans rapport.
"""

import os
import pathlib
import re
import stat
import subprocess
import textwrap

import pytest

REPO_ROOT = pathlib.Path(__file__).resolve().parents[2]
WORKFLOWS = (
    REPO_ROOT / ".github" / "workflows" / "always-on-guards.yml",
    REPO_ROOT / ".github" / "workflows" / "variation-light-genre.yml",
)
SITE_HEAD = 'EXISTING_ID=$(gh pr view "$PR_NUMBER" --json comments'
FORM_FAUTIVE = 'head -1 || echo ""'
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
      [ "${GH_FAKE_WRITE_FAIL:-}" = "1" ] && exit 1
      echo "API_CALL"
      exit 0
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
    """Les 4 sites, avec le bloc shell qui les entoure et leur NATURE.

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
UPSERTS = [s for s in SITES if s[3] == "upsert"]
DELETES = [s for s in SITES if s[3] == "delete"]


def _run(block: str, tmp_path, flags: str, api_fail=False, marker_id="", write_fail=False):
    """Execute un bloc avec un `gh` factice. Rend (stdout, appels, rc)."""
    bindir = tmp_path / "bin"
    bindir.mkdir(exist_ok=True)
    gh = bindir / "gh"
    gh.write_text(FAKE_GH, encoding="utf-8")
    gh.chmod(gh.stat().st_mode | stat.S_IEXEC)
    log = tmp_path / "gh_calls.log"
    log.write_text("", encoding="utf-8")
    script = tmp_path / "bloc.sh"
    script.write_text(block, encoding="utf-8")

    # bash (Git Bash / runner Linux) ne lit pas un PATH mixte : un PATH
    # ':'-sepague d'entrees ';'-separees est re-parse par MSYS et le bin/ du gh
    # factice se perd -- c'est le gh REEL qui repond alors.
    entries = [p.replace("\\", "/") for p in os.environ.get("PATH", "").split(os.pathsep) if p]
    env = dict(
        os.environ,
        PATH=":".join([str(bindir).replace("\\", "/"), *entries]),
        GH_LOG=str(log).replace("\\", "/"),
        GH_REPO="jsboige/CoursIA",
        PR_NUMBER="17265",
        MARK="**G-VAR-2/3 GENRE signals**",
        BODY="corps du commentaire advisory",
        LANE="myia-po-2026:CoursIA",
        TALLY="0/1",
        GH_FAKE_ID=marker_id,
    )
    if api_fail:
        env["GH_FAKE_API_FAIL"] = "1"
    if write_fail:
        env["GH_FAKE_WRITE_FAIL"] = "1"
    proc = subprocess.run(
        [_bash_exe(), *flags.split(), str(script).replace("\\", "/")],
        capture_output=True, text=True, encoding="utf-8", env=env,
    )
    calls = log.read_text(encoding="utf-8")
    return proc.stdout, calls, proc.returncode


def test_les_quatre_sites_decident_sur_le_code_de_sortie():
    """La forme fautive a disparu des 4 sites, et il y en a bien 4 -- 2 + 2.

    Le compte est EXACT : un `>= 4` laisserait passer la reintroduction de la
    forme fautive sur un 5e site ajoute plus tard.
    """
    assert len(SITES) == 4, f"sites trouves : {IDS}"
    assert len(UPSERTS) == 2 and len(DELETES) == 2, IDS
    for wf in WORKFLOWS:
        text = wf.read_text(encoding="utf-8")
        assert text.count(FORM_FAUTIVE) == 0, (
            f"{wf.name} : {text.count(FORM_FAUTIVE)} occurrence(s) de "
            f"`{FORM_FAUTIVE}` -- le repli dans la substitution ne peut pas "
            f"effacer un stdout deja ecrit (#17265)"
        )
        assert text.count('|| EXISTING_ID=""') == 2, wf.name


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
    _, calls, rc = _run(ancienne, tmp_path, "-eo pipefail", api_fail=True)
    assert rc == 0
    assert "api -X PATCH" in calls, f"le defaut n'est pas reproduit : {calls}"
    assert "rate limit exceeded" in calls, (
        "le document d'erreur doit se retrouver DANS l'identifiant de commentaire "
        f"(c'est le defaut) -- appels : {calls}"
    )
    assert "pr comment" not in calls


@pytest.mark.parametrize("flags", ["-e", "-eo pipefail"])
@pytest.mark.parametrize("site", UPSERTS, ids=[s[0] + f":L{s[1]}" for s in UPSERTS])
def test_api_en_echec_le_signal_est_pose_quand_meme(site, flags, tmp_path):
    """Acceptance 1 + 3 : `gh` en echec => EXISTING_ID vide => on POSTE.

    Les deux jeux de flags sont exerces parce que la consequence depend de qui
    porte le rc du pipeline : le point du correctif est justement de ne plus en
    dependre.
    """
    name, line, block, _ = site
    _, calls, rc = _run(block, tmp_path, flags, api_fail=True)
    assert rc == 0, f"{name}:L{line} sort en {rc} sous `bash {flags}`"
    assert "pr comment" in calls, (
        f"{name}:L{line} -- aucune ecriture tentee alors que `gh` a echoue : "
        f"c'est exactement le silence que #17265 corrige. Appels : {calls}"
    )
    assert "rate limit exceeded" not in calls, (
        f"{name}:L{line} -- le document d'erreur est encore pris pour une donnee : {calls}"
    )


@pytest.mark.parametrize("flags", ["-e", "-eo pipefail"])
@pytest.mark.parametrize("site", DELETES, ids=[s[0] + f":L{s[1]}" for s in DELETES])
def test_api_en_echec_aucun_retrait_sur_un_identifiant_inconnu(site, flags, tmp_path):
    """Contrepartie des sites `delete` : ne RIEN supprimer quand on ignore l'id.

    La consequence est l'inverse de l'upsert -- poster serait un doublon benin,
    supprimer sur un identifiant devine serait une ecriture non voulue. Le
    point commun est le meme correctif : decider sur le rc.
    """
    name, line, block, _ = site
    _, calls, rc = _run(block, tmp_path, flags, api_fail=True)
    assert rc == 0, f"{name}:L{line} sort en {rc} sous `bash {flags}`"
    assert "api -X DELETE" not in calls, (
        f"{name}:L{line} -- un DELETE est tente alors que la lecture a echoue : {calls}"
    )
    assert "rate limit exceeded" not in calls, (
        f"{name}:L{line} -- le document d'erreur est promu identifiant : {calls}"
    )


@pytest.mark.parametrize("site", SITES, ids=IDS)
def test_marqueur_existant_reutilise_le_meme_identifiant(site, tmp_path):
    """Acceptance 2 : non-regression de la semantique « mettre a jour ».

    Le marqueur existe deja => PATCH (upsert) ou DELETE (retrait) sur SON
    identifiant, jamais un nouveau commentaire : l'idempotence du signalement
    est la raison d'etre du site.
    """
    name, line, block, kind = site
    _, calls, rc = _run(block, tmp_path, "-eo pipefail", marker_id="555")
    assert rc == 0
    assert "555" in calls, f"{name}:L{line} -- le marqueur existant n'est pas reutilise : {calls}"
    assert "pr comment" not in calls, (
        f"{name}:L{line} -- un second commentaire est cree au lieu de reutiliser le marqueur : {calls}"
    )


@pytest.mark.parametrize("site", UPSERTS, ids=[s[0] + f":L{s[1]}" for s in UPSERTS])
def test_marqueur_absent_poste_un_commentaire(site, tmp_path):
    """Cas nominal inchange : aucun marqueur => un commentaire est cree."""
    name, line, block, _ = site
    _, calls, rc = _run(block, tmp_path, "-eo pipefail")
    assert rc == 0
    assert "pr comment" in calls, f"{name}:L{line} : {calls}"


@pytest.mark.parametrize("site", SITES, ids=IDS)
def test_echec_d_ecriture_ne_se_declare_pas_signale(site, tmp_path):
    """Acceptance 4 : le verdict du log suit l'ECRITURE, pas l'intention.

    Quand l'ecriture echoue elle-meme, le site doit le dire (un `::warning::`)
    et non affirmer un signalement qui n'a pas eu lieu.
    """
    name, line, block, kind = site
    out, _, rc = _run(block, tmp_path, "-eo pipefail", marker_id="555", write_fail=True)
    assert rc == 0, f"{name}:L{line} : l'echec doit etre RAPPORTE, pas propage"
    assert "::warning::" in out, (
        f"{name}:L{line} -- echec d'ecriture silencieux. Sortie : {out!r}"
    )
    assert "::notice::" not in out, (
        f"{name}:L{line} -- un ::notice:: est emis alors qu'aucune ecriture n'a abouti"
    )
