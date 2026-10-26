#!/usr/bin/env python3
"""Tests for the hot-subset ratchet wiring in always-on-guards.yml (#15196).

Issue #15196 (5e occurrence du motif #10416 -- un garde aveugle a son
SUJET) : le cliquet hot-subset de traduction (#13551) vit dans
scripts/translation/tests/test_hot_subset_ratchet.py et se declenchait via
scripts-tests.yml, dont le `pull_request` est filtre par
`paths: [scripts/**, tests/**, ...]`. Or la SOURCE qui fait deriver une
ligne CSV (`SRC_DRIFT`) est un edit de notebook sous
`MyIA.AI.Notebooks/**` -- EXACTEMENT hors de ce filtre. Le cliquet ne
tournait donc jamais sur la PR qui pouvait le casser : son sujet etait
hors de son declencheur.

La correction (Option B) absorbe le cliquet comme organe de
always-on-guards.yml, un workflow WITHOUT filtre `paths:` sur son
declencheur (invariant de canary bloquante, cf en-tete du fichier +
regle 2 d'#10045 + #13232). Sa surface nominale est TOUTES les PR : il ne
peut pas etre aveugle au sujet du cliquet.

Ce test epingle la correspondance sujet <-> declencheur. Il ne execute pas
le workflow -- il parse le YAML et verifie :

  (1) le trigger `pull_request` n'a PAS de filtre `paths:` (couverture
      structurelle de `MyIA.AI.Notebooks/**`) et couvre `synchronize`
      (l'edit de notebook pousse sur une PR ouverte) ;
  (2) le workflow invoque bien le cliquet (`id: hot_subset` + le chemin du
      fichier de test) ;
  (3) l'etape AGREGAT collecte `check hot_subset ...` (sans cela, un rouge
      du ratchet ne rougirait jamais le job = la cecite de #15196 sous un
      autre costume).
"""
from __future__ import annotations

import os
import re
import shutil
import subprocess
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]
ALWAYS_ON = REPO_ROOT / ".github" / "workflows" / "always-on-guards.yml"

RATCHET_TEST_REL = "scripts/translation/tests/test_hot_subset_ratchet.py"


def _yaml_text(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def _extract_pull_request_block(yaml_text: str) -> str:
    """Lines of the `on: pull_request:` block, down to the next sibling key.

    Stops at the first line indented to exactly the key level (2 spaces) or a
    top-level comment at that level -- those are the `on:` siblings. Comments
    THAT ARE DIRECT CHILDREN of `pull_request:` (4-space indented) are part of
    the block and are kept, but they only mention ``paths:`` in prose and are
    correctly ignored by the real-key regex below.
    """
    lines = yaml_text.splitlines()
    out: list[str] = []
    in_block = False
    for line in lines:
        if not in_block:
            if re.match(r"^\s*pull_request:\s*$", line):
                in_block = True
                out.append(line)
            continue
        # Sibling key or top-level comment at key indentation (2 spaces).
        if re.match(r"^  \S", line):
            break
        out.append(line)
    return "\n".join(out)


def _has_real_paths_key(block: str) -> bool:
    """A yaml `paths: <value>` key (not ``paths`` mentioned in a comment)."""
    return re.search(r"^[ \t]+paths:[ \t]*(%.*)?$", block, re.MULTILINE) is not None


# ---------------------------------------------------------------------------
# (1) The `pull_request` trigger covers the ratchet's subject structurally.
# ---------------------------------------------------------------------------


def test_always_on_workflow_exists() -> None:
    """The fused always-on workflow must exist -- the organ rides it."""
    assert ALWAYS_ON.is_file(), (
        f"{ALWAYS_ON} introuvable -- le workflow fusionne (#13384) a-t-il "
        f"ete retire ? L'organe hot-subset (#15196) vivrait sur rien."
    )


def test_pull_request_trigger_has_no_paths_filter() -> None:
    """The `pull_request` trigger must NOT carry a `paths:` filter.

    always-on-guards.yml est la canary bloquante (en-tete du fichier +
    pr-gate.yml) : elle doit rendre un verdict sur TOUTE PR, y compris celles
    qui ne declenchent aucun autre CI. Un filtre `paths:` la desarmerait sur
    les PR hors-scope (#13232) -- et pour le cliquet hot-subset, un edit de
    notebook (`MyIA.AI.Notebooks/**`, le SUJET du cliquet) sortirait du filtre,
    rendant le cliquet aveugle comme sous scripts-tests.yml (#15196).
    """
    text = _yaml_text(ALWAYS_ON)
    trigger = _extract_pull_request_block(text)
    assert not _has_real_paths_key(trigger), (
        "always-on-guards.yml `pull_request:` porte un filtre `paths:` :\n"
        f"{trigger}\nRegle 2 d'#10045 + #13232 : un garde filtre par chemins "
        f"reste `pending` / est desarme sur les PR hors-scope. Retire-le -- "
        f"c'est precisement la cecite que #15196 corrige."
    )


def test_pull_request_trigger_covers_synchronize() -> None:
    """The trigger must include `synchronize` (the notebook-edit push).

    L'espece de PR qui fait deriver une ligne CSV est un edit de notebook
    pousse sur une PR deja ouverte -> `synchronize`. Sans ce type, le cliquet
    ne tournerait pas au moment ou il sert.
    """
    text = _yaml_text(ALWAYS_ON)
    trigger = _extract_pull_request_block(text)
    assert "synchronize" in trigger, (
        f"Le trigger `pull_request:` doit couvrir `synchronize` (edit de "
        f"notebook pousse sur PR ouverte) :\n{trigger}"
    )


# ---------------------------------------------------------------------------
# (2) The workflow invokes the hot-subset ratchet as an organ.
# ---------------------------------------------------------------------------


def test_workflow_invokes_hot_subset_ratchet() -> None:
    """always-on-guards.yml doit executer le cliquet hot-subset."""
    text = _yaml_text(ALWAYS_ON)
    assert "id: hot_subset" in text, (
        "Organe hot_subset manquant : always-on-guards.yml doit porter une "
        "etape avec `id: hot_subset` (l'agregat la collecte)."
    )
    assert RATCHET_TEST_REL in text, (
        f"L'organe hot_subset doit invoquer le cliquet "
        f"`python -m pytest {RATCHET_TEST_REL}`."
    )


def test_hot_subset_is_blocking_organ() -> None:
    """L'organe doit etre bloquant : `continue-on-error: true` + `exit 1`."""
    text = _yaml_text(ALWAYS_ON)
    id_match = re.search(
        r'(?ms)^\s*- name:.*\n\s*id: hot_subset\n((?:\s+.*\n?)+)', text
    )
    assert id_match is not None, "id: hot_subset introuvable."
    step = id_match.group(1)
    assert "continue-on-error: true" in step, (
        "L'organe hot_subset doit porter `continue-on-error: true` (l'etape "
        "veut rougir AU TRAVERS de l'agregat, pas arreter les organes "
        "suivants)."
    )
    assert "exit 1" in step, (
        "L'organe hot_subset doit `exit 1` quand le ratchet echoue (sinon "
        "l'echec est avale)."
    )


# ---------------------------------------------------------------------------
# (3) The aggregate collects the ratchet's outcome.
# ---------------------------------------------------------------------------


def test_aggregate_collects_hot_subset() -> None:
    """L'etape AGREGAT doit collecter `check hot_subset ...`.

    Sans cette ligne, un rouge du ratchet ne rougirait jamais le job -- le
    cliquet passerait en silence = la cecite de #15196, mais en plus silencieux.
    """
    text = _yaml_text(ALWAYS_ON)
    assert "check hot_subset" in text and "steps.hot_subset.outcome" in text, (
        "L'etape AGREGAT doit collecter `check hot_subset \"${{ "
        "steps.hot_subset.outcome }}\"`. (Les outcomes sont injectes au "
        "templating du workflow, chaque organe est enumere explicitement.)"
    )


# ---------------------------------------------------------------------------
# (4) #22435 -- un code retour de pytest n'est pas un verdict de contenu.
#
# Le corps de l'etape traduisait tout rc non nul en « SRC_DRIFT » : un rc 2
# (collecte interrompue, `ImportError` du toolcache) imprimait un verdict de
# derive de traduction alors que la mesure n'avait pas eu lieu. Mesure du
# 25/10 : #22130 et #22264, ratchet pourtant vert sur leur tete exacte.
#
# Ces tests EXECUTENT le corps de l'etape (stubbe : pas de pytest, pas de
# reseau) au lieu de lire sa prose -- le defaut etait precisement que le
# shell disait autre chose que ce qu'il mesurait. Un test de texte n'aurait
# pas vu la difference entre « ecrit NON MESURE » et « sort en 0 ».
# ---------------------------------------------------------------------------

PYTEST_LINE = (
    "python -m pytest scripts/translation/tests/test_hot_subset_ratchet.py "
    "-q && RC=0 || RC=$?"
)
DIFF_LINE = (
    'git diff --no-renames --name-only "origin/${BASE}...HEAD" '
    "> /tmp/hot_subset_diff.txt 2>/dev/null"
)
# #22472 : deuxieme chemin de lecture (SHA de base de l'evenement) du regime
# INDECISE -- le stub doit couvrir les DEUX lectures pour que les tests
# pilotent reellement le chemin pris.
FALLBACK_LINE = (
    'git diff --no-renames --name-only "${PR_BASE_SHA}...HEAD" '
    "> /tmp/hot_subset_diff.txt 2>/dev/null"
)

BASH = shutil.which("bash")


def _hot_subset_run_body() -> str:
    """Corps `run: |` de l'etape hot_subset, dedente (indentation retiree)."""
    lines = _yaml_text(ALWAYS_ON).splitlines()
    start = None
    for i, line in enumerate(lines):
        if re.match(r"^\s*id: hot_subset\s*$", line):
            start = i
            break
    assert start is not None, "id: hot_subset introuvable."
    run_at = None
    for i in range(start, min(start + 40, len(lines))):
        m = re.match(r"^(\s*)run: \|\s*$", lines[i])
        if m:
            run_at, indent = i, len(m.group(1))
            break
    assert run_at is not None, "corps `run: |` de hot_subset introuvable."
    body: list[str] = []
    for line in lines[run_at + 1:]:
        if not line.strip():
            body.append("")
            continue
        cur = len(line) - len(line.lstrip())
        if cur <= indent:
            break
        body.append(line[indent + 2:])
    return "\n".join(body) + "\n"


def _run_step(rc: int, changed: list[str] | None, fallback: list[str] | None = None):
    """Execute le corps de l'etape avec un rc de pytest impose.

    ``changed`` = chemins du diff simule ; ``None`` = diff illisible.
    ``fallback`` = chemins du SECOND chemin de lecture (PR_BASE_SHA) quand
    le premier echoue ; ``None`` = second chemin absent/inactif.

    Renvoie ``(proc, regime_path)`` : ``regime_path`` est le fichier
    ``GITHUB_OUTPUT`` capture -- sa derniere ligne ``regime=`` est le
    regime effectivement exporte vers l'agregat (#22472).
    """
    body = _hot_subset_run_body()
    for needle in (
        "pip install --quiet pytest",
        PYTEST_LINE,
        DIFF_LINE,
        FALLBACK_LINE,
    ):
        assert needle in body, (
            f"Le corps de l'etape ne contient plus `{needle}` : adapter ce "
            f"test, sinon il stube a cote et n'execute plus rien."
        )
    body = body.replace("pip install --quiet pytest", ":")
    body = body.replace(PYTEST_LINE, f"RC={rc}")
    if changed is None:
        body = body.replace(DIFF_LINE, "false > /tmp/hot_subset_diff.txt 2>/dev/null")
    elif changed:
        body = body.replace(
            DIFF_LINE,
            "printf '%s\\n' " + " ".join(changed)
            + " > /tmp/hot_subset_diff.txt 2>/dev/null",
        )
    else:
        body = body.replace(DIFF_LINE, ": > /tmp/hot_subset_diff.txt")
    if fallback is None:
        body = body.replace(FALLBACK_LINE, "false > /tmp/hot_subset_diff.txt 2>/dev/null")
    elif fallback:
        body = body.replace(
            FALLBACK_LINE,
            "printf '%s\\n' " + " ".join(fallback)
            + " > /tmp/hot_subset_diff.txt 2>/dev/null",
        )
    else:
        body = body.replace(FALLBACK_LINE, ": > /tmp/hot_subset_diff.txt")
    import tempfile

    regime_fd, regime_path = tempfile.mkstemp(suffix=".github_output")
    os.close(regime_fd)
    env = dict(os.environ, GITHUB_BASE_REF="main", GITHUB_OUTPUT=regime_path)
    if fallback is None:
        env["PR_BASE_SHA"] = ""
    else:
        env["PR_BASE_SHA"] = "0000000000000000000000000000000000000000"
    proc = subprocess.run(
        [BASH, "-s"], input=body.encode("utf-8"), capture_output=True, env=env
    )
    return proc, Path(regime_path)


def _regime_of(regime_path: Path) -> str:
    """Derniere ligne ``regime=`` exportee par le corps execute."""
    last = ""
    for line in regime_path.read_text(encoding="utf-8").splitlines():
        if line.startswith("regime="):
            last = line[len("regime="):]
    return last


def _out(proc) -> str:
    return (proc.stdout + proc.stderr).decode("utf-8", "replace")


@pytest.mark.skipif(BASH is None, reason="bash absent : corps d'etape non executable")
def test_rc0_is_green() -> None:
    """rc 0 : la mesure a eu lieu, aucun verdict de derive."""
    proc, regime = _run_step(0, ["MyIA.AI.Notebooks/x.ipynb"])
    assert proc.returncode == 0, _out(proc)
    assert "::error::" not in _out(proc), _out(proc)
    assert _regime_of(regime) == "MESURE-VERT"


@pytest.mark.skipif(BASH is None, reason="bash absent : corps d'etape non executable")
def test_rc1_is_the_content_verdict_and_still_blocks() -> None:
    """rc 1 = des tests ont echoue : le seul rc qui parle du contenu."""
    proc, regime = _run_step(1, ["MyIA.AI.Notebooks/x.ipynb"])
    assert proc.returncode == 1, _out(proc)
    out = _out(proc)
    assert "::error::" in out and "SRC_DRIFT" in out, out
    assert _regime_of(regime) == "VERDICT-CONTENU"


@pytest.mark.skipif(BASH is None, reason="bash absent : corps d'etape non executable")
def test_rc2_on_a_notebook_pr_does_not_block() -> None:
    """rc 2 sur une PR hors organe : NON MESURE, pas SRC_DRIFT, non bloquant.

    C'est le cas fondateur (#22130, #22264) : un `ImportError` du toolcache
    partage rougissait une PR dont le contenu etait vert.
    """
    proc, regime = _run_step(2, ["MyIA.AI.Notebooks/x.ipynb"])
    assert proc.returncode == 0, _out(proc)
    out = _out(proc)
    assert "::warning::" in out and "NON MESURE" in out, out
    assert _regime_of(regime) == "NON-MESURE"


@pytest.mark.skipif(BASH is None, reason="bash absent : corps d'etape non executable")
def test_rc2_on_an_organ_pr_blocks_and_names_attribution() -> None:
    """rc 2 sur une PR qui touche l'organe : la cause est attribuable, rouge."""
    proc, regime = _run_step(2, ["scripts/translation/x.py"])
    assert proc.returncode == 1, _out(proc)
    out = _out(proc)
    assert "::error::" in out and "ATTRIBUABLE" in out, out
    assert _regime_of(regime) == "NON-MESURE-ATTRIBUABLE"


@pytest.mark.skipif(BASH is None, reason="bash absent : corps d'etape non executable")
def test_rc2_with_unreadable_diff_stays_non_blocking() -> None:
    """Diff illisible des DEUX chemins : la cause reste a etablir -- jamais un rouge invente.

    Les deux lectures (origin/BASE puis PR_BASE_SHA) echouent : regime
    NON-MESURE-INDECISE, non bloquant, en le disant.
    """
    proc, regime = _run_step(2, None)
    assert proc.returncode == 0, _out(proc)
    out = _out(proc)
    assert "INDECISE" in out and "NON MESURE" in out, out
    assert _regime_of(regime) == "NON-MESURE-INDECISE"


# ---------------------------------------------------------------------------
# (5) #22472 -- reserves NanoClaw : le regime NON MESURE doit etre visible au
# niveau du job (outputs.regime + agregat), et l'INDECISE tente un deuxieme
# chemin de lecture par le SHA de base de l'evenement avant de renoncer.
# ---------------------------------------------------------------------------


@pytest.mark.skipif(BASH is None, reason="bash absent : corps d'etape non executable")
def test_rc2_primary_unreadable_fallback_blocks_on_organ_pr() -> None:
    """origin/BASE illisible MAIS PR_BASE_SHA lisible + PR organe : rouge.

    Reserve 2 de #22472 : le seul regime BLOQUANT neuf de #22435 ne devait
    pas dependre de la seule sante du fetch origin -- le SHA de base de
    l'evenement est local au payload et fournit un second chemin.
    """
    proc, regime = _run_step(2, None, fallback=["scripts/translation/x.py"])
    assert proc.returncode == 1, _out(proc)
    out = _out(proc)
    assert "::error::" in out and "ATTRIBUABLE" in out and "PR_BASE_SHA" in out, out
    assert _regime_of(regime) == "NON-MESURE-ATTRIBUABLE"


@pytest.mark.skipif(BASH is None, reason="bash absent : corps d'etape non executable")
def test_rc2_primary_unreadable_fallback_non_organ_stays_green() -> None:
    """origin/BASE illisible, PR_BASE_SHA lisible, PR hors organe : vert dit."""
    proc, regime = _run_step(2, None, fallback=["MyIA.AI.Notebooks/x.ipynb"])
    assert proc.returncode == 0, _out(proc)
    out = _out(proc)
    assert "::warning::" in out and "NON MESURE" in out, out
    assert _regime_of(regime) == "NON-MESURE"


def test_step_exports_regime_for_every_branch() -> None:
    """Les 5 regimes sont exportes vers GITHUB_OUTPUT (outputs.regime).

    Reserve 1 de #22472 : sans export, l'agregat ne peut pas dire « organes
    verts ou NON MESURES » -- le regime vivrait uniquement dans le log du
    step.
    """
    body = _hot_subset_run_body()
    for regime in (
        "MESURE-VERT",
        "VERDICT-CONTENU",
        "NON-MESURE-ATTRIBUABLE",
        "NON-MESURE",
        "NON-MESURE-INDECISE",
    ):
        assert f'echo "regime={regime}" >>' in body, (
            f"export regime={regime} manquant (GITHUB_OUTPUT)"
        )
    assert '>> "${GITHUB_OUTPUT:-/dev/null}"' in body, (
        "L'export doit ecrire dans ${GITHUB_OUTPUT} avec repli /dev/null "
        "(le harnais execute le corps hors runner)."
    )


def test_aggregate_surfaces_non_mesure_regime() -> None:
    """L'agregat doit dire « organes verts ou NON MESURES » quand c'est le cas.

    Reserve 1 de #22472 : un NON MESURE laisse le statut PR vert (doctrine
    #8819) -- s'il ne se lit que dans le log du step, un runner
    durablement casse produit des PR vertes dont personne ne voit que la
    garde etait aveugle.
    """
    text = _yaml_text(ALWAYS_ON)
    assert "steps.hot_subset.outputs.regime" in text, (
        "L'agregat doit lire `steps.hot_subset.outputs.regime` (l'export du "
        "regime par le step hot_subset ne sert a rien sans consommateur)."
    )
    assert "NON MESURES" in text, (
        "L'agregat doit porter la mention « organes verts ou NON MESURES » "
        "quand le regime hot-subset est un NON-MESURE."
    )


# ---------------------------------------------------------------------------
# (6) #22472 -- reserve Hermes du 25/10 13:01Z : l'attribution ne couvrait pas
# l'organe de l'organe. Le motif etait `^scripts/(translation|notebook_tools)/`
# seul : une PR qui casse le harnais de cablage, ou le workflow qui porte
# l'etape, et fait echouer la collecte pytest repartait VERTE sous NON-MESURE,
# alors que la cause lui est entierement attribuable. Meme classe que la
# reserve 2 fermee par le commit precedent -- la fragilite avait ete retiree du
# fetch, pas du perimetre.
#
# Le motif est aussi ramene a UNE definition partagee par les deux chemins de
# lecture : deux copies textuelles identiques derivent a la premiere edition.
# ---------------------------------------------------------------------------

PERIMETRE_ATTRIBUABLE = [
    "scripts/translation/x.py",
    "scripts/notebook_tools/x.py",
    ".github/workflows/always-on-guards.yml",
    "scripts/tests/test_hot_subset_ratchet_wiring.py",
]


@pytest.mark.skipif(BASH is None, reason="bash absent : corps d'etape non executable")
@pytest.mark.parametrize("path", PERIMETRE_ATTRIBUABLE)
def test_rc2_on_any_perimeter_file_blocks(path: str) -> None:
    """rc 2 + un fichier du perimetre de l'organe : rouge, cause attribuable.

    Inclut l'organe de l'organe : le workflow qui porte l'etape et le harnais
    qui epingle son cablage (#22472).
    """
    proc, regime = _run_step(2, [path])
    assert proc.returncode == 1, _out(proc)
    out = _out(proc)
    assert "::error::" in out and "ATTRIBUABLE" in out, out
    assert path in out, f"le message doit nommer le fichier attribuable : {out}"
    assert _regime_of(regime) == "NON-MESURE-ATTRIBUABLE"


@pytest.mark.skipif(BASH is None, reason="bash absent : corps d'etape non executable")
def test_rc2_on_the_wiring_harness_blocks_via_fallback_too() -> None:
    """Le second chemin (PR_BASE_SHA) applique le MEME perimetre elargi."""
    proc, regime = _run_step(
        2, None, fallback=["scripts/tests/test_hot_subset_ratchet_wiring.py"]
    )
    assert proc.returncode == 1, _out(proc)
    out = _out(proc)
    assert "::error::" in out and "ATTRIBUABLE" in out and "PR_BASE_SHA" in out, out
    assert _regime_of(regime) == "NON-MESURE-ATTRIBUABLE"


def test_attribution_perimeter_is_defined_once_and_shared() -> None:
    """Le perimetre est defini UNE fois et consomme par les DEUX lectures.

    Deux copies du motif derivent a la premiere edition : le chemin principal
    et le repli PR_BASE_SHA doivent lire la meme variable.
    """
    body = _hot_subset_run_body()
    assert body.count("ORGANE_RE=") == 1, (
        "Le perimetre d'attribution doit etre defini une seule fois "
        "(ORGANE_RE=) : deux copies deriveraient.\n" + body
    )
    assert body.count('grep -E "$ORGANE_RE"') == 2, (
        "Les DEUX chemins de lecture du diff (origin/BASE et PR_BASE_SHA) "
        "doivent consommer $ORGANE_RE.\n" + body
    )
    assert "'^scripts/(translation|notebook_tools)/'" not in body, (
        "Un grep sur le motif litteral subsiste : il contourne ORGANE_RE et "
        "reintroduit la derive que ce test ferme.\n" + body
    )


# ---------------------------------------------------------------------------
# #22472 — renames sortants : `--name-only` n'affiche que la DESTINATION.
# Un fichier renomme HORS du perimetre disparaissait de la liste, et la PR
# repartait non attribuable alors que la cause lui etait imputable. Les deux
# lectures portent `--no-renames` (decomposition suppression + ajout).
# ---------------------------------------------------------------------------


@pytest.mark.skipif(BASH is None, reason="bash absent : corps d'etape non executable")
def test_rename_out_of_perimeter_is_attribuable() -> None:
    """Un rename sortant est vu : les DEUX chemins sortent du diff simule.

    C'est la sortie que produit `--no-renames` pour un `git mv` hors du
    perimetre : l'ancien chemin (dans le perimetre) et le nouveau.
    """
    proc, regime = _run_step(2, ["docs_x.py", "scripts/translation/x.py"])
    assert proc.returncode == 1, _out(proc)
    out = _out(proc)
    assert "ATTRIBUABLE" in out, out
    assert "scripts/translation/x.py" in out, (
        f"le message doit nommer le chemin source du rename : {out}"
    )
    assert _regime_of(regime) == "NON-MESURE-ATTRIBUABLE"


def test_both_diff_reads_disable_rename_detection() -> None:
    """Les deux lectures passent `--no-renames`, sinon le point se rouvre.

    Un seul `--name-only` nu suffit a rendre un rename sortant invisible : la
    garde doit porter le drapeau sur CHAQUE chemin de lecture.
    """
    body = _hot_subset_run_body()
    assert body.count("git diff --no-renames --name-only") == 2, (
        "les DEUX lectures du diff (origin/BASE et PR_BASE_SHA) doivent "
        "desactiver la detection de rename.\n" + body
    )
    assert 'git diff --name-only' not in body, (
        "une lecture `git diff --name-only` sans `--no-renames` subsiste : "
        "elle est aveugle au chemin source d'un rename.\n" + body
    )


def test_git_name_only_really_hides_the_rename_source(tmp_path: Path) -> None:
    """La premisse du drapeau est mesuree, pas supposee.

    Sur un vrai depot : `--name-only` seul ne rend que la destination, et
    `--no-renames` rend les deux chemins. Si git changeait ce comportement, ce
    test tombe et le drapeau pourra etre retire en connaissance de cause.
    """
    git = shutil.which("git")
    if git is None:
        pytest.skip("git absent")

    def g(*args: str) -> str:
        proc = subprocess.run([git, "-C", str(tmp_path), *args],
                              capture_output=True, text=True,
                              encoding="utf-8", errors="replace")
        assert proc.returncode == 0, proc.stderr
        return proc.stdout

    g("init", "-q", ".")
    g("config", "user.email", "t@example.invalid")
    g("config", "user.name", "t")
    src = tmp_path / "scripts" / "translation"
    src.mkdir(parents=True)
    (src / "x.py").write_text("contenu assez long pour un rename\n" * 4,
                              encoding="utf-8")
    g("add", "-A")
    g("commit", "-qm", "base")
    g("mv", "scripts/translation/x.py", "docs_x.py")
    with open(tmp_path / "docs_x.py", "a", encoding="utf-8") as f:
        f.write("ligne ajoutee\n")
    g("commit", "-qam", "rename")

    plain = g("diff", "--name-only", "HEAD~1...HEAD")
    no_renames = g("diff", "--no-renames", "--name-only", "HEAD~1...HEAD")
    assert "scripts/translation/x.py" not in plain, (
        "git rend desormais le chemin source sous --name-only : le drapeau "
        "n'est plus necessaire, verifier avant de le retirer.\n" + plain
    )
    assert "scripts/translation/x.py" in no_renames, no_renames
    assert "docs_x.py" in no_renames, no_renames

