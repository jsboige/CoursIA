"""Cas d'essai #28534 : la fusion des deux workflows de la classe `edited`.

Ce que la fusion change
-----------------------
`always-on-metadata-guards.yml` (3 organes de METADONNEES) et
`always-on-guards-body.yml` (5 organes de BODY) sont deux workflows
autonomes sur `pull_request` : deux runs et deux slots de runner par evenement
de PR, pour deux jobs qui lisent les memes surfaces. La fusion les reunit en
`always-on-guards-edited.yml` : un workflow, un job, un checkout.

Ce que la fusion NE doit PAS faire (criteres de #28534)
--------------------------------------------------------
1. **Remplacer les deux gardes `if:` par leur union.** Les deux jobs n'avaient
   pas la meme garde : le job de metadonnees ne parle a l'edited que si la
   BASE a change ; le job de body parle a toute edition de corps. Une union
   posee au niveau du job ferait parler les organes de metadonnees sur une
   edition de corps -- et le run vert qui en resulted effacerait le verdict de
   metadonnees (le fold de `pr_gate.py` plie par NOM).
2. **Confondre les classes d'edition dans le groupe de concurrence.** Une
   edition de body ne doit pas annuler le run de metadonnees en file, ni
   reciproquement (#11649).
3. **Introduire un `paths:`** (verrou #13232, regle 2 d'#10045) ni un filtre
   `branches:` (base-not-main doit voir les PR dont la base n'est PAS main,
   #10918).

Ce qu'elle ne couvre PAS : le comportement runtime de GitHub Actions (les
runs reels, les slots, les annulations) -- mesure dans le body de la PR de
livraison et par le commentaire de mesure 24 h apres le merge.
"""
from __future__ import annotations

import subprocess
import sys
from pathlib import Path

import yaml

REPO_ROOT = Path(__file__).resolve().parents[3]
WORKFLOWS = REPO_ROOT / ".github" / "workflows"
MERGED_WF = WORKFLOWS / "always-on-guards-edited.yml"
MERGED_JOB = "always-on-guards-edited"

# Les deux sources dormantes : leurs jobs sont conserves verbatim, mais ils
# ne doivent plus se declencher sur une PR.
SOURCES = (
    WORKFLOWS / "always-on-metadata-guards.yml",
    WORKFLOWS / "always-on-guards-body.yml",
)

# La garde de chaque groupe d'organes, telle qu'elle etait portee par le job
# d'origine. Elle est NOTEE ICI pour que la fusion ne puisse pas la diluer.
META_GUARD = "github.event.changes.base != null"
BODY_GUARD = "github.event.changes.body != null"


def _load(path: Path) -> dict:
    return yaml.safe_load(path.read_text(encoding="utf-8"))


def _doc() -> dict:
    return _load(MERGED_WF)


def _job() -> dict:
    return _doc()["jobs"][MERGED_JOB]


def _steps() -> list[dict]:
    return _job()["steps"]


def _step(prefix: str) -> dict:
    matches = [s for s in _steps() if str(s.get("name", "")).startswith(prefix)]
    assert len(matches) == 1, "etape introuvable ou dedoublonnee : %s" % prefix
    return matches[0]


def _trigger(doc: dict) -> dict:
    on = doc.get("on", doc.get(True)) or {}
    return on["pull_request"]


# ------------------------------------------- 1. un workflow, un job, un checkout

def test_one_job_only():
    """Un fichier par responsabilite (PR #22244) : le fichier fusionne porte
    UN job -- deux jobs re-introduiraient deux checkouts et deux slots."""
    assert list(_doc()["jobs"]) == [MERGED_JOB]


def test_one_checkout_only():
    """Un seul `actions/checkout` : c'est le gain de la fusion (le slot de
    runner, pas la minute-CPU, est la ressource rare -- #14057)."""
    checkouts = [
        s for s in _steps()
        if str(s.get("uses", "")).startswith("actions/checkout")
    ]
    assert len(checkouts) == 1, "le workflow fusionne doit avoir UN checkout"


def test_sparse_checkout_covers_both_groups():
    """Le sparse-checkout doit contenir ce dont les DEUX groupes ont besoin :
    `.github` (base-not-main lit les workflows) et `scripts` (les deux
    groupes executent leurs scripts)."""
    step = [s for s in _steps() if str(s.get("uses", "")).startswith("actions/checkout")][0]
    sparse = str(step.get("with", {}).get("sparse-checkout", ""))
    assert ".github" in sparse, sparse
    assert "scripts" in sparse, sparse


# --------------------------------------------------------- 2. les declencheurs

def test_trigger_union_includes_ready_for_review():
    """L'UNION des declencheurs des deux sources, `ready_for_review` inclus
    (criterion 1 de #28534)."""
    types = set(_trigger(_doc())["types"])
    assert types == {
        "opened", "reopened", "synchronize", "edited", "ready_for_review",
    }, types


def test_no_paths_filter():
    """Verrou #13232 + regle 2 d'#10045 : un `paths:` desarme l'organe sur
    les PR dont la base n'est pas main, et sort le job de la canary
    `derive_always_on_jobs`."""
    pr = _trigger(_doc())
    assert "paths" not in pr and "paths-ignore" not in pr, pr


def test_no_branches_filter():
    """#10918 : l'organe base-not-main doit voir les PR dont la base n'est
    PAS main -- un filtre `branches: [main]` l'en empecherait."""
    pr = _trigger(_doc())
    assert "branches" not in pr and "branches-ignore" not in pr, pr


# --------------------------------------------- 3. les deux gardes, par organe

def test_job_guard_is_the_union():
    """La garde du JOB est l'union : le job tourne des qu'un des deux groupes
    a quelque chose a dire."""
    cond = _job()["if"]
    assert META_GUARD in cond, cond
    assert BODY_GUARD in cond, cond


def test_metadata_steps_keep_their_own_guard():
    """Les trois organes de METADONNEES ne parlent QUE si la base a change.
    C'est la condition qui empeche un run vert de body d'effacer le verdict
    de metadonnees."""
    for prefix in (
        "Organe base-not-main",
        "Organe stale-base",
        "Organe concurrency-conj",
    ):
        cond = str(_step(prefix).get("if", ""))
        assert META_GUARD in cond, "%s : garde de metadonnees perdue (%s)" % (prefix, cond)


def test_body_steps_do_not_require_a_base_change():
    """Symetrique : les organes de BODY parlent sur une edition de corps,
    meme si la base n'a pas bouge."""
    body_live = str(_step("Body live").get("if", ""))
    body_organs = str(_step("Organes de body").get("if", ""))
    for cond in (body_live, body_organs):
        assert "github.event_name == 'pull_request'" in cond, cond
        assert META_GUARD not in cond, (
            "les organes de body ne doivent pas exiger un changement de base"
        )


def test_body_organs_script_is_called_once():
    """Une seule execution des cinq organes de body par evenement (review
    Hermes #22333) : deux appels doubleraient les cinq postes bloquants."""
    calls = [
        s for s in _steps()
        if "always_on_body_organs.sh" in str(s.get("run", ""))
    ]
    assert len(calls) == 1, "le script d'organes de body doit etre appele une fois"


# --------------------------------------------------- 4. la concurrence (#11649)

def test_concurrency_discriminates_the_edit_classes():
    """Un groupe unique doit distinguer les classes d'edition, sinon une
    edition de body annule le run de metadonnees (et reciproquement)."""
    group = _doc()["concurrency"]["group"]
    assert "'base-edit'" in group, group
    assert "'body-edit'" in group, group
    assert "'meta-edit'" in group, group


def test_concurrency_group_is_isolated_from_the_content_workflow():
    """Un groupe partage avec le workflow de contenu ferait annuler le run de
    contenu par un run de la classe `edited` (le defaut mesure en #22331)."""
    content = _load(WORKFLOWS / "always-on-guards.yml")["concurrency"]["group"]
    merged = _doc()["concurrency"]["group"]
    assert content != merged
    assert "always-on-guards-edited" in merged


# ------------------------------------------------------ 5. le nom de check-run

def test_job_name_keeps_the_guards_prefix():
    """`refresh_stale_adjacency.py` resout le job qui porte l'organe
    d'adjacence par le prefixe `Always-on guards` ; `pick_idle_grain.py`
    classe les agregateurs par le meme prefixe. Un nom qui le perdrait
    rendrait ces deux organes muets."""
    assert _job()["name"].startswith("Always-on guards"), _job()["name"]


def test_job_name_is_not_filtered_as_advisory():
    """`is_advisory()` tairait un nom qui contient « advisory »."""
    name = _job()["name"].lower()
    assert "advisory" not in name and "optional" not in name


# ------------------------------------------- 6. l'instrument de l'identite

def test_absorbed_check_run_identity_is_green():
    """Critere 2 de #28534 : `check_absorbed_check_run_identity.py` exige que
    le nom de chaque garde absorbee soit byte-identique au nom de check-run
    rendu par son workflow source. La fusion ne doit avoir casse aucune
    identite."""
    out = subprocess.run(
        [sys.executable, "scripts/ci/check_absorbed_check_run_identity.py",
         "--check"],
        cwd=str(REPO_ROOT),
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )
    assert out.returncode == 0, out.stdout + out.stderr
