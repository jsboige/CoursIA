"""Tests du census `edited` (#22467).

Deux organes sont pins ici :

* `scripts/ci/list_edited_trigger_workflows.py` -- quels workflows ecoutent
  `pull_request: edited` et si leur verdict bouge quand le body, le titre, la
  base ou le filtre `paths:` de la PR bougent ;
* `scripts/ci/measure_redundant_runs.py` -- combien de premieres tentatives
  redondantes la flotte produit, et **de quelle classe** elles sont.

Le pin le plus important est **negatif, dans les deux sens** : les wrappers
Lean **doivent** continuer d'ecouter `edited`. Le retrait de ce declencheur
re-ouvrirait le defect #15652 (une PR empilee retargetee vers `main` n'a
plus de CI Lean, parce que `base_ref_changed` emet un `edited` que les
workflows sans `edited` ignorent). Ce pin est donc le **contre-pied** de
l'intuition -- d'ou sa valeur.
"""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[3]
CI_DIR = REPO_ROOT / "scripts" / "ci"
sys.path.insert(0, str(CI_DIR))


def _load(name: str):
    spec = importlib.util.spec_from_file_location(name, CI_DIR / f"{name}.py")
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


census = _load("list_edited_trigger_workflows")
measure = _load("measure_redundant_runs")
guards = _load("body_consuming_guards")


# ---------------------------------------------------------------------------
# Census statique
# ---------------------------------------------------------------------------


@pytest.fixture(scope="module")
def rows():
    return census.survey(REPO_ROOT)


def _by_workflow(rows):
    return {row["workflow"]: row for row in rows}


def test_le_census_trouve_la_famille_qui_ecoute_encore_edited(rows):
    found = _by_workflow(rows)
    # `always-on-guards-body.yml` est le workflow des organes de body : il
    # DOIT ecouter `edited` (c'est le verbatim de #22331).
    assert ".github/workflows/always-on-guards-body.yml" in found
    assert "body" in found[".github/workflows/always-on-guards-body.yml"]["depends_on"]


def test_le_census_classe_le_verdict_sur_le_body_lu_directement(rows):
    found = _by_workflow(rows)
    row = found[".github/workflows/always-on-guards-body.yml"]
    assert row["verdict"] == "PR_METADATA_DEPENDENT"
    assert row["direct_body_read"] is True


def test_le_census_ignore_un_workflow_sans_declencheur_edited(rows):
    found = _by_workflow(rows)
    assert ".github/workflows/lean-axiom.yml" not in found


@pytest.mark.parametrize(
    "workflow",
    [
        # lean-knot.yml : retire de la liste a sa migration matricielle
        # (#13751) -- le wrapper est supprime, et c'est lean-ci-matrix.yml
        # qui porte desormais le declencheur `edited` du lake. Idem
        # lean-conway.yml, DERNIER wrapper autonome, supprime a la migration
        # matricielle de conway_lean (#25256) : le garant `edited` migre ici
        # sur le dispatcher lui-meme. Plus fort que le precedent knot (dont
        # le pin "matriciel" de test_axiom_matrix_wiring.py couvre les
        # `paths` mais PAS la liste `types`) : le dispatcher est filtre par
        # `paths:` -- le defaut #15652 (retarget d'une PR empilee change la
        # base-relative du filtre) lui applique EXACTEMENT, et un retrait
        # de `edited` de sa liste `types` serait une regression CI Lean
        # silencieuse sur TOUT le manifeste, pas sur un lake.
        ".github/workflows/lean-ci-matrix.yml",
    ],
)
def test_les_wrappers_lean_continuent_d_ecouter_edited(rows, workflow):
    """Contre-pied du defaut #15652.

    Ces wrappers portent un filtre `paths:`. Le filtre est evalue sur le diff
    **base-relative** : changer la base change la liste des fichiers qui
    matchent. Un workflow qui n'ecoute pas `edited` ne voit jamais le
    retarget d'une PR empilee apres le merge de sa parente -- et la PR traverse
    tout son cycle de review SANS CI Lean. Le retrait du declencheur serait
    donc une regression, pas un gain.
    """
    found = _by_workflow(rows)
    assert workflow in found, (
        f"{workflow} n'ecoute plus `edited` : une PR empilee retargetee vers "
        "`main` n'aura plus de CI Lean (defaut #15652)"
    )
    row = found[workflow]
    assert "paths" in row["depends_on"]
    assert row["verdict"] == "PR_METADATA_DEPENDENT"


def test_le_census_signale_le_dependance_a_la_base(rows):
    """`always-on-metadata-guards.yml` lit la base de la PR : changer de base
    est un evenement `edited`, son verdict bouge -- il doit rester ecoute."""
    found = _by_workflow(rows)
    row = found[".github/workflows/always-on-metadata-guards.yml"]
    assert "base" in row["depends_on"]


def test_le_census_signale_le_dependance_au_filtre_paths(rows):
    """Un workflow filtre par `paths:` est, par construction, dependant de la
    base : c'est l'axe qui empeche de classer `CONTENT_ONLY` un workflow
    filtre."""
    found = _by_workflow(rows)
    filtered = [row for row in rows if row["paths_filtered"]]
    assert filtered, "aucun workflow filtre par `paths:` -- le census est suspect"
    for row in filtered:
        assert "paths" in row["depends_on"]
        assert row["verdict"] == "PR_METADATA_DEPENDENT"


def test_le_verdict_content_only_exige_aucun_axe(rows):
    """Un `CONTENT_ONLY` n'a aucun axe : son verdict ne depend que du code."""
    for row in rows:
        if row["verdict"] == "CONTENT_ONLY":
            assert row["depends_on"] == []


# ---------------------------------------------------------------------------
# Formes de lecture du body reconnues par l'inventaire (#22467, R2)
# ---------------------------------------------------------------------------


def _channels(source: str) -> dict[str, dict]:
    import ast

    return guards._scan_tree(ast.parse(source))


def test_le_detecteur_reconnait_le_body_lu_par_jq_rest():
    """`gh api repos/<o>/<r>/pulls/<n> --jq .body` lit le body de la PR.

    Cette forme n'etait pas reconnue : un script qui lisait le body par elle
    echappait a l'inventaire, et le census pouvait alors classer `CONTENT_ONLY`
    un workflow dont le verdict depend en realite du body."""
    channels = _channels(
        "def read(pr):\n"
        "    return _run(['gh', 'api', f'repos/{o}/{r}/pulls/{pr}', '--jq', '.body'])\n"
    )
    assert "api-gh" in channels


def test_le_detecteur_reconnait_le_body_lu_par_graphql():
    """Une requete GraphQL nommant `pullRequest` et `body` lit le body."""
    channels = _channels(
        "def read():\n"
        "    return _run(['gh', 'api', 'graphql', '-f', "
        "'query=query{pullRequest{number body}}'])\n"
    )
    assert "api-gh" in channels


def test_le_detecteur_ne_compte_pas_le_body_d_un_commentaire():
    """Le `body` d'un COMMENTAIRE ou d'une REVIEW n'est pas le body de la PR.

    Compter ces lectures ferait de `check_unaddressed_nits.py` un consommateur
    de body : l'inventaire dirait alors qu'un workflow garde `edited` pour une
    raison qui n'est pas la sienne."""
    channels = _channels(
        "def read(pr):\n"
        "    return _run(['gh', 'api', f'repos/{o}/{r}/pulls/{pr}/reviews', "
        "'--jq', '.[] | {author: .user.login, body: .body}'])\n"
    )
    assert "api-gh" not in channels


def test_le_detecteur_reconnait_toujours_la_forme_virgule():
    """Contre-pied du fix de #22467 : `--json body,reviews,author` doit rester
    visible (8 consommateurs en dependaient)."""
    channels = _channels(
        "def read(pr):\n"
        "    return _run(['gh', 'pr', 'view', str(pr), "
        "'--json', 'body,reviews,author'])\n"
    )
    assert "api-gh" in channels


# ---------------------------------------------------------------------------
# Ablation : le verdict depend-il de la couverture de l'inventaire ?
# ---------------------------------------------------------------------------


def test_l_ablation_publie_le_verdict_sans_inventaire(rows):
    """Chaque workflow porte son verdict recalcule sans l'inventaire.

    Une dependance invisible serait une conclusion fragile : elle doit etre
    lisible, pas supposee."""
    for row in rows:
        assert row["verdict_without_detector"] in ("CONTENT_ONLY", "PR_METADATA_DEPENDENT")
        if row["verdict_without_detector"] == "CONTENT_ONLY":
            assert row["depends_on_without_detector"] == []


def test_l_ablation_ne_revele_aucun_content_only(rows):
    """Aucun workflow ne peut devenir `CONTENT_ONLY` quand on retire
    l'inventaire : le census complet les couvre tous."""
    without = [
        row["workflow"]
        for row in rows
        if row["verdict_without_detector"] == "CONTENT_ONLY"
    ]
    with_detector = [
        row["workflow"] for row in rows if row["verdict"] == "CONTENT_ONLY"
    ]
    assert with_detector == []
    # Un workflow qui ne dependait que de l'inventaire peut apparaitre ici :
    # c'est le cas, et c'est **voulu** -- la dependance est nommee, pas
    # cachee. Ce qui ne doit jamais arriver, c'est un workflow que le census
    # complet classe `CONTENT_ONLY` et que l'ablation ne voit pas.
    assert set(with_detector) <= set(without)


def test_le_rapport_d_ablation_nomme_les_workflows_dependants(rows):
    report = census.render_ablation(rows)
    dependent = [
        row["workflow"]
        for row in rows
        if row["verdict"] != row["verdict_without_detector"]
    ]
    for workflow in dependent:
        assert workflow in report
    assert "CONTENT_ONLY" in report


# ---------------------------------------------------------------------------
# Mesure des redondances
# ---------------------------------------------------------------------------


def _run(
    run_id: int,
    sha: str,
    created: str,
    attempt: int = 1,
    path: str = ".github/workflows/x.yml",
    pr: int | None = 7,
    event: str = "pull_request",
):
    return {
        "id": run_id,
        "path": path,
        "name": "X",
        "head_sha": sha,
        "run_attempt": attempt,
        "created_at": created,
        "event": event,
        "pull_requests": [{"number": pr}] if pr else [],
    }


def test_la_mesure_compte_les_premieres_tentatives_redondantes():
    runs = [
        _run(1, "aaa", "2026-11-01T10:00:00Z"),
        _run(2, "aaa", "2026-11-01T10:05:00Z"),
        _run(3, "bbb", "2026-11-01T11:00:00Z"),
        _run(4, "aaa", "2026-11-01T10:06:00Z", attempt=2),
    ]
    report = measure.analyze(runs, {})
    totals = report["totals"]
    assert totals["redundant_first_attempts"] == 1
    assert totals["reruns"] == 1
    assert totals["heads"] == 2


def test_la_mesure_classe_la_redondance_meme_tete_pull_request():
    """Deux premieres tentatives du meme workflow sur la MEME tete, toutes
    deux declenchees par `pull_request` : sur une meme tete, le workflow PR ne
    peut rejouer que via `edited` **ou** `reopened`. La classe dit donc
    `edited` ∪ `reopened` -- elle ne separe pas les deux, et `reopened` n'est
    compte nulle part ailleurs : le nombre est un minorant pour `edited`."""
    runs = [
        _run(1, "aaa", "2026-11-01T10:00:00Z"),
        _run(2, "aaa", "2026-11-01T10:05:00Z"),
    ]
    report = measure.analyze(runs, {})
    totals = report["totals"]
    assert totals["redundant_same_head_pull_request"] == 1
    assert totals["redundant_without_linked_pr"] == 0


def test_la_mesure_classe_le_melange_d_evenements():
    runs = [
        _run(1, "aaa", "2026-11-01T10:00:00Z"),
        _run(2, "aaa", "2026-11-01T10:05:00Z", event="push"),
    ]
    report = measure.analyze(runs, {})
    assert report["totals"]["redundant_mixed_event"] == 1


def test_la_mesure_signale_la_redondance_sans_pr_liable():
    """Aucune PR liee -> la timeline est illisible : l'attribution est
    IMPOSSIBLE, ce qui n'est pas « non imputable a `edited` ». Le compteur
    existe pour qu'un zero ne soit pas lu comme une absence de cause."""
    runs = [
        _run(1, "aaa", "2026-11-01T10:00:00Z", pr=None),
        _run(2, "aaa", "2026-11-01T10:05:00Z", pr=None),
    ]
    report = measure.analyze(runs, {})
    totals = report["totals"]
    assert totals["redundant_without_linked_pr"] == 1
    assert totals["redundant_same_head_pull_request"] == 0


def test_la_mesure_corrobore_par_un_retarget_de_base():
    """`base_ref_changed` est lisible sur la timeline : il corrobore qu'un
    `edited` a bien ete emis (donc que le re-fire etait legitime)."""
    runs = [
        _run(1, "aaa", "2026-11-01T10:00:00Z"),
        _run(2, "aaa", "2026-11-01T10:05:00Z"),
    ]
    report = measure.analyze(runs, {"7": ["2026-11-01T10:04:30Z"]})
    assert report["totals"]["redundant_corroborated_base_change"] == 1


def test_la_mesure_ne_corrobore_pas_sans_retarget():
    runs = [
        _run(1, "aaa", "2026-11-01T10:00:00Z"),
        _run(2, "aaa", "2026-11-01T10:05:00Z"),
    ]
    report = measure.analyze(runs, {"7": ["2026-11-01T18:00:00Z"]})
    totals = report["totals"]
    assert totals["redundant_first_attempts"] == 1
    assert totals["redundant_corroborated_base_change"] == 0


def test_la_mesure_compte_par_workflow():
    runs = [
        _run(1, "aaa", "2026-11-01T10:00:00Z"),
        _run(2, "aaa", "2026-11-01T10:05:00Z"),
        _run(3, "ccc", "2026-11-01T10:00:00Z", path=".github/workflows/y.yml"),
    ]
    report = measure.analyze(runs, {})
    rows = {row["workflow"]: row for row in report["workflows"]}
    assert rows[".github/workflows/x.yml"]["redundant_first_attempts"] == 1
    assert rows[".github/workflows/y.yml"]["redundant_first_attempts"] == 0
