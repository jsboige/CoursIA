"""Invariant E1 (#25510) : les trois advisories de starvation ont la MEME ancre.

Le 2026-10-23, deux sondes d'extinction de runners self-hosted ont ete
livrees, une par label : `coursia-linux`
(`linux-runner-starvation-advisory.yml`) et `coursia-waiter`
(`coursia-waiter-starvation-advisory.yml`). Chacune porte un heartbeat
`workflow_run` ancre sur « Secret Scan » et « Enrich-quality gate » (#15332 :
le scheduler GitHub a cesse de livrer l'evenement `schedule`, et un organe
porte par le schedule seul meurt de la panne qu'il observe ; #23195 :
l'ancre « Enrich-quality gate » est la seule jambe hebergee declenchee par
l'activite PR).

La troisieme sonde, `runner-starvation-advisory.yml` (pool
`coursia-ephemeral`, celui qui sert les jobs Lean), n'avait PAS de heartbeat :
elle etait le seul des trois advisories a dependre entierement du scheduler.
Mesure du 2026-11-12 sur son propre historique (API `runs?event=schedule`) :
sa jambe `schedule` n'est livree que toutes les ~8 h (18:28Z, 10:22Z,
02:33Z, 21:36Z, 14:44Z...) alors que le cron declare `23,53 * * * *`
(30 min) -- le meme phenomene que chez ses deux freres (linux : 13:19Z,
04:23Z, 23:43Z ; waiter : 16:13Z, 07:39Z, 00:33Z), qui eux survivent
grace a leur heartbeat.

Ce fichier fixe l'invariant plutot que de le laisser au relecture :
les trois sondes declarent les MEMES ancres, chacune une porte de mesure
declaree (`MEASURE_EVERY_N_RUNS`, #22937), la MEME garde anti-fork au niveau
du JOB, et AUCUNE ne se declenche sur `pull_request`/`push` -- un run rouge
d'un advisory ne peut jamais bloquer une PR.

La porte de mesure est une borne de COUT, pas une invariant d'egalite : la
troisieme sonde est gatee a 12 (le cout API de son ancrage, ajoute par
#25510 E1), la paire a 4 jusqu'a ce que la porte de job de #26246 soit
corrigee. L'egalite porte sur le FAIT qu'une porte est declaree et qu'elle
est calculee dans le shell -- l'operateur `%` n'existe pas dans les
expressions GitHub, une porte ecrit `github.run_number % 12 == 0` ne
s'evalue pas.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "scripts" / "ci"))

import check_heartbeat_anchor_independence as chi  # noqa: E402

ADVISORIES = (
    ".github/workflows/linux-runner-starvation-advisory.yml",
    ".github/workflows/coursia-waiter-starvation-advisory.yml",
    ".github/workflows/runner-starvation-advisory.yml",
)
# La troisieme sonde (pool `coursia-ephemeral`), seule a porter un heartbeat
# depuis #25510 E1.
THIRD_PROBE = ".github/workflows/runner-starvation-advisory.yml"
# Borne de la porte de mesure (#22937), par sonde : le cout API de
# l'ancrage de la troisieme sonde justifie 12 ; la paire garde 4.
MEASURE_GATE_BY_ADVISORY = {
    ".github/workflows/linux-runner-starvation-advisory.yml": "4",
    ".github/workflows/coursia-waiter-starvation-advisory.yml": "4",
    THIRD_PROBE: "12",
}
EXPECTED_ANCHORS = ["Secret Scan", "Enrich-quality gate"]

# Garde anti-fork : le job saute quand le heartbeat declenche par une PR de
# fork. Sans elle, GitHub attribue le run a l'auteur de la PR de fork et lui
# envoie un email « Run cancelled » quand un run plus recent le remplace
# dans le groupe de concurrence (mesure du 2026-10-16, incident APP3).
ANTIFORK = ("github.event.workflow_run.head_repository.full_name"
            " == github.repository")


def _text(rel: str) -> str:
    return (REPO_ROOT / rel).read_text(encoding="utf-8")


def _jobs_block(text: str) -> str:
    """Corps du bloc `jobs:` (le reste du fichier).

    Parsing texte, pas YAML : le depot ne garantit pas PyYAML sur toutes les
    machines, et `on` est un booleen en YAML 1.1 (meme pari que
    `check_heartbeat_anchor_independence._yaml_on_block`).
    """
    assert "\njobs:\n" in text, "bloc `jobs:` introuvable"
    return text.split("\njobs:\n", 1)[1]


@pytest.mark.parametrize("rel", ADVISORIES)
def test_advisory_declares_the_same_workflow_run_anchors(rel: str) -> None:
    assert chi.load_anchor_names(REPO_ROOT / rel) == EXPECTED_ANCHORS


@pytest.mark.parametrize("rel", ADVISORIES)
def test_advisory_never_triggers_on_pull_request_or_push(rel: str) -> None:
    """Advisory par construction : `workflow_run` ne cree pas de check-run
    sur une PR, mais `pull_request`/`push` le feraient -- et un run rouge
    d'infrastructure bloquerait alors la PR."""
    events = chi._declared_events(_text(rel))
    assert "pull_request" not in events
    assert "push" not in events


@pytest.mark.parametrize("rel", ADVISORIES)
def test_advisory_has_job_level_antifork_guard(rel: str) -> None:
    assert ANTIFORK in _jobs_block(_text(rel))


@pytest.mark.parametrize("rel", ADVISORIES)
def test_concurrency_lives_at_job_level_not_workflow_level(rel: str) -> None:
    """Au niveau du workflow, un run en attente est annule AVANT
    l'evaluation du `if` anti-fork, et l'email part quand meme. La
    concurrence doit donc vivre au niveau du JOB."""
    text = _text(rel)
    assert re.search(r"^    concurrency:\n      group: ", text, re.M), (
        "concurrence de job introuvable")
    assert not re.search(r"^concurrency:\n", text, re.M), (
        "concurrence au niveau du workflow : le run en attente serait "
        "annule avant l'evaluation de la garde anti-fork")


@pytest.mark.parametrize("rel", ADVISORIES)
def test_measure_gate_is_declared(rel: str) -> None:
    """#22937 : la porte borne la MESURE complete (l'inventaire + la lecture
    des jobs), pas le RUN -- c'est la SURVIE de l'observateur qui est la
    garantie. Sans la porte, la troisieme sonde recreerait la saturation du
    jeton du 2026-10-28 (18 rouges sur `main` en 10 min).

    La valeur est une borne de cout : 12 pour la troisieme sonde (dont
    #25510 E1 ajoute l'ancrage), 4 pour la paire."""
    expected = MEASURE_GATE_BY_ADVISORY[rel]
    assert f'MEASURE_EVERY_N_RUNS: "{expected}"' in _text(rel)


def test_la_porte_de_mesure_est_calculee_dans_le_shell() -> None:
    """`%` n'existe pas dans les expressions GitHub.

    Une porte de mesure ecrit `github.run_number % 12 == 0` dans un `if:`
    ne s'evalue pas : le job ne part jamais, ou part toujours, et la borne
    de cout devient un decor. Le calcul se fait en arithmetique shell, et
    les etapes qui paient (checkout + mesure) sont conditionnees par la
    sortie de l'etape de porte.
    """
    text = _text(THIRD_PROBE)
    # Les commentaires expliquent la faute : ils la citent. Seules les
    # lignes effectives du workflow sont inspectees.
    code = "\n".join(
        line for line in text.splitlines() if not line.strip().startswith("#")
    )
    assert "github.run_number %" not in code
    assert "id: gate" in text
    assert "RUN_NUMBER % MEASURE_EVERY_N" in text
    assert "steps.gate.outputs.measure == 'true'" in text
    # Les etapes qui paient sont conditionnees par la porte.
    assert text.count("steps.gate.outputs.measure == 'true'") >= 2


@pytest.mark.parametrize("rel", ADVISORIES)
def test_served_cadence_is_declared(rel: str) -> None:
    """#15332 : le rapport de cadence servie est emis a chaque passage --
    c'est lui qui prouve que l'advisory survit au scheduler muet."""
    assert "SELF_WORKFLOW: " in _text(rel)
    assert "DECLARED_CADENCE_MINUTES: " in _text(rel)


def test_anchor_organ_covers_the_three_advisories() -> None:
    """L'organe d'independance des ancres doit mesurer les trois
    declarations : une ancre declaree n'est pas une ancre prouvee."""
    for rel in ADVISORIES:
        assert rel in chi.DEFAULT_ADVISORIES


def test_control_a_file_without_anchor_is_detected(tmp_path: Path) -> None:
    """Controle positif : l'invariant doit etre capable de voir une
    regression. Un fichier sans bloc `workflow_run` rend une liste vide --
    c'est ce vide que le test compare a la liste attendue."""
    fake = tmp_path / "advisory.yml"
    fake.write_text(
        "on:\n  schedule:\n    - cron: '1 * * * *'\njobs:\n  x:\n"
        "    runs-on: ubuntu-latest\n", encoding="utf-8")
    assert chi.load_anchor_names(fake) == []
    assert chi.load_anchor_names(fake) != EXPECTED_ANCHORS
