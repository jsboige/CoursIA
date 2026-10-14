"""Le balayage stale-gate ne doit pas conclure `success` sans avoir balaye (#17230).

Mesure 2026-09-21 (lane `myia-po-2026`, datapoint d'`hermes-agent`, reverifie
firsthand) : le run 35609182069 (schedule 13:59:54Z) a conclu `success` en 33 s
sans rien reparer -- le log s'arretait sur

    [stale-sweep] PR listing failed (upstream) -- skip this sweep

puis `exit 0`.

Ce n'est pas un detail de log. `pr-gate-sweep-health-advisory.yml` mesure la
fraicheur du secours par `gh run list --status success --limit 1` : un no-op
etant un succes, il satisfaisait la sonde. L'age restait sous les 60 min,
l'alarme restait verte, et la population de PR a gate rouge ne bougeait pas.
Sur 84 succes mesures, 82 portaient un vrai passage (353-601 s) ; le no-op
etait le SEUL succes depuis 02:23:36Z -- la sonde lisait donc un run qui
n'avait pas travaille.

La propriete pinnee n'est pas « le no-op est logue » (il l'etait) mais **« le
no-op ne conclut pas success »** -- un `::warning` seul n'aurait rien corrige,
puisque c'est la CONCLUSION du run que la sonde filtre, pas ses annotations.
S'y ajoute la coherence des deux moities : la correction ne vaut que tant que
la sonde filtre sur les succes.
"""

from __future__ import annotations

import re
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
SWEEP = REPO_ROOT / ".github" / "workflows" / "pr-gate-stale-sweep.yml"
ADVISORY = (
    REPO_ROOT / ".github" / "workflows" / "pr-gate-sweep-health-advisory.yml"
)

# La branche de no-op est une ligne unique `|| { ...; }` : on la localise par
# son message, pas par son numero de ligne (le workflow bouge souvent).
_NOOP_RE = re.compile(r"\|\|\s*\{(?P<corps>[^}]*PR listing failed[^}]*)\}")


def _branche_noop() -> str:
    texte = SWEEP.read_text(encoding="utf-8")
    trouve = _NOOP_RE.search(texte)
    assert trouve, (
        "branche de no-op introuvable dans pr-gate-stale-sweep.yml : le "
        "message a change, ou l'echappement du listing PR a ete retire"
    )
    corps = trouve.group("corps")
    # Controle de non-vacuite : si le motif se met a capturer autre chose, les
    # assertions ci-dessous passeraient en ne regardant rien.
    assert "exit" in corps, corps
    return corps


def test_le_no_op_ne_conclut_pas_success():
    # `exit 0` = la run conclut `success` = la sonde de fraicheur compte ce
    # balayage comme un service rendu. C'est exactement le defaut mesure.
    corps = _branche_noop()
    assert "exit 0" not in corps, (
        "un balayage qui n'a rien balaye ne doit pas conclure success : la "
        "sonde lit `--status success` et resterait verte (#17230)"
    )
    assert re.search(r"exit\s+1\b", corps), corps


def test_le_no_op_est_annote_pour_le_triage():
    # La run concluant desormais `failure`, elle doit etre triable comme « le
    # balayage n'a pas eu lieu » et non comme un rouge de contenu :
    # `scripts/ci/classify_job_deaths.py` classe par annotation, et une
    # annotation generique ne distingue pas les deux.
    corps = _branche_noop()
    assert "::error::" in corps or "::warning::" in corps, (
        "le no-op doit porter une annotation qui le nomme, sinon la run rouge "
        "est indistinguishable d'un echec de contenu au triage"
    )
    assert "NO-OP" in corps, corps


def test_la_sonde_de_fraicheur_filtre_toujours_les_succes():
    # Coherence des deux moities. La correction ci-dessus vaut parce que la
    # sonde ne regarde que les succes : un no-op devenu `failure` est saute et
    # l'age vieillit vers l'alarme. Si la sonde se mettait a lire tous les runs
    # (`--limit 1` sans filtre), un echec isole tripperait l'alarme
    # immediatement -- un autre arbitrage, a re-trancher, pas a subir.
    texte = ADVISORY.read_text(encoding="utf-8")
    assert "--status success" in texte, (
        "la sonde de fraicheur ne filtre plus les succes : l'invariant qui "
        "rend le no-op `failure` inoffensif pour un blip isole est rompu"
    )
    assert "--workflow pr-gate-stale-sweep.yml" in texte, texte[:200]
