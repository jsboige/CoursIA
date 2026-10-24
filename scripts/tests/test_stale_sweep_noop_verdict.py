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
import shutil
import subprocess
from pathlib import Path

import pytest

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


# --- Nommer la cause du no-op (#22215, point 2) -----------------------------
#
# Un no-op qui dit seulement « PR listing failed » laisse deux causes
# incompatibles ouvertes : le quota d'API (attendre), ou une panne d'endpoint /
# un jeton refuse (agir). Le triage ne peut pas trancher, et la prochaine lane
# refait le diagnostic a la main. Ces tests pincent donc la propriete « le
# verdict nomme l'endpoint ET le code HTTP », plus la mecanique qui rend le
# code reel : il est EXTRAIT du stderr de `gh` (`(HTTP 404)`), jamais ecrit en
# dur -- une constante mentirait des le premier incident different.


def test_le_no_op_du_listing_nomme_endpoint_et_code():
    corps = _branche_noop()
    assert "endpoint=GET repos/$REPO/pulls" in corps, (
        "le no-op doit nommer l'endpoint appele, sinon « PR listing failed » "
        "ne distingue pas un quota d'un endpoint casse"
    )
    assert "code=$LIST_CODE" in corps, corps
    # Le code vient du stderr de gh, pas d'une constante : `gh` ecrit
    # `gh: <message> (HTTP 403)` ; on garde le dernier (le plus proche de
    # l'echec) et on nomme l'absence quand il n'y en a pas.
    assert "grep -oE 'HTTP [0-9]+'" in corps, (
        "le code HTTP doit etre extrait du stderr de gh, jamais ecrit en dur"
    )
    assert "detail=$LIST_DETAIL" in corps, corps


def test_les_replis_du_listing_sont_poses_avant_l_appel():
    # Le step tourne sous `set -u` : une variable lue sans etre initialisee tue
    # le shell AVANT d'ecrire l'annotation, et le no-op redevient muet -- le
    # defaut meme que la correction supprime. Les replis sont donc nommes, et
    # poses avant l'appel reseau qu'ils protegent.
    texte = SWEEP.read_text(encoding="utf-8")
    appel = texte.index('gh api "repos/$REPO/pulls?state=open')
    for repli in ("LIST_CODE='aucun code HTTP'", "LIST_DETAIL='aucun message de gh'"):
        assert repli in texte, f"repli absent sous set -u : {repli}"
        assert texte.index(repli) < appel, (
            f"le repli {repli} est pose apres l'appel qu'il protege : sous "
            "set -u, l'echec tue le shell avant l'annotation"
        )


def test_le_no_op_des_check_runs_nomme_le_dernier_endpoint_et_le_code():
    # Le no-op « check-runs unreadable for all N PRs » couvre une boucle : la
    # cause utile est celle du DERNIER echec, d'ou le SHA de la PR concernee.
    texte = SWEEP.read_text(encoding="utf-8")
    assert re.search(
        r"check-runs unreadable for all \$LISTED listed PRs: last endpoint=GET "
        r"repos/\$REPO/commits/\$OMIT_SHA/check-runs code=\$OMIT_CODE",
        texte,
    ), "le no-op des check-runs ne nomme plus le dernier endpoint et son code"
    assert "OMIT_SHA=$SHA" in texte, (
        "sans le SHA, « last endpoint=.../commits//check-runs » ne designe rien"
    )
    assert "code=$OMIT_CODE" in texte and "detail=$OMIT_DETAIL" in texte


def test_l_appel_par_pr_ne_jette_plus_le_stderr():
    # `2>/dev/null` etait la cause mecanique du mutisme : le message de gh
    # (donc le code HTTP) etait jete a la source. La capture doit le garder.
    texte = SWEEP.read_text(encoding="utf-8")
    appel = re.search(
        r"--jq '\[\.check_runs\[\][^\n]*", texte
    )
    assert appel, "l'appel check-runs par PR est introuvable"
    assert "2>/dev/null" not in appel.group(0), (
        "le stderr de l'appel check-runs est encore jete : le code HTTP "
        "devient inextraignable et le no-op ne peut pas le nommer"
    )
    assert '2>"$OMIT_ERR"' in appel.group(0), appel.group(0)


def test_les_avertissements_de_timing_nomment_endpoint_et_code():
    # Les deux avertissements de mesure (run, jobs) sont *advisory* : ils ne
    # font pas rougir le run, mais une duree absente est indistinguable d'un
    # balayage instantane si la cause n'est pas nommee.
    texte = SWEEP.read_text(encoding="utf-8")
    assert re.search(
        r"timing unavailable: endpoint=GET repos/\$REPO/actions/runs/\$RUN_ID "
        r"code=\$TIM_CODE",
        texte,
    ), "l'avertissement de timing ne nomme plus l'endpoint du run"
    assert re.search(
        r"timing unavailable: endpoint=GET repos/\$REPO/actions/runs/\$RUN_ID/jobs\?"
        r"filter=latest code=\$TIM_CODE",
        texte,
    ), "l'avertissement de timing ne nomme plus l'endpoint des jobs"
    assert texte.count("grep -oE 'HTTP [0-9]+'") >= 3, (
        "chaque famille d'echec (listing, check-runs, timing) doit extraire le "
        "code du stderr, pas le deduire"
    )


# --- Execution sous le shell REEL de GitHub Actions --------------------------
#
# Les tests ci-dessus lisent le YAML, et une lecture statique ne voit pas
# `errexit`. Un step sans `shell:` tourne sous `bash --noprofile --norc -eo
# pipefail` : `-e` est actif, et une affectation `X=$(grep ...)` qui ne trouve
# rien rend 1 -- le shell sort AVANT la ligne de repli, l'annotation n'est
# jamais ecrite. La ligne de repli existe pourtant, donc tous les tests
# statiques passent. Mesure du 2026-10-24 (CHANGES_REQUESTED ai-01 sur
# `1c16d8825e`) : la branche de no-op etait morte a l'execution, et le pire cas
# etait la boucle des check-runs, ou une lecture ratee faisait `continue` avant
# la correction et tuait tout le balayage apres.
#
# D'ou ces trois tests : ils extraient le texte reel et l'executent sous les
# memes options que la CI. Un `|| true` manquant les fait echouer.

_BASH = shutil.which("bash")

# Toute affectation qui extrait le code HTTP du stderr de `gh` : c'est la forme
# exacte que `errexit` tue quand le motif ne matche pas.
_ASSIGN_RE = re.compile(
    r"[A-Z_]+=\$\(grep -oE 'HTTP \[0-9\]\+' \"\$[A-Z_]+\" \| tail -1[^)]*\)"
)


def _run_bash(script: str, cwd: Path) -> subprocess.CompletedProcess:
    """Execute `script` sous les options du shell par defaut de la CI."""
    return subprocess.run(
        [_BASH, "--noprofile", "--norc", "-e", "-o", "pipefail", "-c", script],
        cwd=str(cwd),
        capture_output=True,
        text=True,
        encoding="utf-8",
        timeout=60,
    )


def _exige_bash() -> None:
    if _BASH is None:
        pytest.skip("bash absent : l'execution sous le shell de la CI est impossible")


def _script_noop(tmp_path: Path, stderr_gh: str) -> subprocess.CompletedProcess:
    corps = _branche_noop()
    (tmp_path / "err.txt").write_text(stderr_gh, encoding="utf-8")
    script = (
        "REPO=jsboige/CoursIA\n"
        "LIST_ERR=err.txt\n"
        "LIST_CODE='aucun code HTTP'\n"
        "LIST_DETAIL='aucun message de gh'\n"
        f"{corps}\n"
    )
    return _run_bash(script, tmp_path)


def test_la_branche_de_no_op_s_execute_quand_le_stderr_ne_porte_aucun_code(tmp_path):
    # Cas reel d'une panne reseau : `gh` ecrit un message SANS `(HTTP nnn)`.
    # C'est exactement l'entree qui faisait mourir le shell sans annotation.
    _exige_bash()
    r = _script_noop(tmp_path, "dial tcp: lookup api.github.com: no such host\n")
    sortie = r.stdout + r.stderr
    assert r.returncode == 1, (
        f"le no-op doit sortir en 1, pas mourir avant d'annoter (rc={r.returncode})"
        f" -- sortie : {sortie!r}"
    )
    assert "code=aucun code HTTP" in sortie, (
        f"le repli du code n'a pas ete atteint sous errexit : {sortie!r}"
    )
    assert "detail=dial tcp" in sortie, sortie


def test_la_branche_de_no_op_s_execute_quand_le_stderr_porte_un_code(tmp_path):
    # Controle positif : quand le code est la, il est extrait et nomme.
    _exige_bash()
    r = _script_noop(tmp_path, "gh: Resource not accessible (HTTP 403)\n")
    sortie = r.stdout + r.stderr
    assert r.returncode == 1, sortie
    assert "code=HTTP 403" in sortie, (
        f"le code doit etre extrait du stderr, pas remplace par le repli : {sortie!r}"
    )


def test_chaque_extraction_de_code_survit_a_un_stderr_vide(tmp_path):
    # Les quatre familles (listing, check-runs, les deux timing) sont couvertes
    # d'un coup : la forme fautive est la meme partout, seule la variable change.
    # Un stderr vide est le pire cas -- `grep` rend 1 sans rien ecrire.
    _exige_bash()
    affectations = _ASSIGN_RE.findall(SWEEP.read_text(encoding="utf-8"))
    assert len(affectations) >= 4, (
        f"moins de quatre extractions trouvees ({len(affectations)}) : le motif "
        "ne couvre plus la famille, le test ne prouverait rien"
    )
    (tmp_path / "err.txt").write_text("", encoding="utf-8")
    for aff in affectations:
        var = aff.split("=", 1)[0]
        script = (
            "LIST_ERR=err.txt\nOMIT_ERR=err.txt\nTIM_ERR=err.txt\n"
            f"{var}=''\n"
            f"{aff}\n"
            f"printf 'SURVECU [%s]\\n' \"${var}\"\n"
        )
        r = _run_bash(script, tmp_path)
        assert r.returncode == 0, (
            f"`{aff}` tue le shell sous `bash -e -o pipefail` : errexit sort "
            f"avant le repli (rc={r.returncode}) -- {r.stderr!r}"
        )
        assert "SURVECU []" in r.stdout, (
            f"la substitution doit rendre une chaine vide, pas un echec : {r.stdout!r}"
        )
