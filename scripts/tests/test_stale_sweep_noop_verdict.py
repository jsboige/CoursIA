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

import importlib.util
import json
import re
import subprocess
import sys
from pathlib import Path

import pytest

from ._bash_resolution import resolve_bash

REPO_ROOT = Path(__file__).resolve().parents[2]
SWEEP = REPO_ROOT / ".github" / "workflows" / "pr-gate-stale-sweep.yml"
ADVISORY = (
    REPO_ROOT / ".github" / "workflows" / "pr-gate-sweep-health-advisory.yml"
)
# #26739 -- la lecture des check-runs par PR a quitte le shell du balayeur
# pour le COLLECTEUR (`scripts/ci/fetch_pr_checkruns.py`). Les pins qui
# portaient sur la forme du shell sont re-pointes sur le collecteur : la
# PROPRIETE est la meme (nommer le dernier echec, garder le stderr), sa
# porte est changee.
COLLECTOR = REPO_ROOT / "scripts" / "ci" / "fetch_pr_checkruns.py"

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


def _exige_omitter_sha_alimente_par_le_resume(texte: str) -> None:
    """OMIT_SHA doit etre ALIMENTE par le resume du collecteur, AVANT la
    branche de no-op qui le lit.

    La boucle shell qui assignait `OMIT_SHA=$SHA` est partie au collecteur
    (#26739) : la variable n'etait plus assignee, et la branche (dans un
    step `set -uo pipefail`) la lisait quand meme. La branche etait donc du
    CODE MORT PIEGE : le premier qui la rendait atteignable faisait avorter
    le step AVANT l'annotation, et le no-op redevenait muet -- le defaut
    meme que ce fichier existe pour empecher.
    """
    assign = re.search(
        r"^[ 	]*OMIT_SHA=\$\(python3 -c .*LEGS_SUMMARY.*\)\s*$", texte, re.M
    )
    assert assign, (
        "OMIT_SHA n'est plus alimente par le resume du collecteur : la "
        "branche du no-op lit une variable jamais assignee (code mort piege)"
    )
    usage = texte.index("check-runs unreadable for all")
    assert assign.start() < usage, (
        f"OMIT_SHA est assigne APRES la branche qui le lit (position "
        f"{assign.start()}, branche a {usage}) : hors de sa branche, la "
        "lecture sous `set -u` avorte le step sans annotation"
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
    # La branche est VIVANTE : ses variables sont posees AVANT elle, depuis le
    # resume du collecteur. Sans cela, elle lisait des variables jamais
    # assignee -- un code mort piege sous `set -u` (#26739).
    _exige_omitter_sha_alimente_par_le_resume(texte)
    assert "code=$OMIT_CODE" in texte and "detail=$OMIT_DETAIL" in texte
    # Et le resume porte reellement le dernier echec : PR, SHA, endpoint, code
    # HTTP et detail. Sans ce contenu, la branche nommerait « aucun ».
    source = COLLECTOR.read_text(encoding="utf-8")
    for cle in ('"last_unreadable"', '"unreadable_detail"', '"code"',
                '"endpoint"', '"detail"'):
        assert cle in source, f"le resume du collecteur ne porte pas {cle}"


def _charge_collecteur(source: str, path: Path):
    """Charge le collecteur depuis un SOURCE donne (temoin : source mutee)."""
    path.write_text(source, encoding="utf-8")
    spec = importlib.util.spec_from_file_location("fetch_pr_checkruns_pin", path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def _scenario_une_pr_illisible(module):
    """Une PR qui ECHOUE et une PR qui REUSSIT : le resume doit nommer
    l'echouee (sa PR, sa SHA, le code HTTP extrait du message)."""
    def rest(path: str) -> dict:
        if "sha1" in path:
            raise module.CollectionError(
                "GET repos/o/r/commits/sha1/check-runs : gh: Not Found (HTTP 404)")
        return {"total_count": 1, "check_runs": [{
            "name": "PR gate", "status": "completed", "conclusion": "failure",
            "started_at": "", "details_url": "", "output": {}}]}

    prs = [{"number": 1, "sha": "sha1", "fork": False, "merge_state": ""},
           {"number": 2, "sha": "sha2", "fork": False, "merge_state": ""}]
    _lines, summary = module.collect(
        repo="o/r", prs=prs, rest=rest, use_run_map=False,
        use_run_conclusions=False)
    return summary


def _exige_sha_du_dernier_echec(summary: dict) -> None:
    """Le resume nomme le DERNIER ECHEC, pas une PR lue.

    Equivalent du pin positionnel d'avant (#22278) : hors de la branche
    d'echec, le SHA enregistre serait celui d'une PR lue -- le no-op
    nommerait alors une PR qui n'a pas echoue.
    """
    last = summary.get("last_unreadable") or {}
    assert last.get("pr") == 1, (
        f"le resume ne nomme pas la PR illisible (pr={last.get('pr')}) : "
        "le no-op designerait une PR qui a reussi"
    )
    assert last.get("sha") == "sha1", (
        f"le SHA enregistre n'est pas celui de la PR illisible "
        f"({last.get('sha')}) : hors de sa branche, il serait celui d'une PR lue"
    )
    assert last.get("code") == "HTTP 404", (
        f"le code HTTP n'est pas extrait du message ({last.get('code')}) : "
        "il doit etre tire du stderr de gh, jamais ecrit en dur"
    )


def test_le_resume_nomme_le_dernier_echec_et_son_code(tmp_path: Path):
    source = COLLECTOR.read_text(encoding="utf-8")
    module = _charge_collecteur(source, tmp_path / "collecteur.py")
    summary = _scenario_une_pr_illisible(module)
    _exige_sha_du_dernier_echec(summary)


def test_temoin_le_sha_du_dernier_echec_ne_peut_pas_devenir_celui_d_une_pr_lue(
    tmp_path: Path,
):
    # Preuve que la verification a des dents : on mute le collecteur pour
    # qu'il enregistre le SHA d'une PR LUE (au lieu de celle qui a echoue) --
    # le defaut exact que le pin doit empecher -- et on exige que la
    # verification le refuse. Sans ce temoin, le pin pourrait passer par
    # accident.
    source = COLLECTOR.read_text(encoding="utf-8")
    mutante = source.replace(
        "_unreadable_entry(\n                        repo, wanted[number], error)",
        "_unreadable_entry(\n                        repo, {\"sha\": \"sha-lu\"}, error)")
    assert mutante != source, (
        "la mutation du temoin n'a rien change : le collecteur n'a plus la "
        "forme attendue, le temoin ne prouve plus rien"
    )
    module = _charge_collecteur(mutante, tmp_path / "collecteur_mutant.py")
    summary = _scenario_une_pr_illisible(module)
    with pytest.raises(AssertionError, match="illisible|PR lue"):
        _exige_sha_du_dernier_echec(summary)


def _bloc_noop_check_runs(texte: str) -> str:
    """Le bloc qui ALIMENTE puis LIT la branche de no-op des check-runs."""
    debut = texte.index("read -r LISTED INSPECTED OMITTED")
    fin = texte.index("check-runs unreadable for all")
    fin = texte.index("\n", texte.index("exit 1", fin)) + 1
    fin = texte.index("\n", texte.index("fi", fin)) + 1
    return texte[debut:fin]


def test_le_no_op_des_check_runs_s_execute_sous_set_u(tmp_path: Path):
    """Le code mort piege, verifie a l'EXECUTION (#26739).

    Sous `set -u`, une variable lue sans etre assignee tue le shell AVANT
    l'annotation -- le no-op redevient muet, ce qui est exactement le defaut
    que ce fichier empeche. Le bloc est extrait du workflow et execute sous
    les memes options que la CI : une lecture statique ne voit pas `errexit`
    ni `nounset`.
    """
    _exige_bash()
    if subprocess.run(["bash", "-c", "command -v python3"],
                      capture_output=True).returncode != 0:
        pytest.skip("python3 absent : le bloc ne peut pas etre execute")
    texte = SWEEP.read_text(encoding="utf-8")
    bloc = _bloc_noop_check_runs(texte)
    resume = {
        "prs_listed": 3, "prs_inspected": 0, "prs_omitted": 3,
        "api_quota": "api-quota: 3 appel(s) REST", "run_conclusion_failures": 0,
        "unreadable_prs": [7],
        "last_unreadable": {"pr": 7, "sha": "sha7",
                            "endpoint": "GET repos/jsboige/CoursIA/commits/sha7/check-runs",
                            "code": "HTTP 404", "detail": "gh: Not Found (HTTP 404)"},
        "truncated_prs": [], "rest_page_cap": 5000,
        "graphql_errors": [], "null_repository_pages": 0,
    }
    chemin = tmp_path / "legs_summary.json"
    chemin.write_text(json.dumps(resume), encoding="utf-8")
    script = (
        "REPO=jsboige/CoursIA\n"
        f'LEGS_SUMMARY="{chemin}"\n'
        f"{bloc}\n"
    )
    r = _run_bash(script, tmp_path)
    sortie = r.stdout + r.stderr
    assert r.returncode == 1, (
        f"le no-op des check-runs doit conclure 1, pas mourir sous `set -u` "
        f"(rc={r.returncode}) -- sortie : {sortie!r}"
    )
    assert "check-runs unreadable for all 3 listed PRs" in sortie, sortie
    assert "sha7" in sortie, (
        f"le no-op ne nomme plus la SHA du dernier echec : {sortie!r}"
    )
    assert "HTTP 404" in sortie, (
        f"le no-op ne nomme plus le code HTTP du dernier echec : {sortie!r}"
    )


def test_l_appel_par_pr_ne_jette_plus_le_stderr():
    # `2>/dev/null` etait la cause mecanique du mutisme : le message de gh
    # (donc le code HTTP) etait jete a la source. La capture doit le garder.
    # L'appel par PR vit dans le COLLECTEUR depuis #26739.
    source = COLLECTOR.read_text(encoding="utf-8")
    assert "2>/dev/null" not in source, (
        "le stderr d'un appel est encore jete dans le collecteur : le code "
        "HTTP devient inextractible et le no-op ne peut pas le nommer"
    )
    assert "capture_output=True" in source, (
        "le collecteur ne capture pas la sortie de gh : le stderr, donc le "
        "code HTTP, se perd"
    )
    assert "proc.stderr" in source, (
        "le collecteur ne lit pas le stderr de gh : le code HTTP ne peut pas "
        "etre extrait"
    )
    # Et le code HTTP en est TIRE, jamais ecrit en dur.
    assert "_HTTP_CODE_RE" in source, (
        "le code HTTP doit etre extrait du message de gh, pas une constante"
    )
def test_les_avertissements_de_timing_nomment_endpoint_et_code():
    # Les deux avertissements de mesure (run, jobs) sont *advisory* : ils ne
    # font pas rougir le run, mais une duree absente est indistinguable d'un
    # balayage instantane si la cause n'est pas nommee. #22278 : l'endpoint
    # nomme est l'appel REEL -- `&per_page=100` compris, sinon un lecteur qui
    # recopie l'URL pour rejouer l'echec interpelle un autre endpoint.
    texte = SWEEP.read_text(encoding="utf-8")
    assert re.search(
        r"timing unavailable: endpoint=GET repos/\$REPO/actions/runs/\$RUN_ID "
        r"code=\$TIM_CODE",
        texte,
    ), "l'avertissement de timing ne nomme plus l'endpoint du run"
    assert re.search(
        r"timing unavailable: endpoint=GET repos/\$REPO/actions/runs/\$RUN_ID/jobs\?"
        r"filter=latest&per_page=100 code=\$TIM_CODE",
        texte,
    ), "l'avertissement de timing ne nomme plus l'endpoint REEL des jobs (avec per_page)"
    assert texte.count("grep -oE 'HTTP [0-9]+'") >= 3, (
        "chaque famille d'echec (listing, check-runs, timing) doit extraire le "
        "code du stderr, pas le deduire"
    )


# --- Muet ou nomme : l'inventaire des 2>/dev/null (#22278) --------------------


def test_chaque_redirection_dev_null_restante_est_justifiee():
    # Critere #22278 : chaque `2>/dev/null` actif restant du sweep emet un
    # signal nomme (stderr capture, code extrait) OU porte son commentaire
    # « silence justifie ». Les appels qui signalent ne redirigent plus vers
    # /dev/null du tout (ils capturent), donc ce garde ne voit QUE les muets :
    # un muet nouveau ou non justifie le fait rougir -- et un inventaire vide
    # aussi, parce que les commentaires de justification seraient devenus du
    # code mort a retirer.
    texte = SWEEP.read_text(encoding="utf-8")
    lignes = texte.splitlines()
    muets = [
        (i, ligne)
        for i, ligne in enumerate(lignes)
        if "2>/dev/null" in ligne and not ligne.lstrip().startswith("#")
    ]
    assert muets, (
        "plus aucun 2>/dev/null actif : les commentaires « silence justifie » "
        "sont devenus du code mort, a retirer avec ce garde"
    )
    for i, ligne in muets:
        # le bloc de commentaires contigu juste au-dessus du site porte la
        # justification (le marker peut y etre en premiere ligne d'un bloc
        # de plusieurs)
        bloc = []
        j = i - 1
        while j >= 0 and lignes[j].lstrip().startswith("#"):
            bloc.append(lignes[j])
            j -= 1
        contexte = " ".join(bloc)
        assert "# silence justifie" in ligne or "# silence justifie" in contexte, (
            f"2>/dev/null muet et non justifie ligne {i + 1} : {ligne.strip()!r} "
            "(#22278 : capturer le stderr et nommer le code, ou justifier le silence)"
        )


def test_les_details_gh_sont_tronques_a_une_meme_largeur():
    # #22278 : le listing coupait son detail a 300, les familles OMIT et TIM
    # a 200 -- deux `detail=` lus cote a cote ne peuvent pas dire si un ecart
    # de longueur est un vrai contenu ou un budget different. Une seule
    # largeur pour tous les details extraits du stderr de gh.
    texte = SWEEP.read_text(encoding="utf-8")
    largeurs = {int(m) for m in re.findall(r"cut -c1-(\d+)", texte)}
    assert largeurs == {300}, (
        f"largeurs de troncature divergentes : {sorted(largeurs)} -- unifier "
        "(300, le budget historique du listing) ou justifier l'ecart"
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

# Pas `shutil.which("bash")` : sous le PATH d'une tache planifiee Windows,
# il rend le lanceur WSL de System32, qui avale le chemin Windows du script
# (exit 127) -- c'est ce qui faisait rougir l'arbre fusionne de merge_ready
# sur toutes les PRs approuvees (#17201, mesure du 2026-11-06).
_BASH = resolve_bash()

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
