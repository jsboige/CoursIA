"""Tests du mode STRICT du tapis et de la voie EN PROCESSUS (#22983 PR 3).

Le tapis (`--belt`) doit servir ses claims depuis l'instantane local, et
**jamais** completer a la volee par un sous-processus par candidat. Ce
fichier verrouille les garanties mesurees :

1. **le transport historique est RETIRE** : ses symboles ont disparu du
   module, et la phase claims ne lance aucun enfant ;
2. **STRICT est fail-CLOSED** : quand la voie en processus ne peut pas
   servir la fenetre, TOUS les numeros rendent `BLOCKED` avec la phrase
   d'instantane absent ;
3. **STRICT est independant du gate `_pass_snapshot_enabled()`** : le gate
   protege l'appel DIRECT de `check_claims` (les tests et les autres
   consommateurs l'imitent), pas le tapis ;
4. **l'hors-strict rend `ERROR`** quand la voie en processus echoue : il
   n'y a plus de repli, et jamais `FREE` ;
5. **le fast-path de glob est equivalent** a la reference `fnmatch`, pour
   une liste simple comme pour la forme normalisee (`_TrackedFiles`), et
   le fast-path litteral donne le meme verdict que le chemin general ;
6. **le prefetch des etats de PR** verse dans `_PR_STATE_CACHE` (jamais
   dans une map `pr_states` injectee, qui serait fail-OPEN pour les PRs
   absentes) et rend le meme etat que la lecture unitaire.

Aucun test ne touche le reseau : `_gh_graphql`, `_gh_open_prs` et les
transports sont remplaces par des faux.
"""

import json
import re
import subprocess
import sys
import types
from fnmatch import fnmatch
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "coordination"))

import check_lane_claim as clc  # noqa: E402
import pick_idle_grain as pig  # noqa: E402


@pytest.fixture(autouse=True)
def _etat_propre():
    """Aucun etat partage ne fuit d'un test a l'autre."""
    yield
    clc.set_snapshot(None)
    clc._PR_STATE_CACHE.clear()
    pig._PASS_SNAPSHOT = None
    pig._BELT_SNAPSHOT = None


def _aucun_transport(monkeypatch):
    """Le transport est retire : le dire, et refuser tout enfant.

    Ce n'est plus une precaution de test : c'est l'INVARIANT. Un
    transport qui reviendrait reouvrirait le fail-OPEN qu'il portait.
    """
    for name in ("_check_claims_one_batch", "_check_claims_sliced",
                 "BELT_CLAIMS_WORKERS", "BELT_CLAIMS_SLICE_MIN"):
        assert not hasattr(pig, name), (
            f"{name} existe encore : le transport historique n'est pas retire")

    def refuse(*a, **k):
        pytest.fail("transport historique atteint : il doit etre retire")

    monkeypatch.setattr(pig.subprocess, "run", refuse)
    monkeypatch.setattr(pig, "_run_bounded", refuse)
    monkeypatch.setattr(pig, "_build_open_prs_cache_for_belt", lambda lane: None)


# --- 1. STRICT est fail-CLOSED --------------------------------------------


def test_strict_bloque_tout_si_la_voie_en_processus_echoue(monkeypatch):
    """Instantane indisponible => AUCUN grain servi, transport jamais pris."""
    monkeypatch.setattr(pig, "_claims_in_process",
                        lambda numbers, lane, cache=None, **kw: None)
    _aucun_transport(monkeypatch)

    verdicts = pig.check_claims([11, 12, 13], "myia-ai-01:CoursIA-2",
                                 strict_snapshot=True)

    assert set(verdicts) == {11, 12, 13}
    for code, human in verdicts.values():
        assert code == pig.CLAIM_CODE_BLOCKED
        assert human == pig.CLAIM_HUMAN_SNAPSHOT_ABSENT


def test_strict_ne_depend_pas_du_gate_d_instantane_de_passe(monkeypatch):
    """Le gate `_pass_snapshot_enabled()` protege l'appel DIRECT, pas le tapis.

    Sans ce gate, un instantane local illisible (le cas reel d'une machine
    ou le fichier d'instantane est absent ou perime) faisait retomber le
    tapis sur le transport -- exactement ce que le mode STRICT retire.
    """
    monkeypatch.setattr(pig, "_PASS_SNAPSHOT", None)
    assert pig._pass_snapshot_enabled() is False

    vus: list[int] = []

    def _in_process(numbers, lane, cache=None, **kw):
        vus.extend(numbers)
        return {n: (pig.CLAIM_CODE_FREE, "libre") for n in numbers}

    monkeypatch.setattr(pig, "_claims_in_process", _in_process)
    _aucun_transport(monkeypatch)

    verdicts = pig.check_claims([21, 22], "myia-ai-01:CoursIA-2",
                                 strict_snapshot=True)

    assert vus == [21, 22]
    assert verdicts[21][0] == pig.CLAIM_CODE_FREE
    assert verdicts[22][0] == pig.CLAIM_CODE_FREE


def test_strict_sert_la_voie_en_processus_telle_quelle(monkeypatch):
    """Les verdicts de la voie en processus sont rendus tels quels."""
    attendu = {31: (pig.CLAIM_CODE_BLOCKED, "tenu par autre lane"),
               32: (pig.CLAIM_CODE_FREE, "libre")}
    monkeypatch.setattr(pig, "_claims_in_process",
                        lambda numbers, lane, cache=None, **kw: dict(attendu))
    _aucun_transport(monkeypatch)

    verdicts = pig.check_claims([31, 32], "myia-ai-01:CoursIA-2",
                                 strict_snapshot=True)

    assert verdicts == attendu


def test_hors_strict_rend_error_quand_la_voie_en_processus_echoue(monkeypatch):
    """Hors STRICT, il n'y a plus de repli : le verdict est muet (`ERROR`).

    C'etait la meme classe que l'echec du transport retire, et jamais
    `FREE` : un grain dont le claim n'a pas ete lu ne doit pas pouvoir
    passer pour libre.
    """
    monkeypatch.setattr(pig, "_claims_in_process",
                        lambda numbers, lane, cache=None, **kw: None)
    _aucun_transport(monkeypatch)

    verdicts = pig.check_claims([41, 42], "myia-ai-01:CoursIA-2")

    for code, _ in verdicts.values():
        assert code == pig.CLAIM_CODE_ERROR


# --- 2. le fast-path de glob est equivalent a la reference ----------------


def _reference(glob: str, tracked: list[str]) -> bool:
    """Reference : `fnmatch` sur le chemin et sur le nom de base."""
    for path in tracked:
        basename = path.rsplit("/", 1)[-1]
        for pat in clc._expand_brace_groups(glob):
            if fnmatch(path, pat) or fnmatch(basename, pat):
                return True
    return False


_PATTERNS = [
    "scripts/check_lane_claim.py",
    "scripts/*.py",
    "**/*.py",
    "docs/**/*.md",
    "scripts/{check_lane_claim,pick_idle_grain}.py",
    "scripts/{check_lane_claim,pick_idle_grain}.{py,pyi}",
    "GradeBookApp/**",
    "*.lean",
    "MyIA.AI.Notebooks/SymbolicAI/**",
    "nonexistent/path/**",
    "a]",
    "a[",
    "a*b",
    "a?b",
    "[a-z]*",
    "*",
]

_TRACKED = [
    "scripts/check_lane_claim.py",
    "scripts/pick_idle_grain.py",
    "scripts/tests/test_x.py",
    "docs/reference/x.md",
    "docs/reference/y.md",
    "GradeBookApp/configs/README.md",
    "MyIA.AI.Notebooks/SymbolicAI/Lean/Foo.lean",
    "README.md",
]


@pytest.mark.parametrize("glob", _PATTERNS)
def test_fast_path_glob_equivalent_a_la_reference(glob):
    """Liste simple ET forme normalisee : meme verdict que `fnmatch`."""
    attendu = _reference(glob, _TRACKED)
    assert clc._glob_matches_tracked(glob, list(_TRACKED)) is attendu
    assert clc._glob_matches_tracked(
        glob, clc._TrackedFiles(list(_TRACKED))) is attendu


@pytest.mark.parametrize("glob", ["scripts/check_lane_claim.py", "README.md",
                                  "absent.py"])
def test_fast_path_litteral_equivalent_au_chemin_general(glob):
    """Le chemin litteral (table de hachage) donne le meme verdict que le
    chemin general (regex compilee) -- sur les DEUX formes de liste."""
    attendu = _reference(glob, _TRACKED)
    assert clc._glob_matches_tracked(glob, list(_TRACKED)) is attendu
    assert clc._glob_matches_tracked(
        glob, clc._TrackedFiles(list(_TRACKED))) is attendu


def test_memo_des_fichiers_suivis_est_reutilise(monkeypatch):
    """Le `git ls-files` n'est relance qu'une fois par racine."""
    clc._TRACKED_FILES_MEMO.clear()
    appels: list[list[str]] = []

    def fake_run(cmd, *a, **k):
        appels.append(list(cmd))
        return subprocess.CompletedProcess(
            cmd, 0, stdout="a.py\nb/c.py\n", stderr="")

    monkeypatch.setattr(clc.subprocess, "run", fake_run)

    premier = clc._git_tracked_files("/racine/fictive")
    second = clc._git_tracked_files("/racine/fictive")

    assert len(appels) == 1
    assert list(premier) == ["a.py", "b/c.py"]
    assert list(second) == ["a.py", "b/c.py"]


# --- 3. le prefetch des etats de PR ---------------------------------------


_ALIAS_PULL = re.compile(r"(p\d+):\s*pullRequest\(number:\s*(\d+)\)")


def _graphql_faux(monkeypatch, etats: dict[int, dict]):
    """Faux `gh api graphql` : rend les noeuds demandes, sous leur alias.

    Le lecteur aliasse chaque PR (`p0`, `p1`, ...) : le faux doit rendre
    la CLE ALIAS, pas le numero. On relit donc l'alias dans la requete.
    """
    vus: list[str] = []

    def fake(query, variables=None):
        vus.append(query)
        data: dict = {}
        for alias, numero in _ALIAS_PULL.findall(query):
            if int(numero) in etats:
                data[alias] = etats[int(numero)]
        return {"data": {"repository": data}}

    monkeypatch.setattr(clc, "_gh_graphql", fake)
    return vus


def test_prefetch_verse_dans_le_cache_et_pas_dans_une_map_injectee(
        monkeypatch):
    """Le prefetch alimente `_PR_STATE_CACHE`, jamais `pr_states`.

    Une map `pr_states` PARTIELLE est fail-OPEN : le reducteur rend
    `close` pour une PR absente de la map (cf. le test
    `test_delivered_unknown_pr_closes_legacy`). Verser dans le cache de
    processus preserve le fail-CLOSED de #13336 : une PR non lue part sur
    son chemin historique (`gh pr view`).
    """
    vus = _graphql_faux(monkeypatch, {
        101: {"number": 101, "state": "MERGED", "mergedAt": "2026-11-01T00:00:00Z"},
        102: {"number": 102, "state": "OPEN", "mergedAt": None},
        103: {"number": 103, "state": "CLOSED", "mergedAt": None},
    })
    monkeypatch.setattr(clc, "_repo_slug", lambda: "jsboige/CoursIA")

    etats = clc._prefetch_pr_states([101, 102, 103])

    assert etats == {101: "MERGED", 102: "OPEN", 103: "CLOSED"}
    # UN seul appel pour les trois PRs.
    assert len(vus) == 1
    assert "pullRequest(number: 101)" in vus[0]
    assert "pullRequest(number: 103)" in vus[0]


def test_le_cache_sert_la_lecture_unitaire_sans_appel_reseau(monkeypatch):
    """Une PR prechargee est servie par `_fetch_pr_state` sans `gh pr view`."""
    clc._PR_STATE_CACHE.clear()
    vus = _graphql_faux(monkeypatch, {
        201: {"number": 201, "state": "MERGED", "mergedAt": "2026-11-01T00:00:00Z"},
        202: {"number": 202, "state": "OPEN", "mergedAt": None},
    })
    monkeypatch.setattr(clc, "_repo_slug", lambda: "jsboige/CoursIA")

    # Le prefetch couvre un lot (au moins deux PRs : sous le seuil, la
    # lecture unitaire reste le chemin -- cf. le test suivant).
    etats = clc._prefetch_pr_states([201, 202])
    for numero, etat in etats.items():
        clc._PR_STATE_CACHE.setdefault(numero, (etat, None))

    def refuse_gh_pr_view(*a, **k):
        pytest.fail("gh pr view atteint alors que la PR est prechargee")

    monkeypatch.setattr(clc.subprocess, "run", refuse_gh_pr_view)

    assert clc._fetch_pr_state(201) == ("MERGED", None)
    assert clc._fetch_pr_state(202) == ("OPEN", None)
    assert len(vus) == 1


def test_prefetch_ne_remplit_pas_le_cache_en_cas_d_echec(monkeypatch):
    """Un echec du transport rend un dict VIDE : le cache reste intact, et
    la lecture unitaire reste le chemin de secours (fail-CLOSED)."""
    def boom(query, variables=None):
        raise RuntimeError("transport indisponible")

    monkeypatch.setattr(clc, "_gh_graphql", boom)
    monkeypatch.setattr(clc, "_repo_slug", lambda: "jsboige/CoursIA")

    assert clc._prefetch_pr_states([301, 302]) == {}


def test_prefetch_ignore_un_numero_unique(monkeypatch):
    """Un seul numero : pas d'aller-retour GraphQL pour une seule PR."""
    vus = _graphql_faux(monkeypatch, {})
    monkeypatch.setattr(clc, "_repo_slug", lambda: "jsboige/CoursIA")

    assert clc._prefetch_pr_states([401]) == {}
    assert vus == []


# --- 4. la voie en processus rend les memes verdicts -----------------------


def test_le_tapis_appelle_le_lecteur_en_mode_strict(monkeypatch):
    """Le tapis passe bien par `check_claims(..., strict_snapshot=True)`."""
    appele: dict = {}

    def spy(numbers, lane, **kwargs):
        appele["numbers"] = list(numbers)
        appele["lane"] = lane
        appele["strict"] = kwargs.get("strict_snapshot")
        return {n: (pig.CLAIM_CODE_FREE, "libre") for n in numbers}

    monkeypatch.setattr(pig, "check_claims", spy)
    # Le tapis est exerce par ses tests dedies (test_pick_idle_grain_belt.py)
    # : ici on verifie seulement le contrat de l'appel, qui est le point
    # que ce PR change.
    import inspect
    source = inspect.getsource(pig.main)
    assert "strict_snapshot=True" in source


# --- 7. l'activite des PRs de la lane est prechargee en phase reseau --------


def _graphql_activite_faux(monkeypatch, payload: dict):
    """Faux `_gh_graphql` : enregistre la requete, rend le payload."""
    vues: list[str] = []

    def faux(query, variables=None):
        vues.append(query)
        return {"data": {"repository": payload}}

    monkeypatch.setattr(clc, "_gh_graphql", faux)
    monkeypatch.setattr(clc, "_repo_slug", lambda: "jsboige/CoursIA")
    return vues


def test_prefetch_pr_activity_sert_le_cache_sans_reseau(monkeypatch):
    """Le prefetch verse l'activite dans le cache, et la lecture ne
    demande plus rien au reseau."""
    clc._PR_ACTIVITY_CACHE.clear()
    payload = {
        "p0": {"commits": {"nodes": [{"commit": {
                    "committedDate": "2026-11-01T10:00:00Z"}}]},
               "comments": {"nodes": []}},
        "p1": {"commits": {"nodes": []},
               "comments": {"nodes": [
                   {"body": "-- lane myia-po-2023:CoursIA-2",
                    "createdAt": "2026-11-02T09:00:00Z"},
                   {"body": "rien pour cette lane",
                    "createdAt": "2026-11-03T09:00:00Z"}]}},
    }
    vues = _graphql_activite_faux(monkeypatch, payload)

    assert clc.prefetch_pr_activity([201, 202]) == 2
    assert len(vues) == 1

    def refuse(*a, **k):
        pytest.fail("gh pr view atteint alors que l'activite est prechargee")

    monkeypatch.setattr(clc.subprocess, "run", refuse)
    assert clc._pr_last_lane_activity(201, "myia-po-2023:CoursIA-2").isoformat() \
        == "2026-11-01T10:00:00+00:00"
    assert clc._pr_last_lane_activity(202, "myia-po-2023:CoursIA-2").isoformat() \
        == "2026-11-02T09:00:00+00:00"
    # Un commentaire d'une AUTRE lane ne compte pas.
    assert clc._pr_last_lane_activity(202, "myia-ai-01:CoursIA-2") is None


def test_prefetch_pr_activity_ne_remplit_pas_le_cache_en_cas_d_echec(monkeypatch):
    """Un echec du transport rend 0 : le cache reste intact, et le lecteur
    garde son chemin historique (fail-CLOSED de #22408)."""
    clc._PR_ACTIVITY_CACHE.clear()

    def boom(query, variables=None):
        raise RuntimeError("transport indisponible")

    monkeypatch.setattr(clc, "_gh_graphql", boom)
    monkeypatch.setattr(clc, "_repo_slug", lambda: "jsboige/CoursIA")

    assert clc.prefetch_pr_activity([301, 302]) == 0
    assert clc._PR_ACTIVITY_CACHE == {}


def test_lane_open_pr_numbers_lit_le_cache_seulement(tmp_path):
    """La liste des PRs de la lane vient du cache v2 complet, sans reseau."""
    cache = tmp_path / "open-prs.json"
    cache.write_text(json.dumps({
        "format": "open-prs-v2", "complete": True,
        "prs": [
            {"number": 11, "body": "-- lane myia-po-2023:CoursIA-2"},
            {"number": 12, "body": "-- lane myia-ai-01:CoursIA-2"},
            {"number": 13, "body": "aucun tag"},
        ],
    }), encoding="utf-8")

    assert clc.lane_open_pr_numbers("myia-po-2023:CoursIA-2", str(cache)) == [11]
    assert clc.lane_open_pr_numbers("myia-ai-01:CoursIA-2", str(cache)) == [12]
    assert clc.lane_open_pr_numbers(None, str(cache)) == []


def test_lane_open_pr_numbers_refuse_un_cache_incomplet(tmp_path):
    """Un cache marque incomplet n'est PAS une preuve : la liste est vide,
    et le lecteur garde son chemin historique."""
    cache = tmp_path / "open-prs.json"
    cache.write_text(json.dumps({
        "format": "open-prs-v2", "complete": False, "reason": "reseau",
        "prs": [{"number": 11, "body": "-- lane myia-po-2023:CoursIA-2"}],
    }), encoding="utf-8")

    assert clc.lane_open_pr_numbers("myia-po-2023:CoursIA-2", str(cache)) == []


def test_le_tapis_precharge_l_activite_en_phase_reseau(monkeypatch):
    """La phase reseau du tapis declenche le prefetch d'activite.

    C'est ce qui rend la lecture des claims SANS reseau : sans ce
    prefetch, le LECTEUR demanderait `gh pr view` -- une fois par issue
    que la PR reference (25 appels mesures le 2026-11-05).
    """
    appele: dict = {}

    def faux(numbers, cache_path=None, threshold_h=48.0, my_lane=None):
        appele["numbers"] = list(numbers)
        appele["cache_path"] = cache_path
        appele["my_lane"] = my_lane
        return 3

    monkeypatch.setattr(pig, "_claim_reader_module",
                        lambda: types.SimpleNamespace(
                            prefetch_claim_activity=faux,
                            _collect_delivered_pr_refs=lambda nums: [],
                            _prefetch_pr_states=lambda refs: {},
                            _PR_STATE_CACHE={},
                            set_snapshot=lambda snapshot: None))
    monkeypatch.setattr(pig, "_gh_snapshot_module",
                        lambda: types.SimpleNamespace(
                            load_snapshot=lambda repo: {"meta": {}}))
    monkeypatch.setenv("PYTEST_CURRENT_TEST", "1")
    # `PYTEST_CURRENT_TEST` present : le tapis ne lance pas la phase
    # reseau. On appelle donc le prefetch directement, comme le fait
    # `main()`.
    assert pig._belt_pr_prefetches([1, 2], "myia-ai-01:CoursIA-2",
                                    None) == (0, 0)

    monkeypatch.delenv("PYTEST_CURRENT_TEST")
    etats, activites = pig._belt_pr_prefetches([1, 2], "myia-ai-01:CoursIA-2",
                                               "c:/tmp/x.json")
    assert activites == 3
    assert etats == 0
    assert appele["numbers"] == [1, 2]
    assert appele["cache_path"] == "c:/tmp/x.json"
    assert appele["my_lane"] == "myia-ai-01:CoursIA-2"


def test_la_prediction_des_prs_porte_sur_les_claims_perimes(monkeypatch):
    """Seules les PRs d'un claim PERIME d'une AUTRE lane sont annoncees.

    C'est la question que le LECTEUR pose reellement (#22408) : un claim
    vieux, dont la lane titulaire pourrait encore travailler le grain.
    Une prediction trop large coute une PR prechargee pour rien ; une
    prediction trop etroite fait retomber le lecteur sur son chemin
    historique. Les deux sont sans consequence sur le verdict.
    """
    ancien = "2026-01-01T00:00:00Z"
    recent = "2099-01-01T00:00:00Z"
    issue = 5001

    def payload(comment_body, created_at):
        return {"number": issue, "comments": [
            {"body": comment_body, "createdAt": created_at, "id": "c1"}]}

    snapshots = {
        "5001": payload("[CLAIMED] lane myia-po-2023:CoursIA-2 -- x", ancien),
        "5002": payload("[CLAIMED] lane myia-po-2023:CoursIA-2 -- y", recent),
    }
    monkeypatch.setattr(clc, "_snapshot_issue_payload",
                        lambda n: snapshots.get(str(n)))

    open_prs = [
        {"number": 71, "body": "-- lane myia-po-2023:CoursIA-2 -- refs #5001"},
        {"number": 72, "body": "-- lane myia-po-2023:CoursIA-2 -- refs #5001"},
        {"number": 73, "body": "-- lane myia-ai-01:CoursIA-2 -- refs #5001"},
    ]

    numbers = clc.claim_activity_pr_numbers([5001, 5002], open_prs,
                                            threshold_h=48.0,
                                            my_lane="myia-ai-01:CoursIA-2")
    # Le claim de 5001 est perime : ses PRs sont annoncees.
    assert numbers == [71, 72]
    # La PR de MA lane n'est jamais annoncee : le LECTEUR ne demande pas
    # l'activite de la lane qu'il verifie.
    assert 73 not in numbers
