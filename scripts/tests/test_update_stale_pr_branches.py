"""Tests de `scripts/ci/update_stale_pr_branches.py` (#16149).

Aucun appel reseau : `gh` est remplace par une doublure a la couture unique
`run_gh`, et la sortie JSON est lue sur stdout. Chaque cas exerce une garde du
contrat -- les neuf conditions d'application, dont la garde du registre des
mises a jour en vol.

Deux proprietes sont verifiees dans TOUS les cas ou l'organe ecrit, parce que
ce sont elles qui rendent le geste sur :

  * `--rebase` n'est jamais passe (un rebase reecrit les commits d'auteur) ;
  * aucun repli n'existe -- `update-branch` est le seul appel d'ecriture, jamais
    un force-push, jamais un `git` de secours.

Un troisieme point est un test de NON-INERTIE, et c'est le plus important du
fichier : le retard ne se lit PAS dans `mergeStateStatus` (0 `BEHIND` sur les
200 lignes ouvertes lues, mesure 2026-09-17), mais dans le `behind_by` de l'API de
comparaison. `test_clean_and_behind_is_updated_from_the_compare_api` tombe si
quelqu'un rebranche l'organe sur `mergeStateStatus` : la PR y est `CLEAN` ET en
retard de 11 commits, exactement le cas que le pool porte en masse.
"""

import importlib.util
import json
import re
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
SCRIPT = HERE.parent / "ci" / "update_stale_pr_branches.py"
spec = importlib.util.spec_from_file_location("update_stale_pr_branches", SCRIPT)
mod = importlib.util.module_from_spec(spec)
sys.modules["update_stale_pr_branches"] = mod
spec.loader.exec_module(mod)

H1 = "1" * 40
H2 = "2" * 40
REPO = "jsboige/CoursIA"
LANE_BASE = "feature/16000-parent"
#: Retard par defaut des fixtures : la valeur mesuree sur le pool reel (#16546).
BEHIND = 11

COMPARE_RE = re.compile(r"^repos/[^/]+/[^/]+/compare/(.+)\.\.\.(.+)$")


def view(number, *, state="OPEN", base="main", head=H1, mergeable="MERGEABLE",
         status="CLEAN", draft=False, fork=False, head_ref="feature/x",
         behind_by=BEHIND):
    """Une reponse `gh pr view` minimale, aux champs reellement lus."""
    return {
        "number": number,
        "state": state,
        "isDraft": draft,
        "isCrossRepository": fork,
        "baseRefName": base,
        "headRefName": head_ref,
        "headRefOid": head,
        "mergeable": mergeable,
        "mergeStateStatus": status,
        "url": f"https://github.com/{REPO}/pull/{number}",
        "_behind_by": behind_by,
    }


class FakeGh:
    """Doublure de `run_gh` : file de reponses par PR, appels enregistres."""

    def __init__(self, views, *, update_rc=0, update_stderr="Update failed",
                 compare_error=None):
        self.views = {k: list(v) for k, v in views.items()}
        self.update_rc = update_rc
        self.update_stderr = update_stderr
        self.compare_error = compare_error
        #: Le compare repond par (base, head) -- donc contre la base DECLAREE,
        #: ce qui couvre le cas empile sans code de test dedie.
        self.behind = {}
        for queue in self.views.values():
            for item in queue:
                self.behind[(item["baseRefName"], item["headRefOid"])] = item["_behind_by"]
        self.calls = []

    def __call__(self, args):
        args = list(args)
        self.calls.append(args)
        if args[:2] == ["pr", "view"]:
            pr = int(args[2])
            queue = self.views.get(pr)
            if not queue:
                raise mod.GhError(f"gh: no pull requests found for #{pr}")
            # Une file d'UN element sert toutes les lectures (etat stable) ;
            # une file plus longue simule une valeur qui change entre deux
            # lectures -- c'est ainsi qu'on exerce la garde TOCTOU.
            return json.dumps(queue.pop(0) if len(queue) > 1 else queue[0])
        if args[:2] == ["pr", "update-branch"]:
            if self.update_rc:
                raise mod.GhError(self.update_stderr)
            return ""
        if args[0] == "api":
            match = COMPARE_RE.match(args[1])
            if match is None:
                raise AssertionError(f"appel api inattendu : {args}")
            if self.compare_error:
                raise mod.GhError(self.compare_error)
            key = (match.group(1), match.group(2))
            if key not in self.behind:
                raise AssertionError(f"compare non prepare pour {key}")
            return json.dumps({"behind_by": self.behind[key]})
        raise AssertionError(f"appel gh inattendu : {args}")

    @property
    def writes(self):
        return [c for c in self.calls if c[:2] == ["pr", "update-branch"]]

    @property
    def compares(self):
        return [c for c in self.calls if c[0] == "api"]


def run(monkeypatch, capsys, tmp_path, views, *, prs=(1,), extra=(), update_rc=0,
        compare_error=None):
    """Execute `main` avec gh double et une sortie JSON isolee."""
    fake = FakeGh(views, update_rc=update_rc, compare_error=compare_error)
    monkeypatch.setattr(mod, "run_gh", fake)
    argv = []
    for pr in prs:
        argv += ["--pr", str(pr)]
    argv += ["--state-dir", str(tmp_path), *extra]
    rc = mod.main(argv)
    payload = json.loads(capsys.readouterr().out)
    return rc, payload, fake


def only(payload):
    assert len(payload["results"]) == 1
    return payload["results"][0]


def seed_ledger(tmp_path, pr, head, started_at):
    path = mod.ledger_path(tmp_path)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(
            {mod.ledger_key(REPO, pr): {"previous_head": head, "started_at": started_at}}
        ),
        encoding="utf-8",
    )
    return path


# --- l'instrument : le retard vient du compare, jamais de mergeStateStatus ---


def test_clean_and_behind_is_updated_from_the_compare_api(monkeypatch, capsys, tmp_path):
    """Le cas que le pool porte en masse : CLEAN et pourtant 11 commits de retard.

    Si quelqu'un rebranche l'organe sur `mergeStateStatus == BEHIND`, cette PR
    sort en SKIP et ce test rougit -- c'est son unique raison d'etre.
    """
    rc, payload, fake = run(
        monkeypatch,
        capsys,
        tmp_path,
        {16546: [view(16546, status="CLEAN", behind_by=11)]},
        prs=(16546,),
        extra=["--apply"],
    )
    result = only(payload)
    assert rc == 0
    assert result["action"] == mod.ACTION_UPDATE
    assert result["merge_state_status"] == "CLEAN"
    assert result["behind_by"] == 11
    assert len(fake.writes) == 1


def test_blocked_and_behind_is_updated(monkeypatch, capsys, tmp_path):
    # Meme classe : BLOCKED n'est pas un conflit, c'est une protection de
    # branche -- et il masque le retard dans mergeStateStatus.
    _, payload, fake = run(
        monkeypatch,
        capsys,
        tmp_path,
        {16548: [view(16548, status="BLOCKED", behind_by=11)]},
        prs=(16548,),
        extra=["--apply"],
    )
    assert only(payload)["action"] == mod.ACTION_UPDATE
    assert len(fake.writes) == 1


def test_unreadable_behind_is_skipped_fail_closed(monkeypatch, capsys, tmp_path):
    rc, payload, fake = run(
        monkeypatch,
        capsys,
        tmp_path,
        {1: [view(1)]},
        extra=["--apply"],
        compare_error="HTTP 502",
    )
    result = only(payload)
    # Fail-closed, mais pas un REFUSE : l'organe ne sait pas, il ne decide pas.
    assert rc == 0
    assert result["action"] == mod.ACTION_SKIP
    assert result["code"] == "BEHIND_UNKNOWN"
    assert result["behind_by"] is None
    assert fake.writes == []


# --- base principale -------------------------------------------------------


def test_main_base_behind_is_updated_against_its_declared_base(monkeypatch, capsys, tmp_path):
    rc, payload, fake = run(
        monkeypatch, capsys, tmp_path, {1: [view(1)]}, extra=["--apply"]
    )
    result = only(payload)
    assert rc == 0
    assert result["action"] == mod.ACTION_UPDATE
    assert result["code"] == "OK"
    assert result["base"] == "main"
    assert result["base_kind"] == "main"
    assert result["stacked"] is False
    assert result["base_source"] == "pr.baseRefName"
    assert result["updated"] is True
    assert fake.writes == [["pr", "update-branch", "1", "--repo", REPO]]


def test_update_never_passes_rebase_and_never_forces(monkeypatch, capsys, tmp_path):
    _, _, fake = run(monkeypatch, capsys, tmp_path, {1: [view(1)]}, extra=["--apply"])
    assert len(fake.writes) == 1
    for call in fake.calls:
        assert "--rebase" not in call
        assert "--force" not in call and "--force-with-lease" not in call
        assert "push" not in call[:2]
        assert "rebase" not in call[:2]
        # Aucune base n'est jamais fournie : `gh pr update-branch` fusionne la
        # base DECLAREE de la PR, donc une erreur de base empilee est
        # impossible par construction.
        assert "--base" not in call


# --- PR empilee ------------------------------------------------------------


def test_stacked_pr_updates_against_its_declared_base(monkeypatch, capsys, tmp_path):
    rc, payload, fake = run(
        monkeypatch,
        capsys,
        tmp_path,
        {7: [view(7, base=LANE_BASE)]},
        prs=(7,),
        extra=["--apply"],
    )
    result = only(payload)
    assert rc == 0
    assert result["base"] == LANE_BASE
    assert result["base_kind"] == "stacked"
    assert result["stacked"] is True
    assert result["updated"] is True
    # La base empilee est reportee, et l'appel reste celui de la PR -- jamais
    # un update contre `main`.
    assert fake.writes == [["pr", "update-branch", "7", "--repo", REPO]]


def test_stacked_pr_measures_its_deficit_against_the_declared_base(
    monkeypatch, capsys, tmp_path
):
    _, _, fake = run(
        monkeypatch,
        capsys,
        tmp_path,
        {7: [view(7, base=LANE_BASE)]},
        prs=(7,),
        extra=["--apply"],
    )
    assert fake.compares[0][1] == f"repos/{REPO}/compare/{LANE_BASE}...{H1}"


def test_base_kind_classifies_main_variants_and_stacks():
    assert mod.base_kind("main") == "main"
    assert mod.base_kind("master") == "main"
    assert mod.base_kind(LANE_BASE) == "stacked"
    assert mod.base_kind(None) == "stacked"


# --- conflits : jamais de repli -------------------------------------------


def test_conflicting_pr_is_refused_without_any_write(monkeypatch, capsys, tmp_path):
    rc, payload, fake = run(
        monkeypatch,
        capsys,
        tmp_path,
        {3: [view(3, mergeable="CONFLICTING", status="DIRTY")]},
        prs=(3,),
        extra=["--apply"],
    )
    result = only(payload)
    assert rc == 1
    assert result["action"] == mod.ACTION_REFUSE
    assert result["code"] == "CONFLICTING"
    assert result["updated"] is False
    assert result["refresh_required"] is False
    assert fake.writes == []


def test_dirty_merge_state_without_conflicting_mergeable_is_refused(
    monkeypatch, capsys, tmp_path
):
    rc, payload, fake = run(
        monkeypatch,
        capsys,
        tmp_path,
        {3: [view(3, mergeable="MERGEABLE", status="DIRTY")]},
        prs=(3,),
        extra=["--apply"],
    )
    result = only(payload)
    assert rc == 1
    assert result["code"] == "CONFLICTING"
    assert fake.writes == []


def test_conflict_is_refused_before_the_compare_call(monkeypatch, capsys, tmp_path):
    # Un conflit se decide sur les metadonnees : aucun besoin de mesurer le
    # deficit, et un conflit n'est jamais mis a jour.
    _, _, fake = run(
        monkeypatch,
        capsys,
        tmp_path,
        {3: [view(3, mergeable="CONFLICTING")]},
        prs=(3,),
        extra=["--apply"],
    )
    assert fake.writes == []
    assert fake.compares == []
    # Une seule lecture, la premiere : la relecture TOCTOU n'a pas lieu non plus.
    assert len([c for c in fake.calls if c[:2] == ["pr", "view"]]) == 1


def test_call_budget_for_a_skipped_pr(monkeypatch, capsys, tmp_path):
    """3 lectures pour une PR qui ne sera pas touchee : 2 metadonnees + 1 compare.

    Le budget est borne par construction (entree explicite + plafond), mais il
    est fige ici pour qu'un elargissement silencieux se voie.
    """
    _, _, fake = run(
        monkeypatch, capsys, tmp_path, {1: [view(1, behind_by=0)]}, extra=["--apply"]
    )
    views = [c for c in fake.calls if c[:2] == ["pr", "view"]]
    assert len(views) == 2  # mesure + relecture TOCTOU
    assert len(fake.compares) == 1
    assert fake.compares[0][1] == f"repos/{REPO}/compare/main...{H1}"
    assert fake.writes == []


def test_call_budget_for_an_applied_update(monkeypatch, capsys, tmp_path):
    _, _, fake = run(monkeypatch, capsys, tmp_path, {1: [view(1)]}, extra=["--apply"])
    assert len([c for c in fake.calls if c[:2] == ["pr", "view"]]) == 2
    assert len(fake.compares) == 1
    assert len(fake.writes) == 1
    assert len(fake.calls) == 4


# --- TOCTOU ----------------------------------------------------------------


def test_head_moving_between_reads_is_refused(monkeypatch, capsys, tmp_path):
    rc, payload, fake = run(
        monkeypatch,
        capsys,
        tmp_path,
        {5: [view(5, head=H1), view(5, head=H2)]},
        prs=(5,),
        extra=["--apply"],
    )
    result = only(payload)
    assert rc == 1
    assert result["action"] == mod.ACTION_REFUSE
    assert result["code"] == "HEAD_CHANGED"
    assert result["updated"] is False
    assert fake.writes == []


def test_base_moving_between_reads_is_refused(monkeypatch, capsys, tmp_path):
    rc, payload, fake = run(
        monkeypatch,
        capsys,
        tmp_path,
        {5: [view(5, base="main"), view(5, base="release/next")]},
        prs=(5,),
        extra=["--apply"],
    )
    result = only(payload)
    assert rc == 1
    assert result["code"] == "BASE_CHANGED"
    assert fake.writes == []


def test_stable_second_read_allows_the_update(monkeypatch, capsys, tmp_path):
    _, payload, fake = run(
        monkeypatch,
        capsys,
        tmp_path,
        {5: [view(5), view(5)]},
        prs=(5,),
        extra=["--apply"],
    )
    assert only(payload)["action"] == mod.ACTION_UPDATE
    assert len(fake.writes) == 1


# --- plafond ---------------------------------------------------------------


def test_cap_limits_updates_per_call_and_keeps_the_rest_for_later(
    monkeypatch, capsys, tmp_path
):
    rc, payload, fake = run(
        monkeypatch,
        capsys,
        tmp_path,
        {1: [view(1)], 2: [view(2)]},
        prs=(1, 2),
        extra=["--apply", "--max-updates", "1"],
    )
    assert rc == 0
    assert payload["max_updates"] == 1
    assert payload["updates_applied"] == 1
    first, second = payload["results"]
    assert first["pr"] == 1 and first["updated"] is True
    assert second["pr"] == 2
    assert second["action"] == mod.ACTION_SKIP
    assert second["code"] == "CAP_REACHED"
    assert fake.writes == [["pr", "update-branch", "1", "--repo", REPO]]


def test_cap_reached_costs_no_network_call(monkeypatch, capsys, tmp_path):
    """Le plafond est verifie AVANT toute lecture : la PR 2 ne coute rien.

    Sans ce court-circuit, chaque PR au-dela du plafond payerait deux lectures
    et un appel de comparaison pour un verdict deja connu.
    """
    _, payload, fake = run(
        monkeypatch,
        capsys,
        tmp_path,
        {1: [view(1)], 2: [view(2)]},
        prs=(1, 2),
        extra=["--apply", "--max-updates", "1"],
    )
    assert {c[2] for c in fake.calls if c[:2] == ["pr", "view"]} == {"1"}
    assert len(fake.compares) == 1
    assert payload["results"][1]["previous_head"] is None
    assert payload["results"][1]["base"] is None


def test_cap_zero_means_unbounded(monkeypatch, capsys, tmp_path):
    _, payload, fake = run(
        monkeypatch,
        capsys,
        tmp_path,
        {1: [view(1)], 2: [view(2)], 3: [view(3)], 4: [view(4)]},
        prs=(1, 2, 3, 4),
        extra=["--apply", "--max-updates", "0"],
    )
    assert payload["updates_applied"] == 4
    assert len(fake.writes) == 4


def test_duplicate_pr_numbers_are_processed_once(monkeypatch, capsys, tmp_path):
    _, payload, fake = run(
        monkeypatch,
        capsys,
        tmp_path,
        {1: [view(1)]},
        prs=(1, 1),
        extra=["--apply"],
    )
    assert len(payload["results"]) == 1
    assert len(fake.writes) == 1


# --- dry-run ---------------------------------------------------------------


def test_dry_run_is_the_default_and_writes_nothing(monkeypatch, capsys, tmp_path):
    rc, payload, fake = run(monkeypatch, capsys, tmp_path, {1: [view(1)]})
    result = only(payload)
    assert rc == 0
    assert payload["mode"] == "dry-run"
    assert result["action"] == mod.ACTION_UPDATE
    assert result["updated"] is False
    assert result["freshness"] is None
    assert result["refresh_required"] is False
    assert result["invalidated"] == []
    assert fake.writes == []
    # Rien n'est ecrit dans le registre non plus.
    assert mod.read_ledger(mod.ledger_path(tmp_path)) == {}


def test_dry_run_still_reports_the_toctou_refusal(monkeypatch, capsys, tmp_path):
    rc, payload, fake = run(
        monkeypatch, capsys, tmp_path, {5: [view(5, head=H1), view(5, head=H2)]}, prs=(5,)
    )
    assert rc == 1
    assert only(payload)["code"] == "HEAD_CHANGED"
    assert fake.writes == []


# --- application : succes, fraicheur --------------------------------------


def test_apply_success_marks_stale_and_refresh_required(monkeypatch, capsys, tmp_path):
    rc, payload, fake = run(
        monkeypatch, capsys, tmp_path, {1: [view(1)]}, extra=["--apply"]
    )
    result = only(payload)
    assert rc == 0
    assert result["updated"] is True
    assert result["freshness"] == "STALE"
    assert result["refresh_required"] is True
    assert result["invalidated"] == ["checks", "reviews", "dossier"]
    assert result["rebase"] is False
    assert result["warnings"] == []

    # Le registre enregistre la tete AVANT, pour la garde en vol.
    ledger = mod.read_ledger(mod.ledger_path(tmp_path))
    record = ledger[mod.ledger_key(REPO, 1)]
    assert record["previous_head"] == H1
    assert abs(record["started_at"] - time.time()) < 60


def test_applied_result_names_the_measured_head_previous_head(
    monkeypatch, capsys, tmp_path
):
    """La tete du resultat est celle AVANT l'appel, et elle le DIT.

    Elle n'est pas relue apres coup : `gh pr update-branch` rend la main avant
    que GitHub reecrive la reference, donc une relecture immediate peut rendre
    l'ancienne valeur. Un champ nomme `head` pretendrait decrire l'apres -- un
    `previous_head` decrit exactement ce qui a ete observe.
    """
    _, payload, _ = run(monkeypatch, capsys, tmp_path, {1: [view(1)]}, extra=["--apply"])
    result = only(payload)
    assert result["previous_head"] == H1
    assert "head" not in result


def test_skipped_result_also_names_the_measured_head_previous_head(
    monkeypatch, capsys, tmp_path
):
    _, payload, _ = run(
        monkeypatch, capsys, tmp_path, {1: [view(1, draft=True)]}, extra=["--apply"]
    )
    assert only(payload)["previous_head"] == H1


def test_apply_failure_is_a_structured_refuse_never_a_fallback(
    monkeypatch, capsys, tmp_path
):
    rc, payload, fake = run(
        monkeypatch,
        capsys,
        tmp_path,
        {1: [view(1)]},
        extra=["--apply"],
        update_rc=1,
    )
    result = only(payload)
    assert rc == 1
    assert result["action"] == mod.ACTION_REFUSE
    assert result["code"] == "UPDATE_FAILED"
    assert result["updated"] is False
    # Un seul appel d'ecriture, celui qui a echoue : aucun repli tente derriere.
    assert len(fake.writes) == 1
    assert mod.read_ledger(mod.ledger_path(tmp_path)) == {}


def test_unwritable_state_dir_is_a_warning_not_a_failed_update(
    monkeypatch, capsys, tmp_path
):
    blocker = tmp_path / "blocked"
    blocker.write_text("je suis un fichier, pas un repertoire", encoding="utf-8")
    fake = FakeGh({1: [view(1)]})
    monkeypatch.setattr(mod, "run_gh", fake)
    rc = mod.main(["--pr", "1", "--state-dir", str(blocker), "--apply"])
    result = only(json.loads(capsys.readouterr().out))
    assert rc == 0
    assert result["updated"] is True
    assert result["refresh_required"] is True
    assert len(result["warnings"]) == 1
    assert "UPDATE_IN_FLIGHT" in result["warnings"][0]


# --- registre des mises a jour en vol -------------------------------------


def test_recent_in_flight_record_blocks_a_second_application(
    monkeypatch, capsys, tmp_path
):
    seed_ledger(tmp_path, 1, H1, time.time() - 30)
    rc, payload, fake = run(
        monkeypatch, capsys, tmp_path, {1: [view(1)]}, extra=["--apply"]
    )
    result = only(payload)
    assert rc == 0
    assert result["action"] == mod.ACTION_SKIP
    assert result["code"] == "UPDATE_IN_FLIGHT"
    assert fake.writes == []


def test_expired_in_flight_record_does_not_block(monkeypatch, capsys, tmp_path):
    seed_ledger(tmp_path, 1, H1, time.time() - 10_000)
    _, payload, fake = run(
        monkeypatch, capsys, tmp_path, {1: [view(1)]}, extra=["--apply"]
    )
    assert only(payload)["code"] == "OK"
    assert len(fake.writes) == 1


def test_in_flight_record_on_an_older_head_does_not_block(
    monkeypatch, capsys, tmp_path
):
    # La tete lue differe de celle enregistree : la mise a jour precedente a
    # atterri, la garde ne doit pas la confondre avec une mise a jour en vol.
    seed_ledger(tmp_path, 1, H2, time.time() - 30)
    _, payload, fake = run(
        monkeypatch, capsys, tmp_path, {1: [view(1, head=H1)]}, extra=["--apply"]
    )
    assert only(payload)["code"] == "OK"
    assert len(fake.writes) == 1


def test_in_flight_ttl_is_configurable(monkeypatch, capsys, tmp_path):
    seed_ledger(tmp_path, 1, H1, time.time() - 300)
    _, payload, fake = run(
        monkeypatch,
        capsys,
        tmp_path,
        {1: [view(1)]},
        extra=["--apply", "--in-flight-ttl", "60"],
    )
    assert only(payload)["code"] == "OK"
    assert len(fake.writes) == 1


def test_malformed_ledger_is_read_as_empty_rather_than_failing(
    monkeypatch, capsys, tmp_path
):
    path = mod.ledger_path(tmp_path)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("{ pas du json", encoding="utf-8")
    rc, payload, fake = run(
        monkeypatch, capsys, tmp_path, {1: [view(1)]}, extra=["--apply"]
    )
    assert rc == 0
    assert only(payload)["code"] == "OK"
    assert len(fake.writes) == 1


# --- SKIP benins -----------------------------------------------------------


def test_closed_pr_is_skipped(monkeypatch, capsys, tmp_path):
    rc, payload, fake = run(
        monkeypatch, capsys, tmp_path, {1: [view(1, state="MERGED")]}, extra=["--apply"]
    )
    result = only(payload)
    assert rc == 0
    assert result["action"] == mod.ACTION_SKIP
    assert result["code"] == "NOT_OPEN"
    assert fake.writes == []


def test_closed_pr_costs_no_compare_call(monkeypatch, capsys, tmp_path):
    _, _, fake = run(
        monkeypatch, capsys, tmp_path, {1: [view(1, state="MERGED")]}, extra=["--apply"]
    )
    assert fake.compares == []


def test_draft_pr_is_skipped(monkeypatch, capsys, tmp_path):
    _, payload, fake = run(
        monkeypatch, capsys, tmp_path, {1: [view(1, draft=True)]}, extra=["--apply"]
    )
    assert only(payload)["code"] == "DRAFT"
    assert fake.writes == []


def test_mergeable_unknown_is_skipped_not_refused(monkeypatch, capsys, tmp_path):
    # GitHub calcule encore : c'est reessayable, pas un defaut de la PR.
    rc, payload, fake = run(
        monkeypatch,
        capsys,
        tmp_path,
        {1: [view(1, mergeable="UNKNOWN", status="UNKNOWN")]},
        extra=["--apply"],
    )
    result = only(payload)
    assert rc == 0
    assert result["action"] == mod.ACTION_SKIP
    assert result["code"] == "MERGEABLE_UNKNOWN"
    assert fake.writes == []


def test_up_to_date_branch_is_skipped(
    monkeypatch, capsys, tmp_path
):
    rc, payload, fake = run(
        monkeypatch,
        capsys,
        tmp_path,
        {1: [view(1, status="CLEAN", behind_by=0)]},
        extra=["--apply"],
    )
    result = only(payload)
    assert rc == 0
    assert result["action"] == mod.ACTION_SKIP
    assert result["code"] == "UP_TO_DATE"
    assert result["behind_by"] == 0
    assert fake.writes == []


# --- fork : l'ecriture n'est pas de notre cote -----------------------------


def test_fork_pr_is_refused(monkeypatch, capsys, tmp_path):
    rc, payload, fake = run(
        monkeypatch, capsys, tmp_path, {1: [view(1, fork=True)]}, extra=["--apply"]
    )
    result = only(payload)
    assert rc == 1
    assert result["action"] == mod.ACTION_REFUSE
    assert result["code"] == "FORK"
    assert fake.writes == []


# --- erreurs d'outil : structurees, jamais fatales -------------------------


def test_gh_read_failure_is_a_structured_refuse(monkeypatch, capsys, tmp_path):
    fake = FakeGh({})
    monkeypatch.setattr(mod, "run_gh", fake)
    rc = mod.main(["--pr", "999", "--state-dir", str(tmp_path), "--apply"])
    result = only(json.loads(capsys.readouterr().out))
    assert rc == 1
    assert result["action"] == mod.ACTION_REFUSE
    assert result["code"] == "ERROR"
    assert result["updated"] is False


def test_gh_failure_on_the_second_read_is_structured(monkeypatch, capsys, tmp_path):
    """Le 2e `pr view` echoue : mesure faite, re-mesure impossible -> REFUSE."""
    fake = FakeGh({1: [view(1), view(1)]})
    original = fake.__call__
    views = {"n": 0}

    def flaky(args):
        if args[:2] == ["pr", "view"]:
            views["n"] += 1
            if views["n"] == 2:
                raise mod.GhError("boom")
        return original(args)

    monkeypatch.setattr(mod, "run_gh", flaky)
    rc = mod.main(["--pr", "1", "--state-dir", str(tmp_path), "--apply"])
    result = only(json.loads(capsys.readouterr().out))
    assert rc == 1
    assert result["code"] == "ERROR"
    assert "boom" in result["reason"]


# --- contrat d'entree et forme de sortie -----------------------------------


def test_pr_argument_is_mandatory_never_a_pool(monkeypatch, capsys):
    # Un appel sans --pr doit echouer : l'organe ne devine jamais sa population.
    try:
        mod.parse_args([])
    except SystemExit as exc:
        assert exc.code == 2
    else:
        raise AssertionError("--pr doit etre obligatoire")


def test_negative_cap_is_rejected(monkeypatch, capsys):
    """Un plafond negatif se lirait « depasse des le premier appel » -- un refus muet."""
    for bad in ("-1", "-99"):
        try:
            mod.parse_args(["--pr", "1", "--max-updates", bad])
        except SystemExit as exc:
            assert exc.code == 2
        else:
            raise AssertionError(f"--max-updates {bad} doit etre refuse")


def test_zero_cap_is_accepted_as_unbounded(monkeypatch, capsys):
    assert mod.parse_args(["--pr", "1", "--max-updates", "0"]).max_updates == 0


def test_non_positive_in_flight_ttl_is_rejected(monkeypatch, capsys):
    """Un TTL nul ou negatif rendrait la garde UPDATE_IN_FLIGHT inoperante."""
    for bad in ("0", "-30"):
        try:
            mod.parse_args(["--pr", "1", "--in-flight-ttl", bad])
        except SystemExit as exc:
            assert exc.code == 2
        else:
            raise AssertionError(f"--in-flight-ttl {bad} doit etre refuse")


def test_defaults_are_dry_run_small_cap_and_positive_ttl(monkeypatch, capsys):
    args = mod.parse_args(["--pr", "1"])
    assert args.apply is False
    assert args.max_updates == mod.DEFAULT_MAX_UPDATES == 3
    assert args.in_flight_ttl == mod.DEFAULT_IN_FLIGHT_TTL > 0


def test_output_is_json_with_a_stable_shape(monkeypatch, capsys, tmp_path):
    _, payload, _ = run(
        monkeypatch, capsys, tmp_path, {1: [view(1), view(1)]}, extra=["--apply"]
    )
    assert set(payload) == {"repo", "mode", "max_updates", "updates_applied", "results"}
    assert payload["repo"] == REPO
    assert payload["mode"] == "apply"
    result = payload["results"][0]
    assert set(result) == {
        "pr", "action", "code", "reason", "base", "base_kind", "stacked",
        "base_source", "rebase", "previous_head", "head_ref", "mergeable",
        "merge_state_status", "behind_by", "url", "updated", "freshness",
        "refresh_required", "invalidated", "warnings",
    }


def test_result_does_not_leak_internal_fields(monkeypatch, capsys, tmp_path):
    # `_behind_by` est un champ de fixture ; le resultat ne le porte pas.
    _, payload, _ = run(
        monkeypatch, capsys, tmp_path, {1: [view(1)]}, extra=["--apply"]
    )
    assert "_behind_by" not in payload["results"][0]
    assert "behind_error" not in payload["results"][0]


def test_exit_codes_separate_benign_skips_from_refusals(monkeypatch, capsys, tmp_path):
    # SKIP benignes -> 0.
    rc, _, _ = run(
        monkeypatch, capsys, tmp_path, {1: [view(1, draft=True)]}, extra=["--apply"]
    )
    assert rc == 0
    # Un REFUSE -> 1, meme melange a un succes.
    rc, payload, _ = run(
        monkeypatch,
        capsys,
        tmp_path,
        {1: [view(1)], 2: [view(2, mergeable="CONFLICTING")]},
        prs=(1, 2),
        extra=["--apply"],
    )
    assert rc == 1
    assert payload["updates_applied"] == 1
