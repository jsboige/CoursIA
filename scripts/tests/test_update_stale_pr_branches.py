"""Tests de `scripts/ci/update_stale_pr_branches.py` (#16149).

Aucun appel reseau : `gh` est remplace par une doublure a la couture unique
`run_gh`, et la sortie JSON est lue sur stdout. Chaque cas exerce une garde du
contrat -- les neuf conditions d'application, dont la garde du registre des
mises a jour en vol.

Review 5240194972 (CHANGES_REQUESTED au head e4d22bce) -- les quatre findings
ont chacun leurs tests ici :

  1. TOCTOU par SHA : la base est EPINGLEE par son SHA (une base empilee
     avance sous son nom), le compare porte sur `base_sha...head_sha`, et les
     deux SHA sont RELUS apres le compare, immediatement avant l'ecriture.
     Mutations pendant/apres compare = REFUSE, zero ecriture ;
  2. le registre en vol est une RESERVATION acquise sous verrou
     inter-processus AVANT l'appel distant, en read-merge-write sous verrou,
     fail-closed sur registre corrompu -- y compris CLE PAR CLE (review
     5240575597, F2 residuel : schema structurel minimal par enregistrement,
     une entree invalide refuse tout le registre avant toute mutation ou
     reecriture) -- temporaire unique, et liberee sans perdre les
     enregistrements des autres PR -- avec contention REELLE par
     sous-processus, pas des mocks ;
  3. `mergeStateStatus=UNKNOWN` avec `mergeable=MERGEABLE` est refuse
     fail-closed (test causal) ;
  4. les segments de chemin d'API sont encodes : refs avec `#` et Unicode.

Deux proprietes sont verifiees dans TOUS les cas ou l'organe ecrit, parce que
ce sont elles qui rendent le geste sur :

  * `--rebase` n'est jamais passe (un rebase reecrit les commits d'auteur) ;
  * aucun repli n'existe -- `update-branch` est le seul appel d'ecriture, jamais
    un force-push, jamais un `git` de secours.

Un point central reste un test de NON-INERTIE : le retard ne se lit PAS dans
`mergeStateStatus` (0 `BEHIND` sur les 200 lignes ouvertes lues, mesure
2026-09-17), mais dans le `behind_by` de l'API de comparaison.
`test_clean_and_behind_is_updated_from_the_compare_api` tombe si quelqu'un
rebranche l'organe sur `mergeStateStatus` : la PR y est `CLEAN` ET en retard
de 11 commits, exactement le cas que le pool porte en masse.
"""

import hashlib
import importlib.util
import json
import re
import subprocess
import sys
import time
import urllib.parse
from pathlib import Path

HERE = Path(__file__).resolve().parent
SCRIPT = HERE.parent / "ci" / "update_stale_pr_branches.py"
spec = importlib.util.spec_from_file_location("update_stale_pr_branches", SCRIPT)
mod = importlib.util.module_from_spec(spec)
sys.modules["update_stale_pr_branches"] = mod
spec.loader.exec_module(mod)

H1 = "1" * 40
H2 = "2" * 40
#: SHA de la branche de base dans les fixtures : la base est un SHA desormais.
B1 = "a" * 40
B2 = "b" * 40
REPO = "jsboige/CoursIA"
LANE_BASE = "feature/16000-parent"
#: Retard par defaut des fixtures : la valeur mesuree sur le pool reel (#16546).
BEHIND = 11

COMPARE_RE = re.compile(r"^repos/[^/]+/[^/]+/compare/(.+)\.\.\.(.+)$")
REF_RE = re.compile(r"^repos/[^/]+/[^/]+/git/ref/heads/(.+)$")


def stable_sha(name: str) -> str:
    """SHA deterministe d'un nom de branche : la valeur par defaut de `refs`."""
    return hashlib.sha1(name.encode("utf-8")).hexdigest()


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
    """Doublure de `run_gh` : files de reponses par PR et par ref, appels records.

    `refs` mappe un nom de branche vers une FILE de SHA : une file d'UN element
    sert toutes les lectures (branche immobile) ; une file plus longue simule
    une branche qui avance ENTRE deux lectures -- c'est ainsi qu'on exerce la
    relecture des SHA epingles (review 5240194972, finding 1). Toute branche
    absente du dictionnaire fourni par le test recoit un SHA stable par defaut
    (la base) ou le `headRefOid` de la vue (la tete).

    `on_compare`, fourni, est appele AU moment de l'appel de comparaison : c'est
    la couture pour simuler une mutation PENDANT le compare.
    """

    def __init__(self, views, *, update_rc=0, update_stderr="Update failed",
                 compare_error=None, refs=None, on_compare=None):
        self.views = {k: list(v) for k, v in views.items()}
        self.update_rc = update_rc
        self.update_stderr = update_stderr
        self.compare_error = compare_error
        self.on_compare = on_compare
        self.refs = {k: list(v) for k, v in (refs or {}).items()}
        for queue in self.views.values():
            for item in queue:
                # Valeurs par defaut : la base pointe sur un SHA stable, la
                # tete sur le headRefOid de la vue -- une relecture de SHA
                # immobiles rend les memes SHA.
                self.refs.setdefault(item["baseRefName"], [stable_sha(item["baseRefName"])])
                self.refs.setdefault(item["headRefName"], [item["headRefOid"]])
        #: Le compare repond par (base_sha, head_sha) : le deficit se mesure
        #: contre le SHA EPINGLE de la base declaree, pas contre son nom.
        self.behind = {}
        for queue in self.views.values():
            for item in queue:
                self.behind[(self.refs[item["baseRefName"]][0], item["headRefOid"])] = item["_behind_by"]
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
            match = REF_RE.match(args[1])
            if match is not None:
                name = urllib.parse.unquote(match.group(1))
                queue = self.refs.get(name)
                if not queue:
                    raise AssertionError(f"ref non preparee : {name}")
                sha = queue.pop(0) if len(queue) > 1 else queue[0]
                return json.dumps(
                    {"ref": f"refs/heads/{name}", "object": {"sha": sha, "type": "commit"}}
                )
            match = COMPARE_RE.match(args[1])
            if match is None:
                raise AssertionError(f"appel api inattendu : {args}")
            if self.compare_error:
                raise mod.GhError(self.compare_error)
            if self.on_compare:
                self.on_compare(self)
            key = (urllib.parse.unquote(match.group(1)), urllib.parse.unquote(match.group(2)))
            if key not in self.behind:
                raise AssertionError(f"compare non prepare pour {key}")
            return json.dumps({"behind_by": self.behind[key]})
        raise AssertionError(f"appel gh inattendu : {args}")

    @property
    def writes(self):
        return [c for c in self.calls if c[:2] == ["pr", "update-branch"]]

    @property
    def compares(self):
        return [c for c in self.calls if c[0] == "api" and COMPARE_RE.match(c[1])]

    @property
    def ref_reads(self):
        return [c for c in self.calls if c[0] == "api" and REF_RE.match(c[1])]


def run(monkeypatch, capsys, tmp_path, views, *, prs=(1,), extra=(), update_rc=0,
        compare_error=None, refs=None, on_compare=None):
    """Execute `main` avec gh double et une sortie JSON isolee."""
    fake = FakeGh(
        views,
        update_rc=update_rc,
        compare_error=compare_error,
        refs=refs,
        on_compare=on_compare,
    )
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
    # La base declaree est RESOLUE en son SHA (review 5240194972) : le deficit
    # se mesure contre le commit que la base pointait au moment de la mesure,
    # pas contre son nom mutable.
    assert fake.compares[0][1] == f"repos/{REPO}/compare/{stable_sha(LANE_BASE)}...{H1}"


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
    assert fake.ref_reads == []
    # Une seule lecture, la premiere : la relecture TOCTOU n'a pas lieu non plus.
    assert len([c for c in fake.calls if c[:2] == ["pr", "view"]]) == 1


def test_call_budget_for_a_skipped_pr(monkeypatch, capsys, tmp_path):
    """4 appels pour une PR qui ne sera pas touchee : 2 metadonnees + 1 SHA
    de base + 1 compare.

    Le budget est borne par construction (entree explicite + plafond), mais il
    est fige ici pour qu'un elargissement silencieux se voie.
    """
    _, _, fake = run(
        monkeypatch, capsys, tmp_path, {1: [view(1, behind_by=0)]}, extra=["--apply"]
    )
    views = [c for c in fake.calls if c[:2] == ["pr", "view"]]
    assert len(views) == 2  # mesure + relecture TOCTOU
    assert len(fake.ref_reads) == 1  # epinglage du SHA de base
    assert len(fake.compares) == 1
    assert fake.compares[0][1] == f"repos/{REPO}/compare/{stable_sha('main')}...{H1}"
    assert fake.writes == []


def test_call_budget_for_an_applied_update(monkeypatch, capsys, tmp_path):
    """7 appels pour une mise a jour appliquee : 2 metadonnees + 1 epinglage
    + 1 compare + 2 relectures de SHA (base et tete) + 1 ecriture."""
    _, _, fake = run(monkeypatch, capsys, tmp_path, {1: [view(1)]}, extra=["--apply"])
    assert len([c for c in fake.calls if c[:2] == ["pr", "view"]]) == 2
    assert len(fake.ref_reads) == 3  # epinglage base + relecture base + relecture tete
    assert len(fake.compares) == 1
    assert len(fake.writes) == 1
    assert len(fake.calls) == 7


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


# --- TOCTOU par SHA : la fenetre du compare lui-meme (review 5240194972) ---


def test_compare_pins_base_and_head_shas_not_branch_names(monkeypatch, capsys, tmp_path):
    """Le compare porte sur les SHA epingles, jamais sur le nom de la base.

    Une base empilee qui avance garde le MEME nom : un compare par nom
    mesurerait un deficit calcule contre un commit different de celui que
    `gh pr update-branch` fusionnera.
    """
    _, _, fake = run(
        monkeypatch,
        capsys,
        tmp_path,
        {7: [view(7, base=LANE_BASE)]},
        prs=(7,),
        extra=["--apply"],
        refs={LANE_BASE: [B1]},
    )
    assert fake.compares[0][1] == f"repos/{REPO}/compare/{B1}...{H1}"


def test_base_moving_during_the_compare_call_is_refused(monkeypatch, capsys, tmp_path):
    """La branche de base avance PENDANT l'appel de comparaison.

    Le NOM de base n'a pas change (la passe des noms ne voit rien) mais son
    SHA oui : la decision portait sur B1, ecrire fusionnerait B2 -- REFUSE,
    et la reservation prise entre-temps est liberee.
    """
    def advance(fake):
        fake.refs["main"] = [B2]

    rc, payload, fake = run(
        monkeypatch,
        capsys,
        tmp_path,
        {1: [view(1)]},
        extra=["--apply"],
        refs={"main": [B1]},
        on_compare=advance,
    )
    result = only(payload)
    assert rc == 1
    assert result["action"] == mod.ACTION_REFUSE
    assert result["code"] == "BASE_CHANGED"
    assert fake.writes == []
    assert mod.read_ledger(mod.ledger_path(tmp_path)) == {}


def test_base_moving_after_the_compare_is_refused_before_writing(
    monkeypatch, capsys, tmp_path
):
    """La base avance dans la fenetre ENTRE le compare et l'ecriture.

    File de deux SHA pour `main` : l'epinglage lit B1, la relecture pre-ecriture
    lit B2 -- la mutation est exactement celle que la relecture doit surprendre.
    """
    rc, payload, fake = run(
        monkeypatch,
        capsys,
        tmp_path,
        {1: [view(1)]},
        extra=["--apply"],
        refs={"main": [B1, B2]},
    )
    result = only(payload)
    assert rc == 1
    assert result["action"] == mod.ACTION_REFUSE
    assert result["code"] == "BASE_CHANGED"
    assert B1 in result["reason"] and B2 in result["reason"]
    assert fake.writes == []
    assert mod.read_ledger(mod.ledger_path(tmp_path)) == {}


def test_head_moving_after_the_compare_is_refused_before_writing(
    monkeypatch, capsys, tmp_path
):
    """La tete avance apres le compare : la relecture pre-ecriture la voit.

    La vue annonce H1 ; la branche reelle pointe deja H2 au moment de la
    relecture -- un update-branch maintenant reecrirait le travail de quelqu'un
    d'autre.
    """
    rc, payload, fake = run(
        monkeypatch,
        capsys,
        tmp_path,
        {1: [view(1, head=H1)]},
        extra=["--apply"],
        refs={"feature/x": [H2]},
    )
    result = only(payload)
    assert rc == 1
    assert result["action"] == mod.ACTION_REFUSE
    assert result["code"] == "HEAD_CHANGED"
    assert fake.writes == []
    assert mod.read_ledger(mod.ledger_path(tmp_path)) == {}


def test_pinned_shas_holding_across_the_recheck_allow_the_update(
    monkeypatch, capsys, tmp_path
):
    """L'inverse des trois cas ci-dessus : SHA immobiles, l'ecriture a lieu.

    Le compare et la relecture pre-ecriture voient les MEMES SHA de base et de
    tete -- la garde ne doit declencher aucun faux REFUSE.
    """
    rc, payload, fake = run(
        monkeypatch,
        capsys,
        tmp_path,
        {1: [view(1)]},
        prs=(1,),
        extra=["--apply"],
        refs={"main": [B1], "feature/x": [H1]},
    )
    assert rc == 0
    assert only(payload)["updated"] is True
    assert len(fake.writes) == 1
    assert len(fake.ref_reads) == 3


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

    # Le registre porte la RESERVATION acquise AVANT l'appel distant : elle
    # devient l'enregistrement en vol (review 5240194972, finding 2) --
    # previous_head = la tete AVANT, pour la garde en vol.
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
    # La reservation prise avant l'appel est LIBEREE : plus rien en vol.
    assert mod.read_ledger(mod.ledger_path(tmp_path)) == {}


def test_unwritable_state_dir_refuses_rather_than_updates_blind(
    monkeypatch, capsys, tmp_path
):
    """INVERSE de l'ancien comportement (review 5240194972, finding 2).

    Anciennement : l'ecriture distante passait et l'echec de registre etait un
    warning -- une mutation distante SANS garde en vol. Desormais la
    reservation est une PREcondition : un state-dir inouvrirable refuse, il ne
    met pas a jour en aveugle.
    """
    blocker = tmp_path / "blocked"
    blocker.write_text("je suis un fichier, pas un repertoire", encoding="utf-8")
    fake = FakeGh({1: [view(1)]})
    monkeypatch.setattr(mod, "run_gh", fake)
    rc = mod.main(["--pr", "1", "--state-dir", str(blocker), "--apply"])
    result = only(json.loads(capsys.readouterr().out))
    assert rc == 1
    assert result["action"] == mod.ACTION_REFUSE
    assert result["code"] == "LEDGER_UNWRITABLE"
    assert result["updated"] is False
    assert fake.writes == []


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


def test_malformed_ledger_refuses_fail_closed(monkeypatch, capsys, tmp_path):
    """INVERSE de l'ancien comportement (review 5240194972, finding 2).

    Un registre malforme lu comme vide serait un registre improvise : la garde
    UPDATE_IN_FLIGHT se desarmerait precisement la ou deux processus pourraient
    se marcher dessus. Fail-closed : REFUSE nomme, aucune ecriture distante --
    meme pour une PR par ailleurs parfaite (OPEN, MERGEABLE, en retard).
    """
    path = mod.ledger_path(tmp_path)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("{ pas du json", encoding="utf-8")
    rc, payload, fake = run(
        monkeypatch, capsys, tmp_path, {1: [view(1)]}, extra=["--apply"]
    )
    result = only(payload)
    assert rc == 1
    assert result["action"] == mod.ACTION_REFUSE
    assert result["code"] == "LEDGER_CORRUPT"
    assert fake.writes == []


def test_ledger_that_is_not_an_object_refuses_fail_closed(
    monkeypatch, capsys, tmp_path
):
    path = mod.ledger_path(tmp_path)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text('["pas", "un", "objet"]', encoding="utf-8")
    rc, payload, fake = run(
        monkeypatch, capsys, tmp_path, {1: [view(1)]}, extra=["--apply"]
    )
    result = only(payload)
    assert rc == 1
    assert result["code"] == "LEDGER_CORRUPT"
    assert fake.writes == []


# --- schema structurel de CHAQUE enregistrement (review 5240575597, F2) -----


def _seed_raw_ledger(tmp_path, content):
    """Ecrit un registre brut : contenu arbitraire, forme exacte conservée."""
    path = mod.ledger_path(tmp_path)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(content), encoding="utf-8")
    return path


def test_scalar_record_for_our_pr_refuses_fail_closed(monkeypatch, capsys, tmp_path):
    """Reproduction 1 de la review 5240575597 : le record scalaire ecrase.

    `{"repo#1": "corrupt-record"}` passait la validation racine, echouait le
    isinstance(record, dict) de la reservation, et l'organe reservait
    PAR-DESSUS -- mutation distante autorisee sur un registre corrompu, et
    registre reecrit. Desormais : TOUT le registre refuse, avant toute
    mutation distante et avant toute reecriture.
    """
    key = mod.ledger_key(REPO, 1)
    _seed_raw_ledger(tmp_path, {key: "corrupt-record"})
    rc, payload, fake = run(monkeypatch, capsys, tmp_path, {1: [view(1)]}, extra=["--apply"])
    result = only(payload)
    assert rc == 1
    assert result["action"] == mod.ACTION_REFUSE
    assert result["code"] == "LEDGER_CORRUPT"
    assert fake.writes == []
    # Le registre corrompu est REFUSE, pas repare : octet pour octet, il
    # n'a pas ete reecrit par la tentative.
    assert json.loads(mod.ledger_path(tmp_path).read_text(encoding="utf-8")) == {
        key: "corrupt-record"
    }


def test_list_record_for_another_pr_refuses_fail_closed(monkeypatch, capsys, tmp_path):
    """Reproduction 2 de la review 5240575597 : le record liste conserve.

    `{"other#1": ["bad"]}` etait conserve sans etre regarde -- la corruption
    d'une AUTRE cle n'arretait pas la mutation. Le refus porte sur TOUT le
    registre : une entree qui echoue suffit.
    """
    _seed_raw_ledger(tmp_path, {mod.ledger_key(REPO, 99): ["bad"]})
    rc, payload, fake = run(monkeypatch, capsys, tmp_path, {1: [view(1)]}, extra=["--apply"])
    result = only(payload)
    assert rc == 1
    assert result["action"] == mod.ACTION_REFUSE
    assert result["code"] == "LEDGER_CORRUPT"
    assert fake.writes == []


def test_non_sha_previous_head_refuses_fail_closed(monkeypatch, capsys, tmp_path):
    _seed_raw_ledger(
        tmp_path,
        {mod.ledger_key(REPO, 99): {"previous_head": "pas-un-sha", "started_at": time.time()}},
    )
    rc, payload, fake = run(monkeypatch, capsys, tmp_path, {1: [view(1)]}, extra=["--apply"])
    result = only(payload)
    assert rc == 1
    assert result["code"] == "LEDGER_CORRUPT"
    assert fake.writes == []


def test_non_numeric_started_at_refuses_fail_closed(monkeypatch, capsys, tmp_path):
    """`started_at: "abc"` etait silencieusement lu comme 0 (expire jamais en
    vol) par l'ancien try/except de `record_in_flight`."""
    _seed_raw_ledger(
        tmp_path,
        {mod.ledger_key(REPO, 99): {"previous_head": H1, "started_at": "abc"}},
    )
    rc, payload, fake = run(monkeypatch, capsys, tmp_path, {1: [view(1)]}, extra=["--apply"])
    result = only(payload)
    assert rc == 1
    assert result["code"] == "LEDGER_CORRUPT"
    assert fake.writes == []


def test_missing_required_fields_refuse_fail_closed(monkeypatch, capsys, tmp_path):
    """Aucun des deux champs requis n'est optionnel : l'organe ne les ecrit
    jamais absents, donc leur absence est structurellement impossible et
    signe une ecriture externe."""
    incomplete = [
        {"previous_head": H1},  # started_at manquant
        {"started_at": time.time()},  # previous_head manquant
        {},  # les deux
    ]
    for record in incomplete:
        _seed_raw_ledger(tmp_path, {mod.ledger_key(REPO, 99): record})
        rc, payload, fake = run(
            monkeypatch, capsys, tmp_path, {1: [view(1)]}, extra=["--apply"]
        )
        result = only(payload)
        assert rc == 1, record
        assert result["code"] == "LEDGER_CORRUPT", record
        assert fake.writes == [], record


def test_boolean_started_at_refuses_fail_closed(monkeypatch, capsys, tmp_path):
    """`True` est un int en Python : sans exclusion explicite, un booleen
    passerait la validation numerique -- et `True` n'est pas un instant."""
    _seed_raw_ledger(
        tmp_path,
        {mod.ledger_key(REPO, 99): {"previous_head": H1, "started_at": True}},
    )
    rc, payload, fake = run(monkeypatch, capsys, tmp_path, {1: [view(1)]}, extra=["--apply"])
    result = only(payload)
    assert rc == 1
    assert result["code"] == "LEDGER_CORRUPT"
    assert fake.writes == []


def test_non_finite_started_at_refuses_fail_closed(monkeypatch, capsys, tmp_path):
    """NaN et Infinity : `json.loads` les accepte (extension non standard) --
    un `started_at` infini rendrait la fenetre de TTL incoherente."""
    for bad in (float("nan"), float("inf")):
        _seed_raw_ledger(
            tmp_path,
            {mod.ledger_key(REPO, 99): {"previous_head": H1, "started_at": bad}},
        )
        rc, payload, fake = run(
            monkeypatch, capsys, tmp_path, {1: [view(1)]}, extra=["--apply"]
        )
        result = only(payload)
        assert rc == 1, bad
        assert result["code"] == "LEDGER_CORRUPT", bad
        assert fake.writes == [], bad


def test_unknown_extra_field_stays_forward_compatible(monkeypatch, capsys, tmp_path):
    """La SEULE tolerance de compatibilite, justifiee et testee.

    Un champ supplementaire n'a jamais pu venir d'une version CORROMPUE de
    cet organe : il vient d'une version future. Rejeter l'inconnu casserait
    cette PR a la montee de version sans gagner une miette de surete -- les
    champs requis restent valides.
    """
    key99 = mod.ledger_key(REPO, 99)
    _seed_raw_ledger(
        tmp_path,
        {
            key99: {
                "previous_head": H2,
                "started_at": time.time() - 30,
                "future_field": "peu importe",
            }
        },
    )
    rc, payload, fake = run(monkeypatch, capsys, tmp_path, {1: [view(1)]}, extra=["--apply"])
    result = only(payload)
    assert rc == 0
    assert result["updated"] is True
    assert len(fake.writes) == 1
    # L'enregistrement futur survit INTACT a la reservation mergee.
    ledger = mod.read_ledger(mod.ledger_path(tmp_path))
    assert ledger[key99]["future_field"] == "peu importe"


def test_sha256_previous_head_stays_compatible(monkeypatch, capsys, tmp_path):
    """SHA-256 (hex 64) : GitHub peut rendre une ref migree en SHA-256 --
    l'exclure ferait refuser a l'organe son propre registre sur un tel depot."""
    _seed_raw_ledger(
        tmp_path,
        {mod.ledger_key(REPO, 99): {"previous_head": "c" * 64, "started_at": time.time()}},
    )
    rc, payload, fake = run(monkeypatch, capsys, tmp_path, {1: [view(1)]}, extra=["--apply"])
    result = only(payload)
    assert rc == 0
    assert result["updated"] is True


def test_absent_ledger_is_a_legitimate_empty_registry(monkeypatch, capsys, tmp_path):
    """Le complement des deux cas ci-dessus : ABSENT n'est pas CORROMPU.

    Un registre absent est la situation de premier appel -- le refuser
    boucherait l'organe a jamais. Seul un registre PRESENT et illisible refuse.
    """
    rc, payload, fake = run(
        monkeypatch, capsys, tmp_path, {1: [view(1)]}, extra=["--apply"]
    )
    assert rc == 0
    assert only(payload)["updated"] is True
    assert len(fake.writes) == 1


def test_failed_update_releases_the_reservation_without_losing_other_records(
    monkeypatch, capsys, tmp_path
):
    """Echec distant : NOTRE reservation est liberee, les autres survivent.

    Le release est un read-merge-write sous verrou : l'enregistrement d'une
    autre PR -- y compris ecrit par un concurrent -- ne doit pas disparaitre
    avec le notre (review 5240194972, finding 2).
    """
    other = mod.ledger_key(REPO, 99)
    path = mod.ledger_path(tmp_path)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps({other: {"previous_head": "9" * 40, "started_at": time.time()}}),
        encoding="utf-8",
    )
    rc, payload, fake = run(
        monkeypatch,
        capsys,
        tmp_path,
        {1: [view(1)]},
        extra=["--apply"],
        update_rc=1,
    )
    assert only(payload)["code"] == "UPDATE_FAILED"
    ledger = mod.read_ledger(path)
    assert mod.ledger_key(REPO, 1) not in ledger
    assert other in ledger


def test_ledger_writes_leave_no_temporary_files(monkeypatch, capsys, tmp_path):
    """Le temporaire d'ecriture est UNIQUE et consomme par le replace.

    Le tmp a nom fixe d'une version anterieure (`in-flight.json.tmp`) etait une
    collision entre ecrivains ; `mkstemp` le rend unique. Succes comme echec,
    le state-dir ne garde que le registre et son verrou.
    """
    for subdir, update_rc in (("ok", 0), ("ko", 1)):
        state_dir = tmp_path / subdir
        fake = FakeGh({1: [view(1)]}, update_rc=update_rc)
        monkeypatch.setattr(mod, "run_gh", fake)
        mod.main(["--pr", "1", "--state-dir", str(state_dir), "--apply"])
        capsys.readouterr()
        names = sorted(p.name for p in state_dir.iterdir())
        assert names == ["in-flight.json", "in-flight.json.lock"], (subdir, names)


# --- contention REELLE inter-processus (review 5240194972, finding 2) -------

#: Script execute par de VRAIS sous-processus Python : chacun charge le module
#: par chemin, attend une barriere de depart commune (le fichier `gate`), puis
#: contende la reservation. Aucun mock : le verrou inter-processus est exercé
#: pour de vrai, entre processus distincts.
CONCURRENT_WORKER = """
import importlib.util
import sys
import time
from pathlib import Path

script, state_dir, key, head, gate = sys.argv[1:6]
spec = importlib.util.spec_from_file_location("update_stale_pr_branches", script)
mod = importlib.util.module_from_spec(spec)
# Meme enregistrement pre-exec que le fichier de test : le dataclass du module
# resout ses annotations via sys.modules[cls.__module__].
sys.modules["update_stale_pr_branches"] = mod
spec.loader.exec_module(mod)
while not Path(gate).exists():
    time.sleep(0.005)
now = time.time()
reserved, _ledger = mod.try_reserve_update(
    mod.ledger_path(Path(state_dir)),
    key,
    reservation={"previous_head": head, "started_at": now},
    now=now,
    ttl=900,
)
print("ACQUIRED" if reserved else "BLOCKED")
"""


def _spawn_contenders(tmp_path, count, *, same_key=True):
    """Lance `count` sous-processus qui contendent la reservation, derriere
    une barriere commune. Rend la liste de leurs verdicts stdout."""
    state_dir = tmp_path / "concurrent"
    state_dir.mkdir(parents=True, exist_ok=True)
    gate = tmp_path / "gate"
    specs = []
    for i in range(count):
        key = mod.ledger_key(REPO, 77) if same_key else mod.ledger_key(REPO, 77 + i)
        head = H1 if same_key else (H1 if i == 0 else H2)
        specs.append((key, head))
    procs = [
        subprocess.Popen(
            [
                sys.executable,
                "-c",
                CONCURRENT_WORKER,
                str(SCRIPT),
                str(state_dir),
                key,
                head,
                str(gate),
            ],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            encoding="utf-8",
        )
        for key, head in specs
    ]
    # Laisser tous les interpretes arriver a la barriere, puis l'ouvrir :
    # les reservations partent en salve, la contention est reelle.
    time.sleep(1.0)
    gate.write_text("go", encoding="utf-8")
    outcomes = []
    for proc in procs:
        out, err = proc.communicate(timeout=120)
        assert proc.returncode == 0, f"contender crashed : {err}"
        outcomes.append(out.strip())
    return state_dir, outcomes


def test_concurrent_processes_contend_and_exactly_one_reserves(tmp_path):
    """Quatre vrais processus, une seule reservation possible.

    Sans verrou inter-processus, chaque contender lirait « registre vide » et
    reserverait : plusieurs ACQUIRED. Avec le verrou, le read-merge-write se
    serialize et exactement UN contender gagne -- les autres lisent SA
    reservation sous le meme verrou et sortent BLOCKED.
    """
    state_dir, outcomes = _spawn_contenders(tmp_path, 4, same_key=True)
    assert outcomes.count("ACQUIRED") == 1
    assert outcomes.count("BLOCKED") == 3
    ledger = mod.read_ledger(mod.ledger_path(state_dir))
    assert ledger[mod.ledger_key(REPO, 77)]["previous_head"] == H1


def test_concurrent_processes_on_different_prs_both_reserve_and_merge(tmp_path):
    """Deux processus, deux PR differentes : les DEUX reservent, sans perte.

    C'est la preuve du MERGE sous verrou : sans relecture+fusion, le second
    ecrivain ecraserait le registre du premier et une cle disparaitrait.
    """
    state_dir, outcomes = _spawn_contenders(tmp_path, 2, same_key=False)
    assert outcomes.count("ACQUIRED") == 2
    ledger = mod.read_ledger(mod.ledger_path(state_dir))
    assert ledger[mod.ledger_key(REPO, 77)]["previous_head"] == H1
    assert ledger[mod.ledger_key(REPO, 78)]["previous_head"] == H2


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


def test_mergeable_true_with_merge_state_unknown_is_refused_fail_closed(
    monkeypatch, capsys, tmp_path
):
    """Test CAUSAL du finding 3 (review 5240194972).

    La fixture ne differe d'un cas qui PASSE que par `mergeStateStatus` :
    `mergeable=MERGEABLE` ne suffit pas, un etat de fusion UNKNOWN signifie
    que GitHub n'a pas fini de calculer. La cause (mergeStateStatus) produit
    seule l'effet (aucune mise a jour), et le verdict tombe dans les gardes de
    metadonnees : aucun epinglage, aucun compare, aucune ecriture.
    """
    rc, payload, fake = run(
        monkeypatch,
        capsys,
        tmp_path,
        {1: [view(1, mergeable="MERGEABLE", status="UNKNOWN")]},
        extra=["--apply"],
    )
    result = only(payload)
    assert rc == 0
    assert result["action"] == mod.ACTION_SKIP
    assert result["code"] == "MERGE_STATE_UNKNOWN"
    assert result["mergeable"] == "MERGEABLE"
    assert fake.ref_reads == []
    assert fake.compares == []
    assert fake.writes == []


# --- encodage des segments de chemin d'API (review 5240194972) --------------


def test_compare_path_segments_are_url_encoded(monkeypatch):
    """Refs contenant `#` et Unicode : chaque segment du compare est encode.

    Un `#` cru dans un chemin d'API devient un fragment d'URL : l'endpoint
    reel change silencieusement et le deficit devient `BEHIND_UNKNOWN` sans
    qu'aucune erreur ne le dise.
    """
    seen = []

    def fake(args):
        seen.append(args[1])
        return json.dumps({"behind_by": 3})

    monkeypatch.setattr(mod, "run_gh", fake)
    assert mod.read_behind(REPO, "feat/ü#1", "tête-é#2") == 3
    assert seen == [f"repos/{REPO}/compare/feat%2F%C3%BC%231...t%C3%AAte-%C3%A9%232"]


def test_branch_sha_reads_are_url_encoded(monkeypatch):
    seen = []

    def fake(args):
        seen.append(args[1])
        return json.dumps({"object": {"sha": H1}})

    monkeypatch.setattr(mod, "run_gh", fake)
    assert mod.read_branch_sha(REPO, "feature/ü#x") == H1
    assert seen == [f"repos/{REPO}/git/ref/heads/feature%2F%C3%BC%23x"]


def test_exotic_base_refs_flow_through_encoded_paths(monkeypatch, capsys, tmp_path):
    """Une base contenant `#` et Unicode traverse le flux ENTIER encodee.

    La doublure redecode chaque segment : si l'organe envoyait le `#` cru,
    l'endpoint ref ou compare ne matcherait plus et le test rougirait --
    l'assertion sur l'absence de `#` cru est le filet complementaire.
    """
    exotic = "feature/ü#2"
    rc, payload, fake = run(
        monkeypatch,
        capsys,
        tmp_path,
        {9: [view(9, base=exotic)]},
        prs=(9,),
        extra=["--apply"],
    )
    assert rc == 0
    assert only(payload)["updated"] is True
    for call in fake.calls:
        if call[0] == "api":
            assert "#" not in call[1]
    assert fake.compares[0][1] == (
        f"repos/{REPO}/compare/{stable_sha(exotic)}...{H1}"
    )


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
    # `_behind_by` est un champ de fixture ; `base_sha`/`head_sha`/`behind_error`
    # sont des champs internes d'epinglage -- le resultat ne les porte pas.
    _, payload, _ = run(
        monkeypatch, capsys, tmp_path, {1: [view(1)]}, extra=["--apply"]
    )
    assert "_behind_by" not in payload["results"][0]
    assert "behind_error" not in payload["results"][0]
    assert "base_sha" not in payload["results"][0]
    assert "head_sha" not in payload["results"][0]


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
