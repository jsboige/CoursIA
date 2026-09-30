#!/usr/bin/env python3
"""Tests du pilote de sweep (`scripts/ci/sweep_stale_pr_branches.py`, #16915).

Aucun appel reseau : `gh` est double a la couture unique `run_gh` du module
organe (le pilote delegue tout a `process_one`, qui lit ses etats par la).
La doublure repond AUSSI a `gh pr list` -- la seule commande que le pilote
possede en propre.

Ce que ces tests epinglent, par ordre de degat s'ils cassent :

1. **Le pilote ne reimplemente rien.** Une seule enumeration, puis un
   `process_one` par candidate : jamais de `pr update-branch` qui ne passe
   pas par l'organe (gardes, epinglage TOCTOU, registre en vol, plafond).
2. **La non-inertie heritee.** Une PR `CLEAN` et en retard EST candidate :
   le retard ne se lit pas dans `mergeStateStatus` (mesure 2026-09-17 du
   module) et le pilote ne doit pas reintroduire ce faux filtre.
3. **LE piege #16915 : la peremption rendue.** Un update reecrit la tete et
   perime checks, reviews et dossier `[ADJOINT PREFLIGHT]`. Le payload porte
   `dossiers_invalides` EN TETE -- un sweep qui detruit du premachage en
   silence perd plus qu'il ne gagne.
4. **Le plancher DWELL ne se re-arme pas sur le geste du sweep.** Acceptance
   5 de #16915 : la fusion `update-branch` serveur est content-free, donc
   `last_authoritative_committed_at` (merge_dwell.py, #16149) mesure la date
   AUTEUR -- le test relie les deux modules sur exactement ce geste.

Run: python -m pytest scripts/tests/test_sweep_stale_pr_branches.py
"""
import hashlib
import importlib.util
import json
import re
import sys
import urllib.parse
from pathlib import Path

HERE = Path(__file__).resolve().parent
SCRIPT = HERE.parent / "ci" / "sweep_stale_pr_branches.py"
spec = importlib.util.spec_from_file_location("sweep_stale_pr_branches", SCRIPT)
sweep_mod = importlib.util.module_from_spec(spec)
sys.modules["sweep_stale_pr_branches"] = sweep_mod
spec.loader.exec_module(sweep_mod)

#: Le module organe charge PAR le pilote ( meme objet que
#: sys.modules["update_stale_pr_branches"] ) : la couture `run_gh` y vit.
organe = sweep_mod.organe

sys.path.insert(0, str(HERE.parent))
from ci import merge_dwell  # noqa: E402

REPO = "jsboige/CoursIA"
H1 = "1" * 40
BEHIND = 11

COMPARE_RE = re.compile(r"^repos/[^/]+/[^/]+/compare/(.+)\.\.\.(.+)$")
REF_RE = re.compile(r"^repos/[^/]+/[^/]+/git/ref/heads/(.+)$")


def stable_sha(name: str) -> str:
    return hashlib.sha1(name.encode("utf-8")).hexdigest()


def row(number, *, draft=False, fork=False, updated_at="2026-09-01T00:00:00Z"):
    """Une ligne `gh pr list` : uniquement les champs gratuits."""
    return {
        "number": number,
        "isDraft": draft,
        "isCrossRepository": fork,
        "updatedAt": updated_at,
        "url": f"https://github.com/{REPO}/pull/{number}",
    }


def view(number, *, state="OPEN", base="main", head=None, mergeable="MERGEABLE",
         status="CLEAN", draft=False, fork=False, head_ref="feature/x",
         behind_by=BEHIND):
    #: Tete DISTINCTE par numero : la cle du compare (base_sha, head) doit
    #: isoler chaque PR, sinon les fixtures s'ecrasent entre elles.
    if head is None:
        head = str(number) * 20
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
    """Doublure de `run_gh` pour le pilote : `pr list` rend la photo, le
    reste sert `process_one` (view / ref / compare / update-branch), sur le
    modele de la doublure du test de l'organe."""

    def __init__(self, listing, views):
        self.listing = listing
        self.views = {k: list(v) for k, v in views.items()}
        self.refs = {}
        for queue in self.views.values():
            for item in queue:
                self.refs.setdefault(item["baseRefName"], [stable_sha(item["baseRefName"])])
                self.refs.setdefault(item["headRefName"], [item["headRefOid"]])
        self.behind = {}
        for queue in self.views.values():
            for item in queue:
                self.behind[
                    (self.refs[item["baseRefName"]][0], item["headRefOid"])
                ] = item["_behind_by"]
        self.calls = []

    def __call__(self, args):
        args = list(args)
        self.calls.append(args)
        if args[:2] == ["pr", "list"]:
            return json.dumps(self.listing)
        if args[:2] == ["pr", "view"]:
            pr = int(args[2])
            queue = self.views.get(pr)
            if not queue:
                raise organe.GhError(f"gh: no pull requests found for #{pr}")
            return json.dumps(queue.pop(0) if len(queue) > 1 else queue[0])
        if args[:2] == ["pr", "update-branch"]:
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
                    {"ref": f"refs/heads/{name}", "object": {"sha": sha}}
                )
            match = COMPARE_RE.match(args[1])
            if match is None:
                raise AssertionError(f"appel api inattendu : {args}")
            key = (
                urllib.parse.unquote(match.group(1)),
                urllib.parse.unquote(match.group(2)),
            )
            if key not in self.behind:
                raise AssertionError(f"compare non prepare pour {key}")
            return json.dumps({"behind_by": self.behind[key]})
        raise AssertionError(f"appel gh inattendu : {args}")

    @property
    def writes(self):
        return [c for c in self.calls if c[:2] == ["pr", "update-branch"]]

    @property
    def view_order(self):
        return [c[2] for c in self.calls if c[:2] == ["pr", "view"]]


def run_main(monkeypatch, capsys, tmp_path, listing, views, argv=(), prevalidation=None):
    fake = FakeGh(listing, views)
    monkeypatch.setattr(organe, "run_gh", fake)
    #: Prevalidation hermetique par defaut : rc=1 (EXIT_NO_DOSSIER) -- aucune
    #: branche n'est gelee, tout part a l'organe, comme avant le filtre.
    monkeypatch.setattr(
        sweep_mod,
        "default_run_prevalidation",
        prevalidation or (lambda pr: 1),
    )
    rc = sweep_mod.main(
        ["--state-dir", str(tmp_path / "st")] + list(argv)
    )
    out = json.loads(capsys.readouterr().out)
    return rc, out, fake


# --- 1. le pilote ne reimplemente rien --------------------------------------

def test_enumere_une_seule_fois_puis_delegue(monkeypatch, capsys, tmp_path):
    listing = [row(11), row(14)]
    rc, out, fake = run_main(
        monkeypatch, capsys, tmp_path, listing, {11: [view(11)], 14: [view(14)]}
    )
    lists = [c for c in fake.calls if c[:2] == ["pr", "list"]]
    assert len(lists) == 1
    assert lists[0][lists[0].index("--limit") + 1] == "50"
    assert set(lists[0][lists[0].index("--json") + 1].split(",")) == set(
        sweep_mod.LIST_FIELDS
    )
    # Deux views par candidate (mesure + relecture TOCTOU epinglee) : le
    # pilote ne court-circuite PAS la double lecture de l'organe.
    assert fake.view_order == ["11", "11", "14", "14"]
    assert fake.writes == []
    assert rc == 0


def test_drafts_et_forks_ecartes_sans_aucune_lecture(monkeypatch, capsys, tmp_path):
    """Filtre de COUT seulement : drafts et forks ne meritent meme pas un
    `pr view` -- l'organe les refuserait de toute facon (DRAFT / FORK)."""
    listing = [row(11), row(12, draft=True), row(13, fork=True)]
    rc, out, fake = run_main(
        monkeypatch, capsys, tmp_path, listing, {11: [view(11)]}
    )
    assert fake.view_order == ["11", "11"]
    assert [r["pr"] for r in out["results"]] == [11]
    assert out["scanned"] == 3
    assert out["candidates"] == 1


def test_clean_en_retard_est_candidate(monkeypatch, capsys, tmp_path):
    """Non-inertie heritee : `CLEAN` ne dit rien du retard (0 BEHIND lus sur
    le pool reel). Une PR CLEAN et en retard de 11 DOIT partir a l'organe --
    le cas que le pool porte en masse."""
    rc, out, fake = run_main(
        monkeypatch, capsys, tmp_path, [row(11)], {11: [view(11, behind_by=11)]}
    )
    assert [r["pr"] for r in out["results"]] == [11]
    # Dry-run : l'organe mesure le deficit et refuse d'ecrire, mais la PR a
    # bien ete consideree (result present, pas filtree).
    assert out["results"][0]["behind_by"] == 11


# --- gel des branches sous dossier READY (reserve 5788054957, #16924) -------


def test_ready_dossier_exclu_avant_process_one(monkeypatch, capsys, tmp_path):
    """Controle positif : rc=0 (dossier READY a la tete exacte) => la PR ne
    part JAMAIS a l'organe (pas meme un `pr view`) et figure sous
    `skipped_ready_dossier`. Un update-branch tuerait le dossier a la
    seconde -- le gel dossier->merge (git-workflow.md) l'exige."""
    listing = [row(11), row(12)]
    rc, out, fake = run_main(
        monkeypatch, capsys, tmp_path, listing, {12: [view(12)]},
        prevalidation=lambda pr: 0 if pr == 11 else 1,
    )
    assert fake.view_order == ["12", "12"]
    assert out["skipped_ready_dossier"] == [
        {"pr": 11, "reason": "ready_dossier_at_exact_head"}
    ]
    assert out["candidates"] == 2
    assert [r["pr"] for r in out["results"]] == [12]


def test_blocked_ou_sans_dossier_restent_candidates(monkeypatch, capsys, tmp_path):
    """Controle negatif : rc=1 (EXIT_NO_DOSSIER), rc=2 (EXIT_UNKNOWN) et
    rc=3 (EXIT_BLOCKED_WITH_SUBSTANCE) ne protegent PAS la branche. Le cas
    BLOCKED est justement celui que l'organe #16149 repare (rouge de base
    perimee) -- l'exclure reviendrait a ne plus jamais rafraichir les PRs
    qui en ont le plus besoin."""
    listing = [row(11), row(12), row(13)]
    rc, out, fake = run_main(
        monkeypatch, capsys, tmp_path, listing,
        {11: [view(11)], 12: [view(12)], 13: [view(13)]},
        prevalidation=lambda pr: {11: 1, 12: 2, 13: 3}[pr],
    )
    assert out["skipped_ready_dossier"] == []
    assert fake.view_order == ["11", "11", "12", "12", "13", "13"]
    assert [r["pr"] for r in out["results"]] == [11, 12, 13]


def test_ordre_oldest_d_abord(monkeypatch, capsys, tmp_path):
    listing = [
        row(16, updated_at="2026-09-10T00:00:00Z"),
        row(15, updated_at="2026-09-05T00:00:00Z"),
        row(17, updated_at="2026-09-12T00:00:00Z"),
    ]
    rc, out, fake = run_main(
        monkeypatch, capsys, tmp_path, listing,
        {15: [view(15)], 16: [view(16)], 17: [view(17)]},
    )
    assert fake.view_order == ["15", "15", "16", "16", "17", "17"]


def test_apply_passe_par_lorgane_seulement(monkeypatch, capsys, tmp_path):
    listing = [row(11), row(14)]
    rc, out, fake = run_main(
        monkeypatch, capsys, tmp_path, listing,
        {11: [view(11)], 14: [view(14, mergeable="CONFLICTING")]},
        argv=["--apply"],
    )
    # Une seule ecriture, pour la PR sans conflit ; l'organe a refuse l'autre.
    assert fake.writes == [["pr", "update-branch", "11", "--repo", REPO]]
    assert [r["action"] for r in out["results"]] == ["UPDATE", "REFUSE"]
    assert rc == 1  # parite organe : un REFUSE rend 1


def test_max_updates_propage_le_plafond(monkeypatch, capsys, tmp_path):
    listing = [row(11), row(15)]
    rc, out, fake = run_main(
        monkeypatch, capsys, tmp_path, listing,
        {11: [view(11)], 15: [view(15)]},
        argv=["--apply", "--max-updates", "1"],
    )
    assert fake.writes == [["pr", "update-branch", "11", "--repo", REPO]]
    codes = {r["pr"]: r["code"] for r in out["results"]}
    assert codes[15] == "CAP_REACHED"
    assert out["updates_applied"] == 1


# --- 3. LE piege : la peremption rendue -------------------------------------

def test_dossiers_invalides_en_tete_du_payload(monkeypatch, capsys, tmp_path):
    """> `dossiers_invalides` AVANT `results` dans le JSON : c'est la
    premiere chose que l'adjoint cherche apres un sweep -- un update a
    perime checks, reviews ET dossier."""
    listing = [row(11), row(15)]
    rc, out, fake = run_main(
        monkeypatch, capsys, tmp_path, listing,
        {11: [view(11)], 15: [view(15)]},
        argv=["--apply"],
    )
    assert out["dossiers_invalides"] == [
        {
            "pr": 11,
            "previous_head": H1,
            "invalidated": ["checks", "reviews", "dossier"],
        }
    ]
    keys = list(out)
    assert keys.index("dossiers_invalides") < keys.index("results")


def test_dry_run_ne_perime_rien(monkeypatch, capsys, tmp_path):
    """Dry-run par defaut : aucune ecriture, donc AUCUNE peremption -- le
    champ reste present et vide, pas absent (une absence se lirait « je n'ai
    pas regarde »)."""
    rc, out, fake = run_main(
        monkeypatch, capsys, tmp_path, [row(11)], {11: [view(11)]}
    )
    assert out["mode"] == "dry-run"
    assert out["dossiers_invalides"] == []
    assert fake.writes == []


def test_resume_par_action_et_code(monkeypatch, capsys, tmp_path):
    listing = [row(11), row(14)]
    rc, out, fake = run_main(
        monkeypatch, capsys, tmp_path, listing,
        {11: [view(11, behind_by=0)], 14: [view(14, mergeable="CONFLICTING")]},
    )
    assert out["summary"]["by_code"] == {"UP_TO_DATE": 1, "CONFLICTING": 1}
    assert out["summary"]["by_action"] == {"SKIP": 1, "REFUSE": 1}


# --- 4. acceptance 5 : le geste du sweep ne re-arme pas le plancher ---------

def _commit(sha, date, parents, tree=None):
    payload = {
        "commit": {"committer": {"date": date}},
        "parents": [{"sha": p} for p in parents],
    }
    if tree is not None:
        payload["commit"]["tree"] = {"sha": tree}
    return payload


def _git_proving(auto_tree):
    def run_git(args):
        if args[:2] == ["cat-file", "-e"]:
            return 0, ""
        if args[0] == "fetch":
            return 0, ""
        if args[0] == "merge-base":
            return 0, "b0"
        if args[:2] == ["merge-tree", "--write-tree"]:
            return 0, auto_tree + "\n"
        raise AssertionError("git inattendu: " + " ".join(args))

    return run_git


def test_update_ne_re_arme_pas_le_dwell(monkeypatch, capsys, tmp_path):
    """Acceptance 5 de #16915. Le sweep vient de mettre a jour la #11 : la
    nouvelle tete est le commit de FUSION serveur (parents [auteur, base],
    arbre = auto-merge prouve). `last_authoritative_committed_at` doit
    remonter cette fusion et mesurer la date de l'AUTEUR -- sinon chaque
    sweep re-armerait le plancher DWELL de toutes les PRs rafraichies et le
    cron serait un deni de service temporel contre sa propre file."""
    # 1. Le sweep fait son geste (fusion serveur, content-free).
    rc, out, fake = run_main(
        monkeypatch, capsys, tmp_path, [row(11)], {11: [view(11)]},
        argv=["--apply"],
    )
    assert out["updates_applied"] == 1
    assert out["dossiers_invalides"][0]["pr"] == 11

    # 2. La tete resultante : fusion 11:59, auteur ancien 07:00, tree 7ee0.
    base_sha = stable_sha("main")
    fusion, auteur = "f" * 40, "a" * 40

    def fetch(path):
        if path == f"repos/{REPO}/commits/{fusion}":
            return _commit(fusion, "2026-09-19T11:59:00Z", [auteur, base_sha], tree="7ee0")
        if path == f"repos/{REPO}/commits/{auteur}":
            return _commit(auteur, "2026-09-19T07:00:00Z", ["r" * 40])
        raise AssertionError("chemin inattendu: " + path)

    # 3. Le plancher mesure l'AUTEUR : la fusion content-free est exemptee.
    measured = merge_dwell.last_authoritative_committed_at(
        REPO, fusion, base_sha, fetch=fetch, run_git=_git_proving("7ee0")
    )
    assert measured.strftime("%H:%M") == "07:00", (
        "un update-branch serveur du sweep doit etre mesure a la date de "
        "l'AUTEUR -- sinon le cron re-arme le plancher DWELL de chaque PR "
        "qu'il rafraichit"
    )


def test_update_avec_resolution_d_auteur_re_arme_le_dwell(monkeypatch, capsys, tmp_path):
    """Contre-pied fail-closed : si la fusion porte une resolution
    SUBSTANTIVE (arbre != auto-merge), elle re-arme le plancher. Le sweep ne
    cree jamais ce cas (update-branch serveur = content-free), mais ce test
    epinglle la frontiere : l'exemption est une PREUVE d'equivalence, pas une
    deference au geste du sweep."""
    base_sha = stable_sha("main")
    fusion, auteur = "f" * 40, "a" * 40

    def fetch(path):
        if path == f"repos/{REPO}/commits/{fusion}":
            return _commit(fusion, "2026-09-19T11:59:00Z", [auteur, base_sha], tree="res0")
        if path == f"repos/{REPO}/commits/{auteur}":
            return _commit(auteur, "2026-09-19T07:00:00Z", ["r" * 40])
        raise AssertionError("chemin inattendu: " + path)

    measured = merge_dwell.last_authoritative_committed_at(
        REPO, fusion, base_sha, fetch=fetch, run_git=_git_proving("a010")
    )
    assert measured.strftime("%H:%M") == "11:59"


# --- arguments ---------------------------------------------------------------

def test_limit_et_ordre_invalides_refuses(monkeypatch, capsys, tmp_path):
    import pytest

    with pytest.raises(SystemExit):
        sweep_mod.parse_args(["--limit", "0"])
    with pytest.raises(SystemExit):
        sweep_mod.parse_args(["--order", "nimporte"])
    with pytest.raises(SystemExit):
        sweep_mod.parse_args(["--max-updates", "-1"])
