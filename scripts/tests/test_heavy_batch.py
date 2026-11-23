"""Tests du lot quotidien en ombre (P3 du plan #25510).

Le lot est **advisory** : il mesure, il ne bloque rien. Les proprietes sous
test sont donc deux :

1. **La selection ne laisse pas passer ce qui doit etre exclu.** Une PR de
   fork sans l'APPROVE du coordinateur, ou une PR que le coordinateur n'a
   pas approuvee **a sa tete exacte**, ne doit pas occuper un creneau de
   runner -- et l'exclusion doit etre **nommee**, pas silencieuse.
2. **La mesure est exacte.** L'echeance du creneau est le critere qui
   decide si la cadence tient ; un calcul faux de la duree rendrait la
   cadence indécidable.
3. **Ce que le lot mesure est bien la suite qu'on veut deplacer.** Les
   cibles de la suite sont LUES dans la jambe `Scripts Tests` (pas
   recopiees), et l'environnement est installe par le script partage que
   les deux jambes appellent.
"""

from __future__ import annotations

import json
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

import pytest

CI_DIR = Path(__file__).resolve().parents[1] / "ci"
sys.path.insert(0, str(CI_DIR))

import heavy_batch  # noqa: E402

REPO_ROOT = Path(__file__).resolve().parents[2]


def _entry(number: int, **kwargs) -> dict:
    base = {
        "number": number,
        "title": f"PR {number}",
        "created_at": f"2026-11-0{number}T00:00:00Z",
        "head_sha": f"sha-{number}",
        "fork": False,
        "approved_by_coordinator": True,
        "verdict": "LGTM",
        "merge_state_status": "CLEAN",
    }
    base.update(kwargs)
    return base


# --- Creneaux --------------------------------------------------------------


def test_le_creneau_actif_est_celui_du_debut_du_creneau() -> None:
    now = datetime(2026, 11, 9, 4, 30, tzinfo=timezone.utc)
    slot = heavy_batch.active_slot(now)
    assert slot is not None
    assert slot.name == "creneau-1"


def test_le_creneau_actif_change_a_l_ouverture_du_suivant() -> None:
    now = datetime(2026, 11, 9, 10, 30, tzinfo=timezone.utc)
    slot = heavy_batch.active_slot(now)
    assert slot is not None
    assert slot.name == "creneau-2"


def test_les_creneaux_pavent_la_journee_entiere() -> None:
    # un creneau est toujours actif : les quatre fenetres se recouvrent sans
    # laisser de trou, donc la question "hors creneau" ne se pose pas.
    for hour in range(24):
        now = datetime(2026, 11, 9, hour, 0, tzinfo=timezone.utc)
        assert heavy_batch.active_slot(now) is not None


def test_le_dernier_creneau_couvre_la_nuit() -> None:
    slot = heavy_batch.active_slot(datetime(2026, 11, 9, 23, 0, tzinfo=timezone.utc))
    assert slot is not None
    assert slot.name == "creneau-4"
    slot = heavy_batch.active_slot(datetime(2026, 11, 9, 2, 0, tzinfo=timezone.utc))
    assert slot is not None
    assert slot.name == "creneau-4"


def test_les_quatre_creneaux_ont_une_echeance_qui_suit_leur_debut() -> None:
    for slot in heavy_batch.SLOTS:
        assert slot.deadline_minutes > slot.start_minutes
    # le dernier creneau se termine le lendemain a 00:00
    assert heavy_batch.SLOTS[-1].deadline_minutes == 24 * 60


# --- Selection -------------------------------------------------------------


def test_une_pr_de_fork_sans_approve_du_coordinateur_est_exclue() -> None:
    entries = [_entry(1, fork=True, approved_by_coordinator=False)]
    selected, excluded = heavy_batch.select_batch(entries, 4)
    assert selected == []
    assert "APPROVE" in excluded[0]["motif"]


def test_une_pr_de_fork_avec_approve_du_coordinateur_passe() -> None:
    entries = [_entry(1, fork=True, approved_by_coordinator=True)]
    selected, _excluded = heavy_batch.select_batch(entries, 4)
    assert [e["number"] for e in selected] == [1]


def test_une_pr_sans_approve_du_coordinateur_est_exclue() -> None:
    # La porte est l'APPROVE du coordinateur a la tete exacte. Un `LGTM`
    # dans le corps d'une review Hermes n'est PAS une approbation : c'est un
    # avis. Le motif d'exclusion nomme la porte ET le verdict de revue.
    entries = [_entry(1, verdict="LGTM", approved_by_coordinator=False)]
    selected, excluded = heavy_batch.select_batch(entries, 4)
    assert selected == []
    assert "APPROVE" in excluded[0]["motif"]
    assert "LGTM" in excluded[0]["motif"]


def test_une_pr_sans_voix_est_exclue() -> None:
    entries = [_entry(1, verdict="SANS-REVIEW", approved_by_coordinator=False)]
    selected, excluded = heavy_batch.select_batch(entries, 4)
    assert selected == []
    assert "SANS-REVIEW" in excluded[0]["motif"]


def test_le_verdict_de_revue_ne_selectionne_plus_a_lui_seul() -> None:
    # La porte du lot est celle du merge. Une PR que le coordinateur a
    # approuvee entre dans le lot meme si un corps porte encore un verdict
    # d'avis ; c'est l'inverse -- une PR avec un `LGTM` et sans APPROVE --
    # qui sort.
    entries = [_entry(1, verdict="CONCERNS", approved_by_coordinator=True)]
    selected, _excluded = heavy_batch.select_batch(entries, 4)
    assert [e["number"] for e in selected] == [1]


def test_les_prs_plus_anciennes_passent_en_tete() -> None:
    entries = [
        _entry(3, created_at="2026-11-03T00:00:00Z"),
        _entry(1, created_at="2026-11-01T00:00:00Z"),
        _entry(2, created_at="2026-11-02T00:00:00Z"),
    ]
    selected, _excluded = heavy_batch.select_batch(entries, 4)
    assert [e["number"] for e in selected] == [1, 2, 3]


def test_la_taille_du_lot_est_bornee() -> None:
    entries = [_entry(n, created_at=f"2026-11-0{n}T00:00:00Z") for n in range(1, 8)]
    selected, excluded = heavy_batch.select_batch(entries, 2)
    assert len(selected) == 2
    assert len(excluded) == 5
    assert "lot plein" in excluded[0]["motif"]


def test_le_lot_ne_plafonne_pas_par_defaut() -> None:
    """Pas de plafond par defaut : c'est la porte qui decide du lot.

    Un plafond applique APRES la porte ne fait que retrancher des PRs que
    le merge mergera (mesure du 2026-11-09 : 15 PRs inspectees, 1
    selectionnee sous un plafond de 4).
    """
    entries = [_entry(n, created_at=f"2026-11-{n:02d}T00:00:00Z") for n in range(1, 8)]
    selected, excluded = heavy_batch.select_batch(entries, 0)
    assert len(selected) == 7
    assert excluded == []


def test_la_liste_des_candidates_est_cellule_des_prs_relues_par_le_coordinateur(
    monkeypatch,
) -> None:
    """La population du lot est celle que le MERGE touche.

    C'est la liste des PRs ouvertes que le coordinateur a relues : le lot
    mesure la duree d'un lot reel, donc il ne mesure que des PRs qui
    passent par la revue du coordinateur.
    """
    capture: dict[str, list[str]] = {}

    def fake_run_gh(argv, *args, **kwargs):
        capture["argv"] = list(argv)
        return "[]"

    monkeypatch.setattr(heavy_batch.pool, "run_gh", fake_run_gh)
    heavy_batch.fetch_entries("jsboige/CoursIA", 100)
    argv = capture["argv"]
    assert "reviewed-by:myia-ai-01" in " ".join(argv)
    assert "sort:created-asc" in " ".join(argv)


def test_la_liste_des_candidates_n_est_pas_tronquee(monkeypatch) -> None:
    """La liste n'est PAS tronquee a 15 PRs.

    La troncature ecarte les PRs relues les plus recentes : elle decidait
    du lot, alors que la porte en est une autre.
    """
    nodes = [
        {"number": n, "title": f"PR {n}", "createdAt": f"2026-11-{n:02d}T00:00:00Z",
         "isCrossRepository": False, "headRefOid": f"sha-{n}"}
        for n in range(1, 21)
    ]
    monkeypatch.setattr(heavy_batch.pool, "run_gh",
                        lambda argv, *a, **k: json.dumps(nodes))
    monkeypatch.setattr(heavy_batch.pool, "fetch_prs",
                        lambda repo, numbers: {
                            n: {"verdict": "LGTM"} for n in numbers})
    monkeypatch.setattr(heavy_batch, "has_coordinator_approval",
                        lambda repo, number, head_sha=None: True)
    entries = heavy_batch.fetch_entries("jsboige/CoursIA", 100)
    assert len(entries) == 20
    assert [e["number"] for e in entries][:3] == [1, 2, 3]


# --- Lecture du verdict ----------------------------------------------------


def test_le_verdict_est_lu_dans_le_corps_et_non_dans_review_decision() -> None:
    node = {
        "number": 7,
        "title": "une PR",
        "createdAt": "2026-11-01T00:00:00Z",
        "isCrossRepository": False,
        "mergeStateStatus": "CLEAN",
        "reviewDecision": None,
        "reviews": [],
        "comments": [{"author": {"login": "jsboige"}, "body": "VERDICT: LGTM", "createdAt": "2026-11-02T00:00:00Z"}],
    }
    entry = heavy_batch.build_entry(node)
    assert entry["verdict"] == "LGTM"


def test_une_review_approvee_du_coordinateur_est_reconnue() -> None:
    node = {
        "number": 8,
        "title": "une PR de fork",
        "createdAt": "2026-11-01T00:00:00Z",
        "headRefOid": "sha-8",
        "isCrossRepository": True,
        "mergeStateStatus": "CLEAN",
        "reviewDecision": "APPROVED",
        "reviews": [
            {
                "author": {"login": "myia-ai-01"},
                "state": "APPROVED",
                "commit_id": "sha-8",
                "body": "",
                "submittedAt": "2026-11-02T00:00:00Z",
            }
        ],
        "comments": [],
    }
    entry = heavy_batch.build_entry(node)
    assert entry["approved_by_coordinator"] is True
    assert entry["fork"] is True


def test_une_approve_portede_sur_une_ancienne_tete_ne_vaut_pas_approbation() -> None:
    # L'approbation vaut pour la tete qu'elle couvre. Une tete qui a bouge
    # depuis n'est plus couverte : le contenu approuve n'est plus le contenu
    # qui mergera.
    node = {
        "number": 8,
        "title": "une PR",
        "createdAt": "2026-11-01T00:00:00Z",
        "headRefOid": "sha-8-bis",
        "isCrossRepository": False,
        "mergeStateStatus": "CLEAN",
        "reviews": [
            {
                "author": {"login": "myia-ai-01"},
                "state": "APPROVED",
                "commit_id": "sha-8",
                "body": "",
                "submittedAt": "2026-11-02T00:00:00Z",
            }
        ],
        "comments": [],
    }
    entry = heavy_batch.build_entry(node)
    assert entry["approved_by_coordinator"] is False


def test_une_tete_inconnue_ne_vaut_pas_approbation() -> None:
    # Fail-closed : on ne verifie pas ce qu'on n'a pas lu.
    node = {
        "number": 8,
        "title": "une PR",
        "createdAt": "2026-11-01T00:00:00Z",
        "isCrossRepository": False,
        "mergeStateStatus": "CLEAN",
        "reviews": [
            {
                "author": {"login": "myia-ai-01"},
                "state": "APPROVED",
                "commit_id": "sha-8",
                "body": "",
                "submittedAt": "2026-11-02T00:00:00Z",
            }
        ],
        "comments": [],
    }
    entry = heavy_batch.build_entry(node)
    assert entry["approved_by_coordinator"] is False


def test_une_review_commented_ne_vaut_pas_approve_du_coordinateur() -> None:
    node = {
        "number": 9,
        "title": "une PR",
        "createdAt": "2026-11-01T00:00:00Z",
        "isCrossRepository": True,
        "mergeStateStatus": "CLEAN",
        "reviewDecision": None,
        "reviews": [
            {"author": {"login": "myia-ai-01"}, "state": "COMMENTED", "body": "", "submittedAt": "2026-11-02T00:00:00Z"}
        ],
        "comments": [],
    }
    entry = heavy_batch.build_entry(node)
    assert entry["approved_by_coordinator"] is False


# --- Mesure ----------------------------------------------------------------


def test_la_duree_du_lot_est_calculee_entre_debut_et_fin() -> None:
    results = {
        "started_at": "2026-11-09T04:30:00+00:00",
        "finished_at": "2026-11-09T05:00:00+00:00",
        "prs": [{"number": 1, "statut": "vert", "duree_s": 120}],
    }
    payload = heavy_batch.summarize(results, datetime(2026, 11, 9, 5, 5, tzinfo=timezone.utc))
    assert payload["duree_lot_s"] == 1800
    assert payload["prs_concernes"] == 1
    assert payload["prs_rouges"] == 0


def test_un_lot_fini_avant_l_echeance_est_conforme() -> None:
    results = {
        "started_at": "2026-11-09T04:30:00+00:00",
        "finished_at": "2026-11-09T09:00:00+00:00",
        "prs": [],
    }
    payload = heavy_batch.summarize(results, datetime(2026, 11, 9, 9, 5, tzinfo=timezone.utc))
    assert payload["fin_avant_echeance"] is True


def test_un_lot_qui_deborde_l_echeance_est_signale() -> None:
    # lot lance a 04:30 (creneau 1, echeance 10:00) et fini a 11:00 : trop tard
    results = {
        "started_at": "2026-11-09T04:30:00+00:00",
        "finished_at": "2026-11-09T11:00:00+00:00",
        "prs": [],
    }
    payload = heavy_batch.summarize(results, datetime(2026, 11, 9, 11, 5, tzinfo=timezone.utc))
    assert payload["creneau"]["nom"] == "creneau-1"
    assert payload["fin_avant_echeance"] is False


def test_le_creneau_de_reference_est_celui_du_debut_du_lot() -> None:
    # un lot lance a 04:30 et lu a 11:05 reste juge sur l'echeance de 10:00
    results = {
        "started_at": "2026-11-09T04:30:00+00:00",
        "finished_at": "2026-11-09T09:00:00+00:00",
        "prs": [],
    }
    payload = heavy_batch.summarize(results, datetime(2026, 11, 9, 11, 5, tzinfo=timezone.utc))
    assert payload["creneau"]["nom"] == "creneau-1"
    assert payload["fin_avant_echeance"] is True


def test_le_dernier_creneau_admet_un_fin_apres_minuit() -> None:
    # creneau 4 : 21:30 -> 00:00 (le lendemain). Un lot fini a 23:00 tient ;
    # un lot fini a 01:00 le lendemain a deborde.
    results = {
        "started_at": "2026-11-09T21:30:00+00:00",
        "finished_at": "2026-11-09T23:00:00+00:00",
        "prs": [],
    }
    payload = heavy_batch.summarize(results, datetime(2026, 11, 9, 23, 5, tzinfo=timezone.utc))
    assert payload["creneau"]["nom"] == "creneau-4"
    assert payload["fin_avant_echeance"] is True

    results["finished_at"] = "2026-11-10T01:00:00+00:00"
    payload = heavy_batch.summarize(results, datetime(2026, 11, 10, 1, 5, tzinfo=timezone.utc))
    assert payload["fin_avant_echeance"] is False


def test_sans_heure_de_debut_l_echeance_est_indeterminee() -> None:
    results = {"prs": [], "finished_at": "2026-11-09T11:00:00+00:00"}
    payload = heavy_batch.summarize(results, datetime(2026, 11, 9, 11, 5, tzinfo=timezone.utc))
    assert payload["duree_lot_s"] is None
    assert payload["fin_avant_echeance"] is None


# --- Geste d'execution -----------------------------------------------------


def test_le_plan_des_commandes_decrit_le_geste_complet(tmp_path: Path) -> None:
    commands = heavy_batch.plan_commands(
        tmp_path, 42, tmp_path / "wt", tmp_path / "select_tests.py"
    )
    joined = [" ".join(c) for c in commands]
    assert any("pull/42/merge" in c for c in joined)
    assert any("worktree add" in c for c in joined)
    assert any("worktree remove" in c for c in joined)
    assert any("select_tests.py" in c for c in joined)
    assert any("pytest" in c for c in joined)


def test_sans_selecteur_le_plan_ne_prevoit_pas_de_pytest(tmp_path: Path) -> None:
    commands = heavy_batch.plan_commands(tmp_path, 42, tmp_path / "wt", None)
    runs_pytest = [c for c in commands if "-m" in c and "pytest" in c]
    assert runs_pytest == []


def test_le_lot_en_simulation_ne_lance_aucune_commande(tmp_path: Path) -> None:
    plan = {"selectionnees": [{"number": 42}]}
    results = heavy_batch.run_batch(
        tmp_path, plan, tmp_path / "work", tmp_path / "sel.py", dry_run=True
    )
    assert results["prs"][0]["statut"] == "simulation"
    assert results["started_at"] and results["finished_at"]
    assert not (tmp_path / "work" / "pr-42").exists()


# --- CLI -------------------------------------------------------------------


def test_la_cli_slot_rend_le_creneau_actif() -> None:
    proc = subprocess.run(
        [sys.executable, str(CI_DIR / "heavy_batch.py"), "--slot", "--json"],
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )
    assert proc.returncode == 0, proc.stderr
    payload = json.loads(proc.stdout)
    assert len(payload["creneaux"]) == 4


def test_la_cli_resume_un_lot_deja_produit(tmp_path: Path) -> None:
    results = tmp_path / "results.json"
    results.write_text(
        json.dumps(
            {
                "started_at": "2026-11-09T04:30:00+00:00",
                "finished_at": "2026-11-09T05:00:00+00:00",
                "prs": [{"number": 1, "statut": "rouge", "duree_s": 60}],
            }
        ),
        encoding="utf-8",
    )
    proc = subprocess.run(
        [sys.executable, str(CI_DIR / "heavy_batch.py"), "--results", str(results), "--json"],
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )
    assert proc.returncode == 0, proc.stderr
    payload = json.loads(proc.stdout)
    assert payload["prs_rouges"] == 1


def test_un_resultat_illisible_rend_une_erreur_explicite(tmp_path: Path) -> None:
    bad = tmp_path / "results.json"
    bad.write_text("{pas du json", encoding="utf-8")
    proc = subprocess.run(
        [sys.executable, str(CI_DIR / "heavy_batch.py"), "--results", str(bad)],
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )
    assert proc.returncode == 2


# --- Arbre d'integration et bissection ------------------------------------


def _git(cwd: Path, *args: str) -> str:
    """Lance une commande git et echoue bruyamment si elle rate."""
    proc = subprocess.run(
        ["git", "-C", str(cwd), *args],
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )
    if proc.returncode != 0:
        raise AssertionError(f"git {' '.join(args)} a echoue : {proc.stderr or proc.stdout}")
    return proc.stdout


def _repo(tmp_path: Path, contenus: dict[int, dict[str, str]]) -> tuple[Path, list[int]]:
    """Depot jetable : une `main`, et une ref de fusion par PR.

    Chaque PR est poussee dans le depot nu sous `refs/pull/N/merge` -- la
    forme exacte que GitHub produit, et celle que le lot va chercher.
    """
    origin = tmp_path / "origin.git"
    _git(tmp_path, "init", "--bare", "-b", "main", str(origin))
    seed = tmp_path / "seed"
    _git(tmp_path, "clone", str(origin), str(seed))
    (seed / "racine.txt").write_text("base\n", encoding="utf-8")
    _git(seed, "add", "racine.txt")
    _git(seed, "-c", "user.name=t", "-c", "user.email=t@t", "commit", "-m", "base")
    _git(seed, "branch", "-M", "main")
    _git(seed, "push", "origin", "main")
    numbers: list[int] = []
    for number, files in sorted(contenus.items()):
        _git(seed, "checkout", "-b", f"pr{number}", "main")
        for name, content in files.items():
            (seed / name).write_text(content, encoding="utf-8")
            _git(seed, "add", name)
        _git(seed, "-c", "user.name=t", "-c", "user.email=t@t", "commit", "-m", f"pr {number}")
        _git(seed, "push", "origin", f"pr{number}:refs/pull/{number}/merge")
        numbers.append(number)
    clone = tmp_path / "clone"
    _git(tmp_path, "clone", str(origin), str(clone))
    return clone, numbers


def test_le_sujet_dune_fusion_designe_la_pr() -> None:
    assert heavy_batch.pr_number_from_subject("lot: PR #42") == 42
    assert heavy_batch.pr_number_from_subject("lot: PR #42 (suite)") == 42


def test_un_sujet_hors_marque_ne_designe_aucune_pr() -> None:
    # un commit qui n'est pas une fusion du lot n'est jamais accuse
    assert heavy_batch.pr_number_from_subject("Commit initial") is None
    assert heavy_batch.pr_number_from_subject(None) is None


def test_l_arbre_d_integration_fusionne_les_prs_dans_l_ordre(tmp_path: Path) -> None:
    clone, numbers = _repo(tmp_path, {1: {"a.txt": "A\n"}, 2: {"b.txt": "B\n"}})
    try:
        record = heavy_batch.build_integration_tree(clone, numbers, tmp_path / "work")
        assert record["statut"] == "construit"
        assert record["prs_integrees"] == [1, 2]
        assert record["conflits"] == []
        assert [c["pr"] for c in record["commits"]] == [1, 2]
        # chaque fusion porte le sujet qui la rend identifiable
        tree = Path(record["chemin"])
        for commit in record["commits"]:
            sujet = heavy_batch._commit_subject(tree, commit["commit"])
            assert heavy_batch.pr_number_from_subject(sujet) == commit["pr"]
        # et le sujet seul suffit a nommer la PR quand le coupable est la
        # fusion elle-meme
        assert heavy_batch.pr_culpable(
            tree, record["commits"][1]["commit"], record["commits"]
        ) == 2
    finally:
        heavy_batch.run_git(
            clone, ["worktree", "remove", "--force", str(tmp_path / "work" / "integration")],
            check=False,
        )


def test_un_conflit_d_integration_est_nomme_et_sort_la_pr_de_l_arbre(tmp_path: Path) -> None:
    clone, numbers = _repo(tmp_path, {1: {"meme.txt": "A\n"}, 2: {"meme.txt": "B\n"}})
    try:
        record = heavy_batch.build_integration_tree(clone, numbers, tmp_path / "work")
        assert record["statut"] == "construit"
        assert record["prs_integrees"] == [1]
        assert [c["pr"] for c in record["conflits"]] == [2]
    finally:
        heavy_batch.run_git(
            clone, ["worktree", "remove", "--force", str(tmp_path / "work" / "integration")],
            check=False,
        )


def test_la_bissection_designe_la_pr_coupable(tmp_path: Path) -> None:
    # Le script de bissection rend toujours 1 : tout ce qui est entre la base
    # et la tete est donc « mauvais », et la bissection doit s'arreter sur le
    # PREMIER commit de fusion -- donc nommer la PR #1. C'est le lien
    # commit -> PR qui est verifie ici, pas le verdict de la suite.
    clone, numbers = _repo(tmp_path, {1: {"a.txt": "A\n"}, 2: {"b.txt": "B\n"}})
    arbre = heavy_batch.build_integration_tree(clone, numbers, tmp_path / "work")
    faux = tmp_path / "faux.py"
    faux.write_text("import sys\nsys.exit(1)\n", encoding="utf-8")
    try:
        record = heavy_batch.bisect_lot(
            Path(arbre["chemin"]),
            arbre["base"],
            arbre["tip"],
            faux,
            ["scripts/tests"],
            merges=arbre["commits"],
        )
        assert record["statut"] == "bissection-effectuee"
        # La bissection s'arrete sur le commit de la BRANCHE de la PR #1 --
        # ce commit est un ancetre de sa fusion, et c'est la lecture par
        # ascendance qui rend le coupable nomme. Lire le sujet seul aurait
        # rendu `None` ici.
        assert record["pr_coupable"] == 1
    finally:
        heavy_batch.run_git(
            clone, ["worktree", "remove", "--force", str(tmp_path / "work" / "integration")],
            check=False,
        )


def test_le_code_de_bissection_est_0_sur_suite_verte(monkeypatch, tmp_path: Path) -> None:
    (tmp_path / "cible").write_text("x", encoding="utf-8")
    monkeypatch.setattr(heavy_batch, "run_heavy_suite", lambda *a, **k: (0, ""))
    assert heavy_batch.bisect_run(tmp_path, ["cible"]) == heavy_batch.BISECT_GOOD


def test_le_code_de_bissection_est_1_sur_suite_rouge(monkeypatch, tmp_path: Path) -> None:
    (tmp_path / "cible").write_text("x", encoding="utf-8")
    monkeypatch.setattr(heavy_batch, "run_heavy_suite", lambda *a, **k: (1, "FAILED tests/x.py"))
    assert heavy_batch.bisect_run(tmp_path, ["cible"]) == heavy_batch.BISECT_BAD


def test_le_code_de_bissection_est_125_quand_la_cible_est_absente(monkeypatch, tmp_path: Path) -> None:
    # une dependance absente n'est pas une faute : c'est « indetermine »
    monkeypatch.setattr(heavy_batch, "run_heavy_suite", lambda *a, **k: (1, "ModuleNotFoundError: numpy"))
    assert heavy_batch.bisect_run(tmp_path, ["cible-absente"]) == heavy_batch.BISECT_SKIP


def test_le_code_de_bissection_est_125_quand_la_dependance_manque(
    monkeypatch, tmp_path: Path
) -> None:
    (tmp_path / "cible").write_text("x", encoding="utf-8")
    monkeypatch.setattr(
        heavy_batch, "run_heavy_suite", lambda *a, **k: (1, "ModuleNotFoundError: numpy")
    )
    assert heavy_batch.bisect_run(tmp_path, ["cible"]) == heavy_batch.BISECT_SKIP


def test_la_cli_bisect_run_rend_125_quand_la_cible_est_absente(tmp_path: Path) -> None:
    proc = subprocess.run(
        [
            sys.executable,
            str(CI_DIR / "heavy_batch.py"),
            "--bisect-run",
            "--bisect-target",
            "cible-absente",
        ],
        cwd=str(tmp_path),
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )
    assert proc.returncode == heavy_batch.BISECT_SKIP


def test_une_pr_de_fork_non_approuvee_est_refusee_meme_designee() -> None:
    autorise, motif = heavy_batch.pr_dispatched_autorise(
        {"fork": True, "approved_by_coordinator": False}
    )
    assert autorise is False
    assert "fork" in motif


def test_une_pr_de_fork_approuvee_passe() -> None:
    autorise, motif = heavy_batch.pr_dispatched_autorise(
        {"fork": True, "approved_by_coordinator": True}
    )
    assert autorise is True
    assert motif == ""


def test_une_pr_du_depot_passe_meme_sans_verdict() -> None:
    autorise, _motif = heavy_batch.pr_dispatched_autorise(
        {"fork": False, "approved_by_coordinator": False}
    )
    assert autorise is True


def test_le_resume_nomme_la_pr_coupable() -> None:
    results = {
        "started_at": "2026-11-09T04:30:00+00:00",
        "finished_at": "2026-11-09T05:00:00+00:00",
        "prs": [],
        "integration": {
            "statut": "rouge",
            "arbre": {"prs_integrees": [1, 2], "conflits": []},
            "bissection": {"statut": "bissection-effectuee", "pr_coupable": 2},
        },
    }
    payload = heavy_batch.summarize(
        results, datetime(2026, 11, 9, 5, 5, tzinfo=timezone.utc)
    )
    assert payload["arbre_integration"]["pr_coupable"] == 2
    assert payload["arbre_integration"]["prs_integrees"] == [1, 2]
    assert payload["arbre_integration"]["statut"] == "rouge"


# --- Ce que le lot mesure (suite et environnement) ------------------------


def test_les_cibles_de_la_suite_sont_lues_dans_la_jambe_scripts_tests() -> None:
    # La source de verite est le workflow de la jambe `Scripts Tests`, pas
    # une recopie dans l'organe : une recopie deriverait au premier ajout
    # de cible. Le lot joue donc exactement les chemins de la jambe.
    cibles = heavy_batch.suite_lourde_cible(REPO_ROOT)
    assert "scripts/tests" in cibles
    assert "MyIA.AI.Notebooks/GameTheory/tests" in cibles
    # et la lecture est STABLE : deux lectures donnent la meme liste
    assert cibles == heavy_batch.suite_lourde_cible(REPO_ROOT)


def test_une_suite_absente_est_non_mesurable(tmp_path: Path) -> None:
    # Fail-closed : un lot qui jouerait une liste de cibles vide se
    # presenterait comme un lot vert.
    with pytest.raises(RuntimeError):
        heavy_batch.suite_lourde_cible(tmp_path)


def test_un_bloc_pytest_derive_est_non_mesurable(tmp_path: Path) -> None:
    # Le workflow existe mais son bloc pytest a derive : la lecture rend
    # None, et l'organe leve au lieu de jouer une liste vide.
    workflow = tmp_path / ".github" / "workflows" / "scripts-tests.yml"
    workflow.parent.mkdir(parents=True)
    workflow.write_text("name: x\njobs:\n  a:\n    steps:\n      - run: pytest\n", encoding="utf-8")
    with pytest.raises(RuntimeError):
        heavy_batch.suite_lourde_cible(tmp_path)


def test_le_lot_joue_la_suite_avec_les_memes_options_pytest() -> None:
    # Mêmes options que la jambe `Scripts Tests` : sinon la durée mesurée
    # n'est pas comparable à celle de la jambe qu'on veut déplacer.
    assert heavy_batch.PYTEST_FLAGS == ("-n", "4", "--dist", "loadscope", "--tb=short", "-q")


def test_l_environnement_du_lot_est_celui_de_la_suite() -> None:
    # Un seul script d'installation, appelé par les deux jambes : c'est ce
    # qui rend les durées comparables. Deux listes recopiées dériveraient.
    script = REPO_ROOT / "scripts" / "ci" / "install_scripts_tests_deps.sh"
    assert script.is_file(), "le script d'installation partage doit exister"
    appels = "bash scripts/ci/install_scripts_tests_deps.sh"
    for workflow in ("scripts-tests.yml", "slow-lane.yml"):
        texte = (REPO_ROOT / ".github" / "workflows" / workflow).read_text(encoding="utf-8")
        assert appels in texte, f"{workflow} doit installer via le script partage"


def test_un_lot_vide_measure_la_baseline_sur_main(monkeypatch, tmp_path: Path) -> None:
    # Lot vide : l'arbre est `main` seul. La suite y est jouee quand meme --
    # c'est la baseline de la suite sur `main`, la seule comparable quand la
    # file n'a rien d'approuve a la tete exacte. Le rapport le dit.
    def _fake_tree(root: Path, numbers: list[int], work_root: Path, dry_run: bool = False):
        tree = work_root / "integration"
        tree.mkdir(parents=True, exist_ok=True)
        return {
            "chemin": str(tree),
            "base": "base",
            "tip": "tip",
            "prs_integrees": [],
            "conflits": [],
            "commits": [],
            "statut": "construit",
        }

    monkeypatch.setattr(heavy_batch, "build_integration_tree", _fake_tree)
    monkeypatch.setattr(heavy_batch, "suite_lourde_cible", lambda tree: ["scripts/tests"])
    monkeypatch.setattr(heavy_batch, "run_heavy_suite", lambda *a, **k: (0, "1 passed"))
    record = heavy_batch.run_integration(Path("."), [], tmp_path)
    assert record["lot_vide"] is True
    assert record["statut"] == "vert"
    assert "baseline" in record["detail"]


def test_un_rouge_sur_main_seul_n_est_pas_attribue_a_une_pr(monkeypatch, tmp_path: Path) -> None:
    # Arbre = `main` seul : un rouge la est un rouge HERITE de la base. Il
    # n'y a rien a bissecter (base == tip), et l'accuser d'une PR du lot
    # serait une faute d'attribution.
    def _fake_tree(root: Path, numbers: list[int], work_root: Path, dry_run: bool = False):
        tree = work_root / "integration"
        tree.mkdir(parents=True, exist_ok=True)
        return {
            "chemin": str(tree),
            "base": "base",
            "tip": "tip",
            "prs_integrees": [],
            "conflits": [],
            "commits": [],
            "statut": "construit",
        }

    def _boom(*args, **kwargs):
        raise AssertionError("la bissection ne doit pas etre lancee sur un arbre vide")

    monkeypatch.setattr(heavy_batch, "build_integration_tree", _fake_tree)
    monkeypatch.setattr(heavy_batch, "suite_lourde_cible", lambda tree: ["scripts/tests"])
    monkeypatch.setattr(heavy_batch, "run_heavy_suite", lambda *a, **k: (1, "FAILED tests/x.py"))
    monkeypatch.setattr(heavy_batch, "bisect_lot", _boom)
    record = heavy_batch.run_integration(Path("."), [], tmp_path)
    assert record["statut"] == "rouge"
    assert "herite de la base" in record["detail"]
    assert "bissection" not in record
