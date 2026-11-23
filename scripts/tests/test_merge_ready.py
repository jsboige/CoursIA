"""Tests hermetiques de l'organe merge_ready (Q40) -- aucun reseau, aucun gh.

Toutes les commandes passent par un runner scripte : le module sous test
est charge par importlib (meme convention que test_check_adjoint_prevalidation)
et ses sous-processus ne quittent jamais le processus de test. La porte STACK
(etape 3, en processus depuis le retrait du dossier du 2026-11-05) est
injectee de la meme facon : un fixture autouse remplace
``gate.default_stack_index`` par un index vide, pour qu'aucun test ne lance
de git reel.
"""

import importlib.util
import os
import base64
import json
import re
import subprocess
import sys
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
MERGE_READY_PATH = HERE.parent / "coordination" / "merge_ready.py"
_spec = importlib.util.spec_from_file_location("merge_ready_under_test", MERGE_READY_PATH)
mr = importlib.util.module_from_spec(_spec)
sys.modules["merge_ready_under_test"] = mr
_spec.loader.exec_module(mr)

HEAD = "0123456789abcdef0123456789abcdef01234567"
HEAD_MOVED = "fedcba9876543210fedcba9876543210fedcba98"
TOKEN = "tok-myia-ai-01-fake"
GRAIN_MED = "Grain: MED/guard -- lane myia-po-2026:CoursIA -- prev: MED/guard #1"
GRAIN_DEEP = "Grain: DEEP/lean -- lane myia-po-2026:CoursIA -- prev: MED/guard #1"
BASE = "ba5eba5eba5eba5eba5eba5eba5eba5eba5eba5e"
#: Jambes nominales du chemin `unstable` (#25059) : la porte verte, un check
#: vert, et une jambe ANNULEE d'un run remplace dont le nom a ete repris par
#: une jambe verte plus recente -- le cas mesure sur #24116 (run annule puis
#: run vert pour les memes noms).
DEFAULT_CHECK_RUNS = "\n".join(
    json.dumps(row)
    for row in (
        {"name": "PR gate", "conclusion": "success", "status": "completed",
         "started_at": "2026-11-07T10:00:00Z", "id": 4},
        {"name": "Scripts Tests (CPU)", "conclusion": "success",
         "status": "completed", "started_at": "2026-11-07T10:00:00Z", "id": 5},
        {"name": "Scripts Tests (CPU)", "conclusion": "cancelled",
         "status": "completed", "started_at": "2026-11-07T09:00:00Z", "id": 3},
    )
)
# Sentinelle : « pas precise » n'est pas « aucune approbation ». Par defaut une
# vue porte l'approbation du coordinateur a la tete (le chemin nominal depuis
# Q67) ; une vue dont les reviews sont fournies explicitement n'en recoit que si
# on la demande.
_DEFAULT = object()


def _index_de_pile_vide() -> dict:
    """Index de pile vide : porte MESUREE, aucune PR partenaire, aucune
    raison -- et surtout aucun appel git (la construction reelle de l'index
    lance ``git`` en sous-processus)."""
    return {}


@pytest.fixture(autouse=True)
def _porte_stack_mesuree(monkeypatch):
    """Porte STACK injectee : index de pile vide, porte MESUREE, aucun git.

    Depuis le retrait du dossier (2026-11-05), l'etape 3 appelle la porte du
    gate EN PROCESSUS (``gate.default_stack_index`` puis
    ``gate.stack_reasons``) : sans injection, chaque test lancerait le git
    reel de la construction de l'index. Le defaut est un index vide -- porte
    mesuree, aucune PR partenaire, aucune raison. Les tests de la porte
    surchargent ce defaut par leur propre ``monkeypatch.setattr``.
    """
    monkeypatch.setattr(mr.gate, "default_stack_index", _index_de_pile_vide)


def default_view(
    *,
    pr: int = 123,
    draft: bool = False,
    files: tuple[str, ...] = ("src/a.py",),
    body: str | None = None,
    comments: list[dict] | None = None,
    title: str = "fix(x): une PR ordinaire",
    reviews: list[dict] | None = None,
    coordinator=_DEFAULT,
    head: str = HEAD,
    head_ref: str = "feature/une-pr-ordinaire",
) -> dict:
    rows = list(reviews) if reviews is not None else []
    if coordinator is _DEFAULT:
        coordinator = head if reviews is None else None
    if coordinator is not None:
        rows.append(coordinator_review(oid=coordinator))
    return {
        "number": pr,
        "title": title,
        "isDraft": draft,
        "body": body if body is not None else GRAIN_MED,
        "headRefOid": head,
        "headRefName": head_ref,
        # baseRefName is the branch the PR is targeting. The merge-ready
        # defense-in-depth check (#19002) refuses anything other than
        # `main`. Tests that need a non-`main` base override this field.
        "baseRefName": "main",
        "baseRefOid": BASE,
        "files": [{"path": p} for p in files],
        "changedFiles": len(files),
        "comments": comments
        if comments is not None
        else [{"body": "un commentaire de lane ordinaire"}],
        "reviews": rows,
    }


def review_row(
    *,
    state: str = "APPROVED",
    oid: str = HEAD,
    submitted: str = "2026-09-25T03:00:00Z",
    body: str = "",
    login: str = "clusterManager-Myia",
) -> dict:
    """Forme de ``gh pr view --json reviews`` (l'oid de review est sur ``commit``)."""
    return {
        "author": {"login": login},
        "state": state,
        "body": body,
        "submittedAt": submitted,
        "commit": {"oid": oid},
    }


def coordinator_review(
    *,
    state: str = "APPROVED",
    oid: str = HEAD,
    submitted: str = "2026-09-25T01:00:00Z",
    body: str = "",
) -> dict:
    """Une voix du coordinateur (``myia-ai-01``), anterieure aux voix de bot par defaut."""
    return review_row(
        state=state, oid=oid, submitted=submitted, body=body, login="myia-ai-01"
    )


class ScriptedRunner:
    """Runner fake : dispatch par contenu de commande. Defauts = chemin nominal
    (une PR unique prete au merge, B.0 clear, clean). La porte STACK n'y
    figure pas : elle est injectee en processus par le fixture autouse."""

    def __init__(
        self,
        *,
        token: str = TOKEN,
        token_rc: int = 0,
        prs: tuple[int, ...] = (123,),
        views: dict[int, dict] | None = None,
        # Echec de ``gh pr view`` (toutes les vues) : sert a simuler une
        # erreur de portee generale (jeton refuse) au milieu du balayage.
        view_rc: int = 0,
        view_stderr: str = "",
        nits_rc: int = 0,
        pulls: list[dict] | None = None,
        merge_rc: int = 0,
        # Scenario de merge consomme **dans l'ordre** : chaque appel a
        # `gh pr merge` prend le couple (rc, stderr) suivant ; la liste
        # epuisee, le runner retombe sur ``merge_rc``. Sert a simuler une
        # course de base puis un rejeu (#26771).
        merge_script: list[tuple[int, str]] | None = None,
        fetch_rc: int = 0,
        twin_rc: int = 0,
        twin_stdout: str = "",
        # Porte 5bis.ter (#28202) : attestation jumelle decrivant l'arbre de
        # fusion. 0 = conforme, 1 = defaut trouve, 2 = mesure impossible.
        attest_rc: int = 0,
        attest_stdout: str = "",
        # Revendications d'ordinal des PRs ouvertes (organe
        # twin_open_claims.py) : 0 = liste vide, 1 = liste portee par
        # claims_stdout, 2 = API illisible (fail-closed).
        claims_rc: int = 0,
        claims_stdout: str = '{"claims": []}',
        # Issue #20774 : organe slot-reservation-guard en mode en ligne, au merge.
        # 0 = clear, 1 = collision, 2 = unreadable. Cf. SLOT_DOCUMENTED_RC.
        slot_rc: int = 0,
        slot_stdout: str = "",
        # #27875 : reponse scriptee de la lecture du manifeste des lakes
        # (`gh api repos/.../contents/scripts/lean/ci_lakes.json?ref=<tete>`).
        # `None` (defaut) = 404 : manifeste non lu, la garde retombe sur son
        # motif generique (fail-closed conserve). Une chaine = stdout BRUT
        # (reponse malformee) ; un dict = payload JSON.
        ci_lakes_payload: dict | str | None = None,
        commits: dict[str, dict] | None = None,
        auto_tree: str | None = None,
        base_search: dict[str, list[dict]] | None = None,
        base_search_rc: int = 0,
        # Etape 5quinquies : tests d'integrite sur l'arbre fusionne. Vert par
        # defaut, pour que les tests historiques gardent leur chemin nominal.
        combined_rc: int = 0,
        combined_stdout: str = '{"verdict": "GREEN", "failed": []}',
        # #25059 : etape 6 bis, lecture des jambes de check. Valeur = stdout
        # du ``gh api .../check-runs`` (une ligne JSON par jambe). Defaut :
        # le jeu nominal vert.
        check_runs: str | None = None,
        main_check_runs: str | None = None,
        main_sha: str = "a" * 40,
        # #24828 : historique de main lu par la sentinelle (SHA du plus
        # recent au plus ancien) et check-runs par SHA. Le defaut : un seul
        # commit (la tete), avec le jeu de checks nominal.
        main_history: list[str] | None = None,
        main_checks_by_sha: dict[str, str] | None = None,
        # #17437 : reponses de la sonde d'identite App (DESORMAIS INERTE :
        # la sonde a ete supprimee le 2026-11-12, la preuve d'identite est
        # portee par le type de la ligne. Conservee pour que le test qui
        # prouve l'absence d'appel puisse scripter une reponse ``Bot`` et
        # verifier qu'elle n'est jamais consultee).
        user_types: dict[str, str] | None = None,
        # #17437 (relecture 2026-11-12) : lignes de la surface REST typee
        # ``pulls/N/reviews`` (forme REST brute : ``user.login`` suffixe,
        # ``user.type``, ``submitted_at``, ``commit_id``). Defaut vide :
        # l'organe retombe alors sur les lignes du payload ``pr view``
        # (non typees) — le chemin des tests historiques.
        rest_reviews: list[dict] | None = None,
        # #26799 : etats servis par le RECHAUFFAGE (lecture a effet de bord,
        # qui demarre le calcul de mergeabilite de la PR). La cle est le
        # numero de PR, la valeur l'etat renvoye. Ces lectures NE CONSOMMENT
        # PAS la pile ``pulls`` : elles n'ont aucun etat a faire valoir.
        warmup_states: dict[int, str] | None = None,
        # #26799 (revue coordinateur du 16/11) : PRs qui portent une voix du
        # coordinateur dans ``latestReviews`` (la lecture de liste). Defaut :
        # TOUTES -- le chemin nominal du rechauffage. Une PR absente de la
        # liste n'est pas rechauffee : elle s'arrete a l'etape 2 (pas
        # d'approbation), donc elle n'atteint jamais la lecture de
        # mergeabilite.
        coordinator_voices: tuple[int, ...] | None = None,
        # #25510 T-J : etapes du job associe a un check-run de job. La
        # CLE est l'identifiant de job, la VALEUR est soit le nom de la
        # PREMIERE etape en echec (forme historique : une seule etape en
        # echec, "" = aucune), soit la LISTE des etapes (forme T-J : chaque
        # etape porte son nom `n`, son numero `o`, son statut `s` et sa
        # conclusion `c`). Sert a prouver que la sentinelle distingue une
        # panne d'infrastructure d'un verdict de code, et un runner perdu
        # d'un verdict de code.
        job_steps: dict[str, str | list[dict]] | None = None,
        # Code de sortie de la lecture de job, par identifiant de job.
        # 0 (defaut) = lecture reussie ; autre chose = lecture ILLISIBLE
        # (fail-closed : la retenue doit rester).
        job_steps_rc: dict[str, int] | None = None,
        # Log d'echec du run (`gh run view --log-failed`). Vide par defaut :
        # aucun test n'y est identifie.
        run_log: str = "",
        # #26706 : issue canonique du rouge de `main`. `main_red_issues` =
        # les issues [main-red] VIVantes (comme la recherche GitHub les
        # rendrait) ; `main_red_search_rc` non nul simule une recherche
        # illisible (fail-closed : aucune creation) ; `main_red_issue_rc`
        # non nul simule un refus de creation ou de fermeture.
        main_red_issues: list[dict] | None = None,
        main_red_search_rc: int = 0,
        main_red_issue_rc: int = 0,
        # #26706 : reponse scriptee de ``gh issue view <numero>`` -- la
        # lecture de l'ETAT d'une issue [main-red] connue par son numero.
        # La CLE est le numero ; la VALEUR est soit un payload JSON (dict),
        # soit un stdout BRUT (str : reponse malformee -> illisible).
        # `main_red_view_rc` non nul simule une lecture ILLISIBLE.
        main_red_views: dict[int, dict | str] | None = None,
        main_red_view_rc: int = 0,
        # #27684 : liste COMPLETE des fichiers d'une PR, lue en REST pagine
        # (``/pulls/{n}/files``) quand la vue ``gh pr view --json files`` est
        # tronquee (plafond de 100). Cle = numero de PR, valeur = la liste
        # des chemins, dans l'ordre ; ``pr_files_rc`` non nul simule une
        # lecture ILLISIBLE (quota, 5xx).
        pr_files: dict[int, list[str]] | None = None,
        pr_files_rc: int = 0,
    ):
        self.rest_reviews = list(rest_reviews or [])
        self.user_types = user_types or {}
        self.combined_rc = combined_rc
        self.combined_stdout = combined_stdout
        self.main_red_issues = list(main_red_issues or [])
        self.main_red_search_rc = main_red_search_rc
        self.main_red_issue_rc = main_red_issue_rc
        self.main_red_views = dict(main_red_views or {})
        self.main_red_view_rc = main_red_view_rc
        self.main_red_created: list[dict] = []
        self.main_red_reopened: list[int] = []
        self.main_red_closed: list[int] = []
        self.check_runs = check_runs if check_runs is not None else DEFAULT_CHECK_RUNS
        self.main_check_runs = main_check_runs if main_check_runs is not None else json.dumps([
            {"name": "Scripts Tests (CPU)", "conclusion": "success",
             "status": "completed", "started_at": "2026-11-08T10:00:00Z",
             "output": {"summary": "21 000 passed"}}
        ])
        self.main_sha = main_sha
        self.main_history = list(main_history) if main_history is not None else [main_sha]
        self.main_checks_by_sha = main_checks_by_sha or {}
        self.job_steps = job_steps or {}
        self.warmup_states = warmup_states or {}
        self.coordinator_voices = (
            set(coordinator_voices) if coordinator_voices is not None else None
        )
        self.job_steps_rc = job_steps_rc or {}
        self.run_log = run_log
        self.token = token
        self.token_rc = token_rc
        self.prs = list(prs)
        self.views = views or {}
        self.view_rc = view_rc
        self.view_stderr = view_stderr
        self.nits_rc = nits_rc
        self.pulls = pulls or [{"mergeable_state": "clean", "head": {"sha": HEAD}}]
        self.merge_rc = merge_rc
        self.merge_script = list(merge_script or [])
        self.fetch_rc = fetch_rc
        self.twin_rc = twin_rc
        # stdout de l'organe twin : porte le JSON classifie quand twin_rc=1.
        # Vide par defaut (les tests historiques ``twin-index-collision``
        # n'attendent pas de classification).
        self.twin_stdout = twin_stdout
        # Porte 5bis.ter (#28202) : rapport de l'organe d'attestation.
        self.attest_rc = attest_rc
        self.attest_stdout = attest_stdout
        self.claims_rc = claims_rc
        self.claims_stdout = claims_stdout
        # #20774 : organe slot-reservation-guard, mode en ligne. Meme
        # convention que twin_rc/twin_stdout.
        self.slot_rc = slot_rc
        self.slot_stdout = slot_stdout
        self.ci_lakes_payload = ci_lakes_payload
        # Remontee first-parent de merge_dwell (etape 2ter) : payloads de
        # ``repos/.../commits/<sha>`` et arbre rendu par ``git merge-tree``.
        self.commits = commits or {}
        self.auto_tree = auto_tree
        # #19014 : reponses scriptees pour ``gh pr list --search head:<base>``.
        # Cle = la valeur de ``--search head:<base>`` (avec le prefixe),
        # valeur = la liste JSON de PRs (avec etat) que gh rendrait. La
        # cle absente rend [] ; ``base_search_rc`` non nul fait echouer
        # la commande pour tester le chemin ``unreadable``.
        self.base_search = base_search or {}
        self.base_search_rc = base_search_rc
        # #27684 : fichiers d'une PR en REST pagine.
        self.pr_files = pr_files or {}
        self.pr_files_rc = pr_files_rc
        self.calls: list[tuple[list[str], dict | None]] = []
        self.sleeps: list[float] = []

    # -- helpers d'assertion -------------------------------------------------

    def cmds(self) -> list[list[str]]:
        return [cmd for cmd, _ in self.calls]

    def flat(self) -> list[str]:
        return [" ".join(cmd) for cmd, _ in self.calls]

    # -- contrat Runner ------------------------------------------------------

    def run(self, cmd: list[str], env: dict | None = None) -> mr.RunResult:
        self.calls.append((list(cmd), env))
        c = list(cmd)
        if c[:4] == ["gh", "auth", "token", "--user"]:
            if self.token_rc != 0:
                return mr.RunResult(self.token_rc, "", "auth failed")
            return mr.RunResult(0, self.token + "\n", "")
        if c[:3] == ["gh", "pr", "list"] and "--search" in c:
            # #19014 : ``gh pr list --search head:<branche>`` -- liveness
            # de la base. Le ScriptedRunner regarde la cle correspondante
            # dans ``self.base_search`` et rend cette liste (ou [] si
            # non scriptee). ``base_search_rc != 0`` simule un crash gh.
            search_key = next(
                (arg for arg in c if arg.startswith("head:")), None
            )
            if self.base_search_rc != 0:
                return mr.RunResult(self.base_search_rc, "", "gh failed")
            rows = self.base_search.get(search_key or "", [])
            return mr.RunResult(0, json.dumps(rows), "")
        if c[:3] == ["gh", "pr", "list"]:
            rows = []
            for n in self.prs:
                row = {"number": n}
                if (self.coordinator_voices is None
                        or n in self.coordinator_voices):
                    row["latestReviews"] = [{
                        "author": {"login": "myia-ai-01"},
                        "state": "APPROVED",
                        "body": "",
                    }]
                else:
                    row["latestReviews"] = []
                rows.append(row)
            return mr.RunResult(0, json.dumps(rows), "")
        if c[:3] == ["gh", "pr", "view"]:
            if self.view_rc != 0:
                return mr.RunResult(self.view_rc, "", self.view_stderr)
            pr = int(c[3])
            view = self.views.get(pr, default_view(pr=pr))
            return mr.RunResult(0, json.dumps(view), "")
        if c[:2] == ["gh", "api"] and "/pulls/" in c[2] and "/files" in c[2]:
            # #27684 : lecture paginee de la liste des fichiers d'une PR.
            # Le REST nomme le champ `filename` (la vue gh nomme `path`).
            if self.pr_files_rc != 0:
                return mr.RunResult(self.pr_files_rc, "", "gh failed")
            pr = int(c[2].split("/pulls/")[1].split("/")[0])
            per_page = int(c[2].split("per_page=")[1].split("&")[0])
            page = int(c[2].rsplit("page=", 1)[1].split("&")[0])
            chemins = self.pr_files.get(pr, [])
            tranche = chemins[(page - 1) * per_page: page * per_page]
            return mr.RunResult(
                0, json.dumps([{"filename": ch} for ch in tranche]), ""
            )
        if c[:3] == ["gh", "pr", "merge"]:
            if self.merge_script:
                rc, err = self.merge_script.pop(0)
                return mr.RunResult(rc, "", err)
            if self.merge_rc == 0:
                return mr.RunResult(0, "", "")
            return mr.RunResult(self.merge_rc, "", "merge refused")
        if c[:2] == ["gh", "api"] and "/contents/" in c[2]:
            # #27875 : lecture du manifeste des lakes a la TETE de la PR
            # (garde Lean). Defaut = 404 : un manifeste non lu laisse la
            # garde sur son motif generique -- le fail-closed est conserve.
            payload = self.ci_lakes_payload
            if payload is None:
                return mr.RunResult(1, "", "HTTP 404")
            if isinstance(payload, str):
                return mr.RunResult(0, payload, "")
            return mr.RunResult(0, json.dumps(payload), "")
        if c[:2] == ["gh", "api"] and c[2].startswith("users/"):
            # #17437 : sonde d'identite App (``users/<login>[bot] --jq .type``).
            # Defaut = 404 (rc 1) : une sonde non scriptee est un login
            # inconnu, fail-closed cote organe -- meme silence que la vraie
            # API rend pour un utilisateur qui n'existe pas.
            if c[2] in self.user_types:
                return mr.RunResult(0, self.user_types[c[2]] + "\n", "")
            return mr.RunResult(1, "", "HTTP 404")
        if c[:2] == ["gh", "api"] and "/commits/main" in c[2]:
            return mr.RunResult(0, self.main_sha + "\n", "")
        if "search/issues" in c:
            # #26706 : recherche de l'issue canonique du rouge de `main`.
            if self.main_red_search_rc != 0:
                return mr.RunResult(self.main_red_search_rc, "", "search failed")
            return mr.RunResult(
                0,
                json.dumps(
                    {"total_count": len(self.main_red_issues),
                     "items": self.main_red_issues}
                ),
                "",
            )
        if c[:2] == ["gh", "issue"] and c[2] == "create":
            # #26706 : ouverture de l'issue du rouge de `main`.
            if self.main_red_issue_rc != 0:
                return mr.RunResult(self.main_red_issue_rc, "", "create refused")
            number = 26710 + len(self.main_red_created)
            row = {
                "number": number,
                "title": c[c.index("--title") + 1],
                "body": Path(c[c.index("--body-file") + 1]).read_text(encoding="utf-8"),
            }
            self.main_red_created.append(row)
            self.main_red_issues.append(row)
            return mr.RunResult(
                0, f"https://github.com/jsboige/CoursIA/issues/{number}\n", ""
            )
        if c[:2] == ["gh", "issue"] and c[2] == "close":
            # #26706 : fermeture de l'issue du rouge de `main`.
            if self.main_red_issue_rc != 0:
                return mr.RunResult(self.main_red_issue_rc, "", "close refused")
            number = int(c[3])
            self.main_red_closed.append(number)
            self.main_red_issues = [
                row for row in self.main_red_issues if row["number"] != number
            ]
            return mr.RunResult(0, "", "")
        if c[:2] == ["gh", "issue"] and c[2] == "edit":
            if self.main_red_issue_rc != 0:
                return mr.RunResult(self.main_red_issue_rc, "", "edit refused")
            number = int(c[3])
            for row in self.main_red_issues:
                if row["number"] != number:
                    continue
                if "--title" in c:
                    row["title"] = c[c.index("--title") + 1]
                if "--body-file" in c:
                    row["body"] = Path(
                        c[c.index("--body-file") + 1]
                    ).read_text(encoding="utf-8")
            return mr.RunResult(0, "", "")
        if c[:3] == ["gh", "issue", "view"]:
            # #26706 : lecture de l'ETAT d'une issue [main-red] connue par
            # son numero (`_read_main_red_issue`). Les trois etats doivent
            # etre scriptingables : `ok` (payload conforme), `absent` (le
            # numero rendu ne correspond pas a celui demande) et
            # `illisible` (rc non nul, ou stdout malforme).
            if self.main_red_view_rc != 0:
                return mr.RunResult(self.main_red_view_rc, "", "view refused")
            number = int(c[3])
            scripted = self.main_red_views.get(number)
            if scripted is not None:
                if isinstance(scripted, str):
                    return mr.RunResult(0, scripted, "")
                return mr.RunResult(0, json.dumps(scripted), "")
            # Issue non scriptee : l'etat REEL du runner fait foi (comme
            # pour la recherche), sinon la lecture est un refus.
            for row in self.main_red_issues:
                if row["number"] == number:
                    return mr.RunResult(0, json.dumps({
                        "number": row["number"],
                        "title": row.get("title", ""),
                        "body": row.get("body", ""),
                        "state": row.get("state", "OPEN"),
                    }), "")
            return mr.RunResult(1, "", "issue introuvable")
        if c[:3] == ["gh", "issue", "reopen"]:
            # #26706 : rouverture d'une issue [main-red] fermee a tort, le
            # rouge tenant toujours au commit courant.
            if self.main_red_issue_rc != 0:
                return mr.RunResult(self.main_red_issue_rc, "", "reopen refused")
            number = int(c[3])
            self.main_red_reopened.append(number)
            for row in self.main_red_issues:
                if row["number"] == number:
                    row["state"] = "OPEN"
            return mr.RunResult(0, "", "")
        if c[:2] == ["gh", "api"] and "/commits?sha=" in c[2]:
            # Historique de main lu par la sentinelle (le plus recent d'abord).
            return mr.RunResult(0, "\n".join(self.main_history) + "\n", "")
        if c[:2] == ["gh", "api"] and "/check-runs" in c[2]:
            sha = c[2].split("/commits/", 1)[1].split("/", 1)[0]
            if sha == self.main_sha or sha in self.main_history:
                payload = self.main_checks_by_sha.get(sha, self.main_check_runs)
                return mr.RunResult(0, "\n".join(
                    json.dumps(row) for row in json.loads(payload)
                ), "")
            return mr.RunResult(0, self.check_runs, "")
        if c[:2] == ["gh", "api"] and "/check-runs" in c[2]:
            # #25059 : etape 6 bis. La branche est AVANT celle des commits :
            # l'URL des check-runs porte `/commits/` et serait capturee par
            # elle (le SHA extrait serait `check-runs?per_page=100`).
            return mr.RunResult(0, self.check_runs, "")
        if c[:2] == ["gh", "api"] and "/actions/jobs/" in c[2]:
            # #25510 T-J : etapes du job associe au check-run. La reponse
            # est la LISTE des etapes (nom `n`, numero `o`, statut `s`,
            # conclusion `c`). La forme historique (une chaine) reste
            # acceptee : elle vaut UNE etape en echec.
            job_id = c[2].rsplit("/", 1)[-1]
            rc = self.job_steps_rc.get(job_id, 0)
            if rc != 0:
                return mr.RunResult(rc, "", "gh failed")
            scripted = self.job_steps.get(job_id, [])
            if isinstance(scripted, str):
                steps = ([{"n": scripted, "o": 1, "s": "completed",
                           "c": "failure"}] if scripted else [])
            else:
                steps = list(scripted)
            return mr.RunResult(0, json.dumps(steps), "")
        if c[:3] == ["gh", "run", "view"]:
            # Log d'echec du run : la sentinelle le lit quand le resume du
            # check-run ne nomme aucun test.
            return mr.RunResult(0, self.run_log, "")
        if c[:2] == ["gh", "api"] and "/commits/" in c[2]:
            sha = c[2].rsplit("/", 1)[-1]
            if sha not in self.commits:
                return mr.RunResult(1, "", "HTTP 404")
            return mr.RunResult(0, json.dumps(self.commits[sha]), "")
        if c[:1] == ["git"] and "merge-tree" in c:
            if self.auto_tree is None:
                return mr.RunResult(1, "", "conflict")
            return mr.RunResult(0, self.auto_tree + "\n", "")
        if c[:1] == ["git"] and ("cat-file" in c or "merge-base" in c):
            return mr.RunResult(0, "", "")
        if (c[:2] == ["gh", "api"] and "/pulls/" in c[2]
                and c[2].split("?", 1)[0].endswith("/reviews")):
            # #17437 : surface REST typee des reviews (preuve de type PAR
            # LIGNE, relecture ai-01 2026-11-12). DOIT preceder la branche
            # generique ``/pulls/`` (mergeable_state) : l'URL porte aussi
            # ``/pulls/``. ``--slurp`` rend une liste de pages.
            return mr.RunResult(
                0, json.dumps([list(self.rest_reviews)]), "")
        if c[:2] == ["gh", "api"] and "/pulls/" in c[2] and "--jq" in c:
            # Rechauffage (#26799) : lecture a EFFET DE BORD -- elle demarre
            # le calcul de mergeabilite de la PR cote GitHub. Elle ne consomme
            # donc PAS la pile des etats : la pile alimente les lectures qui,
            # elles, portent un etat a faire valoir.
            pr = int(c[2].rsplit("/", 1)[1])
            return mr.RunResult(
                0, (self.warmup_states.get(pr, "unknown") + "\n"), ""
            )
        if c[:2] == ["gh", "api"] and "/pulls/" in c[2]:
            row = self.pulls.pop(0) if len(self.pulls) > 1 else self.pulls[0]
            return mr.RunResult(0, json.dumps(row), "")
        if len(c) > 1 and "check_unaddressed_nits.py" in c[1]:
            return mr.RunResult(self.nits_rc, "", "")
        if c[:1] == ["git"] and "fetch" in c:
            return mr.RunResult(self.fetch_rc, "", "")
        if c[:1] == ["git"] and "rev-parse" in c:
            # La base RESOLUE du contexte de passe (22/11).
            return mr.RunResult(0, self.main_sha + "\n", "")
        if c[:1] == ["git"] and "worktree" in c:
            # Retrait du worktree de passe : rien a faire dans un test.
            return mr.RunResult(0, "", "")
        if len(c) > 1 and "check_twin_index_collisions.py" in c[1]:
            return mr.RunResult(self.twin_rc, self.twin_stdout, "")
        if len(c) > 1 and "check_twin_attestation_squash.py" in c[1]:
            return mr.RunResult(self.attest_rc, self.attest_stdout, "")
        if len(c) > 1 and "twin_open_claims.py" in c[1]:
            return mr.RunResult(self.claims_rc, self.claims_stdout, "")
        if len(c) > 1 and "check_slot_reservation.py" in c[1]:
            return mr.RunResult(self.slot_rc, self.slot_stdout, "")
        if len(c) > 1 and "premerge_combined_check.py" in c[1]:
            return mr.RunResult(self.combined_rc, self.combined_stdout, "")
        raise AssertionError("commande non scriptee : " + " ".join(c))

    def sleep(self, seconds: float) -> None:
        self.sleeps.append(seconds)

    def run_many(
        self, cmds: list[list[str]], env: dict | None = None
    ) -> list[mr.RunResult]:
        """Lectures en parallele : le fake les sert SEQUENTIELLEMENT.

        L'ordre reste deterministe (une course ici rendrait les assertions
        sur l'ordre des lectures_flaky), et le parallélisme reel n'est
        mesure que par le runner de production.
        """
        return [self.run(cmd, env) for cmd in cmds]


def run_organ(tmp_path: Path, runner: ScriptedRunner, extra: tuple[str, ...] = ()) -> tuple[int, list[dict], Path]:
    """Lance un run avec journal isole ; retourne (rc, lignes de journal, chemin)."""
    journal = tmp_path / "journal.jsonl"
    rc = mr.run(["--journal", str(journal), *extra], runner=runner)
    lines = []
    if journal.is_file():
        lines = [json.loads(row) for row in journal.read_text(encoding="utf-8").splitlines() if row.strip()]
    return rc, lines, journal


def _mergeable_reads(runner: ScriptedRunner) -> list[list[str]]:
    """Lectures de mergeabilite QUI PORTENT UN ETAT.

    Le rechauffage (#26799) est une lecture a effet de bord : elle ne porte
    aucun etat et ne se compte donc pas ici.
    """
    return [
        cmd for cmd in runner.cmds()
        if cmd[:2] == ["gh", "api"] and "/pulls/" in cmd[2]
        and "--jq" not in cmd
        and not cmd[2].split("?", 1)[0].endswith("/reviews")
        # #27684 : la lecture paginee des FICHIERS (`/pulls/{n}/files`) n'est
        # pas une lecture de mergeabilite.
        and not cmd[2].split("?", 1)[0].endswith("/files")
    ]


def _warmup_reads(runner: ScriptedRunner) -> list[list[str]]:
    """Lectures de RECHAUFFAGE (#26799) : une par PR, sans attente."""
    return [
        cmd for cmd in runner.cmds()
        if cmd[:2] == ["gh", "api"] and "/pulls/" in cmd[2] and "--jq" in cmd
    ]


def _evaluated(runner: ScriptedRunner, pr: int) -> list[list[str]]:
    """Commandes qui EVALUENT une PR (vue, merge).

    Le rechauffage (#26799) n'en fait pas partie : c'est une lecture a effet
    de bord, sans etat a faire valoir et sans verdict -- une PR « touchee »
    par le rechauffage n'est pas une PR evaluee.
    """
    return [
        cmd for cmd in runner.cmds()
        if (cmd[:3] == ["gh", "pr", "view"] and cmd[3] == str(pr))
        or (cmd[:3] == ["gh", "pr", "merge"] and cmd[3] == str(pr))
    ]


# --- chaque raison de skip, une par une ----------------------------------------


def test_skip_draft(tmp_path):
    runner = ScriptedRunner(views={123: default_view(draft=True)})
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert lines[-1]["verdict"] == "skipped" and lines[-1]["reason"] == "draft"
    # les organes couteux ne sont jamais appeles sur un brouillon
    assert not any("check_unaddressed_nits.py" in flat for flat in runner.flat())


def test_pr_sans_aucun_dossier_comment_merges(tmp_path):
    """Retrait du dossier (2026-11-05) : une PR SANS AUCUN commentaire
    ``[ADJOINT PREFLIGHT]``, avec l'approbation ``myia-ai-01`` a la tete et
    toutes les portes vertes, rend ``would-merge`` -- le dossier n'est plus
    une condition d'entree, chaque fait qu'il attestait est revifie au
    merge."""
    view = default_view(comments=[{"body": "un commentaire de lane ordinaire"}])
    runner = ScriptedRunner(views={123: view})
    rc, lines, _ = run_organ(tmp_path, runner)  # dry-run : would-merge
    assert rc == 0
    assert lines[-1]["verdict"] == "would-merge"
    assert lines[-1]["reason"] is None
    assert lines[-1]["stack"] == "measured"
    assert "stack_incidents" not in lines[-1]


def test_skip_file_under_claude_dir(tmp_path):
    runner = ScriptedRunner(views={123: default_view(files=(".claude/rules/x.md",))})
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert lines[-1]["reason"].startswith("scope:.claude:")


def test_skip_file_claude_md_any_dir(tmp_path):
    for path in ("CLAUDE.md", "docs/reference/CLAUDE.md"):
        runner = ScriptedRunner(views={123: default_view(files=("src/a.py", path))})
        rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
        assert rc == 0, path
        assert lines[-1]["reason"].startswith("scope:CLAUDE.md"), path


def test_skip_file_under_github_dir(tmp_path):
    runner = ScriptedRunner(views={123: default_view(files=(".github/workflows/a.yml",))})
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert lines[-1]["reason"].startswith("scope:.github:")


def test_skip_frozen_umbrella_in_title(tmp_path):
    # #17021 : mergee sous le veto densite #17040 sur un dossier READY.
    # #13410 ROUVERT le 2026-10-07 : le skip se mesure sur #11601, seul gele.
    view = default_view(title="enrich(qc,#11601): densite QC-Py-06b — tranche g2")
    runner = ScriptedRunner(views={123: view})
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert lines[-1]["reason"] == "frozen:#11601(veto #17040)"
    assert not any("check_unaddressed_nits.py" in flat for flat in runner.flat())
    assert not any(" merge " in f" {flat} " for flat in runner.flat())


def test_skip_frozen_umbrella_in_body(tmp_path):
    view = default_view(body=GRAIN_MED + "\n\nSee #11601 (densite QC).")
    runner = ScriptedRunner(views={123: view})
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert lines[-1]["reason"] == "frozen:#11601(veto #17040)"


def test_frozen_umbrella_prefix_number_not_matched():
    # #13410 ne gele plus (reouverture user 2026-10-07) ; le garde-fou (?!\d)
    # se mesure sur #11601, seul parapluie gele en vie.
    assert mr.frozen_umbrella_exclusion("fix: #13410.", None) is None
    assert mr.frozen_umbrella_exclusion("fix: #116010", "voir #116011") is None
    assert mr.frozen_umbrella_exclusion("fix: #11601.", None) is not None


def test_frozen_umbrella_qc_density_round2():
    # #11601 gele le 2026-09-23 sous le meme veto #17040 (#17386 en est la PR ouverte).
    assert (
        mr.frozen_umbrella_exclusion("enrich(qc,#11601): densite QC-Py-06b", None)
        == "frozen:#11601(veto #17040)"
    )
    assert mr.frozen_umbrella_exclusion("fix: #116010", None) is None


def test_grain_deep_approuve_passe_le_filtre(tmp_path):
    # Q131 (2026-10-19) : DEEP entre dans le perimetre, sous l'approbation
    # prealable du coordinateur posee a la tete (default_view la fournit).
    runner = ScriptedRunner(views={123: default_view(body=GRAIN_DEEP)})
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert lines[-1]["verdict"] == "merged" and lines[-1]["merged"] is True


def test_grain_deep_sans_approbation_du_coordinateur_skip(tmp_path):
    # Q131 : rien ne se merge sans la validation prealable du coordinateur.
    runner = ScriptedRunner(views={123: default_view(body=GRAIN_DEEP, coordinator=None)})
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert lines[-1]["reason"] == "no-coordinator-approval"
    assert lines[-1]["merged"] is False


def test_hors_flotte_sans_tag_approuve_passe_le_filtre(tmp_path):
    # Q131 : une PR de la session cloud (branche claude/*) n'a pas de tag
    # Grain ; l'absence de tag ne l'exclut plus, l'approbation la gouverne.
    view = default_view(body="Hors flotte -- session cloud.", head_ref="claude/fix-readme-links")
    runner = ScriptedRunner(views={123: view})
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert lines[-1]["verdict"] == "merged" and lines[-1]["merged"] is True


def test_hors_flotte_sans_approbation_du_coordinateur_skip(tmp_path):
    view = default_view(
        body="Hors flotte -- session cloud.",
        head_ref="claude/fix-readme-links",
        coordinator=None,
    )
    runner = ScriptedRunner(views={123: view})
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert lines[-1]["reason"] == "no-coordinator-approval"
    assert lines[-1]["merged"] is False


def test_grain_exclusion_prefixe_claude_strict():
    # Seul le prefixe de branche exact ouvre l'exemption de tag.
    assert mr.grain_exclusion("pas de tag", "claude/x") is None
    assert mr.grain_exclusion("pas de tag", "feature/claude/x") == "grain-tier-unparsable"
    assert mr.grain_exclusion("pas de tag", None) == "grain-tier-unparsable"


def test_skip_grain_unparsable(tmp_path):
    runner = ScriptedRunner(views={123: default_view(body="Aucun tag Grain dans ce corps.")})
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert lines[-1]["reason"] == "grain-tier-unparsable"


def test_skip_grain_tier_hors_grammaire_fail_closed(tmp_path):
    # Tier lisible mais hors (DEEP, MED, LIGHT) : la grammaire ne le connait
    # pas, fail-closed (le mandat couvre DEEP et l'illisible ; l'inconnu
    # l'est aussi).
    runner = ScriptedRunner(
        views={123: default_view(body="Grain: ULTRA/x -- lane myia-po-2026:CoursIA")}
    )
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert lines[-1]["reason"].startswith("grain-tier-unknown:")


def test_skip_grain_light_passe_le_filtre(tmp_path):
    # LIGHT est dans le perimetre (b) : la PR arrive jusqu'au merge.
    runner = ScriptedRunner(
        views={123: default_view(body="Grain: LIGHT/guard -- lane myia-po-2026:CoursIA")}
    )
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert lines[-1]["verdict"] == "merged" and lines[-1]["merged"] is True


def test_skip_b0_organ_rc1(tmp_path):
    runner = ScriptedRunner(nits_rc=1)
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert lines[-1]["reason"] == "b0-organ-blocked"
    assert not any(c[:3] == ["gh", "pr", "merge"] for c in runner.cmds())


def test_skip_mergeable_state_not_clean(tmp_path):
    # `unstable` n'est plus dans cette liste : il a son etage a lui (#25059,
    # les quatre tests juste apres) -- il se decide sur les jambes, pas sur
    # le seul libelle de l'etat.
    for state in ("dirty", "blocked", "has_hooks"):
        runner = ScriptedRunner(
            pulls=[{"mergeable_state": state, "head": {"sha": HEAD}}]
        )
        rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
        assert rc == 0, state
        assert lines[-1]["reason"] == f"mergeable-state:{state}", state
        assert not any(c[:3] == ["gh", "pr", "merge"] for c in runner.cmds())


def test_prelecture_blocked_evite_les_tests_d_arbre_fusionne(tmp_path):
    runner = ScriptedRunner(
        pulls=[{"mergeable_state": "blocked", "head": {"sha": HEAD}}]
    )
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert lines[-1]["verdict"] == "skipped"
    assert lines[-1]["reason"] == "mergeable-state:blocked"
    assert not any("premerge_combined_check.py" in flat for flat in runner.flat())
    assert not any(c[:3] == ["gh", "pr", "merge"] for c in runner.cmds())


def test_prelecture_clean_puis_garde_finale_joue_les_tests_d_arbre(tmp_path):
    runner = ScriptedRunner()
    rc, lines, _ = run_organ(tmp_path, runner)
    assert rc == 0
    assert lines[-1]["verdict"] == "would-merge"
    assert lines[-1]["reason"] is None
    assert any("premerge_combined_check.py" in flat for flat in runner.flat())


def test_prelecture_unstable_ne_saute_pas_les_tests_d_arbre(tmp_path):
    runner = _unstable_runner(DEFAULT_CHECK_RUNS)
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert lines[-1]["verdict"] == "merged"
    assert any("premerge_combined_check.py" in flat for flat in runner.flat())


def test_prelecture_tete_deplacee_evite_les_tests_d_arbre_fusionne(tmp_path):
    runner = ScriptedRunner(
        pulls=[{"mergeable_state": "clean", "head": {"sha": HEAD_MOVED}}]
    )
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert lines[-1]["verdict"] == "skipped"
    assert lines[-1]["reason"] == "head-moved"
    assert not any("premerge_combined_check.py" in flat for flat in runner.flat())


# --- etape 6 bis : `unstable` (#25059) -------------------------------------------


def _legs(*rows: dict) -> str:
    """stdout du `gh api .../check-runs` : une ligne JSON par jambe."""
    return "\n".join(json.dumps(row) for row in rows)


def _unstable_runner(check_runs: str) -> ScriptedRunner:
    return ScriptedRunner(
        pulls=[{"mergeable_state": "unstable", "head": {"sha": HEAD}}],
        check_runs=check_runs,
    )


def test_unstable_latest_wins_vert_est_accepte(tmp_path):
    # Pli vert partout : la PR passe, et le journal dit pourquoi elle passait
    # (`unstable-accepted:<n>`) -- un merge mu n'apporte aucune preuve.
    runner = _unstable_runner(DEFAULT_CHECK_RUNS)
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert lines[-1]["verdict"] == "merged"
    assert lines[-1]["reason"].startswith("unstable-accepted:")
    assert any(c[:3] == ["gh", "pr", "merge"] for c in runner.cmds())


def test_unstable_une_jambe_non_advisory_rouge_saute_nomme(tmp_path):
    legs = _legs(
        {"name": "PR gate", "conclusion": "success", "status": "completed",
         "started_at": "2026-11-07T10:00:00Z", "id": 4},
        {"name": "Scripts Tests (CPU)", "conclusion": "failure",
         "status": "completed", "started_at": "2026-11-07T10:00:00Z", "id": 5},
    )
    runner = _unstable_runner(legs)
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert lines[-1]["reason"] == (
        "mergeable-state:unstable:Scripts Tests (CPU):failure"
    )
    assert not any(c[:3] == ["gh", "pr", "merge"] for c in runner.cmds())


def test_unstable_un_rouge_advisory_seul_est_accepte(tmp_path):
    # Un check advisory ne bloque pas le gate (#15548) : il ne doit pas
    # bloquer l'organe de merge non plus.
    legs = _legs(
        {"name": "PR gate", "conclusion": "success", "status": "completed",
         "started_at": "2026-11-07T10:00:00Z", "id": 4},
        {"name": "CJK residue advisory (label, non-blocking)",
         "conclusion": "failure", "status": "completed",
         "started_at": "2026-11-07T10:00:00Z", "id": 5},
    )
    runner = _unstable_runner(legs)
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert lines[-1]["verdict"] == "merged"
    assert lines[-1]["reason"].startswith("unstable-accepted:")


def test_unstable_une_jambe_en_vol_sans_jambe_terminee_saute(tmp_path):
    # Une jambe en vol dont le nom n'a AUCUNE jambe terminee : rien n'a ete
    # mesure pour ce nom, donc rien n'est acquis -- saut nomme.
    legs = _legs(
        {"name": "PR gate", "conclusion": "success", "status": "completed",
         "started_at": "2026-11-07T10:00:00Z", "id": 4},
        {"name": "Scripts Tests (CPU)", "conclusion": "",
         "status": "in_progress", "started_at": "2026-11-07T10:00:00Z",
         "id": 5},
    )
    runner = _unstable_runner(legs)
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert lines[-1]["reason"] == (
        "mergeable-state:unstable:Scripts Tests (CPU):no-completed-leg"
    )
    assert not any(c[:3] == ["gh", "pr", "merge"] for c in runner.cmds())


def test_skip_head_moved(tmp_path):
    # mergeable_state clean mais la tete REST n'est plus celle de la vue,
    # celle que l'approbation couvre : skip nomme.
    runner = ScriptedRunner(
        pulls=[{"mergeable_state": "clean", "head": {"sha": HEAD_MOVED}}]
    )
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert lines[-1]["reason"] == "head-moved"


# --- retry unknown -> clean ------------------------------------------------------


def test_mergeable_unknown_then_clean_merges(tmp_path):
    runner = ScriptedRunner(
        pulls=[
            {"mergeable_state": "unknown", "head": {"sha": HEAD}},
            {"mergeable_state": "clean", "head": {"sha": HEAD}},
        ]
    )
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert lines[-1]["verdict"] == "merged" and lines[-1]["merged"] is True
    # 2 lectures en prelecture (unknown puis clean), 1 garde finale clean,
    # et un seul sommeil entre les deux lectures `unknown` et `clean`.
    assert len(_mergeable_reads(runner)) == 3
    assert runner.sleeps == [mr.MERGEABLE_RETRY_SLEEP_S]


def test_mergeable_unknown_persistant_skippe(tmp_path):
    runner = ScriptedRunner(
        pulls=[{"mergeable_state": "unknown", "head": {"sha": HEAD}}]
    )
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert lines[-1]["reason"] == "mergeable-state:unknown"
    # Budget COURT a son tour (3 lectures), puis rejeu avec le budget LONG
    # (13 lectures) : ce n'est plus une attente serielle de 120 s dans la
    # passe, c'est un PARKING suivi d'un rejeu en fin de passe (#26799).
    assert len(_mergeable_reads(runner)) == (
        mr.MERGEABLE_SHORT_RETRIES + 1 + mr.MERGEABLE_RETRIES + 1
    )
    assert len(runner.sleeps) == (
        mr.MERGEABLE_SHORT_RETRIES + mr.MERGEABLE_RETRIES
    )
    # La PR est parsee puis rejouee : UNE seule ligne de journal, portant le
    # verdict final -- le parking n'est pas un verdict.
    assert len(lines) == 1


# --- rechauffage, budget court, rejeu (#26799) -----------------------------------
#
# Mesure du 16/11 (ai-01) : l'etat de mergeabilite d'une PR passe de `unknown`
# a `clean`/`blocked` en 10 a 20 s, SANS intervention -- le calcul se fait seul
# cote GitHub. L'organe attendait 120 s sur chaque PR rencontree, et chaque
# merge rebascule les PRs soeurs en `unknown` : 28 PRs sur 132 portaient 90 %
# du passage (1 h 41).
#
# Le correctif ne touche pas la GARANTIE (la mergeabilite est relue au moment
# du merge) ; il change QUAND la lecture a lieu.


def test_le_rechauffage_est_emis_en_tete_de_passe(tmp_path):
    """Une lecture sans attente par PR ouverte : elle demarre le calcul de
    mergeabilite de chaque PR, en parallele, au lieu qu'elles soient servies
    une par une par la passe."""
    runner = ScriptedRunner(prs=(101, 102, 103))
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    warm = _warmup_reads(runner)
    assert len(warm) >= 3
    assert [int(cmd[2].rsplit("/", 1)[1]) for cmd in warm[:3]] == [101, 102, 103]


def test_le_rechauffage_rechauffe_les_prs_restantes_apres_chaque_merge(tmp_path):
    """C'est le MERGE qui rebascule les PRs soeurs en `unknown` : le
    rechauffage suit donc chaque merge, sur les PRs restantes seulement."""
    runner = ScriptedRunner(prs=(101, 102, 103))
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    numbers = [int(cmd[2].rsplit("/", 1)[1]) for cmd in _warmup_reads(runner)]
    # tete de passe : les 3 PRs ; puis, apres le merge de 101 : 102 et 103 ;
    # apres le merge de 102 : 103 ; apres le merge de 103 : plus rien.
    assert numbers == [101, 102, 103, 102, 103, 103]


# --- restriction du rechauffage aux candidates (revue du 16/11) ----------------
#
# Le rechauffage de TOUT le pool ouvert coutait ~1 500 lectures REST par
# passage (178 PRs en tete de passe, puis toutes les restantes apres chaque
# merge), sous le jeton que le coordinateur partage avec l'attestation Lean
# et les relectures (05:06Z : 1 879 restants sur 5 000). Seules les PRs qui
# peuvent atteindre l'etape 6 (la lecture de mergeabilite) ont besoin d'etre
# rechauffees : celles qui portent une voix du coordinateur.


def test_le_rechauffage_ne_touche_que_les_prs_avec_une_voix_du_coordinateur(tmp_path):
    """Une PR sans approbation s'arrete a l'etape 2 : la rechauffer
    consommerait le jeton partage pour rien."""
    runner = ScriptedRunner(prs=(301, 302, 303), coordinator_voices=(302,))
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    numbers = sorted({
        int(cmd[2].rsplit("/", 1)[1]) for cmd in _warmup_reads(runner)
    })
    assert numbers == [302]


def test_le_cout_du_rechauffage_est_nomme_dans_le_bilan(tmp_path, capsys):
    """Le nombre de lectures REST du rechauffage est publie : c'est lui qui
    pesait sur le jeton partage (revue du 16/11)."""
    runner = ScriptedRunner(prs=(401, 402), coordinator_voices=(401,))
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    out = capsys.readouterr().out
    assert "rechauffage :" in out
    assert "1 candidate(s)" in out
    assert "pool ouvert : 2 PRs" in out


def test_les_candidates_se_lisent_dans_la_lecture_de_liste():
    """Le critere : une voix du coordinateur, approuvante ou commentant apres
    avoir approuve. Une reserve (`CHANGES_REQUESTED`) ne candidate pas."""
    rows = [
        {"number": 1, "latestReviews": [
            {"author": {"login": "myia-ai-01"}, "state": "APPROVED", "body": ""}]},
        {"number": 2, "latestReviews": [
            {"author": {"login": "myia-ai-01"}, "state": "COMMENTED",
             "body": "leve la reserve, la PR est approuvee"}]},
        {"number": 3, "latestReviews": [
            {"author": {"login": "myia-ai-01"}, "state": "CHANGES_REQUESTED",
             "body": ""}]},
        {"number": 4, "latestReviews": [
            {"author": {"login": "autre-lane"}, "state": "APPROVED", "body": ""}]},
        {"number": 5, "latestReviews": []},
    ]
    assert mr.warm_up_candidates(rows) == [1, 2]


def test_un_comment_qui_porte_un_verdict_reserve_ne_candidate_pas():
    """Le canal du jeton du cluster porte son verdict dans le CORPS : un
    COMMENT qui dit CONCERNS n'est pas une approbation."""
    rows = [
        {"number": 7, "latestReviews": [
            {"author": {"login": "myia-ai-01"}, "state": "COMMENTED",
             "body": "[Hermes] COMMENT_WITH_CONCERNS"}]},
    ]
    assert mr.warm_up_candidates(rows) == []


def test_la_lecture_de_liste_porte_desormais_les_dernieres_reviews(tmp_path):
    """UNE SEULE lecture de liste : elle porte aussi `latestReviews`, sinon le
    choix des candidates coute un appel REST par PR."""
    runner = ScriptedRunner(prs=(501,))
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    list_cmds = [cmd for cmd in runner.cmds() if cmd[:3] == ["gh", "pr", "list"]]
    assert list_cmds
    assert "number,latestReviews" in list_cmds[0]


def test_lordre_des_merges_est_inchange(tmp_path):
    """Le rechauffage ne reordonne rien : les merges se font dans l'ordre de
    la liste, comme avant."""
    runner = ScriptedRunner(prs=(201, 202, 203))
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    merged = [
        int(cmd[3]) for cmd in runner.cmds() if cmd[:3] == ["gh", "pr", "merge"]
    ]
    assert merged == [201, 202, 203]
    assert [row["pr"] for row in lines] == [201, 202, 203]


def test_le_passage_normal_ne_paie_plus_l_attente_de_120_s(tmp_path):
    """Le cas nominal : l'etat est defini, la PR est lue et mergee sans
    aucune attente. Avant #26799, un etat `unknown` coteait 120 s par PR."""
    runner = ScriptedRunner(prs=(123,))
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert runner.sleeps == []
    # prelecture + garde finale : deux lectures, pas plus.
    assert len(_mergeable_reads(runner)) == 2


def test_une_pr_parsee_puis_rejouee_est_mergee_au_rejeu(tmp_path):
    """Une PR dont l'etat etait en cours de calcul a son tour n'est pas
    COMPTEe COMME UN REFUS : elle est parsee, puis rejouee en fin de passe,
    ou son calcul est termine -- et elle est alors mergee.

    Avant #26799, l'organe attendait 120 s sur cette PR, puis la skippait
    (`mergeable-state:unknown`) : une PR mergeable perdait un passage.
    """
    runner = ScriptedRunner(
        prs=(301, 302),
        pulls=[
            {"mergeable_state": "unknown", "head": {"sha": HEAD}},  # 301, prelecture
            {"mergeable_state": "unknown", "head": {"sha": HEAD}},  # 301, relecture
            {"mergeable_state": "unknown", "head": {"sha": HEAD}},  # 301, relecture
            {"mergeable_state": "clean", "head": {"sha": HEAD}},    # 302, puis rejeu de 301
        ],
    )
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    # Les DEUX PRs sont mergees : celle qui etait parsee d'abord, puis celle
    # qui l'a ete apres. L'ordre du rejeu est la seule consequence de forme
    # du correctif (la garantie, elle, est intacte : l'etat est relu au
    # moment du merge).
    merged = [
        int(cmd[3]) for cmd in runner.cmds() if cmd[:3] == ["gh", "pr", "merge"]
    ]
    assert merged == [302, 301]
    assert all(row["verdict"] == "merged" for row in lines)
    assert len(lines) == 2


def test_un_etat_absent_n_est_plus_un_refus_immediat(tmp_path):
    """`mergeable_state: null` (l'absence de valeur) signifie « calcul en
    cours », pas « refus » : avant #26799, l'organe sortait de la lecture
    la-dessus et skippait la PR sans attendre -- il evaluait une PR
    mergeable avant la fin de son calcul.

    Mesure du 16/11 : `#26829` et `#26827` sont passees de `unknown` a
    `blocked`/`clean` en moins de 20 s.
    """
    runner = ScriptedRunner(
        prs=(123,), pulls=[{"head": {"sha": HEAD}}]  # pas de mergeable_state
    )
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    # L'absence de valeur est traitee comme un etat EN COURS DE CALCUL : la
    # PR est parsee puis rejouee, avec le budget court puis le budget long.
    assert len(_mergeable_reads(runner)) == (
        mr.MERGEABLE_SHORT_RETRIES + 1 + mr.MERGEABLE_RETRIES + 1
    )
    assert lines[-1]["reason"] == "mergeable-state:absent"


def test_le_rejeu_dispose_du_budget_long(tmp_path):
    """Le budget long est RESERVE au rejeu : c'est la que l'etat a eu le
    temps de se calculer."""
    runner = ScriptedRunner(
        prs=(123,), pulls=[{"mergeable_state": "unknown", "head": {"sha": HEAD}}]
    )
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    # budget court (passe normale) + budget long (rejeu)
    assert len(runner.sleeps) == (
        mr.MERGEABLE_SHORT_RETRIES + mr.MERGEABLE_RETRIES
    )


def test_une_passe_arretee_ne_perd_pas_les_prs_parquees(tmp_path):
    """Si la passe s'arrete (disjoncteur), les PRs parkees sont journalisees
    telles quelles : une PR ne disparait pas du bilan."""
    runner = ScriptedRunner(
        prs=(123, 124),
        pulls=[{"mergeable_state": "unknown", "head": {"sha": HEAD}}],
    )
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply", "--max", "0"))
    assert rc == 0
    assert [row["pr"] for row in lines] == []
    # --max 0 : la passe n'evalue rien, le journal est vide.
    assert not _evaluated(runner, 123)


# --- dry-run et --apply -----------------------------------------------------------


def test_dry_run_merges_rien(tmp_path):
    runner = ScriptedRunner()
    rc, lines, _ = run_organ(tmp_path, runner, extra=())  # pas de --apply
    assert rc == 0
    # tous les controles lecture-only sont passes (la porte STACK est
    # exercee en processus -- son etat est journalise)...
    assert lines[-1]["stack"] == "measured"
    assert any("check_unaddressed_nits.py" in flat for flat in runner.flat())
    # ...mais AUCUN merge
    assert not any(c[:3] == ["gh", "pr", "merge"] for c in runner.cmds())
    assert lines[-1]["verdict"] == "would-merge" and lines[-1]["merged"] is False


def test_apply_merge_commande_canonique(tmp_path):
    runner = ScriptedRunner()
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert lines[-1]["verdict"] == "merged" and lines[-1]["merged"] is True
    merge_cmds = [c for c in runner.cmds() if c[:3] == ["gh", "pr", "merge"]]
    assert len(merge_cmds) == 1
    cmd = merge_cmds[0]
    assert "--repo" in cmd and cmd[cmd.index("--repo") + 1] == "jsboige/CoursIA"
    assert "--squash" in cmd
    assert "--match-head-commit" in cmd and cmd[cmd.index("--match-head-commit") + 1] == HEAD
    assert "--delete-branch" not in cmd
    assert "--admin" not in cmd


def test_max_arrete_le_run(tmp_path):
    runner = ScriptedRunner(prs=(101, 102))
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply", "--max", "1"))
    assert rc == 0
    merge_cmds = [c for c in runner.cmds() if c[:3] == ["gh", "pr", "merge"]]
    assert len(merge_cmds) == 1
    # la seconde PR n'est meme pas evaluee une fois le plafond atteint
    # (le rechauffage la LIT, sans l'evaluer : il ne porte aucun verdict)
    assert not _evaluated(runner, 102)
    assert [row["pr"] for row in lines] == [101]


# --- borne de duree de la passe (#28009) ------------------------------------------


def _fake_clock(step_s: float):
    """Horloge factice : chaque lecture avance de ``step_s`` secondes.

    La borne de duree se lit sur ``mr._clock`` ; un test doit pouvoir la
    faire avancer sans attendre 45 minutes.
    """
    state = {"t": 0.0}

    def clock() -> float:
        state["t"] += step_s
        return state["t"]

    return clock


def _payload(capsys) -> dict:
    """Payload JSON du run (dernière ligne non vide de stdout)."""
    lines = [ln for ln in capsys.readouterr().out.splitlines() if ln.strip()]
    return json.loads(lines[-1])


def test_le_budget_de_passe_arrete_la_passe_et_journalise_le_reste(
    tmp_path, monkeypatch, capsys
):
    """Budget de duree epuise : arret PROPRE, et les PRs non evaluees sont
    journalisees avec un motif nomme -- jamais une PR disparue du bilan.

    L'horloge factice avance de 100 s par lecture : le budget de 250 s est
    epuise a la TROISIEME lecture de la boucle, donc apres deux PRs
    evaluees. La troisieme PR n'est jamais atteinte.
    """
    monkeypatch.setattr(mr, "_clock", _fake_clock(100.0))
    runner = ScriptedRunner(prs=(101, 102, 103))
    rc, lines, _ = run_organ(
        tmp_path, runner, extra=("--pass-budget-s", "250", "--json")
    )
    assert rc == 0
    payload = _payload(capsys)
    # Le motif d'arret distingue la DUREE du nombre de merges.
    assert payload["stopped_reason"] == mr.PASS_BUDGET_REASON
    # Les deux PRs atteintes sont evaluees normalement ; la troisieme est
    # journalisee avec le meme motif, et un verdict qui dit qu'elle n'a pas
    # ete evaluee (elle ne porte aucun cout d'evaluation).
    assert [row["pr"] for row in lines] == [101, 102, 103]
    assert lines[-1]["verdict"] == mr.VERDICT_NOT_EVALUATED
    assert lines[-1]["reason"] == mr.PASS_BUDGET_REASON
    # Le bilan separe les deux comptes : « evaluee(s) » reste exact, et les
    # PRs non evaluees sont nommees une par une.
    assert len(payload["results"]) == 2
    assert payload["not_evaluated"] == [
        {"pr": 103, "reason": mr.PASS_BUDGET_REASON}
    ]
    assert not _evaluated(runner, 103)


def test_une_passe_sous_budget_se_comporte_comme_avant(
    tmp_path, monkeypatch, capsys
):
    """Controle negatif : sous budget, rien ne change (aucune PR non
    evaluee, aucun arret)."""
    monkeypatch.setattr(mr, "_clock", _fake_clock(1.0))
    runner = ScriptedRunner(prs=(101, 102, 103))
    rc, lines, _ = run_organ(
        tmp_path, runner, extra=("--pass-budget-s", "600", "--json")
    )
    assert rc == 0
    payload = _payload(capsys)
    assert payload["stopped_reason"] is None
    assert payload["not_evaluated"] == []
    assert [row["pr"] for row in lines] == [101, 102, 103]
    assert all(row["verdict"] != mr.VERDICT_NOT_EVALUATED for row in lines)
    assert len(payload["results"]) == 3


def test_un_budget_nul_desactive_la_borne(tmp_path, monkeypatch, capsys):
    """``--pass-budget-s 0`` = pas de borne (le comportement d'avant)."""
    monkeypatch.setattr(mr, "_clock", _fake_clock(1000.0))
    runner = ScriptedRunner(prs=(101, 102))
    rc, lines, _ = run_organ(
        tmp_path, runner, extra=("--pass-budget-s", "0", "--json")
    )
    assert rc == 0
    payload = _payload(capsys)
    assert payload["stopped_reason"] is None
    assert payload["not_evaluated"] == []
    assert [row["pr"] for row in lines] == [101, 102]


def test_un_budget_negatif_est_refuse():
    with pytest.raises(SystemExit):
        mr.run(["--pass-budget-s", "-1"], runner=ScriptedRunner())


# --- curseur de reprise (revue du 22/11) ----------------------------------------


def _passe_evaluatee(tmp_path, prs, extra=("--pass-budget-s", "250", "--json")):
    """Une passe, et la liste des PRs **evaluees** par cette passe.

    Les lignes `unevaluated` sont les PRs que la passe n'a PAS regardees :
    elles ne comptent pas comme evaluees. Le journal **cumule** les passes :
    on ne lit que les lignes de la passe courante.
    """
    journal = tmp_path / "journal.jsonl"
    avant = (len(journal.read_text(encoding="utf-8").splitlines())
             if journal.is_file() else 0)
    runner = ScriptedRunner(prs=tuple(prs))
    rc, lines, _ = run_organ(tmp_path, runner, extra=extra)
    assert rc == 0
    return [row["pr"] for row in lines[avant:]
            if row["verdict"] != mr.VERDICT_NOT_EVALUATED]


def test_le_curseur_de_reprise_continue_apres_la_derniere_pr_evaluee(
    tmp_path, monkeypatch
):
    """Une passee arretee sur le budget ne se rejoue pas au meme endroit.

    La premiere passe s'arrete a #102 (budget de 250 s, horloge de 100 s par
    lecture) ; la seconde doit **continuer** a #103 et non revenir a #101.
    """
    monkeypatch.setattr(mr, "_clock", _fake_clock(100.0))
    prs = (101, 102, 103, 104)
    premiere = _passe_evaluatee(tmp_path, prs)
    assert premiere == [101, 102], "la premiere passe s'arrete apres deux PRs"
    assert mr.read_pass_cursor(tmp_path / "journal.jsonl") == 102
    seconde = _passe_evaluatee(tmp_path, prs)
    assert seconde == [103, 104], "la seconde passe continue apres le curseur"


def test_n_passes_coupees_evaluent_toutes_les_prs_sans_sauter_deux_fois(
    tmp_path, monkeypatch
):
    """Contrat de la revue du 22/11 : la borne doit garanter que chaque PR
    ouverte est evaluee en un nombre **borne** de passes.

    Une horloge qui coupe chaque passe apres deux PRs : six passes successives
    evaluent les douze PRs, et aucune n'est sautee deux fois de suite.

    Sans le curseur de reprise, chaque passe repart de la file entiere et
    s'arrete au meme endroit : les PRs du haut ne sont jamais vues (c'est la
    famine de queue mesuree par le coordinateur sur le journal du 22/11).
    """
    monkeypatch.setattr(mr, "_clock", _fake_clock(100.0))
    prs = tuple(range(101, 113))
    passes = []
    for _ in range(6):
        passes.append(_passe_evaluatee(tmp_path, prs))
    vues = [pr for p in passes for pr in p]
    assert sorted(vues) == list(prs), "les douze PRs doivent etre evaluees"
    assert len(vues) == len(set(vues)), "aucune PR ne doit etre evaluee deux fois"
    for avant, apres in zip(passes, passes[1:]):
        assert not (set(avant) & set(apres)), \
            "aucune PR ne doit etre sautee deux fois de suite"


def test_une_passe_qui_parcourt_la_file_remet_le_curseur_a_zero(
    tmp_path, monkeypatch
):
    """Une passe qui a vu TOUTE la file n'a plus de curseur a rendre : la
    suivante repart du debut de la file."""
    monkeypatch.setattr(mr, "_clock", _fake_clock(100.0))
    journal = tmp_path / "journal.jsonl"
    _passe_evaluatee(tmp_path, (101, 102, 103))
    assert mr.read_pass_cursor(journal) == 102
    # Une passe sous budget (pas d'arret) parcourt toute la file.
    _passe_evaluatee(tmp_path, (101, 102, 103), extra=("--pass-budget-s", "600",
                                                        "--json"))
    assert mr.read_pass_cursor(journal) is None


def test_un_curseur_illisible_vaut_absent_il_ne_bloque_pas_la_passe(
    tmp_path, monkeypatch
):
    """Fail-OPEN : un curseur corrompu ne fait pas echouer la passe, il vaut
    « depuis le debut »."""
    monkeypatch.setattr(mr, "_clock", _fake_clock(100.0))
    journal = tmp_path / "journal.jsonl"
    mr.write_pass_cursor(journal, 102)
    (tmp_path / mr.PASS_CURSOR_FILENAME).write_text("{pas du json", encoding="utf-8")
    assert mr.read_pass_cursor(journal) is None
    assert _passe_evaluatee(tmp_path, (101, 102, 103)) == [101, 102]


def test_argv_organes_relatif_au_depot(tmp_path):
    """#26102 : l'argv journalise ne depend pas du chemin du worktree.

    Repro ai-01 2026-11-13 : ``test_max_arrete_le_run`` echouait depuis un
    worktree nomme pour la PR (``CoursIA-26102``) -- l'assertion cherchait
    « 102 » dans les commandes enregistrees et le CHEMIN ABSOLU de l'organe
    invoque le contenait. La propriete « la seconde PR n'est pas evaluee »
    tenait deja (bilan : 1 evaluee) ; le defaut reel etait le bruit machine
    dans l'argv. Regression : les organes sont invoques par leur chemin
    RELATIF au depot, quel que soit l'endroit ou vit le checkout.
    """
    runner = ScriptedRunner(prs=(101,))
    rc, _, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    nits = [c for c in runner.cmds()
            if len(c) > 1 and "check_unaddressed_nits.py" in c[1]]
    assert nits, "l'organe B.0 doit etre invoque"
    assert nits[0][1] == "scripts/check_unaddressed_nits.py", nits[0]
    combined = [c for c in runner.cmds()
                if len(c) > 1 and "premerge_combined_check.py" in c[1]]
    assert combined, "l'organe premerge doit etre invoque"
    assert combined[0][1] == "scripts/coordination/premerge_combined_check.py", combined[0]
    # et aucun argv n'embarque un chemin absolu de la machine executante
    for cmd in runner.cmds():
        for tok in cmd[1:]:
            assert not re.match(r"^[A-Za-z]:[\\/]", tok), cmd
            assert not tok.startswith("/"), cmd


def test_erreur_de_portee_generale_arrete_le_run(tmp_path):
    # #17672 point 3 : le fail-closed est PRESERVE pour ce qui frappe toute la
    # passe -- ici un jeton refuse (marqueur « bad credentials ») sur la
    # lecture de la vue de la PREMIERE PR. Arret, exit 1, et la PR suivante
    # n'est pas touchee : la repeter ne dirait rien de plus.
    runner = ScriptedRunner(
        prs=(201, 202), view_rc=1, view_stderr="gh: Bad credentials (HTTP 401)"
    )
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 1
    assert lines[-1]["verdict"] == "run-error"
    assert "Bad credentials" in lines[-1]["reason"]
    assert not _evaluated(runner, 202)


def test_erreur_dune_pr_est_isolee_et_le_balayage_continue(tmp_path, capsys):
    """#17672 point 3 : une erreur attribuable a UNE PR ne gele plus les autres.

    Falsification : avant le correctif, le `break` de la boucle emportait le
    balayage entier -- la PR suivante n'etait meme pas evaluee et le run
    s'arretait sur la premiere PR mal formee. Ici la vue de 201 est illisible
    (`gh pr view 201 : la reponse n'est pas un objet`), 202 est une PR normale.
    """
    runner = ScriptedRunner(prs=(201, 202), views={201: ["pas", "un", "objet"]})
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))

    assert rc == 1, "une erreur isolee reste un incident : rc=1"
    assert [row["pr"] for row in lines] == [201, 202]
    assert lines[0]["verdict"] == "run-error"
    assert "n'est pas un objet" in lines[0]["reason"], lines[0]["reason"]
    # La PR SUIVANTE est bien evaluee puis mergee : c'est tout l'objet du point 3.
    assert lines[1]["verdict"] == "merged", lines[1]
    assert any("202" in flat for flat in runner.flat())

    out = capsys.readouterr().out
    # Le run ne s'est PAS arrete : publier « arret » serait un constat faux.
    assert "arret :" not in out
    # ...mais l'erreur isolee doit etre visible, sinon elle disparait du rapport.
    assert "1 erreur(s) isolee(s)" in out, out


def test_is_pass_wide_classe_par_le_texte_de_l_outil():
    # Classification pure, sans boucle : un motif reconnu = portee generale ;
    # tout le reste = attribuable a la PR (donc isole). Le sens de l'erreur par
    # defaut compte : un texte inconnu ne doit JAMAIS arreter le balayage.
    assert mr.is_pass_wide(
        mr.UnexpectedError("gh pr view 9 rc=1 : API rate limit exceeded")
    )
    assert mr.is_pass_wide(
        mr.UnexpectedError("gh pr list rc=1 : could not resolve host: api.github.com")
    )
    assert not mr.is_pass_wide(
        mr.UnexpectedError("gh api pulls/9 rc=7 hors contrat : (sans message)")
    )
    assert not mr.is_pass_wide(
        mr.UnexpectedError("gh pr view 9 : la reponse n'est pas un objet")
    )


def test_merge_echoue_arrete_le_run(tmp_path):
    # un merge refuse est une erreur inattendue : jamais de merge en aveugle
    runner = ScriptedRunner(prs=(301, 302), merge_rc=1)
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 1
    assert lines[-1]["verdict"] == "merge-failed" and lines[-1]["merged"] is False
    assert not _evaluated(runner, 302)


# --- course de base (#26771) ----------------------------------------------------
#
# « Base branch was modified » n'est ni une panne de l'organe ni une PR cassee :
# `main` a bouge entre la lecture de l'etat et la pose du merge. Le passage du
# 15/11 a merge 11 PRs, s'est arrete sur la 12e, et toute la suite de la file
# a attendu un passage de plus. Le motif est REJOUABLE pour la PR.


BASE_RACE_TEXT = (
    "GraphQL: Base branch was modified. Review and try the merge again. "
    "(mergePullRequest)"
)


def test_le_motif_de_course_de_base_est_reconnu():
    assert mr.is_base_modified_race(BASE_RACE_TEXT)
    assert mr.is_base_modified_race(BASE_RACE_TEXT.upper())
    # Un motif non reconnu n'est JAMAIS lu comme une course : il garde le
    # disjoncteur.
    assert not mr.is_base_modified_race("merge refused")
    assert not mr.is_base_modified_race("Head branch was modified")
    assert not mr.is_base_modified_race("")


def test_course_de_base_rejouee_la_pr_est_mergee_et_le_passage_continue(tmp_path):
    """Echec de course puis rejeu reussi : la PR part en `merged`."""
    runner = ScriptedRunner(prs=(501, 502), merge_script=[(1, BASE_RACE_TEXT)])
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert [row["pr"] for row in lines] == [501, 502]
    assert all(row["verdict"] == "merged" for row in lines)
    merges = [c for c in runner.flat() if c.startswith("gh pr merge")]
    # PR 501 : un echec + un rejeu ; PR 502 : un merge.
    assert len(merges) == 3
    # Le rejeu est pose a la MEME tete (--match-head-commit).
    assert all("--match-head-commit" in c for c in merges)
    assert all(c.endswith(HEAD) for c in merges), merges
    # La courte pause prevue a ete respectee.
    assert runner.sleeps == [mr.MERGEABLE_RETRY_SLEEP_S]


def test_course_de_base_rejouee_echouant_la_pr_est_skippee_et_la_suivante_est_evaluee(tmp_path):
    """Deux echecs de course : la PR est `skipped base-modified-race`, et le
    balayage CONTINUE -- c'est le point de la demande."""
    runner = ScriptedRunner(
        prs=(601, 602),
        merge_script=[(1, BASE_RACE_TEXT), (1, BASE_RACE_TEXT)],
    )
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0, "une course de base ne doit pas arreter le passage"
    assert lines[0]["pr"] == 601
    assert lines[0]["verdict"] == "skipped"
    assert lines[0]["reason"] == "base-modified-race"
    assert lines[0]["merged"] is False
    # La PR suivante est bien evaluee (et mergee).
    assert lines[1]["pr"] == 602 and lines[1]["verdict"] == "merged"


def test_autre_echec_de_merge_garde_le_disjoncteur(tmp_path):
    """Non-regression : un motif inconnu arrete TOUJOURS le passage."""
    runner = ScriptedRunner(prs=(701, 702), merge_rc=1)
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 1
    assert lines[-1]["verdict"] == "merge-failed"
    assert lines[-1]["reason"] != "base-modified-race"
    assert not _evaluated(runner, 702)


def test_la_course_ne_declenche_pas_de_rejeu_sur_une_erreur_inconnue(tmp_path):
    """Un echec inconnu ne doit pas lancer de rejeu : un seul appel a
    `gh pr merge`, et le passage s'arrete."""
    runner = ScriptedRunner(prs=(801, 802), merge_rc=1)
    run_organ(tmp_path, runner, extra=("--apply",))
    merges = [c for c in runner.flat() if c.startswith("gh pr merge")]
    assert len(merges) == 1
    assert runner.sleeps == []


# --- journal -----------------------------------------------------------------------


def test_journal_ligne_par_pr(tmp_path):
    runner = ScriptedRunner(prs=(401, 402))
    rc, lines, journal = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert journal.is_file()
    assert len(lines) == 2
    for row in lines:
        assert set(row.keys()) == {
            "ts", "pr", "head", "verdict", "reason", "merged", "review",
            "stack",
        } | ({"stack_incidents"} if row.get("stack_incidents") else set())
        assert re.fullmatch(r"\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z", row["ts"])
        assert isinstance(row["pr"], int)
        assert row["merged"] is True and row["verdict"] == "merged"
        assert row["reason"] is None
        # Une ligne mergee porte la disposition CLASSEE, pas « non evaluee » :
        # le verdict terminal est reconstruit apres le merge, il doit heriter de
        # la classification faite avant.
        assert row["review"] == mr.APPROVED_EXACT_HEAD
    assert [row["pr"] for row in lines] == [401, 402]  # ancienne d'abord


# --- porte STACK en processus (#20251, retrait du dossier 2026-11-05) -------------
#
# Depuis le retrait du dossier, l'etape 3 exerce la porte STACK du gate EN
# PROCESSUS : ``gate.default_stack_index()`` (index cache dans le module,
# injecte par le fixture autouse) puis ``gate.stack_reasons(pr, index)``.
# Deux etats journalises : ``measured`` | ``unmeasured`` (``null`` = la porte
# n'a pas ete atteinte, skip en amont). La porte est fail-open -- un incident
# de mesure ne fabrique aucun refus -- mais l'absence de mesure doit etre
# VISIBLE la ou l'on lit les merges (#22066).


def test_stack_measured_est_journalise(tmp_path):
    """Defaut du fixture : index vide, porte mesuree, aucune parente -- le
    chemin nominal journalise ``stack: measured`` sans incidents."""
    runner = ScriptedRunner(prs=(601,))
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert lines[-1]["stack"] == "measured"
    assert "stack_incidents" not in lines[-1]
    assert lines[-1]["merged"] is True


def test_stack_reasons_non_vides_skip_stack_top(tmp_path, monkeypatch):
    """Un sommet de pile perime (la PR partage des commits avec une PR
    ouverte qui porte des corrections absentes ici) : skip court nommant la
    PR partenaire, porte ``measured``, et aucun organe en aval n'est paye."""
    monkeypatch.setattr(
        mr.gate, "default_stack_index", lambda: {124: "entree-de-la-partenaire"}
    )
    monkeypatch.setattr(
        mr.gate,
        "stack_reasons",
        lambda target, index: [
            (
                "stack top: shares 2 commit(s) with OPEN #124, which carries "
                "1 commit(s) absent here -- merging this one first would land "
                "the earlier version on main (e.g. 'Fix: correctif ulterieur')"
            )
        ],
    )
    runner = ScriptedRunner(prs=(123,))
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert lines[-1]["verdict"] == "skipped"
    assert lines[-1]["reason"] == "stack-top:124"
    assert lines[-1]["stack"] == "measured"
    assert not any("check_unaddressed_nits.py" in flat for flat in runner.flat())
    assert not any(c[:3] == ["gh", "pr", "merge"] for c in runner.cmds())


def test_stack_index_none_fail_open_unmeasured(tmp_path, monkeypatch, capsys):
    """Index de pile illisible (``None``) : fail-open assume -- le merge a
    lieu, mais la ligne de journal porte ``unmeasured`` et les incidents de
    mesure, et le resume humain le signale."""
    monkeypatch.setattr(mr.gate, "default_stack_index", lambda: None)
    monkeypatch.setitem(
        mr.gate._STACK_INDEX_CACHE, "incidents",
        ["tete de PR inatteignable: #9999"],
    )
    runner = ScriptedRunner(prs=(602,))
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    out = capsys.readouterr().out
    assert rc == 0
    assert lines[-1]["stack"] == "unmeasured"
    assert lines[-1]["stack_incidents"] == ["tete de PR inatteignable: #9999"]
    # la decision de merge ne change pas : la porte est fail-open
    assert lines[-1]["merged"] is True and lines[-1]["verdict"] == "merged"
    # mais le resume humain le signale
    assert "STACK non mesure" in out
    assert "tete de PR inatteignable: #9999" in out


def test_le_skip_avant_la_porte_stack_ne_porte_pas_d_etat_stack(tmp_path):
    """Un skip decide avant la porte STACK ne sait rien de son etat : la
    ligne porte ``null``, elle n'invente pas un etat."""
    runner = ScriptedRunner(views={123: default_view(draft=True)})
    rc, lines, _ = run_organ(tmp_path, runner)
    assert rc == 0
    assert lines[-1]["verdict"] == "skipped"
    assert lines[-1]["stack"] is None
    assert "stack_incidents" not in lines[-1]


# --- jeton --------------------------------------------------------------------------


def test_jeton_epingle_sur_chaque_appel_gh(tmp_path):
    runner = ScriptedRunner(prs=(501,))
    rc, _, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert runner.calls, "le run doit avoir appele au moins le resolve du jeton"
    for cmd, env in runner.calls:
        flat = " ".join(cmd)
        assert "switch" not in flat, "gh auth switch est interdit"
        if cmd[:4] == ["gh", "auth", "token", "--user"]:
            # la resolution elle-meme tourne SANS GH_TOKEN ambiant
            assert env is not None and "GH_TOKEN" not in env
            continue
        assert env is not None, f"env absent pour : {flat}"
        assert env.get("GH_TOKEN") == TOKEN, f"jeton non epingle pour : {flat}"


def test_jeton_irresolu_exit_2(tmp_path):
    runner = ScriptedRunner(token_rc=1)
    journal = tmp_path / "journal.jsonl"
    rc = mr.run(["--journal", str(journal)], runner=runner)
    assert rc == 2
    assert not journal.is_file()
    # aucune commande au-dela de la resolution du jeton
    assert len(runner.calls) == 1


# --- garde de troncature de la liste de fichiers (revue ai-01) ----------------


def test_files_truncated_par_la_vue_puis_completes_par_le_rest(tmp_path):
    # #27684 : `gh pr view --json files` plafonne a 100 fichiers. La troncature
    # rendait la PR non mergeable (skip `files-truncated:1/150`) alors que le
    # REST pagine la liste complete : la PR n'est plus bloquee, et le controle
    # de perimetre porte sur la liste COMPLETE.
    view = default_view(files=("src/a.py",))
    view["changedFiles"] = 150
    runner = ScriptedRunner(
        views={123: view},
        pr_files={123: [f"src/f{i}.py" for i in range(150)]},
    )
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert not any(
        str(line.get("reason") or "").startswith("files-truncated")
        for line in lines
    )
    assert any("pulls/123/files" in flat for flat in runner.flat())


def test_liste_des_fichiers_illisible_reste_fail_closed(tmp_path):
    # Le controle de perimetre reste fail-closed : une liste ILLISIBLE
    # (quota, 5xx) bloque la PR, mais le motif dit qu'il s'agit d'une lecture.
    view = default_view(files=("src/a.py",))
    view["changedFiles"] = 150
    runner = ScriptedRunner(views={123: view}, pr_files_rc=1)
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert lines[-1]["reason"] == "files-unreadable"
    assert not any("check_unaddressed_nits.py" in flat for flat in runner.flat())


def test_skip_changed_files_absent_fail_closed(tmp_path):
    view = default_view()
    del view["changedFiles"]
    runner = ScriptedRunner(views={123: view})
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert lines[-1]["reason"] == "files-unknown-count"


def test_wt_vibe_prefix_lifted_with_13410_reopening():
    # Reouverture user du 2026-10-07 : les relais g-XX de #13410 ne gelent
    # plus, meme muets -- le prefixe n'etait gele que pour cette campagne.
    assert (
        mr.frozen_umbrella_exclusion(
            "fix(search,g77): relocate 12 lectures", "Grain: MED/notebook", "wt/vibe-g77-search-26"
        )
        is None
    )
    assert mr.frozen_umbrella_exclusion("fix(x): ordinaire", None, "fix/vibe-check") is None
    assert mr.frozen_umbrella_exclusion("fix(x): ordinaire", None, None) is None


def test_skip_frozen_umbrella_avant_les_organes(tmp_path):
    # Le skip de perimetre precede les organes : la PR gelee n'y est pas
    # passee. (Forme branche wt/vibe-* levee avec la reouverture de #13410,
    # 2026-10-07.)
    view = default_view(title="enrich(qc,#11601): densite QC-Py-07")
    view["headRefName"] = "feature/densite-qc-7"
    runner = ScriptedRunner(views={123: view})
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert lines[-1]["reason"] == "frozen:#11601(veto #17040)"
    assert not any("check_unaddressed_nits.py" in flat for flat in runner.flat())


# --- retenues du coordinateur (hold.txt) ----------------------------------------


def test_hold_skips_before_any_pr_call(tmp_path):
    # La retenue est lue a cote du journal ; la PR retenue n'est ni vue, ni
    # passee aux organes, ni mergee -- la PR suivante suit le chemin nominal.
    (tmp_path / "hold.txt").write_text(
        "# retenues ai-01\n\n16808  # rebase sur #17521 d'abord\n", encoding="utf-8"
    )
    runner = ScriptedRunner(prs=(16808, 124))
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    by_pr = {row["pr"]: row for row in lines}
    assert by_pr[16808]["verdict"] == "skipped"
    assert by_pr[16808]["reason"] == "hold:rebase sur #17521 d'abord"
    assert not any(flat.startswith("gh pr view 16808") for flat in runner.flat())
    assert not any("merge 16808" in flat for flat in runner.flat())
    assert by_pr[124]["verdict"] == "merged"


def test_hold_without_reason_names_the_file(tmp_path):
    (tmp_path / "hold.txt").write_text("123\n", encoding="utf-8")
    runner = ScriptedRunner()
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert lines[-1]["reason"] == "hold:hold.txt"


def test_hold_file_absent_means_no_hold(tmp_path):
    runner = ScriptedRunner()
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert lines[-1]["verdict"] == "merged"


def test_hold_hash_number_is_malformed_not_a_comment(tmp_path):
    # `#17530` lu comme un commentaire ferait tomber la retenue en silence :
    # l'organe refuse de demarrer plutot que de merger sans savoir.
    (tmp_path / "hold.txt").write_text("#123 attente decision\n", encoding="utf-8")
    runner = ScriptedRunner()
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 2
    assert lines == []
    assert not any(" merge " in f" {flat} " for flat in runner.flat())


def test_hold_malformed_line_refuses_to_start(tmp_path):
    (tmp_path / "hold.txt").write_text("PR 123\n", encoding="utf-8")
    runner = ScriptedRunner()
    rc, _, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 2
    assert runner.calls == []


def test_hold_file_override(tmp_path):
    other = tmp_path / "ailleurs" / "retenues.txt"
    other.parent.mkdir()
    other.write_text("123 ordre de stack\n", encoding="utf-8")
    runner = ScriptedRunner()
    rc, lines, _ = run_organ(
        tmp_path, runner, extra=("--apply", "--hold-file", str(other))
    )
    assert rc == 0
    assert lines[-1]["reason"] == "hold:ordre de stack"


def test_main_rouge_pose_hold_nommee_et_bloque_tout_merge(tmp_path):
    disposable = tmp_path / "repo-jetable"
    disposable.mkdir()
    subprocess.run(["git", "init", "-b", "main"], cwd=disposable, check=True, capture_output=True)
    subprocess.run(["git", "config", "user.name", "Test"], cwd=disposable, check=True)
    subprocess.run(["git", "config", "user.email", "test@example.invalid"], cwd=disposable, check=True)
    (disposable / "preuve.txt").write_text("main\n", encoding="utf-8")
    subprocess.run(["git", "add", "preuve.txt"], cwd=disposable, check=True)
    subprocess.run(["git", "commit", "-m", "commit rouge simule"], cwd=disposable, check=True, capture_output=True)
    main_sha = subprocess.run(
        ["git", "rev-parse", "HEAD"], cwd=disposable, check=True,
        capture_output=True, text=True, encoding="utf-8", errors="replace",
    ).stdout.strip()
    journal = tmp_path / "journal.jsonl"
    hold = tmp_path / "hold.txt"
    hold.write_text("16808 attente utilisateur\n", encoding="utf-8")
    red = ScriptedRunner(
        main_check_runs=json.dumps([
            {"name": "Scripts Tests (CPU)", "conclusion": "failure",
             "status": "completed", "started_at": "2026-11-08T11:00:00Z",
             "output": {"summary": "FAILED scripts/tests/test_guard.py::test_case - assertion"}}
        ]),
        main_sha=main_sha,
    )
    rc = mr.run(["--journal", str(journal), "--hold-file", str(hold), "--apply"], runner=red)
    rows = [json.loads(row) for row in journal.read_text(encoding="utf-8").splitlines()]
    assert rc == 0
    assert rows[0]["reason"].startswith("hold:main-red-sentinel sha=" + red.main_sha)
    assert "test=scripts/tests/test_guard.py::test_case" in rows[0]["reason"]
    assert not any("gh pr view" in cmd or "gh pr merge" in cmd for cmd in red.flat())
    assert hold.read_text(encoding="utf-8").splitlines() == [
        "16808 attente utilisateur",
        # #26706 : la retenue porte le numero de l'issue du rouge -- c'est
        # la voie deterministe de reutilisation (l'index de recherche peut
        # avoir du retard, deux runs rapproches ne doivent pas ouvrir deux
        # issues).
        "0 main-red-sentinel sha=" + red.main_sha
        + " check=Scripts Tests (CPU) conclusion=failure test=scripts/tests/test_guard.py::test_case"
        + " issue=26710",
    ]

    # Le vert retire uniquement la ligne appartenant a la sentinelle.
    green = ScriptedRunner(main_sha=main_sha)
    rc = mr.run(["--journal", str(journal), "--hold-file", str(hold), "--apply"], runner=green)
    assert rc == 0
    assert hold.read_text(encoding="utf-8") == "16808 attente utilisateur\n"
    assert any("gh pr merge 123" in cmd for cmd in green.flat())


def test_main_check_absent_fail_closed(tmp_path):
    runner = ScriptedRunner(main_check_runs="[]")
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 2
    assert lines == []
    assert not any("gh pr merge" in cmd for cmd in runner.flat())


# --- remontee dans l'historique de main (revue ai-01 du 2026-11-10) ---------
# Points 1 et 2 : on juge le dernier commit qui porte un VERDICT TERMINE,
# et seul `failure` pose la retenue.


def _scripts_check(conclusion, status="completed", summary="21 000 passed", started="2026-11-10T10:00:00Z", details_url=None):
    row = {"name": "Scripts Tests (CPU)", "conclusion": conclusion, "status": status,
           "started_at": started, "output": {"summary": summary}}
    if details_url:
        row["details_url"] = details_url
    return json.dumps([row])


def _job_url(job_id: int) -> str:
    """`details_url` d'un check-run de job (forme mesuree sur l'API)."""
    return f"https://github.com/jsboige/CoursIA/actions/runs/43316243195/job/{job_id}"


def test_le_rouge_de_main_ouvre_une_issue_et_le_vert_la_ferme(tmp_path):
    """#26706, de bout en bout dans le run : l'issue est le canal de coordination.

    Le 15/11, le rouge de `main` a recu QUATRE reparations concurrentes
    (#26696, #26697, #26698, plus une tentative locale) : rien ne disait
    aux lanes que le rouge etait deja pris. La sentinelle ouvre donc UNE
    issue `[main-red] <check> — <test>`, que la lane de reparation reclame,
    et la ferme des que le verdict redevient vert.
    """
    main_sha = "c" * 40
    runner = ScriptedRunner(
        main_sha=main_sha,
        main_history=[main_sha],
        main_checks_by_sha={
            main_sha: _scripts_check(
                "failure",
                summary="FAILED scripts/tests/test_guard.py::test_case - assertion",
            )
        },
    )
    journal = tmp_path / "journal.jsonl"
    hold = tmp_path / "hold.txt"

    rc = mr.run(["--journal", str(journal), "--hold-file", str(hold)], runner=runner)
    assert rc == 0
    assert len(runner.main_red_created) == 1, "le rouge n'a pas ouvert d'issue"
    assert runner.main_red_created[0]["title"] == (
        "[main-red] Scripts Tests (CPU) — scripts/tests/test_guard.py::test_case"
    )
    assert "0 main-red-sentinel sha=" + main_sha in hold.read_text(encoding="utf-8")

    # Le vert arrive sur `main` : l'issue se ferme et la retenue tombe.
    runner.main_checks_by_sha[main_sha] = _scripts_check("success")
    rc = mr.run(["--journal", str(journal), "--hold-file", str(hold)], runner=runner)
    assert rc == 0
    assert runner.main_red_closed == [runner.main_red_created[0]["number"]]
    assert "main-red-sentinel" not in hold.read_text(encoding="utf-8")


def test_une_recherche_d_issue_illisible_n_ouvre_rien_mais_pose_la_retenue(tmp_path):
    """#26706, fail-closed : une recherche illisible n'ouvre AUCUNE issue.

    Une retention en double est pire qu'une absence : deux lanes y
    reclameraient le meme rouge. La retenue, elle, reste posee.
    """
    main_sha = "d" * 40
    runner = ScriptedRunner(
        main_sha=main_sha,
        main_history=[main_sha],
        main_red_search_rc=1,
        main_checks_by_sha={
            main_sha: _scripts_check(
                "failure",
                summary="FAILED scripts/tests/test_guard.py::test_case - assertion",
            )
        },
    )
    journal = tmp_path / "journal.jsonl"
    hold = tmp_path / "hold.txt"

    rc = mr.run(["--journal", str(journal), "--hold-file", str(hold)], runner=runner)
    assert rc == 0
    assert runner.main_red_created == [], "une issue a ete ouverte malgre la recherche"
    assert "0 main-red-sentinel sha=" + main_sha in hold.read_text(encoding="utf-8")


def test_sentinelle_juge_le_commit_derriere_une_tete_en_cours(tmp_path):
    """Point 1 : un check EN COURS n'est pas un refus de demarrer.

    On remonte l'historique et on juge le premier verdict TERMINE trouve.
    """
    tete = "1" * 40
    ancien = "2" * 40
    runner = ScriptedRunner(
        main_sha=tete,
        main_history=[tete, ancien],
        main_checks_by_sha={
            tete: _scripts_check(None, status="in_progress", summary=""),
            ancien: _scripts_check(
                "failure",
                summary="FAILED scripts/tests/test_x.py::test_y - assertion",
            ),
        },
    )
    hold = tmp_path / "hold.txt"
    journal = tmp_path / "journal.jsonl"
    rc = mr.run(
        ["--journal", str(journal), "--hold-file", str(hold), "--apply"], runner=runner
    )
    assert rc == 0
    # La retenue nomme le commit JUGUE, pas la tete.
    contenu = hold.read_text(encoding="utf-8")
    assert f"sha={ancien}" in contenu
    assert f"sha={tete}" not in contenu
    assert "test=scripts/tests/test_x.py::test_y" in contenu


def test_sentinelle_cancelled_remonte_au_commit_precedent(tmp_path):
    """Point 2 : `cancelled` est de l'INFRA, pas un verdict de code."""
    tete = "3" * 40
    ancien = "4" * 40
    runner = ScriptedRunner(
        main_sha=tete,
        main_history=[tete, ancien],
        main_checks_by_sha={
            tete: _scripts_check("cancelled", summary=""),
            ancien: _scripts_check(
                "failure",
                summary="FAILED scripts/tests/test_x.py::test_y - assertion",
            ),
        },
    )
    hold = tmp_path / "hold.txt"
    rc = mr.run(
        ["--journal", str(tmp_path / "j.jsonl"), "--hold-file", str(hold), "--apply"],
        runner=runner,
    )
    assert rc == 0
    contenu = hold.read_text(encoding="utf-8")
    assert f"sha={ancien}" in contenu
    assert f"sha={tete}" not in contenu


def test_sentinelle_timed_out_remonte_au_commit_precedent(tmp_path):
    """Point 2 : `timed_out` est de l'INFRA ; le verdict vert precedent gagne."""
    tete = "5" * 40
    ancien = "6" * 40
    runner = ScriptedRunner(
        main_sha=tete,
        main_history=[tete, ancien],
        main_checks_by_sha={
            tete: _scripts_check("timed_out", summary=""),
            ancien: _scripts_check("success"),
        },
    )
    hold = tmp_path / "hold.txt"
    rc = mr.run(
        ["--journal", str(tmp_path / "j.jsonl"), "--hold-file", str(hold), "--apply"],
        runner=runner,
    )
    assert rc == 0
    # Aucun verdict de code rouge : la sentinelle n'ecrit aucune retenue.
    contenu = hold.read_text(encoding="utf-8") if hold.exists() else ""
    assert "main-red-sentinel" not in contenu


def test_sentinelle_sans_verdict_termine_fail_closed_borne(tmp_path, capsys):
    """Point 3 : fail-closed AVEC la borne nommee (N ecrit)."""
    history = [f"{i:040x}" for i in range(1, mr.MAIN_RED_HISTORY_LIMIT + 1)]
    runner = ScriptedRunner(
        main_sha=history[0],
        main_history=history,
        main_checks_by_sha={
            sha: _scripts_check(None, status="in_progress", summary="")
            for sha in history
        },
    )
    rc = mr.run(
        ["--journal", str(tmp_path / "j.jsonl"), "--hold-file", str(tmp_path / "h.txt"), "--apply"],
        runner=runner,
    )
    assert rc == 2
    err = capsys.readouterr().err
    assert "fail-closed" in err
    assert str(mr.MAIN_RED_HISTORY_LIMIT) in err


# --- #25510 T-J : `failure` d'infrastructure vs verdict de code ----------
# Un `failure` sans test identifiable peut venir de l'infrastructure (le
# checkout qui tombe, l'install des dependances qui echoue). La sentinelle
# ne doit pas retenir `main` sur une panne d'infrastructure : elle remonte
# au commit precedent. Un `failure` dont la premiere etape en echec est
# une etape de TEST reste une retenue, meme sans nom de test identifiable.


def test_sentinelle_failure_d_infrastructure_ne_pose_pas_de_retenue(tmp_path, capsys):
    """CONTROLE POSITIF : le checkout en echec n'est pas un verdict de code.

    Mesure de reference (run 43316243195, job 131524893709) : la premiere
    etape en echec est `Run actions/checkout@v4`, et le log d'echec ne
    contient aucun jeton `FAILED`/`ERROR` -- donc aucun test n'est
    identifiable. Le commit est ecarte, le verdict remonte au precedent.
    """
    tete = "a1" * 20
    ancien = "b2" * 20
    runner = ScriptedRunner(
        main_sha=tete,
        main_history=[tete, ancien],
        main_checks_by_sha={
            tete: _scripts_check("failure", summary="", details_url=_job_url(131524893709)),
            ancien: _scripts_check(
                "failure",
                summary="FAILED scripts/tests/test_x.py::test_y - assertion",
            ),
        },
        job_steps={"131524893709": "Run actions/checkout@v4"},
    )
    hold = tmp_path / "hold.txt"
    rc = mr.run(
        ["--journal", str(tmp_path / "j.jsonl"), "--hold-file", str(hold), "--apply"],
        runner=runner,
    )
    assert rc == 0
    # Le commit d'infrastructure n'est PAS retenu : le verdict remonte.
    contenu = hold.read_text(encoding="utf-8") if hold.exists() else ""
    assert f"sha={tete}" not in contenu
    assert f"sha={ancien}" in contenu


def test_sentinelle_failure_d_infrastructure_nomme_l_etape_ecartee(tmp_path, capsys):
    """Point 4 du plan : le journal nomme l'etape ecartee."""
    tete = "c3" * 20
    ancien = "c4" * 20
    runner = ScriptedRunner(
        main_sha=tete,
        main_history=[tete, ancien],
        main_checks_by_sha={
            tete: _scripts_check("failure", summary="", details_url=_job_url(42)),
            ancien: _scripts_check("success"),
        },
        job_steps={"42": "Install dependencies"},
    )
    rc = mr.run(
        ["--journal", str(tmp_path / "j.jsonl"), "--hold-file", str(tmp_path / "h.txt"), "--apply"],
        runner=runner,
    )
    assert rc == 0
    out = capsys.readouterr().out
    assert "Install dependencies" in out
    assert "sentinelle main-red" in out


def test_sentinelle_failure_a_l_etape_de_test_garde_la_retenue(tmp_path):
    """CONTROLE NEGATIF : un test non identifiable n'est PAS de l'infra.

    La premiere etape en echec est l'etape de test : la retenue est
    conservee, et elle porte l'absence d'identification du test.
    """
    tete = "d4" * 20
    runner = ScriptedRunner(
        main_sha=tete,
        main_history=[tete],
        main_checks_by_sha={
            tete: _scripts_check("failure", summary="", details_url=_job_url(43)),
        },
        job_steps={"43": "Run tests"},
    )
    hold = tmp_path / "hold.txt"
    rc = mr.run(
        ["--journal", str(tmp_path / "j.jsonl"), "--hold-file", str(hold), "--apply"],
        runner=runner,
    )
    assert rc == 0
    contenu = hold.read_text(encoding="utf-8")
    assert f"sha={tete}" in contenu
    assert "test=test-non-identifie-dans-le-check" in contenu


def test_sentinelle_runner_perdu_en_cours_d_etape_remonte_au_commit_precedent(tmp_path, capsys):
    """CONTROLE POSITIF (#25510 T-J) : un job `failure` SANS etape en echec
    est un runner perdu, pas un verdict de code.

    Mesure du 2026-11-16 (run 43777127542, job 133012644184, runner
    `myia-ai-01-linux-main-1`) : le job a rendu `completed/failure` alors que
    l'etape 11 « Run tests » etait restee `in_progress` (conclusion nulle) et
    que les etapes suivantes etaient `pending` -- le runner avait disparu au
    milieu d'une etape (reboot de l'hote a 00:32Z). Aucune etape n'etant en
    `failure`, la sentinelle lisait un verdict de code et retenait `main` sur
    une perte d'infrastructure : le verdict doit remonter au commit precedent.

    Le controle porte sur le **mecanisme** (`runner perdu`), pas seulement
    sur l'ecart du commit : sans le correctif, l'ancien code lisait la liste
    JSON des etapes comme un NOM d'etape, et le motif retenu etait
    `infra(failure-step:<blob>)` -- un verdict de code deguise en panne.
    """
    tete = "e1" * 20
    ancien = "e2" * 20
    runner = ScriptedRunner(
        main_sha=tete,
        main_history=[tete, ancien],
        main_checks_by_sha={
            tete: _scripts_check("failure", summary="", details_url=_job_url(133012644184)),
            ancien: _scripts_check(
                "failure",
                summary="FAILED scripts/tests/test_x.py::test_y - assertion",
            ),
        },
        job_steps={
            "133012644184": [
                {"n": "Set up job", "o": 1, "s": "completed", "c": "success"},
                {"n": "Run actions/checkout@v4", "o": 5, "s": "completed", "c": "success"},
                {"n": "Run tests", "o": 11, "s": "in_progress", "c": None},
                {"n": "Publish results", "o": 12, "s": "queued", "c": None},
            ],
        },
    )
    hold = tmp_path / "hold.txt"
    rc = mr.run(
        ["--journal", str(tmp_path / "j.jsonl"), "--hold-file", str(hold), "--apply"],
        runner=runner,
    )
    assert rc == 0
    contenu = hold.read_text(encoding="utf-8") if hold.exists() else ""
    assert f"sha={tete}" not in contenu
    assert f"sha={ancien}" in contenu
    out = capsys.readouterr().out
    assert "runner perdu en cours d'etape" in out


def test_sentinelle_une_etape_en_echec_emporte_la_retenue(tmp_path):
    """CONTROLE NEGATIF (#25510 T-J) : la presence d'UNE etape en echec
    interdit la lecture « runner perdu ».

    Meme mesure que le controle positif, mais l'etape de test a rendu
    `failure` : c'est un verdict de code, la retenue doit etre conservee --
    meme si une autre etape du job est restee en cours.
    """
    tete = "e3" * 20
    runner = ScriptedRunner(
        main_sha=tete,
        main_history=[tete],
        main_checks_by_sha={
            tete: _scripts_check("failure", summary="", details_url=_job_url(133012644185)),
        },
        job_steps={
            "133012644185": [
                {"n": "Run actions/checkout@v4", "o": 5, "s": "completed", "c": "success"},
                {"n": "Run tests", "o": 11, "s": "completed", "c": "failure"},
                {"n": "Publish results", "o": 12, "s": "queued", "c": None},
            ],
        },
    )
    hold = tmp_path / "hold.txt"
    rc = mr.run(
        ["--journal", str(tmp_path / "j.jsonl"), "--hold-file", str(hold), "--apply"],
        runner=runner,
    )
    assert rc == 0
    contenu = hold.read_text(encoding="utf-8")
    assert f"sha={tete}" in contenu


def test_sentinelle_lecture_de_job_illisible_garde_la_retenue(tmp_path):
    """CONTROLE NEGATIF (#25510 T-J) : une lecture ILLISIBLE reste
    fail-closed -- elle ne devient jamais un « runner perdu ».

    Une lecture impossible ne vaut pas une preuve : sans etapes, on ne peut
    rien conclure sur le job, donc la retenue est conservee.
    """
    tete = "e4" * 20
    runner = ScriptedRunner(
        main_sha=tete,
        main_history=[tete],
        main_checks_by_sha={
            tete: _scripts_check("failure", summary="", details_url=_job_url(133012644186)),
        },
        job_steps={"133012644186": []},
        job_steps_rc={"133012644186": 1},
    )
    hold = tmp_path / "hold.txt"
    rc = mr.run(
        ["--journal", str(tmp_path / "j.jsonl"), "--hold-file", str(hold), "--apply"],
        runner=runner,
    )
    assert rc == 0
    contenu = hold.read_text(encoding="utf-8")
    assert f"sha={tete}" in contenu


def test_sentinelle_reconnait_les_etapes_du_checkout_borne_t_k(tmp_path):
    """T-K (#25510) : une panne du `git fetch --unshallow` est une panne
    d'INFRASTRUCTURE, pas un verdict de code.

    Les deux etapes du checkout borne portent le prefixe `T-K :`. Si la
    sentinelle ne les reconnait pas, un `curl 28` sur le reseau retient
    `main` au lieu de remonter au commit precedent -- exactement la panne
    que la sentinelle T-J a ete creee pour ecarter.
    """
    tete = "1a" * 20
    ancien = "2b" * 20
    runner = ScriptedRunner(
        main_sha=tete,
        main_history=[tete, ancien],
        main_checks_by_sha={
            tete: _scripts_check("failure", summary="", details_url=_job_url(47)),
            ancien: _scripts_check(
                "failure",
                summary="FAILED scripts/tests/test_x.py::test_y - assertion",
            ),
        },
        job_steps={"47": "T-K : ascendance de la tete + la base, sans les 1 606 branches"},
    )
    hold = tmp_path / "hold.txt"
    rc = mr.run(
        ["--journal", str(tmp_path / "j.jsonl"), "--hold-file", str(hold), "--apply"],
        runner=runner,
    )
    assert rc == 0
    contenu = hold.read_text(encoding="utf-8") if hold.exists() else ""
    assert f"sha={tete}" not in contenu
    assert f"sha={ancien}" in contenu


def test_sentinelle_ne_prend_pas_le_prefixe_t_k_sans_le_deux_points(tmp_path):
    """CONTROLE NEGATIF : le marqueur est `t-k :`, pas `t-k`.

    Un nom d'etape qui porte `T-K` sans les deux points (une etape de
    test du meme prefixe, un workflow nomme T-K) n'est PAS de l'infra : la
    retenue doit etre conservee.
    """
    tete = "3c" * 20
    runner = ScriptedRunner(
        main_sha=tete,
        main_history=[tete],
        main_checks_by_sha={
            tete: _scripts_check("failure", summary="", details_url=_job_url(48)),
        },
        job_steps={"48": "T-K tests du script"},
    )
    hold = tmp_path / "hold.txt"
    rc = mr.run(
        ["--journal", str(tmp_path / "j.jsonl"), "--hold-file", str(hold), "--apply"],
        runner=runner,
    )
    assert rc == 0
    contenu = hold.read_text(encoding="utf-8")
    assert f"sha={tete}" in contenu


def test_sentinelle_success_ne_lit_aucun_job(tmp_path):
    """Un `success` ne declenche aucune lecture de job (cout nul)."""
    tete = "e5" * 20
    runner = ScriptedRunner(
        main_sha=tete,
        main_history=[tete],
        main_checks_by_sha={tete: _scripts_check("success", details_url=_job_url(44))},
        job_steps={"44": "Run actions/checkout@v4"},
    )
    rc = mr.run(
        ["--journal", str(tmp_path / "j.jsonl"), "--hold-file", str(tmp_path / "h.txt"), "--apply"],
        runner=runner,
    )
    assert rc == 0
    lectures = [c for c, _ in runner.calls if "/actions/jobs/" in " ".join(c)]
    assert lectures == []


def test_sentinelle_lit_le_job_une_seule_fois_par_commit_juge(tmp_path):
    """Une seule lecture de job par commit juge, et seulement en cas de
    `failure` sans test identifiable."""
    tete = "f6" * 20
    runner = ScriptedRunner(
        main_sha=tete,
        main_history=[tete],
        main_checks_by_sha={
            tete: _scripts_check("failure", summary="", details_url=_job_url(45)),
        },
        job_steps={"45": "Run tests"},
    )
    rc = mr.run(
        ["--journal", str(tmp_path / "j.jsonl"), "--hold-file", str(tmp_path / "h.txt"), "--apply"],
        runner=runner,
    )
    assert rc == 0
    lectures = [c for c, _ in runner.calls if "/actions/jobs/" in " ".join(c)]
    assert len(lectures) == 1


def test_sentinelle_identifie_un_test_et_ne_lit_aucun_job(tmp_path):
    """Un `failure` dont le resume nomme un test est un verdict de code :
    la retenue porte le nom du test, et aucun job n'est lu."""
    tete = "a7" * 20
    runner = ScriptedRunner(
        main_sha=tete,
        main_history=[tete],
        main_checks_by_sha={
            tete: _scripts_check(
                "failure",
                summary="FAILED scripts/tests/test_x.py::test_y - assertion",
                details_url=_job_url(46),
            ),
        },
        job_steps={"46": "Run actions/checkout@v4"},
    )
    hold = tmp_path / "hold.txt"
    rc = mr.run(
        ["--journal", str(tmp_path / "j.jsonl"), "--hold-file", str(hold), "--apply"],
        runner=runner,
    )
    assert rc == 0
    contenu = hold.read_text(encoding="utf-8")
    assert "test=scripts/tests/test_x.py::test_y" in contenu
    lectures = [c for c, _ in runner.calls if "/actions/jobs/" in " ".join(c)]
    assert lectures == []


def test_clear_main_red_hold_ne_retire_que_la_ligne_de_la_sentinelle(tmp_path):
    """Point 3 : la voie manuelle ne touche PAS les retenues du coordinateur."""
    hold = tmp_path / "hold.txt"
    hold.write_text(
        "16808 attente utilisateur\n"
        "0 main-red-sentinel sha=deadbeef check=Scripts Tests (CPU) "
        "conclusion=failure test=scripts/tests/test_x.py::test_y\n",
        encoding="utf-8",
    )
    assert mr.clear_main_red_hold(hold) is True
    assert hold.read_text(encoding="utf-8") == "16808 attente utilisateur\n"
    # Idempotent : une seconde passe ne trouve plus rien a retirer.
    assert mr.clear_main_red_hold(hold) is False


def test_cli_clear_main_red_hold_nappelle_pas_gh(tmp_path):
    """La voie manuelle sort avant tout appel GitHub."""
    hold = tmp_path / "hold.txt"
    hold.write_text(
        "16808 attente utilisateur\n"
        "0 main-red-sentinel sha=deadbeef check=Scripts Tests (CPU) "
        "conclusion=failure test=scripts/tests/test_x.py::test_y\n",
        encoding="utf-8",
    )
    runner = ScriptedRunner()
    rc = mr.run(
        ["--clear-main-red-hold", "--hold-file", str(hold)], runner=runner
    )
    assert rc == 0
    assert hold.read_text(encoding="utf-8") == "16808 attente utilisateur\n"
    assert runner.flat() == []


# --- disposition de review classee a la tete evaluee (point 1 de #17672) ---------


def test_disposition_approbation_a_la_tete():
    view = default_view(reviews=[review_row(oid=HEAD)])
    assert mr.review_disposition(view, HEAD) == mr.APPROVED_EXACT_HEAD


def test_disposition_approbation_sur_une_tete_ancienne():
    # L'approbation existe, mais elle porte sur un commit anterieur : elle ne
    # couvre pas le commit qui va etre merge.
    view = default_view(reviews=[review_row(oid=HEAD_MOVED)])
    assert mr.review_disposition(view, HEAD) == mr.APPROVAL_NOT_ON_HEAD


def test_disposition_verdict_en_corps_compte_a_la_tete():
    # Le jeton de review du cluster ne peut poster que des COMMENT : son
    # approbation vit dans le CORPS de la voix, pas dans l'etat de l'API (#16926).
    view = default_view(
        reviews=[
            review_row(
                state="COMMENTED",
                oid=HEAD,
                body=(
                    "**[Hermes]** — VERDICT: LGTM "
                    "(contrainte token CoursIA : COMMENT only, #15511)"
                ),
            )
        ]
    )
    assert mr.review_disposition(view, HEAD) == mr.APPROVED_EXACT_HEAD


def test_disposition_voix_posterieure_non_approbatrice_retire_l_approbation():
    # Latest-wins sur la tete : une approbation suivie, sur la MEME tete, d'une
    # voix qui n'approuve pas ne gouverne plus.
    view = default_view(
        reviews=[
            review_row(oid=HEAD, submitted="2026-09-25T03:00:00Z"),
            review_row(
                state="COMMENTED",
                oid=HEAD,
                submitted="2026-09-25T04:00:00Z",
                body="VERDICT: CONCERNS (test rouge depuis le dernier push)",
            ),
        ]
    )
    assert mr.review_disposition(view, HEAD) == mr.APPROVAL_NOT_ON_HEAD


def test_disposition_ligne_non_voix_ne_detronne_pas_l_approbation():
    # Reserve 1 Hermes (2026-09-26) : le latest-wins porte sur les VOIX du
    # canon, pas sur les lignes reviews[]. Un COMMENTED SANS verdict type --
    # la forme reelle des [OVERRIDE] de lane -- n'est pas une voix : il ne
    # detrone pas une approbation posee sur la meme tete. Avant le filtre,
    # cette vue rendait approval-not-on-head alors que l'approbation gouverne.
    view = default_view(
        reviews=[
            review_row(oid=HEAD, submitted="2026-09-25T03:00:00Z"),
            review_row(
                state="COMMENTED",
                oid=HEAD,
                submitted="2026-09-25T04:00:00Z",
                body="[OVERRIDE] lane myia-ai-01:CoursIA -- reserve G-VAR-3 levee",
            ),
        ]
    )
    assert mr.review_disposition(view, HEAD) == mr.APPROVED_EXACT_HEAD


def test_disposition_review_dismissed_n_est_jamais_approbatrice():
    # Reserve 2 Hermes (2026-09-26) : une approbation ANNULEE ne gouverne
    # plus, meme si son corps porte encore le jeton type. Le croisement des
    # deux surfaces (etat DISMISSED + VERDICT en corps) manquait : cette vue
    # rendait approved-exact-head avant le traitement explicite de DISMISSED.
    view = default_view(
        reviews=[
            review_row(
                state="DISMISSED",
                oid=HEAD,
                body="VERDICT: LGTM (annule apres relecture du diff)",
            )
        ]
    )
    assert mr.review_disposition(view, HEAD) == mr.NO_APPROVAL


def test_disposition_sans_approbation_lue():
    assert mr.review_disposition(default_view(coordinator=None), HEAD) == mr.NO_APPROVAL
    # Une voix qui ne type pas de verdict n'est pas une approbation.
    view = default_view(reviews=[review_row(state="COMMENTED")])
    assert mr.review_disposition(view, HEAD) == mr.NO_APPROVAL


def test_deux_prs_qui_ne_different_que_par_la_tete_de_l_approbation(tmp_path):
    """Le defaut vise : a tout le reste egal, l'organe ne distinguait pas une PR
    approuvee a la tete de la PR approuvee sur un commit anterieur."""
    views = {
        201: default_view(pr=201, reviews=[review_row(oid=HEAD)], coordinator=HEAD),
        202: default_view(
            pr=202, reviews=[review_row(oid=HEAD_MOVED)], coordinator=HEAD_MOVED
        ),
    }
    rc, lines, _ = run_organ(
        tmp_path,
        ScriptedRunner(prs=(201, 202), views=views, **refresh_topology()),
    )
    assert rc == 0
    assert [row["verdict"] for row in lines] == ["would-merge", "would-merge"]
    reste = [
        {k: row[k] for k in ("head", "verdict", "reason", "merged")} for row in lines
    ]
    assert reste[0] == reste[1]
    assert lines[0]["review"] == mr.APPROVED_EXACT_HEAD
    assert lines[1]["review"] == mr.APPROVAL_NOT_ON_HEAD


def test_un_skip_porte_la_disposition_de_la_tete_evaluee(tmp_path):
    views = {201: default_view(pr=201, draft=True, reviews=[review_row(oid=HEAD)])}
    rc, lines, _ = run_organ(tmp_path, ScriptedRunner(prs=(201,), views=views))
    assert rc == 0
    assert lines[-1]["reason"] == "draft"
    assert lines[-1]["review"] == mr.APPROVED_EXACT_HEAD


def test_le_bilan_compte_les_candidates_par_disposition(tmp_path, capsys):
    views = {
        201: default_view(pr=201, reviews=[review_row(oid=HEAD)], coordinator=HEAD),
        202: default_view(
            pr=202, reviews=[review_row(oid=HEAD_MOVED)], coordinator=HEAD_MOVED
        ),
    }
    run_organ(
        tmp_path,
        ScriptedRunner(prs=(201, 202), views=views, **refresh_topology()),
    )
    out = capsys.readouterr().out
    assert "candidates : 1 approved-exact-head, 1 approval-not-on-head" in out
    assert "[review: approved-exact-head]" in out

# --- 5bis. collision d'index twin-pairs -----------------------------------------

TWIN_FILE = "scripts/notebook_tools/twin_pairs.d/sw-5-linked-data/0012-2026-09-25-lane.yaml"


def test_twin_organ_not_called_when_registry_untouched(tmp_path):
    """Une PR hors registre twin ne paie ni fetch ni organe."""
    runner = ScriptedRunner()
    rc, lines, _ = run_organ(tmp_path, runner)
    assert rc == 0
    assert lines[0]["verdict"] == "would-merge"
    assert not any("check_twin_index_collisions.py" in f for f in runner.flat())
    assert not any(cmd[:1] == ["git"] for cmd in runner.cmds())


def test_twin_collision_skips(tmp_path):
    view = default_view(files=("src/a.py", TWIN_FILE))
    runner = ScriptedRunner(views={123: view}, twin_rc=1)
    rc, lines, _ = run_organ(tmp_path, runner)
    assert rc == 0
    assert lines[0]["verdict"] == "skipped"
    assert lines[0]["reason"] == "twin-index-collision"


def test_twin_clean_merges_and_compares_the_view_head(tmp_path):
    view = default_view(files=(TWIN_FILE,))
    runner = ScriptedRunner(views={123: view}, twin_rc=0)
    rc, lines, _ = run_organ(tmp_path, runner)
    assert lines[0]["verdict"] == "would-merge"
    twin = [c for c in runner.cmds() if len(c) > 1 and "check_twin_index_collisions.py" in c[1]]
    assert len(twin) == 1
    assert twin[0][twin[0].index("--head") + 1] == HEAD
    assert twin[0][twin[0].index("--base") + 1] == "origin/main"
    # le fetch precede l'organe : le main compare est celui du moment
    flat = runner.flat()
    fetch_at = next(i for i, f in enumerate(flat) if f.startswith("git ") and " fetch " in f)
    twin_at = next(i for i, f in enumerate(flat) if "check_twin_index_collisions.py" in f)
    assert fetch_at < twin_at
    assert "pull/123/head" in flat[fetch_at]


def test_twin_organ_unreadable_is_fail_closed(tmp_path):
    view = default_view(files=(TWIN_FILE,))
    runner = ScriptedRunner(views={123: view}, twin_rc=2)
    rc, lines, _ = run_organ(tmp_path, runner)
    assert lines[0]["verdict"] == "skipped"
    assert lines[0]["reason"] == "twin-collision-unreadable:rc=2"


def test_twin_organ_is_called_with_the_merged_judgment(tmp_path):
    """L'organe est appele en mode `--merged` : c'est l'arbre de fusion qui
    repond a « `main` sera-t-il rouge apres ce merge ? » (mesure du
    2026-11-03 : #23832 et #24010 ont alloue les memes ordinals et sont
    passees tous les deux)."""
    view = default_view(files=(TWIN_FILE,))
    runner = ScriptedRunner(views={123: view}, twin_rc=0)
    run_organ(tmp_path, runner)
    twin = [c for c in runner.cmds()
            if len(c) > 1 and "check_twin_index_collisions.py" in c[1]]
    assert len(twin) == 1
    assert "--merged" in twin[0]


def test_twin_collision_introduite_par_le_merge_skips(tmp_path):
    """Un doublon que le MERGE introduit (et qu'aucune revision ne porte
    isolement) doit faire sauter le merge : c'est exactement le cas que le
    seul jugement base+tete laissait passer."""
    payload = json.dumps({
        "cross_ref": [],
        "merged_reasons": [{
            "pair": "search-05-geneticalgorithms",
            "index": "0024",
            "names": ["0024-a.yaml", "0024-b.yaml"],
            "added": ["0024-b.yaml"],
            "gist": "renumeroter par `git mv` PUR",
        }],
        "merged_unreadable": None,
    })
    view = default_view(files=(TWIN_FILE,))
    runner = ScriptedRunner(views={123: view}, twin_rc=1, twin_stdout=payload)
    rc, lines, _ = run_organ(tmp_path, runner)
    assert lines[0]["verdict"] == "skipped"
    assert lines[0]["reason"].startswith("twin-collision-on-merge:")
    assert "search-05-geneticalgorithms/0024" in lines[0]["reason"]


def test_twin_arbre_de_fusion_illisible_is_fail_closed(tmp_path):
    """« je n'ai pas pu lire » n'est pas « c'est propre » : l'arbre de fusion
    illisible (merge en conflit) fait sauter le merge, meme quand le jugement
    classique ne bloque rien (rc 0)."""
    payload = json.dumps({
        "cross_ref": [],
        "merged_reasons": [],
        "merged_unreadable": "merge-tree --write-tree : conflit",
    })
    view = default_view(files=(TWIN_FILE,))
    runner = ScriptedRunner(views={123: view}, twin_rc=0, twin_stdout=payload)
    rc, lines, _ = run_organ(tmp_path, runner)
    assert lines[0]["verdict"] == "skipped"
    assert lines[0]["reason"] == "twin-collision-unreadable:merged"


# --- 5bis.ter. attestation jumelle decrivant l'arbre de fusion (#28202) --------


def _attestation_payload(verdict: str, reason: str) -> str:
    """Rapport JSON de l'organe d'attestation, forme reelle."""
    return json.dumps({
        "verdict": verdict,
        "base": "origin/main",
        "head": HEAD,
        "tree": "a" * 40,
        "pairs": [{
            "pair": "sw-5-linked-data",
            "verdict": verdict,
            "attestation": "0012-2026-09-25-lane.yaml",
            "details": [reason],
        }],
        "reason": f"sw-5-linked-data {verdict} : {reason}",
    })


def test_twin_attestation_mismatch_skips(tmp_path):
    """Un sha atteste qui ne decrit pas l'arbre de fusion fait sauter le
    merge : c'est la classe que la CI de PR ne voit pas et qui rougit `main`
    apres le squash (#28202)."""
    reason = "csharp_sha atteste aaaaaaaaaaaa / arbre de fusion bbbbbbbbbbbb"
    payload = _attestation_payload("MISMATCH", reason)
    view = default_view(files=(TWIN_FILE,))
    runner = ScriptedRunner(views={123: view}, attest_rc=1, attest_stdout=payload)
    rc, lines, _ = run_organ(tmp_path, runner)
    assert rc == 0
    assert lines[0]["verdict"] == "skipped"
    assert lines[0]["reason"].startswith("twin-attestation-mismatch:")
    assert "sw-5-linked-data" in lines[0]["reason"]


def test_twin_attestation_unreadable_is_fail_closed(tmp_path):
    """« Je n'ai pas pu lire » n'est pas « c'est propre » : une mesure
    impossible (rc 2) fait sauter le merge."""
    view = default_view(files=(TWIN_FILE,))
    runner = ScriptedRunner(views={123: view}, attest_rc=2)
    rc, lines, _ = run_organ(tmp_path, runner)
    assert lines[0]["verdict"] == "skipped"
    assert lines[0]["reason"] == "twin-attestation-unreadable:rc=2"


def test_twin_attestation_sortie_illisible_is_fail_closed(tmp_path):
    """Une sortie non JSON sur rc 1 n'est pas un « conforme » deguise : le
    motif reste un skip fail-closed."""
    view = default_view(files=(TWIN_FILE,))
    runner = ScriptedRunner(views={123: view}, attest_rc=1, attest_stdout="pas du json")
    rc, lines, _ = run_organ(tmp_path, runner)
    assert lines[0]["verdict"] == "skipped"
    assert lines[0]["reason"] == "twin-attestation-unreadable:sortie-illisible"


def test_twin_attestation_clean_merges_and_interroge_le_tete_evaluee(tmp_path):
    """Conforme : le merge se fait, et l'organe est interroge sur la base et
    la tete EVALUEES (pas sur `main` courant, pas sur la branche)."""
    view = default_view(files=(TWIN_FILE,))
    runner = ScriptedRunner(views={123: view}, attest_rc=0)
    rc, lines, _ = run_organ(tmp_path, runner)
    assert lines[0]["verdict"] == "would-merge"
    calls = [c for c in runner.cmds()
             if len(c) > 1 and "check_twin_attestation_squash.py" in c[1]]
    assert len(calls) == 1
    assert calls[0][calls[0].index("--base") + 1] == "origin/main"
    assert calls[0][calls[0].index("--head") + 1] == HEAD


def test_twin_attestation_organ_not_called_when_registry_untouched(tmp_path):
    """Une PR hors registre twin ne paie ni fetch ni organe d'attestation."""
    runner = ScriptedRunner()
    rc, lines, _ = run_organ(tmp_path, runner)
    assert lines[0]["verdict"] == "would-merge"
    assert not any("check_twin_attestation_squash.py" in f for f in runner.flat())


def test_twin_collision_avec_une_pr_ouverte_skips(tmp_path):
    """Un ordinal revendique par une PR CONCURRENTE encore ouverte doit faire
    sauter le merge : ni le jugement base+tete ni l'arbre de fusion ne le
    voient (les deux ne portent que des revisions mergees), et la collision
    n'apparaitrait qu'apres le second merge -- en rouge fleet-wide (mesure du
    2026-11-04 : 5 collisions de ce type etaient vivantes entre PRs
    ouvertes)."""
    payload = json.dumps({
        "cross_ref": [],
        "merged_reasons": [],
        "merged_unreadable": None,
        "open_pr_reasons": [{
            "pair": "csp-6-hybridization",
            "index": "0024",
            "names": ["0024-a.yaml", "0024-b.yaml"],
            "prs": [123, 999],
            "gist": "renumeroter par `git mv` PUR",
        }],
    })
    view = default_view(files=(TWIN_FILE,))
    runner = ScriptedRunner(views={123: view}, twin_rc=1, twin_stdout=payload)
    rc, lines, _ = run_organ(tmp_path, runner)
    assert lines[0]["verdict"] == "skipped"
    assert lines[0]["reason"].startswith("twin-collision-open-pr:")
    assert "csp-6-hybridization/0024" in lines[0]["reason"]


def test_twin_revendications_illisibles_is_fail_closed(tmp_path):
    """« je n'ai pas pu lire » n'est pas « c'est propre » : l'API des PRs
    ouvertes illisible fait sauter le merge, comme le fetch de l'arbre de
    fusion."""
    view = default_view(files=(TWIN_FILE,))
    runner = ScriptedRunner(views={123: view}, claims_rc=2)
    rc, lines, _ = run_organ(tmp_path, runner)
    assert lines[0]["verdict"] == "skipped"
    assert lines[0]["reason"] == "twin-collision-unreadable:open-claims"


def test_twin_fetch_failure_is_fail_closed(tmp_path):
    view = default_view(files=(TWIN_FILE,))
    runner = ScriptedRunner(views={123: view}, fetch_rc=128)
    rc, lines, _ = run_organ(tmp_path, runner)
    assert lines[0]["verdict"] == "skipped"
    assert lines[0]["reason"] == "twin-collision-unreadable:fetch"
    assert not any("check_twin_index_collisions.py" in f for f in runner.flat())


def test_twin_mixed_multipr_and_unknown_then_fails_closed(tmp_path):
    """#18823 : un mix MULTI-PR + verdict absent/inconnu doit refuser, pas
    laisser passer comme avertissement seul. La classification d'UNE
    collision illisible ne peut pas se deduire des autres."""
    view = default_view(files=(TWIN_FILE,))
    twin_stdout = json.dumps({
        "cross_ref": [
            {"pair": "sw-5-linked-data", "index": "0012",
             "verdict": "MULTI-PR"},
            {"pair": "sw-5-linked-data", "index": "0012",
             "verdict": None},
        ],
        "base_ref": "origin/main",
    })
    runner = ScriptedRunner(views={123: view}, twin_rc=1,
                            twin_stdout=twin_stdout)
    rc, lines, _ = run_organ(tmp_path, runner)
    assert lines[0]["verdict"] == "skipped"
    assert lines[0]["reason"] == "twin-index-collision"


def test_twin_pure_multipr_warns_only(tmp_path):
    """Quand toutes les collisions portent MULTI-PR, l'organe laisse passer
    avec avertissement seul (la premiere mergee gagne)."""
    view = default_view(files=(TWIN_FILE,))
    twin_stdout = json.dumps({
        "cross_ref": [
            {"pair": "sw-5-linked-data", "index": "0012",
             "verdict": "MULTI-PR"},
            {"pair": "sw-5-linked-data", "index": "0012",
             "verdict": "MULTI-PR"},
        ],
        "base_ref": "origin/main",
    })
    runner = ScriptedRunner(views={123: view}, twin_rc=1,
                            twin_stdout=twin_stdout)
    rc, lines, _ = run_organ(tmp_path, runner)
    assert lines[0]["verdict"] == "would-merge"


def test_twin_pure_onmain_skips(tmp_path):
    """Quand au moins une collision est ON-MAIN, l'organe skip dur et
    nomme la premiere collision ON-MAIN dans le motif."""
    view = default_view(files=(TWIN_FILE,))
    twin_stdout = json.dumps({
        "cross_ref": [
            {"pair": "sw-5-linked-data", "index": "0012",
             "verdict": "ON-MAIN"},
            {"pair": "sw-5-linked-data", "index": "0013",
             "verdict": "MULTI-PR"},
        ],
        "base_ref": "origin/main",
    })
    runner = ScriptedRunner(views={123: view}, twin_rc=1,
                            twin_stdout=twin_stdout)
    rc, lines, _ = run_organ(tmp_path, runner)
    assert lines[0]["verdict"] == "skipped"
    assert lines[0]["reason"].startswith("twin-collision-on-main:sw-5-linked-data/0012")


# --- 5bis.bis. slot-reservation-guard en mode en ligne (#20774) ----------------


# Un carnet de la serie ICT pour les tests : le prefixe `MyIA.AI.Notebooks/`
# active le filtre prefixe, le suffixe `.ipynb` (et non `_output.ipynb`)
# active le filtre de type.
SLOT_NOTEBOOK = "MyIA.AI.Notebooks/IIT/ICT-Series/ICT-48-Foo-Python.ipynb"
SLOT_OTHER_NOTEBOOK = "MyIA.AI.Notebooks/IIT/ICT-Series/ICT-50-Bar-Python.ipynb"


def test_slot_organ_not_called_when_no_notebook(tmp_path):
    """Une PR sans carnet (CI-only) ne paie ni fetch ni organe slot."""
    runner = ScriptedRunner()
    rc, lines, _ = run_organ(tmp_path, runner)
    assert lines[0]["verdict"] == "would-merge"
    flat = runner.flat()
    assert not any("check_slot_reservation.py" in f for f in flat)


def test_slot_organ_not_called_when_only_output_ipynb(tmp_path):
    """Les `_output.ipynb` (papermill) ne sont pas des carnets source ; le
    filtre de suffixe les exclut. Mesure du 2026-10 : la moitie des PRs qui
    touchent la serie IIT n'edite que la papermill-sortie, jamais le source."""
    view = default_view(
        files=("MyIA.AI.Notebooks/IIT/ICT-Series/ICT-48-Foo_output.ipynb",),
    )
    runner = ScriptedRunner(views={123: view})
    rc, lines, _ = run_organ(tmp_path, runner)
    assert lines[0]["verdict"] == "would-merge"
    flat = runner.flat()
    assert not any("check_slot_reservation.py" in f for f in flat)


def test_slot_clean_merges(tmp_path):
    """slot_rc=0 -> skip a 0, l'organe est appele avec --exclude-pr et --json
    (mode en ligne : pas de --offline, sources arbre + revision + open_prs +
    declared)."""
    view = default_view(files=(SLOT_NOTEBOOK,))
    runner = ScriptedRunner(views={123: view})
    rc, lines, _ = run_organ(tmp_path, runner)
    assert lines[0]["verdict"] == "would-merge"
    flat = runner.flat()
    slot_cmd = next(f for f in flat if "check_slot_reservation.py" in f)
    # Mode en ligne : JAMAIS --offline
    assert "--offline" not in slot_cmd
    # Le merge exclut sa PROPRE PR de la source open_prs (sinon collision
    # avec elle-meme).
    assert "--exclude-pr 123" in slot_cmd
    assert "--json" in slot_cmd
    assert "--base origin/main" in slot_cmd
    # La tete passee est celle de la vue -- celle que l'approbation couvre
    # et que l'etape 6 epingle au merge.
    assert f"--head {HEAD}" in slot_cmd


def test_slot_fetches_pr_head_before_organ(tmp_path):
    """L'organe lit l'arbre de la tete par `git` sans la rapatrier : le fetch
    de `pull/<N>/head` precede l'appel (mesure du 17/10, #20468 et #20471
    sautees en `slot-collision-unreadable` faute d'objet local)."""
    view = default_view(files=(SLOT_NOTEBOOK,))
    runner = ScriptedRunner(views={123: view})
    rc, lines, _ = run_organ(tmp_path, runner)
    assert lines[0]["verdict"] == "would-merge"
    flat = runner.flat()
    fetch_idx = next(i for i, f in enumerate(flat)
                     if f.startswith("git ") and "pull/123/head" in f)
    slot_idx = next(i for i, f in enumerate(flat)
                    if "check_slot_reservation.py" in f)
    assert fetch_idx < slot_idx


def test_slot_fetch_failure_is_fail_closed(tmp_path):
    """Fetch en echec : skip nomme, l'organe n'est pas appele sur une tete
    qu'il ne pourrait pas lire."""
    view = default_view(files=(SLOT_NOTEBOOK,))
    runner = ScriptedRunner(views={123: view}, fetch_rc=128)
    rc, lines, _ = run_organ(tmp_path, runner)
    assert lines[0]["verdict"] == "skipped"
    assert lines[0]["reason"] == "slot-collision-unreadable:fetch"
    assert not any("check_slot_reservation.py" in f for f in runner.flat())


def test_slot_collision_reserved_by_open_pr_skips(tmp_path):
    """L'organe detecte une collision avec une autre PR ouverte (ICT-48 et
    SL-12b mesures le 14/10 dans #20774) : skip dur, motif nomme."""
    view = default_view(files=(SLOT_NOTEBOOK,))
    slot_stdout = json.dumps({
        "verdicts": [
            {"target": SLOT_NOTEBOOK, "verdict": "conflict",
             "conflicts": [{"state": "reserved_by_open_pr",
                            "source": "open_pr", "detail": "#19853"}]},
        ],
    })
    runner = ScriptedRunner(views={123: view}, slot_rc=1,
                            slot_stdout=slot_stdout)
    rc, lines, _ = run_organ(tmp_path, runner)
    assert lines[0]["verdict"] == "skipped"
    reason = lines[0]["reason"]
    assert reason.startswith("slot-collision-on-merge:reserved_by_open_pr")
    assert "ICT-48-Foo-Python.ipynb" in reason


def test_slot_collision_taken_on_base_skips(tmp_path):
    """L'organe detecte qu'un slot est deja tenu par la base (la collision ICT-48
    une fois la premiere PR mergee)."""
    view = default_view(files=(SLOT_OTHER_NOTEBOOK,))
    slot_stdout = json.dumps({
        "verdicts": [
            {"target": SLOT_OTHER_NOTEBOOK, "verdict": "conflict",
             "conflicts": [{"state": "taken_on_base", "source": "base"}]},
        ],
    })
    runner = ScriptedRunner(views={123: view}, slot_rc=1,
                            slot_stdout=slot_stdout)
    rc, lines, _ = run_organ(tmp_path, runner)
    assert lines[0]["verdict"] == "skipped"
    assert lines[0]["reason"].startswith("slot-collision-on-merge:taken_on_base")


def test_slot_collision_legacy_unclassed_falls_back(tmp_path):
    """Un organe anterieur a #20774 rend rc=1 sans JSON classifie : on
    retombe sur le motif historique `slot-collision` (retro-compat)."""
    view = default_view(files=(SLOT_NOTEBOOK,))
    runner = ScriptedRunner(views={123: view}, slot_rc=1, slot_stdout="")
    rc, lines, _ = run_organ(tmp_path, runner)
    assert lines[0]["verdict"] == "skipped"
    assert lines[0]["reason"] == "slot-collision"


def test_slot_organ_unreadable_is_fail_closed(tmp_path):
    """rc=2 = lecture impossible (reseau, gh auth, etc.) : skip, jamais
    merge en aveugle. Meme politique que `twin_collision_reason` 5bis."""
    view = default_view(files=(SLOT_NOTEBOOK,))
    runner = ScriptedRunner(views={123: view}, slot_rc=2)
    rc, lines, _ = run_organ(tmp_path, runner)
    assert lines[0]["verdict"] == "skipped"
    assert lines[0]["reason"] == "slot-collision-unreadable"


def test_slot_organ_unexpected_rc_is_fail_closed(tmp_path):
    """Un rc hors contrat (3, 4, 137 = OOM kill, ...) est inattendu : skip
    nomme plutot que de merger en aveugle."""
    view = default_view(files=(SLOT_NOTEBOOK,))
    runner = ScriptedRunner(views={123: view}, slot_rc=137)
    rc, lines, _ = run_organ(tmp_path, runner)
    assert lines[0]["verdict"] == "skipped"
    assert lines[0]["reason"] == "slot-collision-unreadable:rc=137"


# --- 2ter. approbation du coordinateur (Q67, arbitrage user 2026-09-28) ----------


def refresh_topology(*, tree: str | None = "7ee0", head_parents=None) -> dict:
    """HEAD = fusion de rafraichissement de base au-dessus de HEAD_MOVED.

    ``tree`` est l'arbre de la fusion ; ``auto_tree`` rendu par merge-tree est
    toujours ``7ee0`` -- les deux egaux = fusion PROUVEE content-free.
    """
    parents = head_parents or [HEAD_MOVED, BASE]
    head_commit = {"commit": {"committer": {"date": "2026-09-28T10:00:00Z"}},
                   "parents": [{"sha": p} for p in parents]}
    if tree is not None:
        head_commit["commit"]["tree"] = {"sha": tree}
    return {
        "commits": {
            HEAD: head_commit,
            HEAD_MOVED: {
                "commit": {"committer": {"date": "2026-09-28T08:00:00Z"}},
                "parents": [{"sha": "r00t"}],
            },
        },
        "auto_tree": "7ee0",
    }


def test_sans_approbation_du_coordinateur_skip_avant_les_organes(tmp_path):
    runner = ScriptedRunner(views={123: default_view(coordinator=None)})
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert lines[-1]["reason"] == "no-coordinator-approval"
    assert lines[-1]["merged"] is False
    # une PR non lue ne paie ni la porte STACK ni les organes
    assert not any("check_unaddressed_nits.py" in f for f in runner.flat())


def test_approbation_d_un_autre_login_ne_compte_pas(tmp_path):
    """Un APPROVED de bot ou du login partage des lanes n'est pas la lecture
    du coordinateur, meme a la tete exacte."""
    for login in ("clusterManager-Myia", "jsboige"):
        view = default_view(reviews=[review_row(oid=HEAD, login=login)])
        runner = ScriptedRunner(views={123: view})
        _, lines, _ = run_organ(tmp_path, runner)
        assert lines[-1]["reason"] == "no-coordinator-approval", login


def test_changes_requested_posterieur_retire_l_approbation(tmp_path):
    view = default_view(
        reviews=[
            coordinator_review(oid=HEAD),
            coordinator_review(
                state="CHANGES_REQUESTED", oid=HEAD, submitted="2026-09-26T00:00:00Z"
            ),
        ]
    )
    _, lines, _ = run_organ(tmp_path, ScriptedRunner(views={123: view}))
    assert lines[-1]["reason"] == "no-coordinator-approval"


def test_verdict_concerns_en_corps_posterieur_retire_l_approbation(tmp_path):
    view = default_view(
        reviews=[
            coordinator_review(oid=HEAD),
            coordinator_review(
                state="COMMENTED", oid=HEAD, submitted="2026-09-26T00:00:00Z",
                body="VERDICT: CONCERNS\npoint a reprendre",
            ),
        ]
    )
    _, lines, _ = run_organ(tmp_path, ScriptedRunner(views={123: view}))
    assert lines[-1]["reason"] == "no-coordinator-approval"


def test_commented_sans_verdict_posterieur_ne_retire_pas_l_approbation(tmp_path):
    """Une phrase de levee postee en review n'est pas une voix : l'approbation tient."""
    view = default_view(
        reviews=[
            coordinator_review(oid=HEAD),
            coordinator_review(
                state="COMMENTED", oid=HEAD, submitted="2026-09-26T00:00:00Z",
                body="Point 2 leve : traite par le commit abc.",
            ),
        ]
    )
    _, lines, _ = run_organ(tmp_path, ScriptedRunner(views={123: view}))
    assert lines[-1]["verdict"] == "would-merge"


def test_approbation_dismissed_ne_compte_pas(tmp_path):
    view = default_view(reviews=[coordinator_review(state="DISMISSED", oid=HEAD)])
    _, lines, _ = run_organ(tmp_path, ScriptedRunner(views={123: view}))
    assert lines[-1]["reason"] == "no-coordinator-approval"


def test_rafraichissement_de_base_prouve_ne_perime_pas_la_lecture(tmp_path):
    """Approbation sur HEAD_MOVED, puis update-branch sans conflit -> HEAD :
    la lecture couvre encore le contenu, l'organe merge."""
    view = default_view(coordinator=HEAD_MOVED)
    runner = ScriptedRunner(views={123: view}, **refresh_topology())
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert lines[-1]["merged"] is True


def test_resolution_de_conflit_perime_la_lecture(tmp_path):
    """Meme topologie, mais l'arbre de la fusion differe de l'auto-merge :
    du contenu d'auteur est entre, la lecture est perimee."""
    view = default_view(coordinator=HEAD_MOVED)
    runner = ScriptedRunner(views={123: view}, **refresh_topology(tree="d1ff"))
    _, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert lines[-1]["reason"] == "coordinator-approval-stale"
    assert lines[-1]["merged"] is False


def test_commit_de_contenu_apres_l_approbation_perime_la_lecture(tmp_path):
    """HEAD est un commit ordinaire au-dessus de HEAD_MOVED : perime."""
    view = default_view(coordinator=HEAD_MOVED)
    runner = ScriptedRunner(
        views={123: view}, **refresh_topology(head_parents=[HEAD_MOVED])
    )
    _, lines, _ = run_organ(tmp_path, runner)
    assert lines[-1]["reason"] == "coordinator-approval-stale"


def test_skip_2ter_porte_review_ready_en_disposition(tmp_path):
    """#17672 point 2 : quand une PR skip a l'etape 2ter (approbation
    coordinateur), toutes les portes delegables en amont sont vertes
    (perimetre, tag Grain, parapluie gele). La disposition portee est
    ``review-ready`` -- le dashboard coordinateur distingue alors « PR qui
    n'attend que sa relecture » de « PR qui a un autre probleme »."""
    view = default_view(coordinator=HEAD_MOVED)
    runner = ScriptedRunner(views={123: view}, **refresh_topology(tree="d1ff"))
    _, lines, _ = run_organ(tmp_path, runner)
    assert lines[-1]["reason"] == "coordinator-approval-stale"
    assert lines[-1]["review"] == "review-ready"


def test_skip_sans_approbation_porte_review_ready(tmp_path):
    """#17672 point 2 : variante ``no-coordinator-approval`` (aucune voix
    approbatrice du coordinateur). La disposition est toujours
    ``review-ready`` puisque les portes delegables en amont sont vertes."""
    runner = ScriptedRunner(views={123: default_view(coordinator=None)})
    _, lines, _ = run_organ(tmp_path, runner)
    assert lines[-1]["reason"] == "no-coordinator-approval"
    assert lines[-1]["review"] == "review-ready"


def test_skip_prefiltre_ne_porte_pas_review_ready(tmp_path):
    """#17672 point 2 : un skip en AMONT de 2ter (ici, brouillon) garde
    la disposition review brute (``no-approval``), pas ``review-ready`` :
    les portes delegables ne sont pas toutes vertes, l'etat REVIEW_READY
    ne s'applique pas."""
    view = default_view(coordinator=None)
    view["isDraft"] = True
    runner = ScriptedRunner(views={123: view})
    _, lines, _ = run_organ(tmp_path, runner)
    assert lines[-1]["reason"] == "draft"
    assert lines[-1]["review"] == "no-approval"


def test_preuve_illisible_fail_closed(tmp_path):
    view = default_view(coordinator=HEAD_MOVED)
    runner = ScriptedRunner(views={123: view}, commits={})
    _, lines, _ = run_organ(tmp_path, runner)
    assert lines[-1]["reason"] == "coordinator-approval-unverifiable"


def test_base_absente_fail_closed(tmp_path):
    view = default_view(coordinator=HEAD_MOVED)
    view["baseRefOid"] = ""
    _, lines, _ = run_organ(tmp_path, ScriptedRunner(views={123: view}))
    assert lines[-1]["reason"] == "coordinator-approval-unverifiable:no-base"


# --- #17437 : l'APPROVE du coordinateur sous identite GitHub App -------------
#
# Mesure ai-01 du 2026-11-04 : sous identite App, la porte ne trouvait pas
# l'APPROVE — la voix du coordinateur etait cablee sur le seul login humain.
# L'App de MACHINE a d'abord ete cablee comme seconde voix ; l'arbitrage
# ai-01 du 2026-11-13 l'a RETIREE : la cle privee de ``coursia-lane-ai-01``
# vit sur la machine ai-01 (``.secrets/github-apps/coursia-lane-ai-01.pem``),
# ou tourne aussi la lane worker sœur ``myia-ai-01:CoursIA-2`` : elle lit le
# meme fichier et forge le meme jeton. Une App nommee par MACHINE ne peut
# pas representer la lane coordinateur seule.
#
# L'App PROPRE existe desormais (Q187, 2026-11-14) : App 5763709, slug
# ``coursia-coord-ai01``, cle dediee
# ``.secrets/github-apps/coursia-coord-ai01.pem`` DISTINCTE de la cle de
# machine — seule la lane coordinateur la lit. Elle rejoint la voix du
# coordinateur ; l'App de machine reste refusee.
#
# Le mecanisme de preuve d'identite reste en place et reste teste : la
# preuve est le TYPE PORTE PAR LA LIGNE (REST ``user.type``, GraphQL
# ``author.__typename``), JAMAIS une sonde ``users/<slug>[bot]``. Une ligne
# sans type est refusee ; l'orthographe canonique nue de l'humain
# (``myia-ai-01``) reste valable sur la surface CLI non typee.

APP_LOGIN_BARE = "coursia-lane-ai-01"
APP_LOGIN_REST = "coursia-lane-ai-01[bot]"
COORD_APP_BARE = "coursia-coord-ai01"
COORD_APP_REST = "coursia-coord-ai01[bot]"


def rest_review(*, login: str, type_: str = "Bot",
                state: str = "APPROVED", oid: str = HEAD,
                submitted: str = "2026-09-25T03:00:00Z",
                body: str = "") -> dict:
    """Ligne de la surface REST typee ``pulls/N/reviews`` (forme brute)."""
    return {
        "user": {"login": login, "type": type_},
        "state": state, "body": body,
        "submitted_at": submitted, "commit_id": oid,
    }


def test_17437_app_login_rest_typee_n_est_pas_la_voix(tmp_path):
    """Orthographe REST typée (``pulls/N/reviews`` : login suffixé +
    ``user.type: Bot``) : le TYPE de la ligne est correct, mais l'App de
    MACHINE n'est pas la voix du coordinateur (arbitrage ai-01 du
    2026-11-13) — la lane sœur d'ai-01 forge le même jeton. La porte reste
    fermée, et la preuve vient toujours de la ligne."""
    view = default_view(reviews=[])
    runner = ScriptedRunner(
        views={123: view},
        rest_reviews=[rest_review(login=APP_LOGIN_REST)],
    )
    _, lines, _ = run_organ(tmp_path, runner)
    assert lines[-1]["reason"] == "no-coordinator-approval"
    # la preuve vient de la ligne, jamais d'une sonde users/
    assert not any("users/" in f for f in runner.flat())
    assert any("/reviews" in f for f in runner.flat())


def test_17437_approve_app_login_nu_sans_type_refuse_meme_app_existante(tmp_path):
    """LE test manquant de la relecture ai-01 : une ligne
    ``{"login": "coursia-lane-ai-01"}`` SANS type, la sonde etant scriptee
    a ``Bot`` (l'App existe bel et bien). Elle ne doit NI approuver NI
    compter — la preuve est le type de la ligne, pas l'existence de l'App."""
    view = default_view(reviews=[review_row(oid=HEAD, login=APP_LOGIN_BARE)])
    runner = ScriptedRunner(
        views={123: view},
        user_types={f"users/{APP_LOGIN_BARE}[bot]": "Bot"},
    )
    _, lines, _ = run_organ(tmp_path, runner)
    assert lines[-1]["reason"] == "no-coordinator-approval"
    # la sonde a disparu : meme scriptee, elle n'est plus appelee
    assert not any("users/" in f for f in runner.flat())


def test_17437_app_login_nu_type_dans_payload_refuse(tmp_path):
    """Preuve de type dans le payload (GraphQL ``__typename: Bot``) : la
    normalisation gh_identity reconstruit bien le suffixe, et le résultat
    est refusé — l'App de machine n'est pas la voix coordinatrice."""
    view = default_view(reviews=[{
        "author": {"login": APP_LOGIN_BARE, "__typename": "Bot"},
        "state": "APPROVED", "body": "",
        "submittedAt": "2026-09-25T03:00:00Z",
        "commit": {"oid": HEAD},
    }])
    runner = ScriptedRunner(views={123: view})
    _, lines, _ = run_organ(tmp_path, runner)
    assert lines[-1]["reason"] == "no-coordinator-approval"
    assert not any("users/" in f for f in runner.flat())


def test_17437_approve_humain_surf_rest_typee_compte(tmp_path):
    """L'humain sur la surface typee : ``user.type: User`` nu canonique —
    la normalisation le laisse nu, il est la voix."""
    view = default_view(reviews=[])
    runner = ScriptedRunner(
        views={123: view},
        rest_reviews=[rest_review(login="myia-ai-01", type_="User")],
    )
    rc, lines, _ = run_organ(tmp_path, runner)
    assert lines[-1]["verdict"] == "would-merge"


def test_17437_approve_surf_rest_typee_latest_wins(tmp_path):
    """Latest-wins preserve par le mapping REST, sur la voix qui compte :
    un CHANGES_REQUESTED posterieur de l'HUMAIN retire son approbation
    anterieure."""
    view = default_view(reviews=[])
    runner = ScriptedRunner(
        views={123: view},
        rest_reviews=[
            rest_review(login="myia-ai-01", type_="User", state="APPROVED",
                        submitted="2026-09-25T03:00:00Z"),
            rest_review(login="myia-ai-01", type_="User",
                        state="CHANGES_REQUESTED",
                        submitted="2026-09-25T04:00:00Z"),
        ],
    )
    _, lines, _ = run_organ(tmp_path, runner)
    assert lines[-1]["reason"] == "no-coordinator-approval"


def test_17437_approve_app_d_une_autre_lane_ne_compte_pas(tmp_path):
    """Point Hermes : l'App d'une autre lane, MEME typee Bot sur la surface
    REST, n'est pas la voix du siege — le prefixe seul ne suffit pas."""
    view = default_view(reviews=[])
    runner = ScriptedRunner(
        views={123: view},
        rest_reviews=[rest_review(login="coursia-lane-po-2026[bot]")],
    )
    _, lines, _ = run_organ(tmp_path, runner)
    assert lines[-1]["reason"] == "no-coordinator-approval"


def test_17437_voix_du_coordinateur_humain_et_app_propre():
    """Q187 (2026-11-14) : ``COORDINATOR_VOICES`` porte le login humain PLUS
    l'App PROPRE a la lane coordinateur (cle dediee, hors de portee de la
    lane sœur). Potence double : l'App de MACHINE ``coursia-lane-ai-01[bot]``
    doit rester ABSENTE — si une edition future l'y ajoute (cle lisible par
    ``myia-ai-01:CoursIA-2``), ce rouge le dit avant que la porte Q131 ne
    s'ouvre."""
    assert mr.COORDINATOR_VOICES == frozenset(("myia-ai-01", COORD_APP_REST))
    assert APP_LOGIN_REST not in mr.COORDINATOR_VOICES


def test_17437_approve_app_propre_surf_rest_typee_compte(tmp_path):
    """L'App PROPRE sur la surface REST typee : login suffixe +
    ``user.type: Bot`` — le type porte par la ligne prouve l'identite, la
    cle dediee n'est lisible que de la lane coordinateur : l'APPROVE ouvre
    la porte Q131."""
    view = default_view(reviews=[])
    runner = ScriptedRunner(
        views={123: view},
        rest_reviews=[rest_review(login=COORD_APP_REST, type_="Bot")],
    )
    rc, lines, _ = run_organ(tmp_path, runner)
    assert lines[-1]["verdict"] == "would-merge"
    # la preuve vient de la ligne, jamais d'une sonde users/
    assert not any("users/" in f for f in runner.flat())
    assert any("/reviews" in f for f in runner.flat())


def test_17437_approve_app_propre_typbot_graphql_compte(tmp_path):
    """Orthographe GraphQL : login NU ``coursia-coord-ai01`` avec
    ``__typename: Bot`` — la normalisation reconstruit le suffixe, la ligne
    typee est la voix du coordinateur."""
    view = default_view(reviews=[{
        "author": {"login": COORD_APP_BARE, "__typename": "Bot"},
        "state": "APPROVED", "body": "",
        "submittedAt": "2026-09-25T03:00:00Z",
        "commit": {"oid": HEAD},
    }])
    runner = ScriptedRunner(views={123: view})
    rc, lines, _ = run_organ(tmp_path, runner)
    assert lines[-1]["verdict"] == "would-merge"
    assert not any("users/" in f for f in runner.flat())


def test_17437_approve_app_propre_homonyme_utilisateur_refuse(tmp_path):
    """L'homonyme UTILISATEUR du slug (``__typename: User``) : la
    normalisation laisse le login NU, il echoue la borne suffixee — un
    compte humain nomme comme l'App ne passe pas pour elle."""
    view = default_view(reviews=[{
        "author": {"login": COORD_APP_BARE, "__typename": "User"},
        "state": "APPROVED", "body": "",
        "submittedAt": "2026-09-25T03:00:00Z",
        "commit": {"oid": HEAD},
    }])
    runner = ScriptedRunner(views={123: view})
    _, lines, _ = run_organ(tmp_path, runner)
    assert lines[-1]["reason"] == "no-coordinator-approval"
    assert not any("users/" in f for f in runner.flat())


def test_17437_approve_app_propre_nu_sans_type_refuse(tmp_path):
    """Forme NUE sans type sur la surface CLI : la preuve fait defaut, la
    ligne n'est pas une voix — fail-closed, meme si l'App existe."""
    view = default_view(reviews=[review_row(oid=HEAD, login=COORD_APP_BARE)])
    runner = ScriptedRunner(views={123: view})
    _, lines, _ = run_organ(tmp_path, runner)
    assert lines[-1]["reason"] == "no-coordinator-approval"
    assert not any("users/" in f for f in runner.flat())


# --- #19002 : defense en profondeur sur la base -----------------------------
# Le gate refusait READY si la base n'est pas `main` (cf test_base_* dans
# test_check_adjoint_prevalidation.py) ; depuis le retrait du dossier
# (2026-11-05), merge_ready porte seul ce controle et verifie
# independamment : un chemin futur qui court-circuiterait la verification
# ne doit pas suffire a merger dans une branche morte. Trois tests :
# temoin positif (base main, chemin nominal inchange), temoin negatif sur
# une base de feature ouverte (#18985/#18967), temoin negatif sur une
# base morte (#18819).


def test_base_main_does_not_change_merge_ready_outcome(tmp_path):
    """Temooin positif : avec `view.baseRefName = 'main'`, le merge_ready
    n'invoque pas la nouvelle raison de skip. Le chemin nominal d'une
    PR a base main reste inchange."""
    runner = ScriptedRunner(views={123: default_view()})
    assert runner.views[123]["baseRefName"] == "main"
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    # Le verdict par defaut d'un ScriptedRunner est would-merge (tous les
    # controles passent). Ce qui compte ici : aucune
    # ligne ne porte le motif `base-not-main:` (le champ reason est None
    # sur les merges reussis, donc on teste avec get(..., "")).
    for line in lines:
        reason = line.get("reason") or ""
        assert "base-not-main" not in reason, lines


def test_base_feature_open_triggers_base_live_not_main_skip(tmp_path):
    """Temooin negatif (#19014) : PR empilee sur une branche de feature
    encore ouverte. merge_ready distingue ce cas d'une base morte : le
    motif `base-live-not-main:<branche>` dit a la lane d'attendre le merge
    de la PR porteuse (cf. git-workflow.md L898 collision guard).
    Le ScriptedRunner repond a `gh pr list --search head:<base>` avec une
    PR OPEN pour signifier que la base est vivante."""
    view = default_view()
    view["baseRefName"] = "feature/voltargeting-vol-forecast-sizing"  # #18967
    base_search_rows = [{"number": 18967, "state": "OPEN"}]
    runner = ScriptedRunner(
        views={123: view},
        base_search={f"head:{view['baseRefName']}": base_search_rows},
    )
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0  # l'organe termine, il a juste skip
    assert lines[-1]["verdict"] == "skipped"
    # Le motif inclut la branche fautive ET la liveness -- une lane
    # qui lit `live` sait qu'elle doit attendre la PR porteuse, pas
    # retargeter.
    assert (
        "base-live-not-main:feature/voltargeting-vol-forecast-sizing"
        in lines[-1]["reason"]
    ), lines[-1]


def test_base_dead_triggers_base_gone_skip(tmp_path):
    """Temooin negatif (#19014) : PR empilee sur une branche dont la PR
    porteuse est fermee ou squash-mergee. merge_ready distingue ce cas
    d'une base vivante : le motif `base-gone:<branche>` dit a la lane
    de retargeter sur `main` (cf. git-workflow.md L898 collision guard).
    Le ScriptedRunner repond a `gh pr list --search head:<base>` avec
    une liste vide (la PR porteuse a disparu, sa tete ne reapparait dans
    aucune PR ouverte). Verifie sur la branche morte de #18819
    (squash-mergee le 02/10)."""
    view = default_view()
    view["baseRefName"] = "renum/17063-complexity-05b"  # #18819
    runner = ScriptedRunner(
        views={123: view},
        base_search={f"head:{view['baseRefName']}": []},
    )
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert lines[-1]["verdict"] == "skipped"
    assert (
        "base-gone:renum/17063-complexity-05b" in lines[-1]["reason"]
    ), lines[-1]


def test_base_not_main_unreadable_fail_closed(tmp_path):
    """Temooin degrade (#19014) : si `gh pr list --search head:<base>`
    echoue (rc non nul, reponse non list, ou reseau), merge_ready ne
    declare pas une liveness qu'il n'a pas mesuree. Il emet
    `base-not-main-unreadable:<branche>` -- la lane ne recoit pas un
    message confiant, mais l'organe refuse le merge par defaut : l'echec
    doit etre visible."""
    view = default_view()
    view["baseRefName"] = "feature/inconnu"  # PR qui n'existe pas
    runner = ScriptedRunner(
        views={123: view},
        base_search_rc=1,  # simulateur de crash gh
    )
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0  # l'organe termine
    assert lines[-1]["verdict"] == "skipped"
    assert (
        "base-not-main-unreadable:feature/inconnu" in lines[-1]["reason"]
    ), lines[-1]


# ---------------------------------------------------------------------------
# 5quater (#19002) : PR empilee sur une parente via convention body
# (``Depends on #N`` / ``Blocked by #N`` / ``Stacked on #N`` /
# ``Requires #N`` / ``Stack: #N``) avec baseRefName == main. Cas Origami
# 2026-10-08 : 6 PRs empilees logiquement, baseRefName = main sur chacune,
# 5 d'entre elles sans CI complete parce que la racine n'avait pas ete
# mergee. base_ref_liveness ne s'applique pas (base = main), donc
# merge_ready doit sonder le body de la PR pour trouver la parente.
# Trois cas : parent OPEN (skip), parent MERGED (chemin nominal), parent
# CLOSED (skip, signaler pour que la lane retravaille). Le runner
# ScriptedRunner dispatche deja ``gh pr view <N>`` sur self.views[N] (l.226)
# -- les tests reutilisent ce mecanisme en injectant une vue avec
# state / mergedAt pour la PR parente.
#
# Correctif 2026-10-08 (review du coordinateur) : un body peut declarer
# PLUSIEURS parentes directes -- ``Depends on #A`` puis ``Blocked by #B``.
# Ne lire que la premiere laisse la seconde invisible, et si #A est MERGED
# le chemin nominal repart sans avoir examine #B. Les tests ci-dessous
# couvrent donc aussi : deux parentes dont seule la SECONDE bloque, deux
# parentes toutes deux MERGED, une parente illisible, et l'auto-reference.


def test_stacked_on_main_open_parent_triggers_skip(tmp_path):
    """Temooin negatif (#19002) : PR empilee sur une parente encore OPEN
    (la parente n'a pas ete mergee, donc la CI de la PR courante n'a pas
    couvert le diff de la parente). merge_ready skip avec le motif
    ``stacked-on-main:<N>:OPEN`` -- la lane doit attendre le merge de la
    parente. Cas Origami 2026-10-08 : #19815 / #19819 / #19826 / #19836 /
    #19847 empilees sur #19793 (la racine du pli 1)."""
    view = default_view()
    # body avec convention "Depends on #N" -- premiere ligne preservee pour
    # le prefiltre (GRAIN_MED), le marker d'empilement en bas du body.
    view["body"] = GRAIN_MED + "\n\nDepends on #19793"
    parent_view = {
        "number": 19793,
        "state": "OPEN",
        "mergedAt": None,
    }
    runner = ScriptedRunner(
        views={123: view, 19793: parent_view},
    )
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert lines[-1]["verdict"] == "skipped"
    assert "stacked-on-main:19793:OPEN" in lines[-1]["reason"], lines[-1]


def test_stacked_on_main_merged_parent_is_nominal(tmp_path):
    """Temooin positif (#19002) : parente empilee deja MERGED, le merge
    peut proceder. Le check empilement est un transit, pas un arret :
    une fois la parente absorbee dans main, la CI de la PR courante a
    tourne sur la bonne base. Reutilise le runner ScriptedRunner standard
    (defaut would-merge)."""
    view = default_view()
    view["body"] = GRAIN_MED + "\n\nDepends on #19793"
    parent_view = {
        "number": 19793,
        "state": "MERGED",
        "mergedAt": "2026-10-08T10:26:41Z",
    }
    runner = ScriptedRunner(
        views={123: view, 19793: parent_view},
    )
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    # Le verdict NOMINAL, pas seulement l'absence du motif de refus : une
    # parente MERGED laisse le merge se faire (review du coordinateur --
    # « le test parent MERGED affirme seulement l'absence du motif de
    # refus, ce qui ne prouve pas a lui seul le verdict nominal »).
    assert lines[-1]["verdict"] == "merged", lines[-1]
    assert lines[-1]["merged"] is True, lines[-1]
    assert "stacked-on-main" not in (lines[-1].get("reason") or ""), lines[-1]
    # Et l'appel attendu a bien eu lieu : la parente declaree a ete
    # interroge (le runner n'aurait pas ete sollicite sans la lecture du
    # body), la PR courante aussi, et rien d'autre.
    pr_view_calls = [c[3] for c in runner.cmds() if c[:3] == ["gh", "pr", "view"]]
    assert pr_view_calls == ["123", "19793"], pr_view_calls


def test_stacked_on_main_closed_parent_triggers_skip(tmp_path):
    """Temooin negatif (#19002) : parente fermee (CLOSED sans merge). Le
    motif ``stacked-on-main:<N>:CLOSED`` dit a la lane de rebrancher sur
    la parente viable ou de reouvrir la parente. Le test distingue
    explicitement OPEN et CLOSED pour que la lane puisse adapter son
    geste (attendre vs rebrancher)."""
    view = default_view()
    view["body"] = GRAIN_MED + "\n\nBlocked by #19793"
    parent_view = {
        "number": 19793,
        "state": "CLOSED",
        "mergedAt": None,
    }
    runner = ScriptedRunner(
        views={123: view, 19793: parent_view},
    )
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert lines[-1]["verdict"] == "skipped"
    assert "stacked-on-main:19793:CLOSED" in lines[-1]["reason"], lines[-1]


def test_no_stacked_marker_in_body_keeps_nominal_path(tmp_path):
    """Temooin positif (#19002) : body sans mention de parente empilee
    (PR ordinaire sur main). Le check empilement ne fait rien -- pas de
    round-trip supplementaire vers ``gh pr view <N>``. Le test verifie
    egalement qu'aucune vue de PR parente n'est appelee : le ScriptedRunner
    expose ``runner.cmds()`` qui liste les sous-processus spawnes, et on
    s'attend a n'y voir qu'un appel ``gh pr view 123`` (la PR courante)
    et aucun ``gh pr view <autre>``."""
    view = default_view()
    # body par defaut (GRAIN_MED) -- aucun marker d'empilement.
    runner = ScriptedRunner(views={123: view})
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    # Aucune mention empilement dans la raison de skip.
    assert "stacked-on-main" not in (lines[-1].get("reason") or ""), lines[-1]
    # Verifie qu'aucun appel ``gh pr view <N>`` autre que 123 n'a eu lieu :
    # le check empilement est absent du chemin nominal.
    other_pr_view_calls = [
        cmd for cmd in runner.cmds()
        if cmd[:3] == ["gh", "pr", "view"]
        and cmd[3] != "123"
    ]
    assert other_pr_view_calls == [], (
        f"appels inattendus vers gh pr view (autre que 123) : {other_pr_view_calls}"
    )


# --- Parentes MULTIPLES (review du coordinateur, 2026-10-08) -----------------


def test_find_stacked_parents_extracts_all_deduped():
    """Le lecteur rend TOUTES les parentes declarees, dedupliquees.

    Un body qui declare « Depends on #A » puis « Blocked by #B » porte deux
    dependances **directes** de la meme PR. L'ancien lecteur ne rendait que
    la premiere, ce qui laissait la seconde invisible des qu'on n'examinait
    que son retour."""
    body = (
        GRAIN_MED
        + "\n\nDepends on #19793\nBlocked by #19815\n"
        + "Stacked on #19815\n"          # doublon -> une seule fois
        + "Requires #19819\n"
    )
    assert mr.find_stacked_parents(body) == [19793, 19815, 19819]
    # Aucun marker : liste vide, pas None.
    assert mr.find_stacked_parents(GRAIN_MED) == []
    assert mr.find_stacked_parents(None) == []


def test_stacked_on_main_second_dep_open_triggers_skip(tmp_path):
    """Temooin de la review (#19002) : PREMIERE parente MERGED, SECONDE OPEN.

    C'est le cas que le lecteur precedent laissait passer. La premiere
    parente etant absorbe in dans `main`, le chemin nominal repartait sans
    jamais examiner la seconde -- et le merge se faisait sous une dependance
    encore ouverte. Le refus doit nommer la SECONDE, pas la premiere."""
    view = default_view()
    view["body"] = GRAIN_MED + "\n\nDepends on #19793\nBlocked by #19815"
    runner = ScriptedRunner(
        views={
            123: view,
            19793: {
                "number": 19793,
                "state": "MERGED",
                "mergedAt": "2026-10-08T10:26:41Z",
            },
            19815: {"number": 19815, "state": "OPEN", "mergedAt": None},
        },
    )
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert lines[-1]["verdict"] == "skipped", lines[-1]
    assert "stacked-on-main:19815:OPEN" in lines[-1]["reason"], lines[-1]
    # Les DEUX parentes ont ete interrogees : la seconde n'est pas restee
    # invisible derriere la premiere.
    pr_view_calls = [c[3] for c in runner.cmds() if c[:3] == ["gh", "pr", "view"]]
    assert pr_view_calls == ["123", "19793", "19815"], pr_view_calls


def test_stacked_on_main_two_merged_deps_is_nominal(tmp_path):
    """Temooin positif multi-parente : les deux parentes sont MERGED.

    Le check d'empilement est un transit, pas un arret : deux parentes
    absorbees dans `main` laissent le merge se faire. Verifie le verdict
    ET les appels attendus (les deux parentes sont bien sondees)."""
    view = default_view()
    view["body"] = GRAIN_MED + "\n\nDepends on #19793\nBlocked by #19815"
    runner = ScriptedRunner(
        views={
            123: view,
            19793: {
                "number": 19793,
                "state": "MERGED",
                "mergedAt": "2026-10-08T10:26:41Z",
            },
            19815: {
                "number": 19815,
                "state": "MERGED",
                "mergedAt": "2026-10-08T11:00:00Z",
            },
        },
    )
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert lines[-1]["verdict"] == "merged", lines[-1]
    pr_view_calls = [c[3] for c in runner.cmds() if c[:3] == ["gh", "pr", "view"]]
    assert pr_view_calls == ["123", "19793", "19815"], pr_view_calls


def test_stacked_on_main_unreadable_parent_triggers_skip(tmp_path):
    """Temooin degrade (#19002) : la parente declaree n'est pas lisible.

    ``stacked_parent_state`` rend ``unreadable`` pour tout etat qu'il ne
    peut pas classer (ici un etat inconnu), et le check est fail-CLOSED :
    un refus nomme ``stacked-on-main:<N>:unreadable``, jamais un merge
    confiant sur une dependance qu'on n'a pas mesuree."""
    view = default_view()
    view["body"] = GRAIN_MED + "\n\nDepends on #19793"
    runner = ScriptedRunner(
        views={123: view, 19793: {"number": 19793, "state": "GHOST"}},
    )
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert lines[-1]["verdict"] == "skipped", lines[-1]
    assert "stacked-on-main:19793:unreadable" in lines[-1]["reason"], lines[-1]


def test_stacked_on_main_self_reference_is_explicit(tmp_path):
    """Une PR qui se declare parente d'elle-meme rend un etat EXPLICITE.

    L'ancien code l'ignorait en silence (`parent != pr`) : le body etait
    mal forme et personne ne l'apprenait. Le motif ``self-reference`` dit a
    la lane que son body est a corriger, sans interroger le runner pour un
    numero qu'on a deja sous la main."""
    view = default_view()
    view["body"] = GRAIN_MED + "\n\nDepends on #123"
    runner = ScriptedRunner(views={123: view})
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert lines[-1]["verdict"] == "skipped", lines[-1]
    assert "stacked-on-main:123:self-reference" in lines[-1]["reason"], lines[-1]
    # Aucun appel supplementaire : la PR courante est deja chargee.
    pr_view_calls = [c[3] for c in runner.cmds() if c[:3] == ["gh", "pr", "view"]]
    assert pr_view_calls == ["123"], pr_view_calls


# --- 5quinquies : tests d'integrite sur l'arbre fusionne (2026-11-05) ----------


def _combined_calls(runner):
    """Appels d'EVALUATION de l'organe (les tests d'arbre fusionne).

    Le retrait du worktree de passe passe par le meme binaire en mode
    ``--cleanup`` : ce n'est pas une evaluation, et il ne doit pas etre
    compte comme telle.
    """
    return [c for c in runner.cmds()
            if len(c) > 1 and "premerge_combined_check.py" in c[1]
            and "--cleanup" not in c]


def _cleanup_calls(runner):
    return [c for c in runner.cmds() if "--cleanup" in c]


def test_le_contexte_de_passe_nomme_un_worktree_par_passe():
    """Une passe = UN worktree, nomme par le PID de la passe.

    Deux passes concurrentes ne doivent jamais partager le dossier : les
    tests d'un candidat joueraient alors sur l'arbre d'un autre.
    """
    ctx = mr.combined_pass_context()
    assert ctx is not None
    assert "premerge-passe-" in ctx.worktree.name
    assert str(os.getpid()) in ctx.worktree.name


def test_le_contexte_de_passe_est_eteint_par_le_rollback_operateur(monkeypatch):
    """`MERGE_READY_COMBINED_CHECK=0` retire l'etape : pas de contexte."""
    monkeypatch.setenv(mr.COMBINED_DISABLE_ENV, "0")
    assert mr.combined_pass_context() is None


def test_l_etape_5quinquies_recoit_le_worktree_de_passe(tmp_path):
    """L'argv de l'etape porte le worktree de la passe et le reutilise.

    Sans `--reuse-worktree`, l'organe refait un `worktree add` et un
    `worktree remove` par candidat : 38 s + 9 s, mesures.
    """
    runner = ScriptedRunner(views={123: default_view()})
    rc, _, _ = run_organ(tmp_path, runner)
    calls = _combined_calls(runner)
    assert calls, "l'organe premerge doit etre invoque"
    argv = calls[0]
    assert "--reuse-worktree" in argv
    worktree = argv[argv.index("--worktree") + 1]
    assert worktree.startswith(".tmp/premerge-passe-")
    # Aucun chemin absolu de la machine dans l'argv (#26102).
    assert not any(str(mr.REPO_ROOT) in tok for tok in argv)
    # Le retrait du worktree passe par l'ORGANE (`--cleanup`), jamais par un
    # `git` lance par la passe.
    cleanups = _cleanup_calls(runner)
    assert cleanups, "le worktree de la passe doit etre retire"
    assert not any(c[:1] == ["git"] for c in runner.cmds())


def test_une_passe_sans_evaluation_ne_retire_rien(tmp_path, monkeypatch):
    """Aucune evaluation -> aucun worktree pose -> aucun retrait.

    Une passe dont toutes les PRs sont refusees en amont (porte STACK)
    n'a rien demande au disque : elle ne doit rien demander en sortant.
    """
    monkeypatch.setattr(
        mr.gate, "default_stack_index", lambda: {124: "entree-de-la-partenaire"}
    )
    monkeypatch.setattr(
        mr.gate, "stack_reasons",
        lambda target, index: ["stack top: raison de test"],
    )
    runner = ScriptedRunner(views={123: default_view()})
    run_organ(tmp_path, runner)
    assert _combined_calls(runner) == []
    assert _cleanup_calls(runner) == []


def test_combined_green_merges_and_judges_the_view_head(tmp_path):
    runner = ScriptedRunner(views={123: default_view()})
    rc, lines, _ = run_organ(tmp_path, runner)
    assert lines[0]["verdict"] == "would-merge", lines[0]
    calls = _combined_calls(runner)
    assert len(calls) == 1
    assert calls[0][calls[0].index("--pr") + 1] == "123"
    assert calls[0][calls[0].index("--head") + 1] == HEAD


def test_combined_red_skips_and_names_the_first_red_test(tmp_path):
    stdout = json.dumps({"verdict": "RED",
                         "failed": ["scripts/x/test_a.py::test_u", "b::c"]})
    runner = ScriptedRunner(views={123: default_view()}, combined_rc=1,
                            combined_stdout=stdout)
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert lines[-1]["verdict"] == "skipped"
    assert lines[-1]["reason"] == "combined-tree-red:scripts/x/test_a.py::test_u"
    assert not any(c[:3] == ["gh", "pr", "merge"] for c in runner.cmds())


def test_combined_red_ecrit_la_raon_dans_le_journal(tmp_path):
    """Le journal porte la RAISON du rouge, pas seulement son identifiant.

    Deux PRs approuvees ont ete sautees sur un test qui ne les concernait
    pas (22/11) : `FAILED <id>` obligeait a DEVINER la cause. La section
    FAILURES de pytest la donne.
    """
    stdout = json.dumps({"verdict": "RED",
                         "failed": ["scripts/x/test_a.py::test_u"],
                         "failure_detail": "E   assert proc.returncode == 0\n"})
    runner = ScriptedRunner(views={123: default_view()}, combined_rc=1,
                            combined_stdout=stdout)
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert lines[-1]["verdict"] == "skipped"
    assert lines[-1]["reason"] == "combined-tree-red:scripts/x/test_a.py::test_u"
    assert "assert proc.returncode == 0" in lines[-1]["detail"]


def test_le_journal_dune_pr_sans_detail_ne_porte_pas_la_cle(tmp_path):
    """Une ligne sans raison n'invente pas une cle vide."""
    runner = ScriptedRunner(prs=(401,))
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert "detail" not in lines[0]


def test_combined_conflict_skips(tmp_path):
    runner = ScriptedRunner(views={123: default_view()}, combined_rc=1,
                            combined_stdout='{"verdict": "CONFLICT"}')
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert lines[-1]["reason"] == "combined-tree-conflict"


def test_combined_unreadable_is_fail_closed(tmp_path):
    runner = ScriptedRunner(views={123: default_view()}, combined_rc=2,
                            combined_stdout='{"verdict": "UNREADABLE", "reason": "timeout"}')
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert lines[-1]["reason"] == "combined-tree-unreadable:timeout"
    assert not any(c[:3] == ["gh", "pr", "merge"] for c in runner.cmds())


def test_combined_garbage_output_is_fail_closed(tmp_path):
    runner = ScriptedRunner(views={123: default_view()}, combined_rc=0,
                            combined_stdout="pas du json")
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert lines[-1]["reason"] == "combined-tree-unreadable:rc-0"


def test_combined_is_not_paid_by_a_pr_the_stack_door_refuses(
    tmp_path, monkeypatch
):
    """L'ordre des etapes est porteur : une PR refusee par la porte STACK
    (etape 3) n'atteint jamais l'organe couteux de l'arbre fusionne
    (etape 5quinquies)."""
    monkeypatch.setattr(
        mr.gate, "default_stack_index", lambda: {124: "entree-de-la-partenaire"}
    )
    monkeypatch.setattr(
        mr.gate, "stack_reasons",
        lambda target, index: [
            "stack top: shares 1 commit(s) with OPEN #124, which carries "
            "2 commit(s) absent here -- merging this one first would land "
            "the earlier version on main"
        ],
    )
    runner = ScriptedRunner(views={123: default_view()})
    run_organ(tmp_path, runner)
    assert _combined_calls(runner) == []


def test_combined_operator_rollback_env(tmp_path, monkeypatch):
    monkeypatch.setenv("MERGE_READY_COMBINED_CHECK", "0")
    runner = ScriptedRunner(views={123: default_view()}, combined_rc=1,
                            combined_stdout='{"verdict": "RED", "failed": ["a::b"]}')
    rc, lines, _ = run_organ(tmp_path, runner)
    assert lines[0]["verdict"] == "would-merge"
    assert _combined_calls(runner) == []


# --- #24989 : garde Lean -- attestation de `lake build` local -----------------
# La regle HARD `lean-merge-discipline.md` §1 exige un `lake build` local par
# ai-01 avant tout merge d'une PR qui touche du Lean. La garde exige une
# **preuve** : un commentaire d'attestation pose par `myia-ai-01` et couvrant
# la tete. La couverture de tete suit la meme regle que l'APPROVE (remontee
# first-parent de merge_dwell).

LEAN_FILE = "MyIA.AI.Notebooks/SymbolicAI/Lean/JeuDeLaVie/conway_lean/Conway.lean"
ATTESTED_SHA = "c0ffee00c0ffee00c0ffee00c0ffee00c0ffee00"


def _attestation_body(
    sha: str = HEAD,
    *,
    lakes: str = "conway_lean",
    jobs: int = 2948,
    tag: str = "[ACTION] lake build local",
) -> str:
    """Corps d'un commentaire d'attestation, au format canonique."""
    return (
        "{tag}\n\n"
        "PR #123\n"
        "tete: {sha}\n"
        "lakes: {lakes}\n"
        "jobs: {jobs}\n"
    ).format(tag=tag, sha=sha, lakes=lakes, jobs=jobs)


def _attestation_comment(
    sha: str = HEAD, *, login: str = "myia-ai-01", created: str = "2026-11-06T18:00:00Z",
    body: str | None = None,
) -> dict:
    """Commentaire d'attestation, forme de ``gh pr view --json comments``."""
    return {
        "author": {"login": login},
        "body": body if body is not None else _attestation_body(sha),
        "createdAt": created,
    }


def test_diff_lean_sans_attestation_donne_un_skip(tmp_path):
    """Controle positif : un diff `.lean` sans attestation est bloque."""
    view = default_view(files=(LEAN_FILE,))
    runner = ScriptedRunner(views={123: view})
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert lines[-1]["reason"] == "lean:no-local-build-attestation"
    assert lines[-1]["merged"] is False
    # la garde est en AMONT des organes couteux : rien n'a ete paye
    assert not any("check_unaddressed_nits.py" in flat for flat in runner.flat())


def test_diff_sans_lean_n_est_pas_affecte(tmp_path):
    """Controle negatif : un diff sans Lean n'exige aucune attestation."""
    view = default_view(files=("src/a.py", "docs/b.md"))
    runner = ScriptedRunner(views={123: view})
    rc, lines, _ = run_organ(tmp_path, runner)
    assert rc == 0
    assert lines[-1]["verdict"] == "would-merge"
    assert lines[-1]["reason"] is None


def test_outillage_lean_sans_attestation_donne_un_skip(tmp_path):
    """``lakefile.*``, ``lean-toolchain`` et ``lake-manifest.json`` sont des
    fichiers Lean : changer la toolchain change ce que le build doit prouver."""
    for path in (
        "MyIA.AI.Notebooks/SymbolicAI/Lean/JeuDeLaVie/conway_lean/lakefile.lean",
        "MyIA.AI.Notebooks/SymbolicAI/Lean/JeuDeLaVie/conway_lean/lakefile.toml",
        "MyIA.AI.Notebooks/SymbolicAI/Lean/JeuDeLaVie/conway_lean/lean-toolchain",
        "MyIA.AI.Notebooks/SymbolicAI/Lean/JeuDeLaVie/conway_lean/lake-manifest.json",
    ):
        runner = ScriptedRunner(views={123: default_view(files=(path,))})
        _, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
        assert lines[-1]["reason"] == "lean:no-local-build-attestation", path


def test_attestation_a_la_tete_passe(tmp_path):
    """Attestation posee a la tete exacte : la garde laisse passer."""
    view = default_view(
        files=(LEAN_FILE,), comments=[_attestation_comment(HEAD)]
    )
    runner = ScriptedRunner(views={123: view})
    rc, lines, _ = run_organ(tmp_path, runner)
    assert rc == 0
    assert lines[-1]["verdict"] == "would-merge"
    assert lines[-1]["reason"] is None


def test_attestation_signee_par_un_autre_login_est_refusee(tmp_path):
    """Une attestation posee par une autre lane ne vaut rien : l'acte est
    celui du coordinateur."""
    for login in ("jsboige", "myia-po-2026:CoursIA", "clusterManager-Myia"):
        view = default_view(
            files=(LEAN_FILE,), comments=[_attestation_comment(HEAD, login=login)]
        )
        runner = ScriptedRunner(views={123: view})
        _, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
        assert lines[-1]["reason"] == "lean:no-local-build-attestation", login


def test_attestation_avec_un_autre_tag_est_refusee(tmp_path):
    """Le tag en premiere ligne est le contrat : un corps qui cite le SHA
    dans la prose n'est pas une attestation."""
    body = _attestation_body(HEAD, tag="[DIAG] lake build local")
    view = default_view(
        files=(LEAN_FILE,), comments=[_attestation_comment(HEAD, body=body)]
    )
    runner = ScriptedRunner(views={123: view})
    _, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert lines[-1]["reason"] == "lean:no-local-build-attestation"


def test_attestation_sans_champ_tete_est_refusee(tmp_path):
    """Un SHA cite en prose ne fait pas une attestation : seul le champ
    etiquete ``tete:`` porte le SHA atteste."""
    body = "[ACTION] lake build local\n\nSHA {} cite en prose.\n".format(HEAD)
    view = default_view(
        files=(LEAN_FILE,), comments=[_attestation_comment(HEAD, body=body)]
    )
    runner = ScriptedRunner(views={123: view})
    _, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert lines[-1]["reason"] == "lean:no-local-build-attestation"


def test_attestation_a_une_tete_anterieure_et_commit_de_contenu_donne_un_skip(tmp_path):
    """L'attestation perime quand un commit de contenu passe apres elle."""
    view = default_view(
        files=(LEAN_FILE,),
        comments=[_attestation_comment(HEAD_MOVED)],
    )
    runner = ScriptedRunner(
        views={123: view}, **refresh_topology(head_parents=[HEAD_MOVED])
    )
    _, lines, _ = run_organ(tmp_path, runner)
    assert lines[-1]["reason"] == "lean:no-local-build-attestation"
    assert lines[-1]["merged"] is False


# --- #27875 : un lake INTRODUIT par la PR et non declare au manifeste -------
#
# Cas fondateur : PR #27587 (lake `busybeaver_lean`). L'entree de manifeste
# `scripts/lean/ci_lakes.json` arrive dans une PR EMPILÉE (#27658) : tant
# qu'elle n'est pas mergee, aucune attestation ne peut couvrir le lake, et le
# motif generique « pas d'attestation » ne nomme ni le lake ni le geste. La
# garde rend donc un motif NOMME.

BUSYBEAVER = "MyIA.AI.Notebooks/SymbolicAI/Lean/busybeaver_lean"
BUSYBEAVER_LAKEFILE = BUSYBEAVER + "/lakefile.lean"
CONWAY_LAKEFILE = "MyIA.AI.Notebooks/SymbolicAI/Lean/JeuDeLaVie/conway_lean/lakefile.lean"

#: Manifeste des lakes declares en CI : `conway` y est, `busybeaver` non.
CI_LAKES_MANIFEST = {
    "version": 1,
    "lakes": [
        {
            "lake": "conway",
            "project-path": "MyIA.AI.Notebooks/SymbolicAI/Lean/JeuDeLaVie/conway_lean",
            "paths": [
                "MyIA.AI.Notebooks/SymbolicAI/Lean/JeuDeLaVie/conway_lean/**.lean",
            ],
        }
    ],
}


def _manifest_payload(manifest: dict) -> dict:
    """Payload REST `contents` du manifeste (base64)."""
    raw = json.dumps(manifest).encode("utf-8")
    return {"content": base64.b64encode(raw).decode("ascii")}


def test_lake_introduit_non_declare_donne_un_motif_nomme(tmp_path):
    """#27875 -- la PR INTRODUIT un lake que le manifeste ne declare pas : le
    motif nomme le lake (il nomme aussi le geste), au lieu du generique."""
    view = default_view(
        files=(BUSYBEAVER_LAKEFILE, BUSYBEAVER + "/BusyBeaver.lean")
    )
    runner = ScriptedRunner(
        views={123: view},
        ci_lakes_payload=_manifest_payload(CI_LAKES_MANIFEST),
    )
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert lines[-1]["reason"] == "lean:lake-not-declared:" + BUSYBEAVER
    assert lines[-1]["merged"] is False


def test_lake_declare_donne_le_motif_generique(tmp_path):
    """Controle negatif : un lake DECLARE (son `lakefile` est touche) garde le
    motif generique -- pas de faux positif sur les PRs Lean ordinaires."""
    view = default_view(files=(CONWAY_LAKEFILE,))
    runner = ScriptedRunner(
        views={123: view},
        ci_lakes_payload=_manifest_payload(CI_LAKES_MANIFEST),
    )
    _, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert lines[-1]["reason"] == "lean:no-local-build-attestation"


def test_sans_lakefile_aucune_lecture_de_manifeste(tmp_path):
    """Controle negatif : une PR Lean sans `lakefile.*` ne paie AUCUNE lecture
    de manifeste (le cout de la garde ne bouge pas)."""
    view = default_view(files=(LEAN_FILE,))
    runner = ScriptedRunner(views={123: view})
    _, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert lines[-1]["reason"] == "lean:no-local-build-attestation"
    assert not [cmd for cmd in runner.cmds() if "/contents/" in " ".join(cmd)]


def test_manifeste_illisible_laisse_le_motif_generique(tmp_path):
    """Controle negatif : un manifeste illisible (404) laisse la garde sur son
    motif generique -- le fail-closed est conserve, aucun motif nomme n'est
    forge sur une absence d'information."""
    view = default_view(files=(BUSYBEAVER_LAKEFILE,))
    runner = ScriptedRunner(views={123: view})  # pas de payload : 404
    _, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert lines[-1]["reason"] == "lean:no-local-build-attestation"


def test_attestation_valide_passe_meme_avec_un_lakefile(tmp_path):
    """Non-regression : une attestation valide a la tete passe, meme sur une
    PR qui touche un `lakefile.*` -- la detection ne bloque rien de plus que
    la garde d'avant."""
    view = default_view(
        files=(BUSYBEAVER_LAKEFILE,),
        comments=[_attestation_comment(HEAD)],
    )
    runner = ScriptedRunner(
        views={123: view},
        ci_lakes_payload=_manifest_payload(CI_LAKES_MANIFEST),
    )
    rc, lines, _ = run_organ(tmp_path, runner)
    assert rc == 0
    assert lines[-1]["verdict"] == "would-merge"
    assert lines[-1]["reason"] is None


def test_attestation_suivie_d_un_rafraichissement_seul_laisse_passer(tmp_path):
    """L'attestation survit a un rafraichissement de base PROUVE content-free :
    la couverture de tete suit la meme regle que l'APPROVE."""
    view = default_view(
        files=(LEAN_FILE,),
        comments=[_attestation_comment(HEAD_MOVED)],
    )
    runner = ScriptedRunner(views={123: view}, **refresh_topology())
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert lines[-1]["merged"] is True


def test_attestation_illisible_fail_closed(tmp_path):
    """Preuve illisible (base absente) -> refus, jamais « c'est propre »."""
    view = default_view(
        files=(LEAN_FILE,),
        comments=[_attestation_comment(HEAD_MOVED)],
    )
    view["baseRefOid"] = ""
    runner = ScriptedRunner(views={123: view}, **refresh_topology())
    _, lines, _ = run_organ(tmp_path, runner)
    assert lines[-1]["reason"] == "lean:local-build-attestation-unverifiable:no-base"


def test_l_attestation_la_plus_recente_gagne(tmp_path):
    """Deux attestations : la plus recente regne (l'ordre est celui du
    serveur, ``createdAt``)."""
    view = default_view(
        files=(LEAN_FILE,),
        comments=[
            _attestation_comment(
                ATTESTED_SHA, created="2026-11-06T18:00:00Z"
            ),
            _attestation_comment(
                HEAD, created="2026-11-06T19:00:00Z"
            ),
        ],
    )
    runner = ScriptedRunner(views={123: view})
    _, lines, _ = run_organ(tmp_path, runner)
    assert lines[-1]["verdict"] == "would-merge"


def test_une_attestation_postee_sur_une_autre_pr_ne_suffit_pas(tmp_path):
    """Une attestation qui cite une autre tete (SHA inconnu de la PR) ne
    couvre pas la tete courante : la remontee echoue -> refus explicite."""
    view = default_view(
        files=(LEAN_FILE,),
        comments=[_attestation_comment(ATTESTED_SHA)],
    )
    runner = ScriptedRunner(views={123: view}, commits={})
    _, lines, _ = run_organ(tmp_path, runner)
    assert lines[-1]["reason"] in (
        "lean:local-build-attestation-unverifiable",
        "lean:no-local-build-attestation",
    )
    assert lines[-1]["merged"] is False


def test_format_partage_entre_organe_et_garde():
    """L'organe qui ECRIT et la garde qui LIT partagent le meme format : un
    corps rendu par l'organe est relu par la garde."""
    import importlib.util as _ilu

    spec = _ilu.spec_from_file_location(
        "lean_build_attestation_under_test",
        HERE.parent / "lean" / "lean_build_attestation.py",
    )
    module = _ilu.module_from_spec(spec)
    sys.modules["lean_build_attestation_under_test"] = module
    spec.loader.exec_module(module)

    body = module.render_attestation(
        sha=HEAD, lakes=["conway_lean"], jobs=2948, pr=123
    )
    assert module.first_line(body) == module.ATTESTATION_TAG
    parsed = module.parse_attestation(body)
    assert parsed and parsed["sha"] == HEAD
    assert parsed["lakes"] == ["conway_lean"]
    assert parsed["jobs"] == 2948
