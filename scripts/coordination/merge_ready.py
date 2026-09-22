#!/usr/bin/env python3
r"""Organe merge_ready -- fusion hors cycle des PRs prevalidees (Q40, 2026-09-22).

Mandat (sign-off user 2026-09-22, registre Q40 option b) : les merges ne
doivent plus attendre le cycle de 2 h du coordinateur. Mesure fondatrice :
97 merges en 24 h concentres sur 4 creneaux avec 12 heures vides ; lead time
median d'une PR 28,5 h ; sur un echantillon de 20 PRs dont le dossier
d'adjoint etait rejete par le gate, 14 avaient une tete perimee et 13 une
discussion ayant bouge APRES le dossier, 0 un refus de fond. Un dossier
perit pendant qu'il attend le coordinateur.

L'organe est deterministe et tourne sous l'identite coordinateur
(myia-ai-01) toutes les ~20 minutes : il ne merge QUE ce qui passe
EXACTEMENT les controles du coordinateur lui-meme, et seulement en
perimetre (b) -- hors harnais et hors grains DEEP. Tour de controle par
PR, TOUT doit tenir sinon skip avec raison nommee :

1. pas un brouillon, et au moins un commentaire d'issue dont la premiere
   ligne est ``[ADJOINT PREFLIGHT]`` (prefiltre bon marche avant le gate
   couteux) ;
2. perimetre (b) fail-closed : aucun fichier sous ``.claude/``, aucun
   ``CLAUDE.md`` (n'importe quel repertoire), aucun fichier sous
   ``.github/`` ; tier du tag ``Grain:`` MED ou LIGHT (DEEP refuse, tier
   illisible refuse) -- lecture par le parseur PARTAGE
   ``scripts/grain_tag.py`` (#9485, meme lecteur que variation_light_cap
   et le guard CI), jamais une regex locale ; liste de fichiers TRONQUEE
   (``changedFiles`` > fichiers listes, ou absent) -> skip fail-closed,
   un fichier harnais non liste ne doit pas passer ;
2bis. pre-controle du dernier dossier ``[ADJOINT PREFLIGHT]`` : tete
   perimee ou ``b0:`` different de ``clear`` -> skip SANS payer le gate
   (un dossier illisible est laisse au gate, qui tranche) ;
3. gate d'entree ``check_adjoint_prevalidation.py <PR> --json`` ->
   ``"ready": true`` (exit 0). Les rc documents du gate (1 no-dossier,
   2 unknown, 3 blocked) sont des SKIPS nommes, pas des erreurs ;
4. champ ``b0:`` du dossier ACCEPTE par le gate egale ``clear`` --
   grammaire du dossier relue via ``parse_dossier`` du gate lui-meme
   (import, pas de duplication) ; le gate ne re-verifie pas b0, c'est
   l'etape 5 qui le fait ;
5. organe B.0 ``check_unaddressed_nits.py <PR>`` exit 0 -- code de
   retour capture DIRECTEMENT (subprocess.returncode, jamais a travers
   un pipe) ;
6. REST ``repos/jsboige/CoursIA/pulls/<N>`` : ``mergeable_state`` ==
   ``clean`` (jusqu'a 12 relectures a 10 s d'intervalle pendant ``unknown`` --
   apres un merge les PRs soeurs passent ``unknown``), et ``head.sha``
   identique a la tete evaluee par le gate ;
7. merge ``gh pr merge <N> --repo jsboige/CoursIA --squash
   --match-head-commit <sha>`` -- jamais ``--delete-branch``, jamais
   ``--admin``.

Comportement :
- DRY-RUN par defaut (imprime ce qui serait merge et pourquoi chaque
  autre PR est skippee) ; ``--apply`` merge reellement. ``--max N``
  (defaut 15) plafonne les merges par run (disjoncteur) ; le run
  S'ARRETE sur la premiere erreur inattendue (rc d'un outil hors codes
  documents, erreur d'API) -- jamais de merge en aveugle.
- Jeton : chaque sous-processus gh recoit ``GH_TOKEN`` epingle depuis
  ``gh auth token --user myia-ai-01``, resolu UNE fois au depart ;
  jamais ``gh auth switch``. Jeton irresolu -> exit 2.
- Ordre : PR la plus ancienne d'abord (par numero).
- Journal : une ligne JSON par PR evaluee (ts UTC en Z, pr, head,
  verdict, reason, merged) dans
  ``%LOCALAPPDATA%/CoursIA/merge_ready/journal.jsonl`` (surchargeable
  ``--journal``), plus un resume humain sur stdout ; ``--json`` pour la
  sortie machine.
- Codes de sortie : 0 run termine (merge ou non) ; 1 arret sur erreur
  inattendue ; 2 impossible de demarrer (jeton/env).

Tous les sous-processus passent par un runner injectable -- la logique
est testable sans reseau (scripts/tests/test_merge_ready.py).
"""
from __future__ import annotations

import argparse
import datetime as _dt
import json
import os
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Protocol

# Les modules partages vivent dans scripts/ : grain_tag.py est LE lecteur du
# tag Grain (un seul lecteur depuis #9485, meme discipline que
# variation_light_cap.py) et check_adjoint_prevalidation.py porte la
# grammaire du dossier. L'organe ne re-ecrit NI la grammaire du tag NI celle
# du dossier.
SCRIPTS_DIR = Path(__file__).resolve().parent.parent
if str(SCRIPTS_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPTS_DIR))

from grain_tag import TIERS, parse_grain_tag  # noqa: E402
import check_adjoint_prevalidation as gate  # noqa: E402

REPO = "jsboige/CoursIA"
COORDINATOR_USER = "myia-ai-01"
GATE_PATH = SCRIPTS_DIR / "check_adjoint_prevalidation.py"
NITS_PATH = SCRIPTS_DIR / "check_unaddressed_nits.py"

# Codes de retour DOCUMENTES des organes appeles. Tout autre rc est une
# erreur inattendue -> arret du run, jamais de merge en aveugle.
GATE_DOCUMENTED_RC = frozenset({0, 1, 2, 3})  # ready / no-dossier / unknown / blocked
GATE_RC_REASONS = {1: "gate:no-dossier", 2: "gate:unknown", 3: "gate:blocked"}
NITS_DOCUMENTED_RC = frozenset({0, 1})  # clear / blocked

MAX_MERGES_DEFAULT = 15
PR_LIST_LIMIT = 500  # le pool ouvert mesure ~220 PRs ; au-dela, ordre ancien d'abord
# Mesure du 2026-09-22 (22:15Z-22:45Z), merges en rafale sur la file vivante :
# avec 3 relectures espacees de 5 s, 5 PRs sur 20 restaient `unknown` et
# etaient sautees ; avec 12 relectures espacees de 10 s, les 11 suivantes
# (dont ces 5) sont toutes passees `clean` et ont ete mergees. Le plafond
# d'attente par PR (~2 min) reste petit devant le tour de 20 min.
MERGEABLE_RETRIES = 12
MERGEABLE_RETRY_SLEEP_S = 10.0


class CannotRunError(Exception):
    """Le run ne peut pas demarrer (jeton irresolu, env invalide)."""


class UnexpectedError(Exception):
    """Erreur inattendue d'un outil ou de l'API -- le run doit s'arreter."""


class MergeFailedError(Exception):
    """La commande de merge a echoue -- arret du run (disjoncteur)."""


# --- runner injectable --------------------------------------------------------


@dataclass(frozen=True)
class RunResult:
    returncode: int
    stdout: str
    stderr: str


class Runner(Protocol):
    """Contrat d'execution : un sous-processus capture, un sommeil."""

    def run(self, cmd: list[str], env: dict[str, str] | None = None) -> RunResult: ...

    def sleep(self, seconds: float) -> None: ...


class SubprocessRunner:
    """Runner reel : rc capture DIRECTEMENT (subprocess.returncode, jamais un pipe)."""

    def run(self, cmd: list[str], env: dict[str, str] | None = None) -> RunResult:
        proc = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            env=env,
        )
        return RunResult(proc.returncode, proc.stdout or "", proc.stderr or "")

    def sleep(self, seconds: float) -> None:
        time.sleep(seconds)


# --- petites pieces pures -----------------------------------------------------


@dataclass(frozen=True)
class PRVerdict:
    """Verdict terminal d'une PR pour ce run (forme de la ligne de journal)."""

    pr: int
    head: str | None
    verdict: str  # skipped | would-merge | merged | merge-failed | run-error
    reason: str | None
    merged: bool

    def journal_dict(self) -> dict:
        return {
            "ts": utc_now_iso(),
            "pr": self.pr,
            "head": self.head,
            "verdict": self.verdict,
            "reason": self.reason,
            "merged": self.merged,
        }


def utc_now_iso() -> str:
    """Horodatage UTC explicite, suffixe Z (jamais une heure locale nue)."""
    return _dt.datetime.now(_dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def default_journal_path() -> Path:
    base = Path(os.environ.get("LOCALAPPDATA") or Path.home() / "AppData" / "Local")
    return base / "CoursIA" / "merge_ready" / "journal.jsonl"


def has_preflight_comment(comments: list[dict]) -> bool:
    """True si au moins un commentaire d'issue OUVRIT un dossier (gate.START).

    Meme critere d'ouverture que ``check_adjoint_prevalidation.parse_dossier``
    (premiere ligne == marqueur) : un marqueur au milieu d'un corps n'est pas
    un dossier.
    """
    for row in comments or []:
        lines = (row.get("body") or "").strip().splitlines()
        if lines and lines[0].strip() == gate.START:
            return True
    return False


def scope_exclusion(path: str) -> str | None:
    """Raison d'exclusion de perimetre (b) pour un chemin, sinon None.

    Fail-closed : .claude/ et .github/ (repertoires), CLAUDE.md (tout
    niveau). Les separateurs sont normalises en / (gh rend des /, on
    accepte aussi des \\ par prudence).
    """
    p = (path or "").replace("\\", "/")
    if p == ".claude" or p.startswith(".claude/"):
        return f"scope:.claude:{path}"
    if p == ".github" or p.startswith(".github/"):
        return f"scope:.github:{path}"
    if p == "CLAUDE.md" or p.endswith("/CLAUDE.md"):
        return f"scope:CLAUDE.md:{path}"
    return None


def grain_exclusion(body: str | None) -> str | None:
    """Raison d'exclusion du tag Grain, sinon None.

    Le lecteur est le parseur PARTAGE (grain_tag.parse_grain_tag, #9485) :
    formes tolerees (gras, titre, sans deux-points) et refus de substance
    (aucun TIER/GENRE lisible -> None). DEEP est hors perimetre (b) ; un
    tier hors (DEEP, MED, LIGHT) est illisible au sens de la grammaire ->
    fail-closed.
    """
    tag = parse_grain_tag(body)
    if tag is None:
        return "grain-tier-unparsable"
    tier = tag.get("tier") or ""
    if tier == "DEEP":
        return "grain-tier-DEEP"
    if tier not in TIERS:
        return f"grain-tier-unknown:{tier}"
    return None


# --- appels gh (tous par le runner, tous avec GH_TOKEN epingle) ---------------


def resolve_token(runner: Runner) -> str:
    """Resout UNE fois le jeton du coordinateur, sans jamais ``gh auth switch``.

    GH_TOKEN/GITHUB_TOKEN sont RETIRES de l'env de resolution : une variable
    ambiante prendrait precedent sur ``--user`` et rendrait silencieusement le
    jeton d'une autre identite.
    """
    env = {
        key: value
        for key, value in os.environ.items()
        if key not in ("GH_TOKEN", "GITHUB_TOKEN")
    }
    res = runner.run(["gh", "auth", "token", "--user", COORDINATOR_USER], env=env)
    token = res.stdout.strip()
    if res.returncode != 0 or not token:
        raise CannotRunError(
            f"gh auth token --user {COORDINATOR_USER} a echoue "
            f"(rc={res.returncode}) : {res.stderr.strip()[:200]}"
        )
    return token


def _json_stdout(res: RunResult, what: str) -> object:
    try:
        return json.loads(res.stdout)
    except json.JSONDecodeError as exc:
        raise UnexpectedError(f"{what} : stdout illisible ({exc})") from exc


def list_open_prs(runner: Runner, gh_env: dict[str, str]) -> list[int]:
    """Numeros des PRs ouvertes, triees croissant (la plus ancienne d'abord)."""
    res = runner.run(
        ["gh", "pr", "list", "--repo", REPO, "--state", "open",
         "--limit", str(PR_LIST_LIMIT), "--json", "number"],
        env=gh_env,
    )
    if res.returncode != 0:
        raise UnexpectedError(
            f"gh pr list rc={res.returncode} : {res.stderr.strip()[:200]}"
        )
    rows = _json_stdout(res, "gh pr list")
    if not isinstance(rows, list):
        raise UnexpectedError("gh pr list : la reponse n'est pas une liste")
    numbers = sorted(
        int(row["number"])
        for row in rows
        if isinstance(row, dict) and row.get("number") is not None
    )
    return numbers


PR_VIEW_FIELDS = "number,isDraft,body,headRefOid,files,changedFiles,comments"


def fetch_pr_view(runner: Runner, pr: int, gh_env: dict[str, str]) -> dict:
    """Une vue par PR : brouillon, body (tag Grain), tete, fichiers, commentaires."""
    res = runner.run(
        ["gh", "pr", "view", str(pr), "--repo", REPO, "--json", PR_VIEW_FIELDS],
        env=gh_env,
    )
    if res.returncode != 0:
        raise UnexpectedError(
            f"gh pr view {pr} rc={res.returncode} : {res.stderr.strip()[:200]}"
        )
    view = _json_stdout(res, f"gh pr view {pr}")
    if not isinstance(view, dict):
        raise UnexpectedError(f"gh pr view {pr} : la reponse n'est pas un objet")
    return view


def precheck_dossier(view: dict) -> str | None:
    """Pre-controle bon marche, AVANT le gate : le dernier dossier visible dans la
    vue est-il a la tete courante, et declare-t-il ``b0: clear`` ?

    Ne fait que retrancher des appels : il ne rend un skip que sur une
    condition que le gate (tete perimee) ou l'etape 4 (``b0`` non clear)
    refuseraient de toute facon. Un dossier illisible ici n'est PAS refuse --
    la decision reste au gate. Mesure du 2026-09-22 : sur 20 PRs a dossier
    refuse, 14 avaient une tete perimee ; sans ce pre-controle, chaque tour
    paierait un gate complet pour chacune.
    """
    candidates = [
        row for row in view.get("comments") or []
        if _first_line(row.get("body") or "") == gate.START
    ]
    if not candidates:
        return None
    last = candidates[-1]
    dossier, _errors = gate.parse_dossier(
        last.get("body") or "",
        0,
        ((last.get("author") or {}).get("login")) or "",
        last.get("createdAt") or "",
    )
    if dossier is None:
        return None
    head = dossier.fields.get("head", "")
    if head and head != str(view.get("headRefOid") or ""):
        return "dossier-head-stale"
    b0 = dossier.fields.get("b0", "")
    if b0 and b0 != "clear":
        return f"dossier-b0-not-clear:{b0}"
    return None


def run_gate(runner: Runner, pr: int, gh_env: dict[str, str]) -> tuple[bool, str, str]:
    """Etape 3 : le gate d'entree. Retourne (ready, head, raison si non ready).

    rc hors {0,1,2,3} = erreur inattendue (le gate ne s'est pas prononce).
    """
    res = runner.run(
        [sys.executable, str(GATE_PATH), str(pr), "--json"], env=gh_env
    )
    if res.returncode not in GATE_DOCUMENTED_RC:
        raise UnexpectedError(
            f"gate PR {pr} rc={res.returncode} hors contrat : "
            f"{(res.stderr or res.stdout).strip()[:200]}"
        )
    data = _json_stdout(res, f"gate PR {pr}")
    if not isinstance(data, dict):
        raise UnexpectedError(f"gate PR {pr} : la reponse n'est pas un objet")
    ready = res.returncode == 0 and data.get("ready") is True
    head = str(data.get("head") or "")
    if ready:
        return True, head, ""
    reason = GATE_RC_REASONS.get(res.returncode)
    if reason is None:
        # rc 0 avec ready faux : ne devrait pas se produire, fail-closed.
        reason = "gate:not-ready"
    return False, head, reason


def _first_line(body: str) -> str:
    lines = (body or "").strip().splitlines()
    return lines[0].strip() if lines else ""


def dossier_b0_reason(runner: Runner, pr: int, gh_env: dict[str, str]) -> str | None:
    """Etape 4 : le champ ``b0:`` du dossier ACCEPTE par le gate doit etre ``clear``.

    Le gate a deja valide le dossier (structure, tete, empreinte, absence de
    discussion posterieure) ; on relit ici le meme dossier -- le plus recent
    commentaire ouvrant par le marqueur, meme selection que
    ``gate.evaluate`` (candidates[-1]) -- avec la grammaire du gate
    (``gate.parse_dossier``), sans la re-ecrir. Le gate ne re-verifie pas b0
    lui-meme : c'est cette etape qui porte le controle declaratif, l'etape 5
    portant le controle reel (l'organe B.0).
    """
    res = runner.run(
        ["gh", "api", f"repos/{REPO}/issues/{pr}/comments", "--paginate"],
        env=gh_env,
    )
    if res.returncode != 0:
        raise UnexpectedError(
            f"gh api comments PR {pr} rc={res.returncode} : "
            f"{res.stderr.strip()[:200]}"
        )
    rows = _json_stdout(res, f"comments PR {pr}")
    if not isinstance(rows, list):
        raise UnexpectedError(f"comments PR {pr} : la reponse n'est pas une liste")
    candidates = [row for row in rows if _first_line(row.get("body") or "") == gate.START]
    if not candidates:
        return "dossier-not-found"
    last = candidates[-1]
    dossier, errors = gate.parse_dossier(
        last.get("body") or "",
        0,
        (last.get("user") or {}).get("login", ""),
        last.get("created_at") or "",
    )
    if dossier is None or errors:
        return "dossier-b0-unreadable"
    b0 = dossier.fields.get("b0", "")
    if b0 == "clear":
        return None
    if b0 == "blocked":
        return "dossier-b0-blocked"
    return f"dossier-b0-not-clear:{b0 or 'absent'}"


def run_nits(runner: Runner, pr: int, gh_env: dict[str, str]) -> int:
    """Etape 5 : organe B.0. Retourne son rc (0 = clear), hors contrat -> arret."""
    res = runner.run([sys.executable, str(NITS_PATH), str(pr)], env=gh_env)
    if res.returncode not in NITS_DOCUMENTED_RC:
        raise UnexpectedError(
            f"B.0 PR {pr} rc={res.returncode} hors contrat : "
            f"{(res.stderr or res.stdout).strip()[:200]}"
        )
    return res.returncode


def mergeable_state_and_head(
    runner: Runner, pr: int, gh_env: dict[str, str]
) -> tuple[str, str]:
    """Etape 6 : (mergeable_state, head.sha) via REST, avec retry sur ``unknown``.

    Apres un merge, les PRs soeurs passent ``unknown`` le temps que GitHub
    recalcule : jusqu'a MERGEABLE_RETRIES relectures avec court sommeil avant
    de conclure au skip.
    """
    data: dict = {}
    for attempt in range(MERGEABLE_RETRIES + 1):
        res = runner.run(
            ["gh", "api", f"repos/{REPO}/pulls/{pr}"], env=gh_env
        )
        if res.returncode != 0:
            raise UnexpectedError(
                f"gh api pulls/{pr} rc={res.returncode} : {res.stderr.strip()[:200]}"
            )
        data = _json_stdout(res, f"pulls/{pr}")  # type: ignore[assignment]
        if not isinstance(data, dict):
            raise UnexpectedError(f"pulls/{pr} : la reponse n'est pas un objet")
        state = str(data.get("mergeable_state") or "")
        if state != "unknown":
            return state, str(((data.get("head") or {}).get("sha")) or "")
        if attempt < MERGEABLE_RETRIES:
            runner.sleep(MERGEABLE_RETRY_SLEEP_S)
    state = str(data.get("mergeable_state") or "")
    return state, str(((data.get("head") or {}).get("sha")) or "")


def merge_pr(runner: Runner, pr: int, head: str, gh_env: dict[str, str]) -> None:
    """Etape 7 : squash merge epingle sur la tete evaluee (jamais --admin,
    jamais --delete-branch)."""
    res = runner.run(
        ["gh", "pr", "merge", str(pr), "--repo", REPO,
         "--squash", "--match-head-commit", head],
        env=gh_env,
    )
    if res.returncode != 0:
        raise MergeFailedError(
            f"gh pr merge {pr} rc={res.returncode} : "
            f"{(res.stderr or res.stdout).strip()[:200]}"
        )


# --- tour de controle par PR ---------------------------------------------------


def evaluate_pr(
    view: dict, pr: int, runner: Runner, gh_env: dict[str, str]
) -> PRVerdict:
    """Applique dans l'ordre les 6 controles pre-merge. Tout echec = skip nomme.

    Les controles bon marche (brouillon, commentaire, perimetre, tag) passent
    AVANT le gate couteux ; le gate avant les organes B.0 ; le REST en
    dernier, juste avant le merge, pour minimiser la fenetre de course.
    """

    def skip(reason: str) -> PRVerdict:
        return PRVerdict(pr, str(view.get("headRefOid") or ""), "skipped", reason, False)

    # 1. prefiltre bon marche.
    if view.get("isDraft"):
        return skip("draft")
    if not has_preflight_comment(view.get("comments") or []):
        return skip("no-adjoint-preflight-comment")
    # 2. perimetre (b), fail-closed.
    for file_row in view.get("files") or []:
        reason = scope_exclusion(str((file_row or {}).get("path") or ""))
        if reason is not None:
            return skip(reason)
    # `gh pr view --json files` plafonne la liste : une PR plus grosse que ce
    # plafond cacherait peut-etre un fichier hors perimetre -> fail-closed.
    changed = view.get("changedFiles")
    listed = len(view.get("files") or [])
    if not isinstance(changed, int) or changed > listed:
        return skip(f"files-truncated:{listed}/{changed}")
    reason = grain_exclusion(view.get("body"))
    if reason is not None:
        return skip(reason)
    reason = precheck_dossier(view)
    if reason is not None:
        return skip(reason)
    # 3. gate d'entree.
    ready, gate_head, gate_reason = run_gate(runner, pr, gh_env)
    if not ready:
        return skip(gate_reason)
    # 4. b0 declaratif du dossier accepte.
    reason = dossier_b0_reason(runner, pr, gh_env)
    if reason is not None:
        return skip(reason)
    # 5. organe B.0 (re-verification reelle).
    if run_nits(runner, pr, gh_env) != 0:
        return skip("b0-organ-blocked")
    # 6. REST : mergeable + tete.
    state, live_head = mergeable_state_and_head(runner, pr, gh_env)
    if state != "clean":
        return skip(f"mergeable-state:{state or 'absent'}")
    if live_head != gate_head:
        return skip("head-moved")
    return PRVerdict(pr, gate_head, "would-merge", None, False)


# --- journal -------------------------------------------------------------------


def append_journal(path: Path, verdict: PRVerdict) -> None:
    """Une ligne JSON par PR evaluee ; repertoire cree si absent."""
    try:
        path.parent.mkdir(parents=True, exist_ok=True)
        with path.open("a", encoding="utf-8") as fh:
            fh.write(json.dumps(verdict.journal_dict(), ensure_ascii=False) + "\n")
    except OSError as exc:
        raise UnexpectedError(f"ecriture du journal {path} impossible : {exc}") from exc


# --- sortie --------------------------------------------------------------------


def _describe(verdict: PRVerdict) -> str:
    if verdict.verdict == "merged":
        return f"PR #{verdict.pr} MERGED ({verdict.head})"
    if verdict.verdict == "would-merge":
        return f"PR #{verdict.pr} WOULD MERGE ({verdict.head}) [dry-run]"
    if verdict.verdict == "merge-failed":
        return f"PR #{verdict.pr} MERGE ECHOUE : {verdict.reason}"
    if verdict.verdict == "run-error":
        return f"PR #{verdict.pr} ERREUR INATTENDUE : {verdict.reason}"
    return f"PR #{verdict.pr} skip : {verdict.reason}"


def emit_output(
    args: argparse.Namespace,
    results: list[PRVerdict],
    stopped_reason: str | None,
    exit_code: int,
) -> None:
    """Resume humain sur stdout, ou payload machine unique en --json."""
    if args.json:
        payload = {
            "apply": args.apply,
            "max": args.max,
            "stopped_reason": stopped_reason,
            "exit_code": exit_code,
            "results": [v.journal_dict() for v in results],
        }
        print(json.dumps(payload, ensure_ascii=False))
        return
    mode = "APPLY" if args.apply else "DRY-RUN"
    print(f"== merge_ready ({mode}, max {args.max}) ==")
    for verdict in results:
        print(_describe(verdict))
    merged = sum(1 for v in results if v.merged)
    would = sum(1 for v in results if v.verdict == "would-merge")
    skipped = sum(1 for v in results if v.verdict == "skipped")
    print(
        f"bilan : {len(results)} evaluee(s), {merged} merge(s), "
        f"{would} would-merge, {skipped} skip(s)"
    )
    if stopped_reason:
        print(f"arret : {stopped_reason}")


# --- boucle de run ---------------------------------------------------------------


def run(argv: list[str] | None = None, runner: Runner | None = None) -> int:
    """Point d'entree testable : parse les arguments, execute un run complet."""
    args = _parse_args(argv)
    active_runner = runner if runner is not None else SubprocessRunner()
    journal_path = (
        args.journal if args.journal is not None else default_journal_path()
    )
    try:
        token = resolve_token(active_runner)
    except CannotRunError as exc:
        print(f"merge_ready : impossible de demarrer -- {exc}", file=sys.stderr)
        return 2
    gh_env = {**os.environ, "GH_TOKEN": token}

    results: list[PRVerdict] = []
    stopped_reason: str | None = None
    exit_code = 0
    try:
        prs = list_open_prs(active_runner, gh_env)
    except UnexpectedError as exc:
        # Echec avant la boucle : aucune PR evaluee, rien a journeler.
        print(f"merge_ready : ARRET sur erreur inattendue -- {exc}", file=sys.stderr)
        emit_output(args, results, f"unexpected-error:{exc}", 1)
        return 1

    merged_count = 0
    for pr in prs:
        # Disjoncteur --max : plafond de DECISIONS de merge du run (merges
        # reels en --apply, would-merge en dry-run : le dry-run doit refléter
        # ce que --apply ferait). Une fois le plafond atteint, les PRs
        # restantes ne sont pas evaluees (le journal ne couvre que l'evalue).
        if merged_count >= args.max:
            stopped_reason = "max-merges-reached"
            break
        try:
            view = fetch_pr_view(active_runner, pr, gh_env)
            decision = evaluate_pr(view, pr, active_runner, gh_env)
            if decision.verdict == "would-merge":
                if args.apply:
                    try:
                        merge_pr(active_runner, pr, decision.head or "", gh_env)
                    except MergeFailedError as exc:
                        failed = PRVerdict(
                            pr, decision.head, "merge-failed", str(exc), False
                        )
                        results.append(failed)
                        append_journal(journal_path, failed)
                        stopped_reason = f"merge-failed:PR-{pr}"
                        exit_code = 1
                        break
                    decision = PRVerdict(pr, decision.head, "merged", None, True)
                merged_count += 1
            results.append(decision)
            append_journal(journal_path, decision)
        except UnexpectedError as exc:
            errored = PRVerdict(pr, None, "run-error", str(exc), False)
            results.append(errored)
            append_journal(journal_path, errored)
            stopped_reason = f"unexpected-error:{exc}"
            exit_code = 1
            break

    emit_output(args, results, stopped_reason, exit_code)
    return exit_code


def _parse_args(argv: list[str] | None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=__doc__.splitlines()[0],
    )
    parser.add_argument(
        "--apply",
        action="store_true",
        help="merger reellement (defaut : dry-run, aucun merge)",
    )
    parser.add_argument(
        "--max",
        type=int,
        default=MAX_MERGES_DEFAULT,
        metavar="N",
        help=f"plafond de merges par run, disjoncteur (defaut {MAX_MERGES_DEFAULT})",
    )
    parser.add_argument(
        "--journal",
        type=Path,
        default=None,
        help=(
            "chemin du journal JSONL (defaut "
            "%%LOCALAPPDATA%%/CoursIA/merge_ready/journal.jsonl)"
        ),
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="sortie machine (un seul objet JSON) sur stdout",
    )
    args = parser.parse_args(argv)
    if args.max < 0:
        parser.error("--max doit etre >= 0")
    return args


def main() -> int:
    return run()


if __name__ == "__main__":
    sys.exit(main())
