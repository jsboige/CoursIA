"""Census des consommateurs du quota d'installation (jeton `GITHUB_TOKEN`).

Le quota d'installation du depot est de 1 000 appels/h sur le seau partage de
`GITHUB_TOKEN`. Depuis #26739, deux Dispatchs se disputent ce seau :

- le **controleur de debordement CI**, qui paie ~300 appels par passage ;
- les **sweepers** de verdicts perimes, qui paient une lecture `check-runs` par
  PR ouverte.

Le recensement du 2026-11-15 (volet B de #26739) a produit un tableau ou
cinq lignes etaient des **estimations**, faute d'instrument : `api-quota:`
n'etait publie que par quelques organes. Ce script rend la mesure
reproductible et distingue ce qui est **mesure** de ce qui ne l'est pas.

Trois colonnes, trois instruments :

| colonne | instrument | ce qu'elle dit |
|---|---|---|
| runs/24 h | un `total_count` par workflow | le nombre de passages (mesure exacte) |
| appels payes/passage | lignes `api-quota:` des journaux | les appels **payes** (les 304 sont gratuits) -- `n.m.` si l'organe ne publie pas la ligne |
| appels visibles/passage | lignes `##[command]gh api` des journaux | borne inferieure : les appels faits par un script Python (sortie capturee) n'apparaissent pas |

**Un zero n'est pas une mesure indisponible.** Une lecture qui echoue rend
`None` (`indisponible`), jamais `0` : un `0` fake ferait disparaitre un
consommateur du classement -- et un 403 sur le plus gros consommateur
disparait silencieusement, sans que l'incompletude soit signalee. Le rapport
porte donc une **couverture** (`complet`, `pagination_complete`, workflows
illisibles) et le classement n'est annonce exact que si elle est complete ; le
code de sortie vaut `2` sinon.

**Pourquoi un compte par workflow et non le listing global.** Le listing
`GET /repos/{owner}/{repo}/actions/runs` est plafonne a **1 000 resultats**
(mesure : la page 11 rend `total_count: 0` sur une fenetre de 24 h qui en
produit plusieurs milliers). Compter workflow par workflow rend la mesure
exacte : `total_count` ne depend pas de la pagination.

Usage :

```
python scripts/ci/census_installation_quota.py --hours 24 --sample 3
python scripts/ci/census_installation_quota.py --json
```

Code de sortie : `0` census complet, `2` couverture partielle (une lecture a
echoue, ou la pagination des workflows a ete interrompue) -- le rapport est
malgre tout produit, mais son classement n'est **pas** exact.

Cout du census : une lecture de la liste des workflows, plus une lecture par
workflow (environ 100 appels), plus un journal par passage echantillonne des
N workflows les plus sollicites. A lancer une fois par jour, pas dans une
jambe de PR.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from dataclasses import dataclass, field
from datetime import datetime, timedelta, timezone
from typing import Sequence

DEFAULT_REPO = "jsboige/CoursIA"
DEFAULT_HOURS = 24
DEFAULT_SAMPLE = 3
DEFAULT_TOP = 15
DEFAULT_SAMPLE_TOP = 20

# Ligne publiee par les organes qui comptent leurs appels payes :
#   `pr_gate.py`                 -> "[pr-gate] api-quota: N gh api call(s)"
#   `check_runner_starvation.py` -> "api-quota: N appel(s) API sur ce passage"
#   `fetch_pr_checkruns.py`      -> "api-quota: N appel(s) REST"
API_QUOTA_RE = re.compile(r"api-quota:\s*(\d+)\s+(?:gh api|appel)", re.IGNORECASE)
# Appels `gh api` NOMMES dans le journal : les appels inline du workflow.
# Un appel lance par un script Python (sortie capturee) n'est PAS visible :
# cette colonne est une borne inferieure, jamais un compte exhaustif.
VISIBLE_CALL_RE = re.compile(r"##\[command\]gh api\b")


class MesureIndisponible(Exception):
    """Une lecture a echoue : la mesure est INCONNUE, pas nulle.

    Distincte d'une mesure a zero. Rendre `0` ou une liste vide a la place
    ferait croire a une absence de consommation -- et le classement perdrait
    silencieusement le consommateur qu'on cherche.
    """


@dataclass
class Passage:
    """Un passage d'un workflow, mesure sur la fenetre.

    `statut` distingue deux etats qui ne se confondent jamais :

    - `mesure` : le volume de passages est connu -- y compris ZERO ;
    - `indisponible` : la lecture a echoue, le volume est INCONNU.
    """

    workflow: str
    runs_24h: int | None
    statut: str = "mesure"
    paid_calls: float | None = None
    visible_calls: float | None = None
    samples: list[int] = field(default_factory=list)
    erreur: str | None = None

    @property
    def calls_24h(self) -> float | None:
        if self.paid_calls is None or self.runs_24h is None:
            return None
        return self.paid_calls * self.runs_24h


def run_gh(args: Sequence[str]) -> tuple[int, str, str]:
    """Execute `gh` et rend (code, stdout, stderr)."""
    proc = subprocess.run(
        ["gh", *args],
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )
    return proc.returncode, proc.stdout, proc.stderr


def parse_timestamp(value: str) -> datetime:
    return datetime.fromisoformat(value.replace("Z", "+00:00"))


def window_start(hours: int, now: datetime | None = None) -> datetime:
    reference = now or datetime.now(timezone.utc)
    return reference - timedelta(hours=hours)


def fetch_workflows(
    repo: str, max_pages: int = 20
) -> tuple[list[tuple[int, str]], bool]:
    """Liste des workflows du depot : (identifiant, nom) + couverture complete.

    La lecture est **paginee** : l'API rend 100 workflows par page, et un depot
    qui en compte davantage perdrait sa queue -- c'est-a-dire les workflows les
    plus sollicites, ceux que le census cherche. Rend
    `(workflows, pagination_complete)` : `False` signale une pagination
    interrompue (erreur sur une page laterale, ou plafond de pages atteint).

    Une erreur de transport sur la **premiere** page leve `MesureIndisponible` :
    rendre une liste vide ferait croire a un depot sans workflow, donc a un
    census exact de zero consommateur.
    """
    workflows: list[tuple[int, str]] = []
    vus: set[int] = set()
    complete = True
    for page in range(1, max_pages + 1):
        code, out, err = run_gh(
            ["api", f"repos/{repo}/actions/workflows?per_page=100&page={page}"]
        )
        if code != 0:
            if page == 1:
                raise MesureIndisponible(
                    "liste des workflows illisible (page 1) : "
                    + (err.strip() or f"code {code}")
                )
            complete = False
            break
        try:
            data = json.loads(out)
        except json.JSONDecodeError:
            if page == 1:
                raise MesureIndisponible(
                    "liste des workflows illisible (JSON invalide, page 1)"
                )
            complete = False
            break
        items = data.get("workflows", [])
        for item in items:
            identifiant = int(item["id"])
            if identifiant not in vus:
                vus.add(identifiant)
                workflows.append((identifiant, str(item.get("name", "?"))))
        if len(items) < 100:
            break
    else:
        # plafond de pages atteint sans page courte : la queue est peut-etre laissee
        complete = False
    return workflows, complete


def count_runs(repo: str, workflow_id: int, since: datetime) -> int | None:
    """Nombre de runs d'un workflow sur la fenetre (`total_count`, exact).

    Rend `None` quand la lecture est IMPOSSIBLE (erreur de transport, JSON
    invalide) : `None` dit « je ne sais pas », `0` dit « j'ai mesure zero ».
    Confondre les deux ferait disparaitre un consommateur du classement sans
    que l'incompletude soit signalee.
    """
    stamp = since.strftime("%Y-%m-%dT%H:%M:%SZ")
    code, out, _ = run_gh(
        [
            "api",
            f"repos/{repo}/actions/workflows/{workflow_id}/runs"
            f"?created=>={stamp}&per_page=1",
        ]
    )
    if code != 0:
        return None
    try:
        return int(json.loads(out).get("total_count", 0))
    except (json.JSONDecodeError, TypeError, ValueError):
        return None


def fetch_run_ids(repo: str, workflow_id: int, since: datetime, limit: int) -> list[int]:
    """Identifiants des runs les plus recents d'un workflow sur la fenetre."""
    stamp = since.strftime("%Y-%m-%dT%H:%M:%SZ")
    code, out, _ = run_gh(
        [
            "api",
            f"repos/{repo}/actions/workflows/{workflow_id}/runs"
            f"?created=>={stamp}&per_page={limit}",
        ]
    )
    if code != 0:
        return []
    try:
        data = json.loads(out)
    except json.JSONDecodeError:
        return []
    return [int(r["id"]) for r in data.get("workflow_runs", [])]


def sample_run_logs(repo: str, run_ids: Sequence[int]) -> list[str]:
    """Journaux des runs donnes (un texte par run)."""
    logs = []
    for run_id in run_ids:
        code, out, _ = run_gh(["run", "view", "--repo", repo, str(run_id), "--log"])
        logs.append(out if code == 0 else "")
    return logs


def measure_passages(
    repo: str,
    workflows: list[tuple[int, str]],
    since: datetime,
    sample: int,
    sample_top: int = DEFAULT_SAMPLE_TOP,
) -> list[Passage]:
    """Un `Passage` par workflow : volume de passages, puis appels mesures.

    `sample_top` borne la lecture des journaux aux N workflows les plus
    sollicites : chaque journal est un zip, et un census qui lit 60 journaux
    coute plus de quota qu'il n'en mesure. Les workflows non echantillonnes
    gardent leur volume de passages et restent `n.m.` sur les colonnes de
    compte -- un trou nomme, jamais une valeur inventee.

    Un workflow dont la **lecture du compteur** echoue est conserve avec le
    statut `indisponible` : il ne disparait pas du rapport (c'est precisement
    lui qu'on cherche), et il n'est jamais rendu 0. Un workflow mesure a zero
    passages sort du tableau : il n'a rien consomme.
    """
    counted: list[tuple[int, str, int | None]] = []
    for workflow_id, name in workflows:
        counted.append((workflow_id, name, count_runs(repo, workflow_id, since)))
    actifs = [row for row in counted if row[2] is not None and row[2] > 0]
    actifs.sort(key=lambda row: (-row[2], row[1]))
    sampled = {row[0] for row in actifs[:sample_top]} if sample_top else {
        row[0] for row in actifs
    }
    passages: list[Passage] = []
    for workflow_id, name, runs_24h in actifs:
        passage = Passage(workflow=name, runs_24h=runs_24h)
        if workflow_id in sampled and runs_24h:
            run_ids = fetch_run_ids(repo, workflow_id, since, sample)
            logs = sample_run_logs(repo, run_ids)
            paid: list[int] = []
            visible: list[int] = []
            for log in logs:
                values = [int(m) for m in API_QUOTA_RE.findall(log)]
                if values:
                    paid.append(max(values))
                visible.append(len(VISIBLE_CALL_RE.findall(log)))
            if paid:
                passage.paid_calls = sum(paid) / len(paid)
                passage.samples = paid
            if visible and any(visible):
                passage.visible_calls = sum(visible) / len(visible)
        passages.append(passage)
    for workflow_id, name, runs_24h in counted:
        if runs_24h is None:
            passages.append(
                Passage(
                    workflow=name,
                    runs_24h=None,
                    statut="indisponible",
                    erreur="compteur de runs illisible",
                )
            )
    return passages


def render_table(passages: list[Passage], top: int) -> str:
    """Rend le tableau Markdown (colonnes mesurees, `n.m.` explicite).

    Les workflows `indisponible` sont **toujours** rendus, meme au-dela du
    `top` : ils sont la raison pour laquelle le classement n'est pas exact, et
    un tableau qui les cache reproduit exactement le defaut corrige ici.
    """
    mesures = [p for p in passages if p.statut == "mesure"]
    indisponibles = [p for p in passages if p.statut != "mesure"]
    ranked = sorted(
        mesures,
        key=lambda p: (
            -(p.calls_24h or 0),
            -(p.visible_calls or 0) * (p.runs_24h or 0),
            -(p.runs_24h or 0),
        ),
    )[:top]
    ranked = ranked + sorted(
        indisponibles, key=lambda p: p.workflow
    )
    lines = [
        "| # | Consommateur | runs/24 h | appels payes/passage | appels payes/24 h | "
        "appels visibles/passage | statut |",
        "|---|---|---|---|---|---|---|",
    ]
    for index, passage in enumerate(ranked, 1):
        paid = f"{passage.paid_calls:.1f}" if passage.paid_calls is not None else "n.m."
        per_day = f"{passage.calls_24h:.0f}" if passage.calls_24h is not None else "n.m."
        visible = (
            f"{passage.visible_calls:.1f}"
            if passage.visible_calls is not None
            else "n.m."
        )
        runs = passage.runs_24h if passage.runs_24h is not None else "inconnu"
        lines.append(
            f"| {index} | {passage.workflow} | {runs} | {paid} | "
            f"{per_day} | {visible} | {passage.statut} |"
        )
    return "\n".join(lines)


def build(args: argparse.Namespace) -> dict:
    since = window_start(args.hours)
    erreur: str | None = None
    try:
        workflows, pagination_complete = fetch_workflows(args.repo)
    except MesureIndisponible as exc:
        workflows, pagination_complete, erreur = [], False, str(exc)
    passages = measure_passages(
        args.repo, workflows, since, args.sample, args.sample_top
    )
    mesures = [p for p in passages if p.statut == "mesure"]
    indisponibles = [p for p in passages if p.statut != "mesure"]
    complet = (
        erreur is None
        and pagination_complete
        and not indisponibles
    )
    return {
        "repo": args.repo,
        "hours": args.hours,
        "since": since.strftime("%Y-%m-%dT%H:%M:%SZ"),
        "complet": complet,
        "couverture": {
            "workflows_lus": len(workflows),
            "workflows_mesures": len(mesures),
            "workflows_indisponibles": len(indisponibles),
            "pagination_complete": pagination_complete,
            "erreur": erreur,
        },
        "workflows_measured": len(mesures),
        "table": render_table(passages, args.top),
        "passages": [
            {
                "workflow": p.workflow,
                "runs_24h": p.runs_24h,
                "statut": p.statut,
                "erreur": p.erreur,
                "paid_calls": p.paid_calls,
                "paid_calls_24h": p.calls_24h,
                "visible_calls": p.visible_calls,
            }
            for p in sorted(
                passages,
                key=lambda p: (
                    -(p.calls_24h or 0),
                    -(p.runs_24h or 0),
                    p.workflow,
                ),
            )
        ],
    }


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", default=DEFAULT_REPO)
    parser.add_argument("--hours", type=int, default=DEFAULT_HOURS)
    parser.add_argument("--sample", type=int, default=DEFAULT_SAMPLE)
    parser.add_argument("--sample-top", type=int, default=DEFAULT_SAMPLE_TOP)
    parser.add_argument("--top", type=int, default=DEFAULT_TOP)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)
    report = build(args)
    if args.json:
        print(json.dumps(report, indent=2, ensure_ascii=False))
    else:
        print(f"# Census du quota d'installation -- {report['repo']}")
        print(
            f"fenetre : {report['since']} -> now ({report['hours']} h), "
            f"{report['workflows_measured']} workflows actifs"
        )
        print()
        print(report["table"])
        print()
        print(
            "`n.m.` = non mesurable : l'organe ne publie pas de ligne `api-quota:` "
            "(les appels payes sont alors une borne, pas un compte). "
            "`appels visibles` = appels `gh api` nommes dans le journal : "
            "borne inferieure, les appels faits par un script Python "
            "(sortie capturee) n'y figurent pas."
        )
        if not report["complet"]:
            couverture = report["couverture"]
            print()
            print(
                "**COUVERTURE PARTIELLE -- le classement ci-dessus n'est PAS "
                "exact.** "
                f"{couverture['workflows_indisponibles']} workflow(s) en echec de "
                "lecture (ils sont lists avec le statut `indisponible` et un "
                "volume `inconnu`, pas 0) ; "
                f"pagination des workflows : "
                f"{'complete' if couverture['pagination_complete'] else 'INTERROMPUE'}"
                + (f" ; erreur : {couverture['erreur']}" if couverture["erreur"] else "")
                + "."
            )
    return 0 if report["complet"] else 2


if __name__ == "__main__":
    sys.exit(main())
