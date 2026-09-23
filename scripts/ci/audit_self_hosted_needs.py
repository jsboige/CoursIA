#!/usr/bin/env python3
"""Audit des besoins locaux des jobs GitHub Actions auto-heberges (#17397).

Repond a une question mesurable : parmi les workflows dont un job tourne sur
`self-hosted`, lesquels n'ont besoin d'**rien qui n'existe que la** ? La reponse
n'est pas un avis, c'est une classification avec sa preuve.

Pourquoi un organe plutot qu'un grep
------------------------------------
Le premier classement de #17397 etait un grep sur le **texte** du workflow. Deux
defauts mesures le rendent non reproductible :

1. **La prose accuse.** Le motif `elan` matche le mot francais « relance »
   (r-e-l-a-n-c-e) et « appelant » (a-p-p-e-l-a-n-t). Sur les 32 workflows
   declares « sans besoin local », deux (`adjacency-stale-sweep`,
   `translation-hot-drift-advisory`) etaient en fait ecartes par ce faux
   positif : le classement manuel a rendu 32 la ou le meme grep lance en boucle
   en rend 30. Un motif sans borne de mot ne se valide pas par ses hits, mais
   par ses faux negatifs.
2. **Un besoin peut s'exprimer sans son mot.** `uses: leanprover/lean4-action`
   ou un job `container:` avec une image CUDA sont des besoins reels qu'un
   motif `lake|elan|mathlib` ne voit pas.

Cet organe lit le YAML **structurellement** (les commentaires n'existent plus
apres parsing), matche des motifs **a bornes de mot**, et inspecte les seules
surfaces executables -- `uses`, `run`, `with`, `env`, `if`, `container`,
`services` -- jamais les champs de prose (`name`). La comparaison avec l'ancien
grep textuel est rendue dans le meme rapport : c'est la mesure du defaut.

Cet organe **ne route rien**. Il classe et il prouve. Le re-routage effectif
(etapes 1-4 de #17397) reste une decision d'arbitrage.

Usage :
    python scripts/ci/audit_self_hosted_needs.py
    python scripts/ci/audit_self_hosted_needs.py --json
    python scripts/ci/audit_self_hosted_needs.py --out-dir docs/audit/self-hosted-needs

Codes de sortie :
    0  mesure produite (y compris « aucun workflow sans besoin »)
    2  instrument casse (workflow illisible ou YAML invalide)
"""

from __future__ import annotations

import argparse
import datetime as dt
import json
import re
import sys
from collections.abc import Iterable
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

try:
    import yaml
except ImportError:  # pragma: no cover - PyYAML est une dependance de CI
    print("[self-hosted-needs] PyYAML absent : instrument casse", file=sys.stderr)
    raise SystemExit(2)

EXIT_OK = 0
EXIT_BROKEN = 2

DEFAULT_WORKFLOWS_DIR = Path(".github/workflows")

# Chaque famille porte les motifs qui expriment le besoin. Les motifs sont
# bornes par `\b` des deux cotes : c'est ce qui ferme le faux positif
# « relance »/« appelant » du motif `elan`, et ce qui empeche `\blake\b` de
# matcher `lakefile` (couvert explicitement, lui).
NEED_PATTERNS: dict[str, tuple[str, ...]] = {
    "notebook": (
        r"\bpapermill\b",
        r"\bjupyter\b",
        r"\.ipynb\b",
        r"\bnbconvert\b",
        r"\bnbformat\b",
    ),
    "lean": (
        r"\blake\b",
        r"\blakefile\b",
        r"\belan\b",
        r"\bmathlib\b",
        r"\.lake\b",
        r"\bleanprover\b",
        r"\blean4?\b",
    ),
    "dotnet": (
        r"\bdotnet\b",
        r"\bnuget\b",
        r"\bcsproj\b",
    ),
    "conda": (
        r"\bconda\b",
        r"\bmamba\b",
        r"\bmicromamba\b",
    ),
    "docker": (
        r"\bdocker\b",
        r"\bdocker-compose\b",
    ),
    "gpu": (
        r"\bcuda\b",
        r"\bgpu\b",
        r"\bnvidia\b",
    ),
    "wsl": (
        r"\bwsl\b",
        r"\bwslpath\b",
    ),
    "secret": (
        r"\bsecrets\.(?!GITHUB_TOKEN\b)[A-Za-z_][A-Za-z0-9_]*",
        r"\bsecrets\s*:\s*inherit",
    ),
    # Axe implicite que #17397 signale sans pouvoir le mesurer par grep textuel :
    # un job qui adresse un service joignable depuis le runner n'a pas de
    # substitut GitHub-hosted. Seuls des **locators reseau litteraux** sont
    # retenus : un nom de service (`comfyui`, `owui`, `genai-stack`) est aussi un
    # nom de REPERTOIRE dans ce depot -- mesure faite, `\bowui\b` accusait
    # `Playwright-OWUI/package-lock.json`, soit exactement la classe de faux
    # positif que l'organe existe pour fermer.
    "internal-network": (
        r"\blocalhost\b",
        r"\b127\.0\.0\.1\b",
        r"\b0\.0\.0\.0\b",
        r"\bhost\.docker\.internal\b",
    ),
}

# Mesures informatives : elles n'expriment aucun besoin local, et ne font donc
# jamais basculer un workflow dans « a un besoin ». Elles sont rendues pour que
# le retrait soit auditable -- un motif retire en silence est indiscernable d'un
# motif oublie.
AUTOMATIC_PATTERNS: dict[str, tuple[str, ...]] = {
    "secret-automatic": (
        r"secrets\.GITHUB_TOKEN\b",
        r"github\.token\b",
    ),
}

# Motifs retires apres mesure, avec la raison -- un motif se valide par ses
# faux positifs, et ceux-ci sont la trace de la validation :
# - `notebook_tools` (famille notebook) : matche le CHEMIN d'un script
#   (`python scripts/notebook_tools/generate_catalog.py`), pas un besoin
#   d'executer un notebook. Mesure sur le depot : il accusait 11 workflows
#   parmi les « sous-accuses » -- soit la meme classe de defaut que le
#   `elan`/« relance » qu'il devait corriger, reproduite sous une autre forme.
RETIRED_PATTERNS: dict[str, str] = {
    "notebook_tools": "chemin de script, pas besoin d'executer un notebook",
}

# Un secret automatique existe sur n'importe quel runner : il n'exprime aucun
# besoin **local**. Le compter comme tel serait une sur-accusation de plus.
# Il est mesure separement, jamais fondu dans `secret` ni silencieusement jete.
AUTOMATIC_FAMILIES = frozenset(AUTOMATIC_PATTERNS)
AUTOMATIC_SECRET_PATTERN = re.compile(
    "|".join(
        pattern for patterns in AUTOMATIC_PATTERNS.values() for pattern in patterns
    ),
    re.IGNORECASE,
)


_COMPILED: dict[str, tuple[re.Pattern[str], ...]] = {
    family: tuple(re.compile(pattern, re.IGNORECASE) for pattern in patterns)
    for family, patterns in NEED_PATTERNS.items()
}
_AUTOMATIC_COMPILED: dict[str, tuple[re.Pattern[str], ...]] = {
    family: tuple(re.compile(pattern, re.IGNORECASE) for pattern in patterns)
    for family, patterns in AUTOMATIC_PATTERNS.items()
}

# Le grep textuel d'origine (#17397), conserve ici comme temoin : c'est contre
# lui que la mesure du defaut se prend. Ni borne de mot, ni retrait des
# commentaires -- exactement les deux causes du faux positif.
LEGACY_PATTERN = re.compile(
    r"secrets\.|docker|cuda|gpu|lake|elan|mathlib|dotnet|papermill|jupyter"
    r"|\.ipynb|conda|wsl",
    re.IGNORECASE,
)

# Champs de prose : jamais inspectes. Un besoin ne s'exprime pas dans un
# libelle ; l'inspecter, c'est laisser la prose accuser -- le defaut meme que
# cet organe mesure.
PROSE_KEYS = frozenset({"name"})

# Champs executables d'un job ou d'une etape : la surface ou un besoin reel
# peut se lire.
_EXECUTABLE_STEP_KEYS = ("uses", "run", "with", "env", "if")
_EXECUTABLE_JOB_KEYS = ("env", "if", "container", "services", "with")


@dataclass
class Evidence:
    """Un besoin local avec sa preuve : ou il a ete lu, et sous quelle forme."""

    family: str
    location: str
    matched: str
    snippet: str

    def to_dict(self) -> dict[str, str]:
        return {
            "family": self.family,
            "location": self.location,
            "matched": self.matched,
            "snippet": self.snippet,
        }


@dataclass
class JobVerdict:
    job: str
    runs_on: str
    self_hosted: bool
    evidence: list[Evidence] = field(default_factory=list)

    @property
    def families(self) -> list[str]:
        return sorted(
            {item.family for item in self.evidence if item.family not in AUTOMATIC_FAMILIES}
        )

    @property
    def automatic(self) -> list[str]:
        return sorted(
            {item.family for item in self.evidence if item.family in AUTOMATIC_FAMILIES}
        )

    @property
    def has_local_need(self) -> bool:
        return bool(self.families)

    def to_dict(self) -> dict[str, Any]:
        return {
            "job": self.job,
            "runs_on": self.runs_on,
            "self_hosted": self.self_hosted,
            "families": self.families,
            "automatic": self.automatic,
            "evidence": [item.to_dict() for item in self.evidence],
        }


@dataclass
class WorkflowVerdict:
    name: str
    path: str
    self_hosted_jobs: list[JobVerdict] = field(default_factory=list)
    legacy_has_need: bool = False
    legacy_matches: list[str] = field(default_factory=list)
    legacy_source: str = "none"

    @property
    def has_local_need(self) -> bool:
        return bool(self.families)

    @property
    def families(self) -> list[str]:
        return sorted(
            {family for job in self.self_hosted_jobs for family in job.families}
        )

    def to_dict(self) -> dict[str, Any]:
        return {
            "name": self.name,
            "path": self.path,
            "has_local_need": self.has_local_need,
            "families": self.families,
            "legacy_has_need": self.legacy_has_need,
            "legacy_matches": self.legacy_matches,
            "legacy_source": self.legacy_source,
            "jobs": [job.to_dict() for job in self.self_hosted_jobs],
        }


def _as_strings(value: Any) -> Iterable[str]:
    """Aplatit une valeur YAML arbitraire en chaines inspectables."""
    if value is None or isinstance(value, bool):
        return ()
    if isinstance(value, str):
        return (value,)
    if isinstance(value, (int, float)):
        return (str(value),)
    if isinstance(value, dict):
        out: list[str] = []
        for key, item in value.items():
            out.append(str(key))
            out.extend(_as_strings(item))
        return tuple(out)
    if isinstance(value, (list, tuple, set)):
        out = []
        for item in value:
            out.extend(_as_strings(item))
        return tuple(out)
    return (str(value),)


def _strip_shell_comments(script: str) -> str:
    """Retire les commentaires shell pleine ligne d'un bloc `run:`.

    Les faux positifs mesures vivaient dans des commentaires. Un `#` en milieu
    de ligne n'est PAS retire : sans analyse de quoting shell, le couper
    risquerait d'amputer une chaine legitime. La limite est assumee et
    documentee plutot que devinee.
    """
    kept: list[str] = []
    for line in script.splitlines():
        if line.lstrip().startswith("#"):
            continue
        kept.append(line)
    return "\n".join(kept)


def _legacy_matches(text: str) -> list[str]:
    return sorted({match.group(0).lower() for match in LEGACY_PATTERN.finditer(text)})


def _strip_comment_lines(text: str) -> str:
    return "\n".join(
        line for line in text.splitlines() if not line.lstrip().startswith("#")
    )


def _legacy_accusation_source(raw: str) -> str:
    """Ou vivait le motif qui a fait accuser ce workflow ?

    Trois classes, mesurees et non supposees :

    - `comment` : le motif disparait des qu'on retire les lignes de commentaire.
      C'est la classe du `elan`/« relance ».
    - `automatic-secret` : il ne reste rien quand on retire `secrets.GITHUB_TOKEN`
      et `github.token`, disponibles sur n'importe quel runner.
    - `name-or-trigger` : le motif survit aux deux retraits sans etre dans un
      champ executable -- c'est un `name:` de workflow ou un filtre `paths:` de
      declencheur, c'est-a-dire un titre ou une condition d'entree, jamais un
      besoin d'execution (classe de `paths: ['**.ipynb']`).
    """
    if not _legacy_matches(raw):
        return "none"
    if not _legacy_matches(_strip_comment_lines(raw)):
        return "comment"
    without_automatic = AUTOMATIC_SECRET_PATTERN.sub("", raw)
    if not _legacy_matches(without_automatic):
        return "automatic-secret"
    return "name-or-trigger"


def _scan_text(
    text: str, location: str, evidence: list[Evidence]
) -> None:
    for compiled in (_COMPILED, _AUTOMATIC_COMPILED):
        for family, patterns in compiled.items():
            for pattern in patterns:
                match = pattern.search(text)
                if match is None:
                    continue
                start = max(0, match.start() - 30)
                end = min(len(text), match.end() + 30)
                evidence.append(
                    Evidence(
                        family=family,
                        location=location,
                        matched=match.group(0),
                        snippet=text[start:end].replace("\n", " ").strip(),
                    )
                )


def _scan_mapping(
    data: Any, location: str, evidence: list[Evidence], keys: tuple[str, ...]
) -> None:
    if not isinstance(data, dict):
        return
    for key in keys:
        if key not in data:
            continue
        value = data[key]
        if key == "run" and isinstance(value, str):
            value = _strip_shell_comments(value)
        for text in _as_strings(value):
            if text in PROSE_KEYS:
                continue
            _scan_text(text, f"{location}.{key}", evidence)


def _is_self_hosted(runs_on: Any) -> bool:
    """Vrai si le libelle porte `self-hosted`, y compris dans une expression.

    Un `runs-on` dynamique qui resout vers le pool local (forme de `pr-gate.yml`)
    contient la chaine dans son expression : il est donc classe auto-heberge,
    pas « GitHub-hosted par defaut ».
    """
    values = [item.lower() for item in _as_strings(runs_on)]
    return any("self-hosted" in value for value in values)


def _runs_on_label(runs_on: Any) -> str:
    values = [item for item in _as_strings(runs_on)]
    return ", ".join(values) if values else "(absent)"


def audit_workflow(path: Path) -> WorkflowVerdict:
    """Classe un workflow. Leve ValueError si le YAML est illisible."""
    raw = path.read_text(encoding="utf-8", errors="replace")
    data = yaml.safe_load(raw)
    if not isinstance(data, dict):
        raise ValueError(f"{path}: YAML racine non-mapping")

    jobs = data.get("jobs")
    verdict = WorkflowVerdict(name=path.name, path=str(path))
    if not isinstance(jobs, dict):
        return verdict

    for job_name, job in jobs.items():
        if not isinstance(job, dict):
            continue
        runs_on = job.get("runs-on")
        if not _is_self_hosted(runs_on):
            continue

        evidence: list[Evidence] = []
        _scan_mapping(job, f"jobs.{job_name}", evidence, _EXECUTABLE_JOB_KEYS)

        # `secrets: inherit` et tout mapping `secrets:` de job sont des besoins
        # structurels : aucun mot « secrets » n'a besoin d'apparaitre dans un
        # `run` pour qu'un job consomme un secret.
        if isinstance(job.get("secrets"), (dict, str)):
            evidence.append(
                Evidence(
                    family="secret",
                    location=f"jobs.{job_name}.secrets",
                    matched="secrets:",
                    snippet=str(job.get("secrets"))[:60],
                )
            )

        steps = job.get("steps")
        if isinstance(steps, list):
            for index, step in enumerate(steps):
                if not isinstance(step, dict):
                    continue
                _scan_mapping(
                    step, f"jobs.{job_name}.steps[{index}]", evidence, _EXECUTABLE_STEP_KEYS
                )

        verdict.self_hosted_jobs.append(
            JobVerdict(
                job=str(job_name),
                runs_on=_runs_on_label(runs_on),
                self_hosted=True,
                evidence=evidence,
            )
        )

    verdict.legacy_matches = _legacy_matches(raw)
    verdict.legacy_has_need = bool(verdict.legacy_matches)
    verdict.legacy_source = _legacy_accusation_source(raw)
    return verdict


def audit(workflows_dir: Path) -> tuple[list[WorkflowVerdict], list[str]]:
    """Classe tous les workflows. Rend (verdicts, chemins illisibles)."""
    verdicts: list[WorkflowVerdict] = []
    broken: list[str] = []
    for path in sorted(workflows_dir.glob("*.y*ml")):
        try:
            verdict = audit_workflow(path)
        except (ValueError, yaml.YAMLError) as exc:
            broken.append(f"{path.name}: {exc}")
            continue
        if verdict.self_hosted_jobs:
            verdicts.append(verdict)
    return verdicts, broken


def build_report(
    verdicts: list[WorkflowVerdict], broken: list[str], workflows_dir: Path
) -> dict[str, Any]:
    no_need = [v for v in verdicts if not v.has_local_need]
    with_need = [v for v in verdicts if v.has_local_need]

    # Deux defauts distincts du grep textuel, mesures separement.
    over_accused = [
        v
        for v in no_need
        if v.legacy_has_need
    ]
    under_accused = [v for v in with_need if not v.legacy_has_need]

    # Decomposition de la sur-accusation par SOURCE : c'est ce qui rend le
    # chiffre auditable au lieu d'etre un total a croire.
    source_counts: dict[str, int] = {}
    for verdict in over_accused:
        source_counts[verdict.legacy_source] = (
            source_counts.get(verdict.legacy_source, 0) + 1
        )

    family_counts: dict[str, int] = {}
    for verdict in with_need:
        for family in verdict.families:
            family_counts[family] = family_counts.get(family, 0) + 1

    return {
        "generated_at": dt.datetime.now(dt.timezone.utc).isoformat(timespec="seconds"),
        "workflows_dir": str(workflows_dir),
        "self_hosted_workflows": len(verdicts),
        "with_local_need": len(with_need),
        "without_local_need": len(no_need),
        "family_counts": dict(sorted(family_counts.items())),
        "legacy_over_accused": [v.name for v in over_accused],
        "legacy_over_accused_sources": dict(sorted(source_counts.items())),
        "legacy_under_accused": [v.name for v in under_accused],
        "broken": broken,
        "without_local_need_workflows": [v.name for v in no_need],
        "workflows": [v.to_dict() for v in verdicts],
    }


def render_text(report: dict[str, Any], verbose: bool) -> str:
    lines: list[str] = []
    lines.append("[self-hosted-needs] audit des besoins locaux (#17397)")
    lines.append("")
    lines.append(
        f"  workflows avec job auto-heberge : {report['self_hosted_workflows']}"
    )
    lines.append(f"  au moins un besoin local      : {report['with_local_need']}")
    lines.append(f"  AUCUN besoin local detecte    : {report['without_local_need']}")
    lines.append("")
    if report["family_counts"]:
        lines.append("  besoins par famille :")
        for family, count in report["family_counts"].items():
            lines.append(f"    {family:<10} {count}")
        lines.append("")

    lines.append("  defauts mesures du grep textuel (#17397) :")
    over = report["legacy_over_accused"]
    under = report["legacy_under_accused"]
    lines.append(f"    sur-accuses (mot sans besoin reel)  : {len(over)}")
    for source, count in report["legacy_over_accused_sources"].items():
        lines.append(f"      source={source:<18} {count}")
    for name in over:
        lines.append(f"      - {name}")
    lines.append(f"    sous-accuses (besoin sans son mot) : {len(under)}")
    for name in under:
        lines.append(f"      - {name}")
    lines.append("")

    lines.append(f"  workflows sans besoin local ({report['without_local_need']}) :")
    for name in report["without_local_need_workflows"]:
        lines.append(f"    {name}")
    lines.append("")

    if report["broken"]:
        lines.append("  INSTRUMENT CASSE -- workflows illisibles :")
        for item in report["broken"]:
            lines.append(f"    {item}")
        lines.append("")

    if verbose:
        lines.append("  preuves par workflow :")
        for workflow in report["workflows"]:
            lines.append(f"    {workflow['name']} [{', '.join(workflow['families'])}]")
            for job in workflow["jobs"]:
                for item in job["evidence"]:
                    lines.append(
                        f"      {job['job']} {item['location']} "
                        f"<- {item['matched']!r} ({item['family']}) : {item['snippet']}"
                    )
    return "\n".join(lines)


def render_markdown(report: dict[str, Any]) -> str:
    lines = [
        "# Audit des besoins locaux des jobs auto-heberges (#17397)",
        "",
        f"Mesure : {report['generated_at']}",
        "",
        f"- workflows avec job auto-heberge : **{report['self_hosted_workflows']}**",
        f"- au moins un besoin local : **{report['with_local_need']}**",
        f"- aucun besoin local detecte : **{report['without_local_need']}**",
        "",
    ]
    if report["family_counts"]:
        lines.append("## Besoins par famille")
        lines.append("")
        lines.append("| famille | workflows |")
        lines.append("|---|---:|")
        for family, count in report["family_counts"].items():
            lines.append(f"| {family} | {count} |")
        lines.append("")

    lines.append("## Defauts du grep textuel")
    lines.append("")
    lines.append("| sens | workflows |")
    lines.append("|---|---:|")
    lines.append(f"| sur-accuses (mot dans la prose) | {len(report['legacy_over_accused'])} |")
    lines.append(
        f"| sous-accuses (besoin sans son mot) | {len(report['legacy_under_accused'])} |"
    )
    lines.append("")

    lines.append(f"## Sans besoin local ({report['without_local_need']})")
    lines.append("")
    for name in report["without_local_need_workflows"]:
        lines.append(f"- `{name}`")
    lines.append("")
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workflows-dir", type=Path, default=DEFAULT_WORKFLOWS_DIR)
    parser.add_argument("--json", action="store_true", help="rapport JSON complet")
    parser.add_argument("--verbose", action="store_true", help="preuves par workflow")
    parser.add_argument("--out-dir", type=Path, default=None, help="ecrit latest.json/.md")
    args = parser.parse_args(argv)

    if not args.workflows_dir.is_dir():
        print(
            f"[self-hosted-needs] repertoire introuvable : {args.workflows_dir}",
            file=sys.stderr,
        )
        return EXIT_BROKEN

    verdicts, broken = audit(args.workflows_dir)
    report = build_report(verdicts, broken, args.workflows_dir)

    if args.json:
        print(json.dumps(report, indent=2, ensure_ascii=False))
    else:
        print(render_text(report, args.verbose))

    if args.out_dir is not None:
        args.out_dir.mkdir(parents=True, exist_ok=True)
        (args.out_dir / "latest.json").write_text(
            json.dumps(report, indent=2, ensure_ascii=False) + "\n",
            encoding="utf-8",
        )
        (args.out_dir / "latest.md").write_text(
            render_markdown(report) + "\n", encoding="utf-8"
        )

    return EXIT_BROKEN if broken else EXIT_OK


if __name__ == "__main__":
    raise SystemExit(main())
