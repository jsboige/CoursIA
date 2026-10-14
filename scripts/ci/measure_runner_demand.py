#!/usr/bin/env python3
"""Measure GitHub Actions runner demand without silent API truncation.

The live mode collects a time-bounded cohort of workflow runs and all their
jobs. The offline mode replays the exact same snapshot without network access.
Every metric carries its denominator; an incomplete job is never converted to
zero runtime, and a broken collection exits 2 instead of returning a clean 0.

Examples:
  python scripts/ci/measure_runner_demand.py --repo owner/repo \
      --since 2026-08-24T09:00:00Z --until 2026-08-24T10:00:00Z \
      --output runner-demand.json
  python scripts/ci/measure_runner_demand.py --input runner-demand.json

Co-residence (#15574) : l'analyse croise, par job, sa duree avec le nombre de
jobs qui tournent sur le meme hote physique -- l'hote etant presume du prefixe
du `runner_name` (`<hote>-<n>`). Deux blocs en sortent : `co_residence`, mesure
DYNAMIQUE (par job, pic et moyenne de concurrence sur son hote, borne
inferieure), et `runners_inventory`, mesure STATIQUE des slots enregistres par
hote (avec `--runners`, droit d'administration requis). Les deux sont requis
pour trancher une sur-souscription : la premiere dit ce qui s'est produit, la
seconde dit la capacite qui l'a produit.
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from collections import Counter, defaultdict
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Callable
from urllib.parse import urlencode

EXIT_OK = 0
EXIT_BROKEN = 2
PER_PAGE = 100
SEARCH_CAP = 1000
MIN_SLICE = timedelta(seconds=1)

# Convention de nommage du pool self-hosted : un slot est `<hote>-<n>`, l'hote
# etant le reste du nom (cf docs/ci/self-hosted-runners.md). Le suffixe est
# donc ce qui separe deux slots d'un meme hote de deux hotes distincts.
_RUNNER_SLOT_SUFFIX = re.compile(r"^(?P<host>.+)-\d+$")


class MeasurementError(RuntimeError):
    """The instrument cannot prove that its result is complete or coherent."""


def parse_time(value: str) -> datetime:
    text = value.strip()
    if text.endswith("Z"):
        text = text[:-1] + "+00:00"
    try:
        parsed = datetime.fromisoformat(text)
    except ValueError as exc:
        raise MeasurementError(f"invalid ISO-8601 timestamp: {value!r}") from exc
    if parsed.tzinfo is None:
        raise MeasurementError(f"timestamp must include a timezone: {value!r}")
    return parsed.astimezone(timezone.utc)


def iso_z(value: datetime) -> str:
    return value.astimezone(timezone.utc).isoformat().replace("+00:00", "Z")


def host_of(runner_name: object) -> str | None:
    """Hote physique PRESUME d'un runner, derive de son nom.

    Le pool nomme ses slots `<hote>-<n>` (`myia-po-2024-linux-docker-1/-2`).
    Deux slots d'un meme hote ne different donc que par leur suffixe numerique,
    et le regroupement par prefixe reconstitue l'hote -- c'est le seul chemin
    vers « combien de runners partagent un hote », que les distributions par
    runner ne peuvent pas rendre (docs/ci/self-hosted-runners.md).

    Un nom qui ne porte aucun suffixe numerique n'est PAS attribue : il rend
    ``None`` plutot qu'un hote d'un seul slot. Inventer un hote pour chaque nom
    irreductible fabriquerait exactement le chiffre qu'on cherche a mesurer.
    """
    if not isinstance(runner_name, str) or not runner_name or runner_name.startswith("<"):
        return None
    match = _RUNNER_SLOT_SUFFIX.match(runner_name)
    return match.group("host") if match else None


def gh_api(endpoint: str) -> object:
    completed = subprocess.run(
        ["gh", "api", endpoint],
        capture_output=True,
        text=True,
        encoding="utf-8",
        check=False,
    )
    if completed.returncode != 0:
        detail = completed.stderr.strip() or completed.stdout.strip()
        raise MeasurementError(f"gh api failed for {endpoint}: {detail}")
    try:
        return json.loads(completed.stdout)
    except json.JSONDecodeError as exc:
        raise MeasurementError(f"gh api returned invalid JSON for {endpoint}") from exc


def _run_endpoint(repo: str, start: datetime, end: datetime, page: int) -> str:
    # The API range is inclusive at both ends. Adjacent slices therefore share
    # their boundary; run IDs are de-duplicated after collection.
    query = urlencode({
        "created": f"{iso_z(start)}..{iso_z(end)}",
        "per_page": PER_PAGE,
        "page": page,
    })
    return f"repos/{repo}/actions/runs?{query}"


def _collect_run_slice(
    repo: str,
    start: datetime,
    end: datetime,
    fetch: Callable[[str], object],
) -> list[dict]:
    first = fetch(_run_endpoint(repo, start, end, 1))
    if not isinstance(first, dict) or not isinstance(first.get("workflow_runs"), list):
        raise MeasurementError("actions/runs response has no workflow_runs list")
    total = first.get("total_count")
    if not isinstance(total, int) or total < 0:
        raise MeasurementError("actions/runs response has no valid total_count")

    if total >= SEARCH_CAP:
        if end - start <= MIN_SLICE:
            raise MeasurementError(
                f"actions/runs remains capped at {total} in one-second slice "
                f"{iso_z(start)}..{iso_z(end)}"
            )
        middle = start + (end - start) / 2
        return (
            _collect_run_slice(repo, start, middle, fetch)
            + _collect_run_slice(repo, middle, end, fetch)
        )

    rows = list(first["workflow_runs"])
    page = 2
    while len(rows) < total:
        payload = fetch(_run_endpoint(repo, start, end, page))
        if not isinstance(payload, dict) or not isinstance(payload.get("workflow_runs"), list):
            raise MeasurementError(f"invalid actions/runs page {page}")
        chunk = payload["workflow_runs"]
        if not chunk:
            raise MeasurementError(
                f"actions/runs page {page} empty before total_count={total} "
                f"(collected={len(rows)})"
            )
        rows.extend(chunk)
        page += 1
    if len(rows) != total:
        raise MeasurementError(
            f"actions/runs pagination mismatch: total_count={total}, collected={len(rows)}"
        )
    return rows


def collect_runs(
    repo: str,
    since: datetime,
    until: datetime,
    fetch: Callable[[str], object] = gh_api,
) -> list[dict]:
    if since >= until:
        raise MeasurementError("--since must be earlier than --until")
    rows = _collect_run_slice(repo, since, until, fetch)
    by_id: dict[int, dict] = {}
    for row in rows:
        if not isinstance(row, dict) or not isinstance(row.get("id"), int):
            raise MeasurementError("workflow run without an integer id")
        created = parse_time(str(row.get("created_at") or ""))
        if since <= created < until:
            by_id[row["id"]] = row
    return sorted(by_id.values(), key=lambda row: (row.get("created_at") or "", row["id"]))


def collect_jobs(
    repo: str,
    run_id: int,
    fetch: Callable[[str], object] = gh_api,
) -> list[dict]:
    rows: list[dict] = []
    page = 1
    total: int | None = None
    while total is None or len(rows) < total:
        endpoint = (
            f"repos/{repo}/actions/runs/{run_id}/jobs?"
            + urlencode({"filter": "all", "per_page": PER_PAGE, "page": page})
        )
        payload = fetch(endpoint)
        if not isinstance(payload, dict) or not isinstance(payload.get("jobs"), list):
            raise MeasurementError(f"invalid jobs response for run {run_id}, page {page}")
        reported = payload.get("total_count")
        if not isinstance(reported, int) or reported < 0:
            raise MeasurementError(f"jobs response for run {run_id} has no valid total_count")
        if total is None:
            total = reported
        elif reported != total:
            raise MeasurementError(f"jobs total_count changed while paging run {run_id}")
        chunk = payload["jobs"]
        if not chunk and len(rows) < total:
            raise MeasurementError(
                f"jobs page {page} empty before total_count={total} for run {run_id}"
            )
        rows.extend(chunk)
        page += 1
    if len(rows) != total:
        raise MeasurementError(
            f"jobs pagination mismatch for run {run_id}: total_count={total}, collected={len(rows)}"
        )
    return rows


def _minimal_run(row: dict, jobs: list[dict]) -> dict:
    head_repo = row.get("head_repository") or {}
    return {
        "id": row["id"],
        "name": row.get("name"),
        "event": row.get("event"),
        "status": row.get("status"),
        "conclusion": row.get("conclusion"),
        "created_at": row.get("created_at"),
        "run_started_at": row.get("run_started_at"),
        "updated_at": row.get("updated_at"),
        "head_repository": {"full_name": head_repo.get("full_name")},
        "pull_requests": [
            {"number": pr.get("number")}
            for pr in (row.get("pull_requests") or [])
            if isinstance(pr, dict)
        ],
        "jobs": [
            {
                "id": job.get("id"),
                "name": job.get("name"),
                "status": job.get("status"),
                "conclusion": job.get("conclusion"),
                "created_at": job.get("created_at"),
                "started_at": job.get("started_at"),
                "completed_at": job.get("completed_at"),
                "runner_name": job.get("runner_name"),
                "labels": job.get("labels") or [],
            }
            for job in jobs
        ],
    }


def collect_runners(repo: str, fetch: Callable[[str], object] = gh_api) -> list[dict]:
    """Inventaire des runners enregistres : la moitie STATIQUE de la co-residence.

    Le nombre de slots par hote se lit directement ici -- c'est le chiffre que
    les distributions par label ou par runner ne peuvent pas rendre, et que
    `docs/ci/po2024-topology-baseline.md` classe « non mesurable OS-localement ».
    Il l'est, mais cote API, pas cote machine.

    L'appel exige un droit d'administration sur le depot. L'echec remonte comme
    echec : un inventaire vide et un « je n'ai pas le droit de lire » ne se
    ressemblent pas et ne doivent jamais etre confondus.
    """
    rows: list[dict] = []
    page = 1
    total: int | None = None
    while total is None or len(rows) < total:
        endpoint = f"repos/{repo}/actions/runners?" + urlencode(
            {"per_page": PER_PAGE, "page": page}
        )
        payload = fetch(endpoint)
        if not isinstance(payload, dict) or not isinstance(payload.get("runners"), list):
            raise MeasurementError(f"invalid actions/runners response, page {page}")
        reported = payload.get("total_count")
        if not isinstance(reported, int) or reported < 0:
            raise MeasurementError("actions/runners response has no valid total_count")
        if total is None:
            total = reported
        elif reported != total:
            raise MeasurementError("actions/runners total_count changed while paging")
        chunk = payload["runners"]
        if not chunk and len(rows) < total:
            raise MeasurementError(
                f"actions/runners page {page} empty before total_count={total}"
            )
        rows.extend(chunk)
        page += 1
    if len(rows) != total:
        raise MeasurementError(
            f"actions/runners pagination mismatch: total_count={total}, collected={len(rows)}"
        )
    return [
        {
            "id": row.get("id"),
            "name": row.get("name"),
            "status": row.get("status"),
            "busy": row.get("busy"),
            "labels": sorted(
                label.get("name")
                for label in (row.get("labels") or [])
                if isinstance(label, dict) and label.get("name")
            ),
        }
        for row in rows
        if isinstance(row, dict)
    ]


def collect_snapshot(
    repo: str,
    since: datetime,
    until: datetime,
    fetch: Callable[[str], object] = gh_api,
    include_runners: bool = False,
) -> dict:
    runs = collect_runs(repo, since, until, fetch)
    collected = [
        _minimal_run(run, collect_jobs(repo, run["id"], fetch))
        for run in runs
    ]
    snapshot = {
        "schema_version": 1,
        "repo": repo,
        "since": iso_z(since),
        "until": iso_z(until),
        "runs": collected,
    }
    if include_runners:
        # Un inventaire illisible ne doit pas emporter la mesure de temps avec
        # lui : l'echec est consigne dans le snapshot, et l'analyse le rendra
        # comme « non disponible » plutot que comme un parc vide.
        try:
            snapshot["runners"] = collect_runners(repo, fetch)
        except MeasurementError as exc:
            snapshot["runners"] = {"error": str(exc)}
    return snapshot


def _duration_minutes(start: str, end: str, label: str) -> float | None:
    a, b = parse_time(start), parse_time(end)
    if b < a:
        # GitHub timestamps occasionally invert adjacent events -- observed in
        # the wild up to several seconds (job 98968836743, 2026-08-28: started
        # 6 s after completed). An inverted duration is unmeasurable, not
        # negative: exclude the datum and let the caller count it in the
        # timestamp_skew denominator. Never fatal, never a clean zero.
        return None
    return (b - a).total_seconds() / 60.0


def _percentile(values: list[float], quantile: float) -> float | None:
    if not values:
        return None
    ordered = sorted(values)
    position = (len(ordered) - 1) * quantile
    lower = int(position)
    upper = min(lower + 1, len(ordered) - 1)
    fraction = position - lower
    return ordered[lower] + (ordered[upper] - ordered[lower]) * fraction


def _timing_group() -> dict:
    return {
        "jobs": 0,
        "timed_jobs": 0,
        "incomplete_or_untimed_jobs": 0,
        "timestamp_skew_jobs": 0,
        "queue_waits": [],
        "runtimes": [],
    }


def _record_job(group: dict, state: str, wait: float | None, work: float | None) -> None:
    group["jobs"] += 1
    if state == "incomplete":
        group["incomplete_or_untimed_jobs"] += 1
    elif state == "skew":
        group["timestamp_skew_jobs"] += 1
    else:
        group["timed_jobs"] += 1
        group["queue_waits"].append(wait)
        group["runtimes"].append(work)


def _render_timing_groups(groups: dict[str, dict], key: str) -> list[dict]:
    rendered = []
    for name in sorted(groups):
        group = groups[name]
        waits = group["queue_waits"]
        runtimes = group["runtimes"]
        rendered.append({
            key: name,
            "jobs": group["jobs"],
            "timed_jobs": group["timed_jobs"],
            "incomplete_or_untimed_jobs": group["incomplete_or_untimed_jobs"],
            "timestamp_skew_jobs": group["timestamp_skew_jobs"],
            "timing_coverage": (
                round(group["timed_jobs"] / group["jobs"], 6)
                if group["jobs"] else None
            ),
            "queue_wait_minutes": {
                percentile: (
                    round(value, 3) if value is not None else None
                )
                for percentile, value in (
                    ("p50", _percentile(waits, 0.5)),
                    ("p90", _percentile(waits, 0.9)),
                    ("max", max(waits) if waits else None),
                )
            },
            "runtime_minutes": {
                percentile: (
                    round(value, 3) if value is not None else None
                )
                for percentile, value in (
                    ("p50", _percentile(runtimes, 0.5)),
                    ("p90", _percentile(runtimes, 0.9)),
                    ("max", max(runtimes) if runtimes else None),
                )
            },
        })
    return rendered


def _runtime_percentiles(values: list[float]) -> dict:
    return {
        name: (round(value, 3) if value is not None else None)
        for name, value in (
            ("p50", _percentile(values, 0.5)),
            ("p90", _percentile(values, 0.9)),
            ("max", max(values) if values else None),
        )
    }


def _ratio_by_quantile(solo: list[float], shared: list[float]) -> dict:
    """Rapport partage/seul a chaque quantile rapporte -- pas au seul median.

    Le median ne tranche pas la question qui compte pour un budget de timeout :
    la co-residence degrade-t-elle les jobs LONGS ? Un rapport median proche de 1
    peut coexister avec une queue qui double, et c'est la queue qui fait mourir un
    job au timeout. Le rapport est donc rendu a p50, p90 et max, pour que le
    verdict de queue soit dans l'artefact au lieu d'etre a recalculer a la main
    depuis les deux blocs de percentiles.

    L'effectif des deux populations reste publie a cote (`solo_jobs`,
    `shared_jobs`) : un p90 tire de cinq jobs n'est pas un p90, et un rapport de
    queue sur une population mince ne doit pas se lire comme une mesure.
    """
    ratios: dict[str, float | None] = {}
    for name, quantile in (("p50", 0.5), ("p90", 0.9)):
        low, high = _percentile(solo, quantile), _percentile(shared, quantile)
        ratios[name] = (
            round(high / low, 3)
            if low and high is not None and low > 0
            else None
        )
    low = max(solo) if solo else None
    high = max(shared) if shared else None
    ratios["max"] = (
        round(high / low, 3) if low and high is not None and low > 0 else None
    )
    return ratios


def _coresidence(records: list[dict]) -> dict:
    """Croise la duree d'un job avec le nombre de jobs qui tournent sur son hote.

    Deux statistiques par job, parce qu'elles repondent a deux questions
    distinctes : la concurrence de PIC (combien de jobs l'hote a-t-il portes
    simultanement pendant ce job -- c'est elle qui dit le plafond atteint) et la
    concurrence MOYENNE (quelle part de la duree s'est faite en compagnie).

    Le pic est calcule sur les bornes des intervalles : entre deux bornes le
    compte ne peut pas changer, et un echantillon unique (un point median) rate
    un job qui chevauche un autre sur la moitie de sa duree.

    La concurrence mesuree est une BORNE INFERIEURE de la vraie : seuls les jobs
    de la fenetre collectee sont connus, et un job hors fenetre qui tournait en
    parallele est invisible. Elle ne peut donc pas servir a prouver qu'un hote
    n'est jamais sur-souscrit -- seulement a montrer qu'il l'est.
    """
    per_host: dict[str, list[dict]] = defaultdict(list)
    unplaced = 0
    for record in records:
        if record["host"] is None:
            unplaced += 1
            continue
        per_host[record["host"]].append(record)

    solo: list[float] = []
    shared: list[float] = []
    rendered = []
    for host in sorted(per_host):
        host_records = per_host[host]
        buckets: dict[int, list[float]] = defaultdict(list)
        for record in host_records:
            start, end = record["start"], record["end"]
            points = {start}
            for other in host_records:
                # Les seuls instants ou le compte peut changer sont les bornes
                # des intervalles : echantillonner ailleurs ne peut rien
                # apprendre, et un point median unique rate un job qui
                # chevauche un autre sur la moitie de sa duree.
                for bound in (other["start"], other["end"]):
                    if start <= bound < end:
                        points.add(bound)
            peak = max(
                (sum(1 for other in host_records
                     if other["start"] <= point < other["end"]) or 1)
                for point in points
            )
            duration = (end - start).total_seconds()
            if duration > 0:
                overlapped = sum(
                    max(0.0, (min(end, other["end"]) - max(start, other["start"])).total_seconds())
                    for other in host_records
                    if other is not record
                )
                record["mean_concurrency"] = 1.0 + overlapped / duration
            else:
                record["mean_concurrency"] = float(peak)
            buckets[max(1, peak)].append(record["work"])
        for level, values in buckets.items():
            if level <= 1:
                solo.extend(values)
            else:
                shared.extend(values)

        # La queue est clairsemee par construction : au-dela de 4 jobs
        # concurrents sur un hote, les niveaux exacts ne portent plus de signal
        # distinct, seul le fait d'etre sature compte.
        tail: list[float] = []
        groups = []
        for level in sorted(buckets):
            if level >= 5:
                tail.extend(buckets[level])
                continue
            groups.append({
                "concurrency": level,
                "jobs": len(buckets[level]),
                "runtime_minutes": _runtime_percentiles(buckets[level]),
            })
        if tail:
            groups.append({
                "concurrency": "5+",
                "jobs": len(tail),
                "runtime_minutes": _runtime_percentiles(tail),
            })

        rendered.append({
            "host": host,
            "runners": sorted({record["runner"] for record in host_records}),
            "slots_observed": len({record["runner"] for record in host_records}),
            "jobs": len(host_records),
            "max_concurrency_observed": max(buckets) if buckets else None,
            "mean_concurrency_overall": (
                round(
                    sum(record["mean_concurrency"] for record in host_records)
                    / len(host_records),
                    3,
                )
                if host_records else None
            ),
            "runtime_by_concurrency": groups,
        })

    return {
        "method": (
            "hote prefixe du runner_name (`<hote>-<n>`) ; par job, "
            "concurrence de PIC (max sur les bornes des intervalles) et "
            "concurrence MOYENNE (integral du recouvrement / duree)"
        ),
        "caveats": [
            "la concurrence est une borne inferieure : les jobs hors fenetre de collecte sont invisibles",
            "l'hote est presume du nom du runner ; un nom sans suffixe numerique n'est pas attribue",
            "une correlation n'est pas une cause : une duree plus longue en concurrence peut venir du job lui-meme",
            "le rapport partage/seul confronte deux populations d'effectifs tres differents : les quantiles de queue (p90, max) ne se lisent qu'avec `solo_jobs` et `shared_jobs` a cote",
        ],
        "hosts": rendered,
        "summary": {
            "hosts": len(rendered),
            "jobs_placed": len(records) - unplaced,
            "jobs_unplaced": unplaced,
            "solo_jobs": len(solo),
            "shared_jobs": len(shared),
            "solo_runtime_minutes": _runtime_percentiles(solo),
            "shared_runtime_minutes": _runtime_percentiles(shared),
            "shared_over_solo_runtime_ratio": _ratio_by_quantile(solo, shared),
        },
    }


def _runners_inventory(raw: object) -> dict:
    """Slots enregistres par hote -- ou l'aveu explicite qu'on ne les a pas lus.

    Trois etats distincts, jamais confondus : `measured`, `unavailable` (le
    droit de lecture manque -- le detail porte la raison) et `not_collected`
    (l'inventaire n'a pas ete demande). Aucun des trois ne rend un parc vide.
    """
    if isinstance(raw, dict) and "error" in raw:
        return {"availability": "unavailable", "detail": str(raw["error"])}
    if not isinstance(raw, list):
        return {
            "availability": "not_collected",
            "detail": "inventaire non demande : relancer la collecte avec --runners",
        }

    per_host: dict[str, dict] = defaultdict(
        lambda: {"slots": 0, "online": 0, "busy": 0, "labels": set()}
    )
    unplaced = 0
    for runner in raw:
        if not isinstance(runner, dict):
            continue
        host = host_of(runner.get("name"))
        if host is None:
            unplaced += 1
            continue
        entry = per_host[host]
        entry["slots"] += 1
        if runner.get("status") == "online":
            entry["online"] += 1
        if runner.get("busy"):
            entry["busy"] += 1
        entry["labels"].update(
            label for label in (runner.get("labels") or []) if isinstance(label, str)
        )

    return {
        "availability": "measured",
        "total_runners": len(raw),
        "unplaced_runners": unplaced,
        "hosts": [
            {
                "host": host,
                "slots": data["slots"],
                "online": data["online"],
                "busy": data["busy"],
                "labels": sorted(data["labels"]),
            }
            for host, data in sorted(per_host.items())
        ],
    }


def analyze(snapshot: dict) -> dict:
    if snapshot.get("schema_version") != 1:
        raise MeasurementError("unsupported or missing snapshot schema_version")
    repo = snapshot.get("repo")
    runs = snapshot.get("runs")
    if not isinstance(repo, str) or not repo or not isinstance(runs, list):
        raise MeasurementError("snapshot must contain repo and runs")
    since, until = parse_time(snapshot.get("since", "")), parse_time(snapshot.get("until", ""))
    window_hours = (until - since).total_seconds() / 3600.0
    if window_hours <= 0:
        raise MeasurementError("snapshot window must have positive duration")

    provenance = Counter()
    conclusions = Counter()
    burst = Counter()
    workflow_data: dict[str, dict[str, float | int]] = defaultdict(
        lambda: {"runs": 0, "jobs": 0, "timed_jobs": 0, "runner_minutes": 0.0, "queue_minutes": 0.0}
    )
    workflow_conclusions: dict[str, Counter] = defaultdict(Counter)
    label_data: dict[str, dict] = defaultdict(_timing_group)
    runner_data: dict[str, dict] = defaultdict(_timing_group)
    total_jobs = timed_jobs = incomplete_jobs = skipped_without_start = 0
    timestamp_skew_jobs = 0
    runner_minutes = queue_minutes = 0.0
    timed_records: list[dict] = []

    seen_runs: set[int] = set()
    for run in runs:
        if not isinstance(run, dict) or not isinstance(run.get("id"), int):
            raise MeasurementError("snapshot contains a run without integer id")
        if run["id"] in seen_runs:
            raise MeasurementError(f"duplicate run id in snapshot: {run['id']}")
        seen_runs.add(run["id"])
        created = parse_time(str(run.get("created_at") or ""))
        if not (since <= created < until):
            raise MeasurementError(f"run {run['id']} lies outside snapshot window")
        burst[created.strftime("%Y-%m-%dT%H:%MZ")] += 1
        head_name = ((run.get("head_repository") or {}).get("full_name"))
        provenance["unknown" if not head_name else ("same_repo" if head_name == repo else "fork")] += 1
        conclusions[str(run.get("conclusion") or "incomplete")] += 1
        workflow = str(run.get("name") or "<unnamed>")
        workflow_data[workflow]["runs"] += 1
        workflow_conclusions[workflow][str(run.get("conclusion") or "incomplete")] += 1
        jobs = run.get("jobs")
        if not isinstance(jobs, list):
            raise MeasurementError(f"run {run['id']} has no jobs list")
        for job in jobs:
            total_jobs += 1
            workflow_data[workflow]["jobs"] += 1
            raw_labels = job.get("labels")
            if not isinstance(raw_labels, list) or any(
                not isinstance(label, str) for label in raw_labels
            ):
                raise MeasurementError(f"job {job.get('id')} labels must be a list of strings")
            labels = sorted({label for label in raw_labels if label})
            if not labels:
                labels = ["<unlabelled>"]
            runner = str(job.get("runner_name") or "<unassigned>")
            groups = [label_data[label] for label in labels] + [runner_data[runner]]

            started, completed = job.get("started_at"), job.get("completed_at")
            created_job = job.get("created_at")
            if not started:
                incomplete_jobs += 1
                if job.get("conclusion") == "skipped":
                    skipped_without_start += 1
                for group in groups:
                    _record_job(group, "incomplete", None, None)
                continue
            if not completed:
                incomplete_jobs += 1
                for group in groups:
                    _record_job(group, "incomplete", None, None)
                continue
            if not created_job:
                raise MeasurementError(f"started job {job.get('id')} has no created_at")
            work = _duration_minutes(started, completed, f"job {job.get('id')} runtime")
            wait = _duration_minutes(created_job, started, f"job {job.get('id')} queue wait")
            if work is None or wait is None:
                timestamp_skew_jobs += 1
                for group in groups:
                    _record_job(group, "skew", wait, work)
                continue
            timed_jobs += 1
            runner_minutes += work
            queue_minutes += wait
            timed_records.append({
                "job_id": job.get("id"),
                "workflow": workflow,
                "runner": runner,
                "host": host_of(runner),
                "start": parse_time(str(started)),
                "end": parse_time(str(completed)),
                "work": work,
                "wait": wait,
            })
            workflow_data[workflow]["timed_jobs"] += 1
            workflow_data[workflow]["runner_minutes"] += work
            workflow_data[workflow]["queue_minutes"] += wait
            for group in groups:
                _record_job(group, "timed", wait, work)

    by_workflow = []
    for name, data in workflow_data.items():
        by_workflow.append({
            "workflow": name,
            **{key: (round(value, 3) if isinstance(value, float) else value) for key, value in data.items()},
            "run_conclusions": dict(sorted(workflow_conclusions[name].items())),
        })
    by_workflow.sort(key=lambda row: (-row["runner_minutes"], row["workflow"]))

    return {
        "window": {
            "since": iso_z(since),
            "until": iso_z(until),
            "hours": round(window_hours, 6),
        },
        "denominators": {
            "runs": len(runs),
            "jobs": total_jobs,
            "timed_jobs": timed_jobs,
            "incomplete_or_untimed_jobs": incomplete_jobs,
            "timestamp_skew_jobs": timestamp_skew_jobs,
            "skipped_without_start": skipped_without_start,
            "timing_coverage": round(timed_jobs / total_jobs, 6) if total_jobs else None,
        },
        "runner": {
            "runner_minutes": round(runner_minutes, 3),
            "runner_minutes_per_wall_hour": round(runner_minutes / window_hours, 3),
            "average_runner_equivalents": round(runner_minutes / (window_hours * 60.0), 6),
            "queue_minutes_for_timed_jobs": round(queue_minutes, 3),
        },
        "provenance": {
            "same_repo": provenance["same_repo"],
            "fork": provenance["fork"],
            "unknown": provenance["unknown"],
        },
        "run_conclusions": dict(sorted(conclusions.items())),
        "runs_created_per_minute": dict(sorted(burst.items())),
        "by_workflow": by_workflow,
        "by_label": _render_timing_groups(label_data, "label"),
        "by_runner": _render_timing_groups(runner_data, "runner_name"),
        "co_residence": _coresidence(timed_records),
        "runners_inventory": _runners_inventory(snapshot.get("runners")),
    }


def load_snapshot(path: Path) -> dict:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise MeasurementError(f"cannot read snapshot {path}: {exc}") from exc
    if not isinstance(value, dict):
        raise MeasurementError("snapshot root must be an object")
    # A prior output can be replayed directly; retain only its source snapshot.
    if "snapshot" in value and isinstance(value["snapshot"], dict):
        return value["snapshot"]
    return value


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument("--input", type=Path, help="replay an existing JSON snapshot")
    source.add_argument("--repo", help="owner/repository for live collection")
    parser.add_argument("--since", help="inclusive UTC ISO-8601 start (live mode)")
    parser.add_argument("--until", help="exclusive UTC ISO-8601 end (live mode)")
    parser.add_argument("--output", type=Path, help="write JSON result (default: stdout)")
    parser.add_argument(
        "--runners",
        action="store_true",
        help=(
            "collecter aussi l'inventaire des runners enregistres (slots par hote). "
            "Exige un droit d'administration sur le depot : sans lui l'inventaire "
            "sort `unavailable` avec sa raison, jamais un parc vide."
        ),
    )
    args = parser.parse_args(argv)

    try:
        if args.input:
            if args.since or args.until:
                raise MeasurementError("--since/--until cannot be combined with --input")
            if args.runners:
                raise MeasurementError("--runners cannot be combined with --input")
            snapshot = load_snapshot(args.input)
        else:
            if not args.since or not args.until:
                raise MeasurementError("live mode requires --since and --until")
            snapshot = collect_snapshot(
                args.repo,
                parse_time(args.since),
                parse_time(args.until),
                include_runners=args.runners,
            )
        result = {"snapshot": snapshot, "analysis": analyze(snapshot)}
        rendered = json.dumps(result, indent=2, ensure_ascii=False) + "\n"
        if args.output:
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(rendered, encoding="utf-8")
            print(f"[runner-demand] wrote {args.output}")
        else:
            print(rendered, end="")
        return EXIT_OK
    except MeasurementError as exc:
        print(f"[runner-demand] BROKEN INSTRUMENT: {exc}", file=sys.stderr)
        return EXIT_BROKEN


if __name__ == "__main__":
    raise SystemExit(main())
