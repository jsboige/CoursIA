"""
QuantConnect MCP Lite — lightweight MCP server for CoursIA workflows.

Exposes only the QC REST endpoints used in backtesting workflows:
- compile: create_compile, read_compile
- backtest: create_backtest, read_backtest, list_backtests
- project: list_projects, read_project
- file: read_file, update_file_contents, create_file

Auth: QC_API_USER_ID + QC_API_ACCESS_TOKEN env vars.
  Uses SHA256(token:timestamp) + Basic auth + Timestamp header.
Rate limit: 10 calls/min enforced in-process.
Schema target: <5k tokens (vs ~40k for full quantconnect/mcp-server).

Usage: python server.py
Config: see docs/quantconnect.md for .mcp.json setup.
"""

import base64
import hashlib
import os
import time
from collections import deque
from datetime import datetime, timezone
from typing import Any, Optional

import requests
from mcp.server.fastmcp import FastMCP

API_BASE = "https://www.quantconnect.com/api/v2"
RATE_LIMIT_WINDOW = 60
RATE_LIMIT_MAX = 10

mcp = FastMCP("qc-mcp-lite")

_call_timestamps: deque = deque()


def _get_credentials() -> tuple[str, str]:
    user_id = os.environ.get("QC_API_USER_ID", "")
    token = os.environ.get("QC_API_ACCESS_TOKEN", "")
    if not user_id or not token:
        raise ValueError(
            "QC_API_USER_ID and QC_API_ACCESS_TOKEN env vars required"
        )
    return user_id, token


def _rate_limit():
    now = time.time()
    while _call_timestamps and _call_timestamps[0] < now - RATE_LIMIT_WINDOW:
        _call_timestamps.popleft()
    if len(_call_timestamps) >= RATE_LIMIT_MAX:
        wait = _call_timestamps[0] + RATE_LIMIT_WINDOW - now + 0.1
        if wait > 0:
            time.sleep(wait)
    _call_timestamps.append(time.time())


def _auth_headers() -> dict[str, str]:
    user_id, token = _get_credentials()
    timestamp = str(int(datetime.now(timezone.utc).timestamp()))
    hashed = hashlib.sha256(f"{token}:{timestamp}".encode("utf-8")).hexdigest()
    basic = base64.b64encode(f"{user_id}:{hashed}".encode()).decode()
    return {
        "Authorization": f"Basic {basic}",
        "Timestamp": timestamp,
    }


def _api_post(path: str, data: Optional[dict] = None) -> dict:
    _rate_limit()
    resp = requests.post(
        f"{API_BASE}{path}",
        headers=_auth_headers(),
        json=data or {},
        timeout=120,
    )
    resp.raise_for_status()
    payload = resp.json()
    # QC v2 always returns HTTP 200, even on API-level failures: the body carries
    # {"success": false, "errors": [...]}. raise_for_status() does NOT catch these.
    # Without this guard, a rejected call (e.g. backtest create on a not-ready
    # compile, or a duplicate name) flows through and create_backtest returns an
    # empty backtestId with NO error text — forcing blind retries. Surface it.
    if isinstance(payload, dict) and payload.get("success") is False:
        errors = payload.get("errors") or []
        msg = "; ".join(str(e) for e in errors) or "unknown error"
        raise RuntimeError(f"QC API {path} rejected the request: {msg[:1000]}")
    return payload


def _parse_int(value: Any) -> int:
    """Parse a QC statistics string to int.

    QC statistics values are strings ('318', '1,234', '-'); '-' is the
    'not applicable' marker (a 0-trade backtest shows '-' for several fields).
    Returns 0 for None, '', '-', or anything unparseable.
    """
    if value is None:
        return 0
    text = str(value).strip().replace(",", "")
    if text in ("", "-", "nan", "NaN", "None"):
        return 0
    try:
        return int(float(text))
    except (ValueError, TypeError):
        return 0


def _extract_stats(bt: dict) -> dict:
    stats = bt.get("statistics", {}) or {}
    runtime_stats = bt.get("runtimeStatistics", {}) or {}
    # Surface runtime errors so a failed backtest is diagnosable without a
    # separate raw dump (QC returns 'error' + 'stacktrace' on Runtime Error).
    error = bt.get("error") or ""
    stacktrace = bt.get("stacktrace") or ""
    # totalOrders is NOT reliably at the top level of the QC backtests/read
    # object: on completed backtests it is null there. The authoritative count
    # lives in statistics['Total Orders'] (a string like '318'). The top-level
    # field is only used as a fallback for summary/list responses that omit the
    # statistics dict. Without this, a real strategy that placed 318 orders is
    # reported as totalOrders=0 and falsely diagnosed as 'never traded'.
    total_orders_raw = stats.get("Total Orders")
    if total_orders_raw not in (None, "", "-"):
        total_orders = _parse_int(total_orders_raw)
    else:
        total_orders = bt.get("totalOrders") or 0
    result = {
        "backtestId": bt.get("backtestId", ""),
        "name": bt.get("name", ""),
        "status": bt.get("status", ""),
        "created": bt.get("created", ""),
        "completed": bt.get("completed", ""),
        "tradeableDates": bt.get("tradeableDates", 0),
        "totalOrders": total_orders,
        "equity": bt.get("equity", {}),
        "statistics": {
            "sharpeRatio": stats.get("Sharpe Ratio", "-"),
            "compoundingAnnualReturn": stats.get("Compounding Annual Return", "-"),
            "drawdown": stats.get("Drawdown", "-"),
            # QC's statistics dict keys net profit as 'Net Profit' (a
            # percentage like '76.088%'), NOT 'Total Net Profit' — the latter
            # is a runtimeStatistics label and never appears in statistics.
            "totalNetProfit": stats.get("Net Profit", "-"),
            "probabilisticSharpeRatio": stats.get(
                "Probabilistic Sharpe Ratio", "-"
            ),
        },
        "progress": bt.get("progress", 0),
    }
    # Surface the dollar-denominated net profit from runtimeStatistics (e.g.
    # '$59,745.60') alongside the percentage figure in statistics — useful for
    # diagnosis and disambiguates the '%' return from an absolute PnL.
    runtime_profit = runtime_stats.get("Net Profit")
    if runtime_profit:
        result["statistics"]["netProfitAbsolute"] = runtime_profit
    if error or stacktrace:
        # 'error' and 'stacktrace' are often identical; keep both but cap size.
        result["error"] = error[:1200]
        result["stacktrace"] = stacktrace[:1200]
    return result


# ─── Compile ──────────────────────────────────────────────────────────


@mcp.tool()
def create_compile(project_id: int) -> dict:
    """Create a compile job for a QC project. Returns compileId."""
    data = _api_post("/compile/create", {"projectId": project_id})
    return {
        "compileId": data.get("compileId", ""),
        "state": data.get("state", ""),
        "projectId": project_id,
    }


@mcp.tool()
def read_compile(project_id: int, compile_id: str) -> dict:
    """Read compile job status and results."""
    data = _api_post(
        f"/compile/read",
        {"projectId": project_id, "compileId": compile_id},
    )
    return {
        "compileId": compile_id,
        "state": data.get("state", ""),
        "errors": data.get("errors", []),
        "projectId": project_id,
    }


# ─── Backtest ─────────────────────────────────────────────────────────


@mcp.tool()
def create_backtest(
    project_id: int,
    compile_id: str,
    backtest_name: str,
    parameters: Optional[dict] = None,
) -> dict:
    """Create a backtest from a compiled project. Returns backtestId."""
    body: dict[str, Any] = {
        "projectId": project_id,
        "compileId": compile_id,
        "backtestName": backtest_name,
    }
    if parameters:
        body["parameters"] = parameters
    data = _api_post("/backtests/create", body)
    bt = data.get("backtest", data)
    return {
        "backtestId": bt.get("backtestId", data.get("backtestId", "")),
        "projectId": project_id,
        "status": bt.get("status", data.get("status", "")),
    }


@mcp.tool()
def read_backtest(project_id: int, backtest_id: str) -> dict:
    """Read backtest results including Sharpe, CAGR, MaxDD."""
    data = _api_post(
        "/backtests/read",
        {"projectId": project_id, "backtestId": backtest_id},
    )
    bt = data.get("backtest", data)
    return _extract_stats(bt)


@mcp.tool()
def list_backtests(project_id: int) -> dict:
    """List all backtests for a project."""
    data = _api_post(
        "/backtests/list",
        {"projectId": project_id, "includeStatistics": False},
    )
    backtests = data.get("backtests", [])
    return {
        "count": len(backtests),
        "backtests": [
            {
                "backtestId": bt.get("backtestId", ""),
                "name": bt.get("name", ""),
                "created": bt.get("created", ""),
                "status": bt.get("status", ""),
            }
            for bt in backtests[:20]
        ],
    }


# ─── Project ──────────────────────────────────────────────────────────


@mcp.tool()
def create_project(name: str, language: str = "Py") -> dict:
    """Create a new QC project. Returns projectId.

    ``language`` is "Py" (default) or "C#". The project is created in the
    account's default organization unless the account has a single org. Used
    to deploy local-only baseline-clone strategies (e.g. QC Strategy Library
    references like LongShortHarvest) to QC Cloud so they can be compiled and
    backtested — ``create_file`` requires an existing project.
    """
    data = _api_post("/projects/create", {"name": name, "language": language})
    # QC returns {"projects": [{projectId, name, organizationId}], ...} — mirror
    # the read_project shape so callers get a consistent projectId field.
    projects = data.get("projects", [])
    proj = projects[0] if projects else {}
    return {
        "projectId": proj.get("projectId", 0),
        "name": proj.get("name", name),
        "language": language,
        "organizationId": proj.get("organizationId", ""),
    }


@mcp.tool()
def list_projects(name_contains: str = "") -> dict:
    """List all QC projects.

    The full list is fetched in one call but capped (client-side) to keep the
    response under the schema token budget. Pass ``name_contains`` to filter
    case-insensitively BEFORE the cap — needed to locate project IDs by strategy
    name when the account has many projects (the cap otherwise hides them).
    """
    data = _api_post("/projects/read")
    projects = data.get("projects", [])
    total = len(projects)
    if name_contains:
        nc = name_contains.lower()
        projects = [p for p in projects if nc in (p.get("name", "") or "").lower()]
    return {
        "count": len(projects),
        "total": total,
        "projects": [
            {
                "projectId": p.get("projectId", 0),
                "name": p.get("name", ""),
                "created": p.get("created", ""),
                "language": p.get("language", ""),
                "organizationId": p.get("organizationId", ""),
            }
            for p in projects[:30]
        ],
    }


@mcp.tool()
def read_project(project_id: int) -> dict:
    """Read a single project's details and files."""
    data = _api_post(
        "/projects/read",
        {"projectId": project_id},
    )
    proj = data.get("projects", [{}])[0] if data.get("projects") else data
    return {
        "projectId": proj.get("projectId", project_id),
        "name": proj.get("name", ""),
        "description": proj.get("description", ""),
        "language": proj.get("language", ""),
        "organizationId": proj.get("organizationId", ""),
        "files": [
            {"name": f.get("name", ""), "content": f.get("content", "")[:200]}
            for f in (proj.get("files") or [])
        ],
    }


# ─── File ─────────────────────────────────────────────────────────────


@mcp.tool()
def read_file(project_id: int, name: Optional[str] = None) -> dict:
    """Read file(s) from a project. If name is omitted, returns all files."""
    body: dict[str, Any] = {"projectId": project_id}
    if name:
        body["name"] = name
    data = _api_post("/files/read", body)
    files = data.get("files", [])
    if name and files:
        return {
            "name": files[0].get("name", name),
            "content": files[0].get("content", ""),
        }
    return {
        "count": len(files),
        "files": [
            {"name": f.get("name", ""), "size": len(f.get("content", ""))}
            for f in files
        ],
    }


@mcp.tool()
def update_file_contents(project_id: int, name: str, content: str) -> dict:
    """Update a file's contents in a project."""
    data = _api_post(
        "/files/update",
        {"projectId": project_id, "name": name, "content": content},
    )
    return {"success": data.get("success", True), "name": name}


@mcp.tool()
def create_file(project_id: int, name: str, content: str = "") -> dict:
    """Create a new file in a project."""
    data = _api_post(
        "/files/create",
        {"projectId": project_id, "name": name, "content": content},
    )
    return {"success": data.get("success", True), "name": name}


# ─── Entry point ──────────────────────────────────────────────────────

if __name__ == "__main__":
    mcp.run(transport="stdio")
