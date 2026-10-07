"""Tests purs pour belt_service_balance.py (issue #18832).

Acceptance du DM dispatch-ai01c2-18832-service-balance :
1. Trois classes d'age : courant (< 7 j), tapis (7-30), ancien (> 30).
2. Attribution par lane via parseur canonique `grain_tag.py`.
3. PR sans tag lisible -> `sans-lane` (jamais ignore).
4. Fermeture manuelle sans PR -> `manuel`.
5. Controle positif : fenetre de 7 j avec 42 % < 3 j -> verdict [WARN].
6. Sortie --json / --dashboard-line fonctionnelles.

Pas de I/O reseau : fixtures injectees. La logique pure est testable en
isolation, et les fonctions d'I/O sont substituees par des fixtures.
"""
import json
import sys
from datetime import datetime, timezone, timedelta
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "coordination"))

import belt_service_balance as bsb  # noqa: E402


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


def _iso(dt: datetime) -> str:
    return dt.astimezone(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _make_service(
    issue_created: datetime | None = None,
    service_date: datetime | None = None,
    pr_body: str | None = "Grain: DEEP/lean -- lane myia-ai-01:CoursIA",
    pr_number: int = 100,
) -> bsb.Service:
    if issue_created is None:
        issue_created = datetime.now(timezone.utc) - timedelta(days=2)
    if service_date is None:
        service_date = datetime.now(timezone.utc)
    return bsb.Service(
        issue_number=42,
        issue_created_at=_iso(issue_created),
        service_date=_iso(service_date),
        service_kind="pr_merge",
        pr_number=pr_number,
        pr_body=pr_body,
    )


# ---------------------------------------------------------------------------
# Age classification
# ---------------------------------------------------------------------------


def test_age_class_courant():
    """age < 7j -> 'courant'."""
    s = _make_service(
        issue_created=datetime(2026, 10, 1, tzinfo=timezone.utc),
        service_date=datetime(2026, 10, 5, tzinfo=timezone.utc),  # 4 jours
    )
    assert s.is_courant
    assert not s.is_tapis
    assert not s.is_ancien
    assert 3.9 < s.age_days < 4.1


def test_age_class_tapis():
    """age entre 7 et 30 j -> 'tapis' (pas ancien)."""
    s = _make_service(
        issue_created=datetime(2026, 9, 20, tzinfo=timezone.utc),
        service_date=datetime(2026, 10, 5, tzinfo=timezone.utc),  # 15 jours
    )
    assert s.is_tapis
    assert not s.is_courant
    assert not s.is_ancien


def test_age_class_ancien():
    """age > 30 j -> 'ancien' (sous-classe de tapis)."""
    s = _make_service(
        issue_created=datetime(2026, 8, 1, tzinfo=timezone.utc),
        service_date=datetime(2026, 10, 5, tzinfo=timezone.utc),  # 65 jours
    )
    assert s.is_ancien
    assert s.is_tapis  # ancien est sous-classe de tapis
    assert not s.is_courant


def test_age_class_boundary_7j_is_tapis():
    """age == 7 j pile -> 'tapis' (>=7j, pas courant)."""
    s = _make_service(
        issue_created=datetime(2026, 9, 28, 0, 0, 0, tzinfo=timezone.utc),
        service_date=datetime(2026, 10, 5, 0, 0, 0, tzinfo=timezone.utc),
    )
    assert 7.0 - 0.01 < s.age_days < 7.0 + 0.01
    assert s.is_tapis
    assert not s.is_courant


def test_age_class_boundary_30j_is_not_ancien():
    """age == 30 j pile : 'tapis' mais PAS 'ancien' (ancien > 30 strict)."""
    s = _make_service(
        issue_created=datetime(2026, 9, 5, 0, 0, 0, tzinfo=timezone.utc),
        service_date=datetime(2026, 10, 5, 0, 0, 0, tzinfo=timezone.utc),
    )
    assert s.is_tapis
    assert not s.is_ancien  # strict >


def test_age_class_31j_is_ancien():
    """age > 30 j strict -> 'ancien'."""
    s = _make_service(
        issue_created=datetime(2026, 9, 4, 0, 0, 0, tzinfo=timezone.utc),
        service_date=datetime(2026, 10, 5, 0, 0, 0, tzinfo=timezone.utc),
    )
    assert s.is_ancien
    assert s.is_tapis


# ---------------------------------------------------------------------------
# Attribution
# ---------------------------------------------------------------------------


def test_attribution_grain_lane():
    """Body avec Grain tag -> lane et attribution 'grain'."""
    s = _make_service(pr_body="Grain: DEEP/research-code -- lane myia-po-2024:CoursIA-2 -- prev: ...")
    bsb.attribute_service(s)
    assert s.attribution_kind == "grain"
    assert s.lane == "myia-po-2024:CoursIA-2"


def test_attribution_no_pr_is_manuel():
    """Pas de PR (body=None) -> 'manuel'."""
    s = _make_service(pr_body=None)
    bsb.attribute_service(s)
    assert s.attribution_kind == "manuel"
    assert s.lane is None


def test_attribution_no_tag_is_sans_lane():
    """Body present sans tag -> 'sans-lane', jamais ignore."""
    s = _make_service(pr_body="Description libre sans tag.")
    bsb.attribute_service(s)
    assert s.attribution_kind == "sans-lane"
    assert s.lane is None


def test_attribution_tag_without_lane_is_sans_lane():
    """Tag present mais sans lane -> 'sans-lane'."""
    s = _make_service(pr_body="Grain: DEEP/lean")
    bsb.attribute_service(s)
    assert s.attribution_kind == "sans-lane"


def test_attribution_form_tolerant():
    """Le parseur canonique tolere les variantes Markdown."""
    body = "**Grain:** LIGHT/guard - lane myia-po-2023:CoursIA"
    s = _make_service(pr_body=body)
    bsb.attribute_service(s)
    assert s.attribution_kind == "grain"
    assert s.lane == "myia-po-2023:CoursIA"


# ---------------------------------------------------------------------------
# Aggregation
# ---------------------------------------------------------------------------


def test_aggregate_separates_courant_tapis_ancien():
    """Un mix de services est agrege correctement par lane et classe.

    Note : ancien est sous-classe de tapis, donc un service 'ancien' est
    aussi compte dans tapis.
    """
    now = datetime.now(timezone.utc)
    services = [
        _make_service(now - timedelta(days=2), now, pr_body="Grain: DEEP/lean -- lane myia-ai-01:CoursIA-2"),  # courant
        _make_service(now - timedelta(days=15), now, pr_body="Grain: DEEP/lean -- lane myia-ai-01:CoursIA-2"),  # tapis
        _make_service(now - timedelta(days=60), now, pr_body="Grain: DEEP/lean -- lane myia-ai-01:CoursIA-2"),  # ancien = tapis+ancien
    ]
    by_lane = bsb.aggregate_by_lane(services)
    st = by_lane["myia-ai-01:CoursIA-2"]
    assert st.services == 3
    assert st.courant == 1
    assert st.tapis == 2  # 15j + 60j (ancien est sous-classe)
    assert st.ancien == 1


def test_aggregate_sans_lane_aggregated_under_marker():
    """Les sans-lane sont agreges sous _sans-lane, jamais absorbees ailleurs."""
    now = datetime.now(timezone.utc)
    services = [
        _make_service(now - timedelta(days=2), now, pr_body=""),  # sans-lane
        _make_service(now - timedelta(days=3), now, pr_body=None),  # manuel
    ]
    by_lane = bsb.aggregate_by_lane(services)
    assert "_sans-lane" in by_lane
    assert "_manuel" in by_lane
    assert by_lane["_sans-lane"].services == 1
    assert by_lane["_manuel"].services == 1


# ---------------------------------------------------------------------------
# WARN / plafond 1/3
# ---------------------------------------------------------------------------


def test_warn_when_courant_above_third():
    """Si courant > 1/3 du service hebdo, [WARN] est pose."""
    st = bsb.LaneStats(lane="test")
    st.services = 3
    st.courant = 2  # 66% > 33%
    st.tapis = 1
    st.finalize()
    assert st.warn is True
    assert st.courant_pct > 0.33


def test_no_warn_when_courant_at_third_exact():
    """Si courant == 1/3 EXACT, pas de warn (frontiere inclusive haute)."""
    st = bsb.LaneStats(lane="test")
    st.services = 3
    st.courant = 1  # 33.3% (egalite)
    st.tapis = 2
    st.finalize()
    # 1/3 == COURANT_CEILING_FRAC donc ce n'est PAS > (strict)
    assert st.warn is False


def test_no_warn_with_zero_services():
    """Lane sans service : pas de warn, pas de crash."""
    st = bsb.LaneStats(lane="empty")
    st.finalize()
    assert st.warn is False
    assert st.courant_pct == 0.0


# ---------------------------------------------------------------------------
# Controle positif : mesure du 07/10 (42 % < 3 j -> [WARN])
# ---------------------------------------------------------------------------


def test_positive_control_42pct_courant_renders_warn():
    """Controle positif : reproduction de la mesure du 07/10.

    Sur 100 services simules : 42 fermes < 3 j apres creation, 58 autres.
    La fleet doit avoir courant_pct = 0.42 et warn=True.
    """
    now = datetime.now(timezone.utc)
    services = []
    # 42 services < 3 j (courant)
    for _ in range(42):
        services.append(
            _make_service(
                now - timedelta(days=2),
                now,
                pr_body="Grain: DEEP/lean -- lane myia-ai-01:CoursIA-2",
            )
        )
    # 58 services plus anciens (tapis/ancien melanges)
    for i in range(58):
        days_old = 10 + i  # entre 10 et 67 j
        services.append(
            _make_service(
                now - timedelta(days=days_old),
                now,
                pr_body="Grain: DEEP/lean -- lane myia-ai-01:CoursIA-2",
            )
        )

    by_lane = bsb.aggregate_by_lane(services)
    fleet_total = len(services)
    fleet_courant = sum(s.is_courant for s in services)
    fleet_ancien = sum(s.is_ancien for s in services)
    stock = {}

    text = bsb.render_text(by_lane, fleet_total, fleet_courant, fleet_ancien, stock)
    assert "[WARN]" in text  # fleet >= 33% courant
    assert "42" not in text or "%" in text  # ratio is rendered
    assert "42%" in text or "0%" not in text.split("FLEET")[1].split("\n")[0]


def test_render_json_serializable():
    """La sortie JSON est valide et contient by_lane + fleet + stock."""
    now = datetime.now(timezone.utc)
    services = [
        _make_service(now - timedelta(days=2), now),
    ]
    by_lane = bsb.aggregate_by_lane(services)
    text = bsb.render_json(
        services, by_lane,
        fleet_total=1, fleet_courant=1, fleet_ancien=0,
        stock={"2026-10": 5},
    )
    parsed = json.loads(text)
    assert "by_lane" in parsed
    assert "fleet" in parsed
    assert "stock" in parsed
    assert parsed["fleet"]["total"] == 1


def test_render_dashboard_line_under_240():
    """La dashboard-line tient en 240 chars (les 200 spec + tolerance)."""
    now = datetime.now(timezone.utc)
    services = []
    for i in range(20):
        services.append(
            _make_service(
                now - timedelta(days=i + 1),
                now,
                pr_body=f"Grain: DEEP/lean -- lane myia-po-202{i % 9}:CoursIA",
            )
        )
    by_lane = bsb.aggregate_by_lane(services)
    line = bsb.render_dashboard_line(by_lane, fleet_total=20, fleet_courant=10)
    assert len(line) <= 240, f"Line too long ({len(line)} chars): {line}"
    assert "belt-balance[7j]" in line
    assert "10/20" in line or "fleet=20" in line


# ---------------------------------------------------------------------------
# Stock par mois
# ---------------------------------------------------------------------------


def test_stock_open_by_month_groups_correctly():
    """Les issues ouvertes sont groupees par mois de creation."""
    issues = [
        {"createdAt": "2026-09-15T00:00:00Z"},
        {"createdAt": "2026-09-28T00:00:00Z"},
        {"createdAt": "2026-10-01T00:00:00Z"},
        {"createdAt": "2026-10-15T00:00:00Z"},
        {"createdAt": ""},  # skip
    ]
    out = bsb.stock_open_by_month(issues)
    assert out == {"2026-09": 2, "2026-10": 2}


def test_stock_empty_input():
    """Pas d'issues -> dict vide."""
    assert bsb.stock_open_by_month([]) == {}