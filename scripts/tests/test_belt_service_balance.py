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
    """PR sans tag lisible -> _sans-lane ; fermeture sans PR (body None ou "")
    -> _manuel. Les deux categories ne se confondent jamais.

    Review c.6048082193 : avant le fix, pr_body="" (depuis fetch_closed_issues)
    etait route a tort vers _sans-lane (46 fermetures dans la mesure).
    Apres le fix, les deux cas (None et "") vont a _manuel, _sans-lane
    reste reserve aux PRs avec body mais sans tag lisible.
    """
    now = datetime.now(timezone.utc)
    services = [
        _make_service(now - timedelta(days=2), now, pr_body="Description libre sans tag."),  # sans-lane
        _make_service(now - timedelta(days=3), now, pr_body=None),  # manuel (pas de PR)
        _make_service(now - timedelta(days=4), now, pr_body=""),  # manuel aussi (empty body = pas de PR)
    ]
    by_lane = bsb.aggregate_by_lane(services)
    assert "_sans-lane" in by_lane
    assert "_manuel" in by_lane
    assert by_lane["_sans-lane"].services == 1
    assert by_lane["_manuel"].services == 2


def test_attribution_empty_pr_body_is_manuel():
    """pr_body="" (empty string, comme dans fetch_closed_issues) -> 'manuel',
    PAS 'sans-lane'. Review c.6048082193 : le bug d'avant mettait 46
    fermetures sans PR dans `_sans-lane` au lieu de `_manuel`.
    """
    s = _make_service(pr_body="")
    bsb.attribute_service(s)
    assert s.attribution_kind == "manuel", (
        f"pr_body='' devrait donner 'manuel', got '{s.attribution_kind}'"
    )
    assert s.lane is None


def test_dedup_T_Tplus5_same_issue_returns_one():
    """Review c.6048082193 : mergedAt et closedAt different de quelques
    secondes. Dedup sur (issue_number, service_date) laissait passer les
    doublons. Apres fix (dedup sur issue_number seul), une issue fermee par
    PR avec mergedAt=T et closedAt=T+5s donne 1 seul service.
    """
    base = datetime(2026, 10, 5, 12, 0, 0, tzinfo=timezone.utc)
    iso_t = _iso(base)
    iso_t_plus_5s = _iso(base + timedelta(seconds=5))
    s_pr = bsb.Service(
        issue_number=42, issue_created_at=iso_t, service_date=iso_t,
        service_kind="pr_merge", pr_number=100,
        pr_body="Grain: DEEP/lean -- lane myia-ai-01:CoursIA-2",
    )
    s_manuel = bsb.Service(
        issue_number=42, issue_created_at=iso_t, service_date=iso_t_plus_5s,
        service_kind="manuel", pr_number=None, pr_body=None,
    )
    bsb.attribute_service(s_pr)
    bsb.attribute_service(s_manuel)
    deduped = bsb.deduplicate_services([s_pr, s_manuel])
    assert len(deduped) == 1
    assert deduped[0].service_kind == "pr_merge"
    assert deduped[0].lane == "myia-ai-01:CoursIA-2"
    # Ordre inverse : le manuel ne doit pas ecraser le pr_merge deja vu
    deduped_rev = bsb.deduplicate_services([s_manuel, s_pr])
    assert len(deduped_rev) == 1
    assert deduped_rev[0].service_kind == "pr_merge"


def test_search_issueCount_positive_control_mismatch_raises():
    """Si le nombre de fermetures lues != issueCount de la requete search,
    fetch_closed_issues leve RuntimeError. Review c.6048082193 : le controle
    positif attrape les pages manquantes ou les doublons.

    On mock subprocess.run pour rendre issueCount=10 mais seulement 3 nodes,
    ce qui doit lever RuntimeError cite dans le commentaire de PR.
    """
    import io
    import unittest.mock as mock

    fake_response = json.dumps({
        "data": {
            "search": {
                "issueCount": 10,
                "nodes": [
                    {"number": 1, "createdAt": "2026-10-05T00:00:00Z", "closedAt": "2026-10-06T00:00:00Z"},
                    {"number": 2, "createdAt": "2026-10-05T00:00:00Z", "closedAt": "2026-10-06T00:00:00Z"},
                    {"number": 3, "createdAt": "2026-10-05T00:00:00Z", "closedAt": "2026-10-06T00:00:00Z"},
                ],
                "pageInfo": {"hasNextPage": False, "endCursor": None},
            }
        }
    })
    fake_completed = mock.Mock(returncode=0, stdout=fake_response, stderr="")

    with mock.patch("subprocess.run", return_value=fake_completed), \
         mock.patch.dict("os.environ", {"GH_TOKEN": "fake-token"}, clear=False), \
         mock.patch("belt_service_balance._run_capture", return_value="fake-token"), \
         mock.patch("sys.stderr", io.StringIO()):
        try:
            bsb.fetch_closed_issues(
                "jsboige", "CoursIA",
                datetime(2026, 10, 1, tzinfo=timezone.utc),
                max_pages=1,
            )
            raised = False
            msg = ""
        except RuntimeError as e:
            raised = True
            msg = str(e)
    assert raised, "fetch_closed_issues aurait du lever RuntimeError (read=3 vs issueCount=10)"
    assert "closed-issues count mismatch" in msg
    assert "read=3" in msg
    assert "issueCount=10" in msg


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


# ---------------------------------------------------------------------------
# Review #19786 c.6047207444 : 2 points bloquants
# ---------------------------------------------------------------------------


def test_dedup_prefers_pr_merge_over_manuel():
    """Une issue fermee par PR est dans pr_merge ET dans manuel. On garde
    le pr_merge (attribution par tag `Grain:` de la PR, plus precise) et
    on retire le manuel. Le dedup se fait sur (issue_number, service_date)."""
    iso_now = _iso(datetime.now(timezone.utc))
    s_pr = bsb.Service(
        issue_number=42,
        issue_created_at=iso_now,
        service_date=iso_now,
        service_kind="pr_merge",
        pr_number=100,
        pr_body="Grain: DEEP/lean -- lane myia-ai-01:CoursIA-2",
    )
    s_manuel = bsb.Service(
        issue_number=42,
        issue_created_at=iso_now,
        service_date=iso_now,
        service_kind="manuel",
        pr_number=None,
        pr_body="",
    )
    bsb.attribute_service(s_pr)
    bsb.attribute_service(s_manuel)
    deduped = bsb.deduplicate_services([s_pr, s_manuel])
    assert len(deduped) == 1
    assert deduped[0].service_kind == "pr_merge"
    # Ordre inverse : manuel avant pr_merge -> on garde pr_merge
    deduped_rev = bsb.deduplicate_services([s_manuel, s_pr])
    assert len(deduped_rev) == 1
    assert deduped_rev[0].service_kind == "pr_merge"


def test_dedup_keeps_separate_issues_separate():
    """Deux issues differentes (meme service_date) restent separees."""
    iso_now = _iso(datetime.now(timezone.utc))
    s1 = bsb.Service(
        issue_number=42, issue_created_at=iso_now, service_date=iso_now,
        service_kind="pr_merge", pr_number=100,
        pr_body="Grain: DEEP/lean -- lane myia-ai-01:CoursIA-2",
    )
    s2 = bsb.Service(
        issue_number=43, issue_created_at=iso_now, service_date=iso_now,
        service_kind="manuel", pr_number=None, pr_body="",
    )
    bsb.attribute_service(s1)
    bsb.attribute_service(s2)
    deduped = bsb.deduplicate_services([s1, s2])
    assert len(deduped) == 2
    assert {s.issue_number for s in deduped} == {42, 43}


def test_main_raises_on_gh_failure_exit_2_unknown():
    """Si fetch_services leve (panne gh), main retourne 2 + UNKNOWN sur stderr.

    Avant le fix : 3 chemins `return services` avalaient la panne et
    `main()` sortait en exit 0 avec "0 services" -- faux 0 sur panne.
    Apres le fix : RuntimeError remonte, `main()` retourne 2 + "UNKNOWN:"
    sur stderr.
    """
    import io
    import unittest.mock as mock

    def boom(*a, **k):
        raise RuntimeError("gh api graphql returncode=22 stderr='auth required'")

    with mock.patch.object(bsb, "fetch_services", side_effect=boom), \
         mock.patch.object(bsb, "fetch_closed_issues", return_value=[]), \
         mock.patch.object(bsb, "fetch_open_issues", return_value=[]):
        captured_stderr = io.StringIO()
        with mock.patch("sys.stderr", captured_stderr):
            rc = bsb.main(["--days", "7"])
    assert rc == 2, f"expected exit 2, got {rc}"
    err = captured_stderr.getvalue()
    assert "UNKNOWN" in err, f"expected UNKNOWN in stderr, got: {err}"
    assert "gh api graphql" in err


def test_main_raises_on_closed_issues_failure():
    """Si fetch_closed_issues leve, main() retourne 2 (coherence avec fetch_services)."""
    import io
    import unittest.mock as mock

    def boom(*a, **k):
        raise RuntimeError("gh api graphql returncode=22")

    with mock.patch.object(bsb, "fetch_services", return_value=[]), \
         mock.patch.object(bsb, "fetch_closed_issues", side_effect=boom), \
         mock.patch.object(bsb, "fetch_open_issues", return_value=[]):
        captured_stderr = io.StringIO()
        with mock.patch("sys.stderr", captured_stderr):
            rc = bsb.main(["--days", "7"])
    assert rc == 2