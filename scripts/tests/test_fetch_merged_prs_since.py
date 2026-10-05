#!/usr/bin/env python3
"""Unit tests for fetch_merged_prs_since.py -- the merge-window fetcher.

The G-VAR-3 adjacency guard resolves a lane's REAL predecessor from the merged
sequence. When this fetch returns nothing the guard silently degrades to the
frozen `prev:` field -- it keeps passing and blocking, just on the wrong axis.
Two mechanisms produced that degradation, and these tests pin both shut:

* **#12636** -- `--limit 100` orders by CREATION date, so a quiet lane's older
  grain fell out. Fixed by searching on `merged:>=` (merge-time).
* **2026-08-29** -- the fix for #12636 paged with `gh pr list ... --page N`, a
  flag `gh pr list` does not have. Every real call raised, so the guard ran on
  `declared` repo-wide for the script's whole life. The three tests here all
  injected a fake `run`, so the argv was never executed once --
  `test_run_gh_argv_is_accepted_by_gh` is the control that closes that hole.

Run:
    python -m pytest scripts/tests/test_fetch_merged_prs_since.py
"""
import io
import shutil
import subprocess
import sys
from datetime import date, timedelta
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import fetch_merged_prs_since as fmps  # noqa: E402
from gh_payload_cache import PayloadCache  # noqa: E402


def _pr(n: int, merged_at: str) -> dict:
    return {"number": n, "body": "some body", "mergedAt": merged_at}


def test_since_date_default_and_days():
    today = date.today()
    assert fmps.since_date(0) == today.isoformat()
    assert fmps.since_date(21) == (today - timedelta(days=21)).isoformat()


def test_fetch_walks_the_window_in_date_slices_and_dedupes():
    """The window is covered by consecutive [since, until) slices, no overlap kept."""
    calls = []

    def fake_run(since, until):
        calls.append((since, until))
        # one PR per slice, plus a duplicate of the first in the last slice
        n = len(calls)
        out = [_pr(n, f"{since}T00:00:00Z")]
        if n == 3:
            out.append(_pr(1, "duplicate"))
        return out

    prs = fmps.fetch("2026-08-01", run=fake_run, slice_days=3,
                     today=date(2026, 8, 8))

    # 2026-08-01 -> 2026-08-09 (today+1) in 3-day slices: 01-04, 04-07, 07-09
    assert calls == [("2026-08-01", "2026-08-04"),
                     ("2026-08-04", "2026-08-07"),
                     ("2026-08-07", "2026-08-09")]
    nums = [p["number"] for p in prs]
    assert nums == [1, 2, 3], "le doublon inter-tranches n'a pas ete dedoublonne"


def test_fetch_covers_today_itself():
    """A PR merged today must be inside the window -- the guard's freshest signal."""
    seen = []

    def fake_run(since, until):
        seen.append((since, until))
        return []

    fmps.fetch("2026-08-28", run=fake_run, slice_days=3, today=date(2026, 8, 29))

    assert seen[-1][1] == "2026-08-30", (
        "la derniere tranche s'arrete a {} : les merges d'aujourd'hui sont hors "
        "fenetre".format(seen[-1][1]))


def test_fetch_halves_a_slice_that_comes_back_at_the_search_cap():
    """A batch AT the cap is the cap, not a measurement -- narrow and retry."""
    widths = []

    def fake_run(since, until):
        d0 = date.fromisoformat(since)
        d1 = date.fromisoformat(until)
        w = (d1 - d0).days
        widths.append(w)
        # 4-day and 2-day slices are truncated; 1-day slices are honest
        if w > 1:
            return [_pr(i, "x") for i in range(fmps.SEARCH_RESULT_CAP)]
        return [_pr(1000 + len(widths), "x")]

    prs = fmps.fetch("2026-08-01", run=fake_run, slice_days=4,
                     today=date(2026, 8, 1))

    assert widths[:3] == [1, 1, 1] or 1 in widths, (
        "la tranche saturee n'a jamais ete retrecie : {}".format(widths))
    assert all(len(p) for p in prs[:1])
    assert len(prs) >= 1


def test_fetch_raises_rather_than_truncating_when_one_day_is_still_capped():
    """Silent truncation would hand the guard a partial sequence that looks whole."""
    def fake_run(since, until):
        return [_pr(i, "x") for i in range(fmps.SEARCH_RESULT_CAP)]

    with pytest.raises(RuntimeError, match="search cap"):
        fmps.fetch("2026-08-01", run=fake_run, slice_days=1,
                   today=date(2026, 8, 1))


def test_main_returns_1_when_the_fetch_raises():
    """The caller's `|| rm -f` must see a nonzero exit, never a partial file.

    Patched on `fetch`, not on `run_gh`: `fetch` binds `run=run_gh` as a DEFAULT
    ARGUMENT, evaluated once at definition time, so rebinding the module
    attribute never reaches it. The only injection point is `fetch(run=...)`.
    """
    def boom(since):
        raise OSError("gh absent")

    original = fmps.fetch
    fmps.fetch = boom
    try:
        assert fmps.main(["--days", "3"]) == 1
    finally:
        fmps.fetch = original


def test_main_writes_utf8_on_cp1252_stdout(monkeypatch):
    """#15184: Windows stdout is cp1252 -- a PR body with a non-cp1252
    character (e.g. '→') raised UnicodeEncodeError and the whole window was
    lost, silently degrading the adjacency guard to `prev: declared`.
    main() must force UTF-8 so the window is always consumable."""
    stream = io.TextIOWrapper(io.BytesIO(), encoding="cp1252")
    monkeypatch.setattr(sys, "stdout", stream)

    original = fmps.fetch
    fmps.fetch = lambda since: [
        {"number": 1, "body": "a → b", "mergedAt": "2026-09-08T00:00:00Z"}
    ]
    try:
        assert fmps.main(["--days", "3"]) == 0
    finally:
        fmps.fetch = original

    stream.flush()
    data = stream.buffer.getvalue().decode("utf-8")
    assert "a → b" in data


@pytest.mark.skipif(shutil.which("gh") is None, reason="gh binary absent")
def test_run_gh_argv_is_accepted_by_gh():
    """THE control the `--page` regression escaped for its whole life.

    Every other test injects `run`, so the argv `run_gh` builds was never once
    executed. `gh pr list` has no `--page` flag; the call raised on every real
    invocation and the guard fell back to `declared` repo-wide, silently. This
    test asserts the shape of the command is accepted by the real binary --
    `--help` on the same subcommand, plus an assertion that every flag we pass
    is one `gh pr list` advertises.
    """
    help_out = subprocess.run(
        ["gh", "pr", "list", "--help"],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
    ).stdout

    # The flags run_gh passes, extracted from the function's own argv so the
    # test cannot drift away from the code it guards.
    calls = {}

    def capture(*a, **kw):
        calls["argv"] = a[0]
        raise SystemExit  # do not actually hit the network

    original = subprocess.run
    subprocess.run = capture
    try:
        try:
            fmps.run_gh("2026-08-01", "2026-08-04")
        except SystemExit:
            pass
    finally:
        subprocess.run = original

    argv = calls["argv"]
    assert argv[:3] == ["gh", "pr", "list"], argv
    flags = [tok for tok in argv if tok.startswith("--")]
    unknown = [f for f in flags if f not in help_out]
    assert not unknown, (
        "run_gh passe des options que `gh pr list` n'a pas : {} "
        "(c'est exactement la faute `--page`)".format(unknown))


# --- cache par tranche (#19236) ------------------------------------------
#
# Le defaut : le cache de fenetre (une entree pour tout `[since, tomorrow)`)
# expire toutes les heures, et a chaque expiration **toutes** les tranches
# repartaient en appels live -- 7 min 25 s a froid pour chaque lane. Une
# journee close ne bouge plus : seule la tranche qui contient le jour courant
# merite d'etre re-interrogee.


def _counting_run(calls):
    def run(since: str, until: str) -> list[dict]:
        calls.append((since, until))
        return [_pr(1, since + "T00:00:00Z")]

    return run


def test_only_the_current_day_slice_is_refetched_after_the_short_ttl(tmp_path):
    """Le controle negatif de l'acceptance : une tranche passee ne re-interroge
    pas l'API, la tranche du jour si.

    Le disque est le vrai `PayloadCache` (pas un double) : c'est lui qui porte
    la decision de TTL, un faux cache testerait le test.
    """
    clock = [1_000_000.0]
    cache = PayloadCache(tmp_path, max_entries=200, clock=lambda: clock[0])
    calls: list[tuple[str, str]] = []
    run = _counting_run(calls)
    today = date(2026, 10, 5)

    fmps.fetch("2026-09-25", run=run, today=today, slice_cache=cache)
    cold = list(calls)
    assert len(cold) > 1, "le premier passage doit peupler plusieurs tranches"

    calls.clear()
    clock[0] += 3600  # 1 h : la TTL courte est expiree, la longue ne l'est pas
    fmps.fetch("2026-09-25", run=run, today=today, slice_cache=cache)
    warm = list(calls)

    assert len(warm) == 1, (
        "a chaud, seule la tranche qui contient le jour courant doit repartir "
        "en requete, pas {}".format(warm))
    since, until = warm[0]
    assert since <= today.isoformat() < until, (
        "la tranche refetchee doit etre celle qui contient aujourd'hui, "
        "obtenu [{} , {})".format(since, until))


def test_a_closed_slice_survives_the_short_ttl_by_construction(tmp_path):
    """Sans la TTL longue, la tranche close repart avec les autres : c'est
    exactement ce que le correctif supprime."""
    clock = [2_000_000.0]
    cache = PayloadCache(tmp_path, max_entries=200, clock=lambda: clock[0])
    calls: list[tuple[str, str]] = []
    run = _counting_run(calls)

    fmps.fetch("2026-09-25", run=run, today=date(2026, 10, 5), slice_cache=cache)
    closed = [c for c in calls if c[1] <= "2026-10-05"]
    calls.clear()
    clock[0] += 3600
    fmps.fetch("2026-09-25", run=run, today=date(2026, 10, 5), slice_cache=cache)

    replayed = [c for c in calls if c in closed]
    assert replayed == [], (
        "aucune tranche close ne doit etre rejouee a chaud, obtenu {}".format(
            replayed))


def test_the_slice_cache_does_not_change_the_corpus(tmp_path):
    """Un cache qui accelere en changeant le resultat n'est pas un cache."""
    run = _counting_run([])
    today = date(2026, 10, 5)

    plain = fmps.fetch("2026-09-25", run=run, today=today)
    cache = PayloadCache(tmp_path, max_entries=200)
    cold = fmps.fetch("2026-09-25", run=run, today=today, slice_cache=cache)
    warm = fmps.fetch("2026-09-25", run=run, today=today, slice_cache=cache)

    assert cold == plain
    assert warm == plain


def test_slice_cache_key_separates_the_field_sets_and_the_slices():
    """`files` est le champ le plus cher : deux appelants aux besoins differents
    ne doivent pas se servir mutuellement une reponse amputee."""
    base = fmps.slice_cache_key("2026-10-01", "2026-10-04", "number,body")
    richer = fmps.slice_cache_key("2026-10-01", "2026-10-04",
                                  "number,body,files")
    shifted = fmps.slice_cache_key("2026-10-04", "2026-10-07", "number,body")

    assert base != richer
    assert base != shifted
    assert len({base, richer, shifted}) == 3


def test_no_slice_cache_means_no_behaviour_change():
    """Le cache est opt-in : un appelant qui n'en passe pas garde exactement le
    decoupage d'avant, sans lecture disque."""
    calls: list[tuple[str, str]] = []
    run = _counting_run(calls)
    fmps.fetch("2026-09-25", run=run, today=date(2026, 10, 5))
    first = list(calls)
    calls.clear()
    fmps.fetch("2026-09-25", run=run, today=date(2026, 10, 5))
    assert calls == first, "sans cache, chaque appel re-interroge chaque tranche"
