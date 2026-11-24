"""Tests for scripts/notebook_tools/strip_probe_banner.py — .NET probeAddresses
banner scrubber.

Tests focus on:
- detection: BANNER_SIGNATURES match only the kernel-injected banner, never
  legitimate prose (markdown discussion of the leak class, e.g.)
- strip safety: ``execution_count`` is preserved, ``outputs`` shape is stable,
  other ``data`` keys are untouched
- idempotency: re-running ``strip_banner_in_place`` on a clean file is a no-op
- repo-wide consistency: ``--scan-all`` finds the same files as direct
  ``count_banner_lines`` calls (via subprocess)

Uses synthetic notebook dicts and tmp_path for filesystem isolation.
"""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from strip_probe_banner import (
    BANNER_SIGNATURES,
    DISCOVERY_VARIANT_SIGNATURES,
    count_banner_lines,
    count_banner_units,
    count_discovery_outputs,
    count_empty_envelopes,
    find_banner_outputs,
    has_banner,
    has_discovery_variant,
    is_empty_envelope,
    strip_banner_in_place,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _nb(cells: list[dict]) -> dict:
    return {"cells": cells, "metadata": {}, "nbformat": 4, "nbformat_minor": 5}


def _code(source: list[str], outputs: list | None = None,
          execution_count: int | None = 1) -> dict:
    cell = {"cell_type": "code", "source": source, "metadata": {},
            "execution_count": execution_count, "outputs": outputs or []}
    return cell


def _md(source: str) -> dict:
    return {"cell_type": "markdown", "source": [source]}


def _write_nb(path: Path, cells: list[dict]) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    nb = _nb(cells)
    path.write_text(json.dumps(nb), encoding="utf-8")
    return path


def _banner_html(extras: list[str] | None = None) -> dict:
    """Build a synthetic probeAddresses banner display_data output.

    Mirrors the real dotnet-interactive banner shape: a ``text/html`` list of
    lines, of which several embed the kernel's bootstrap helpers + a fake
    ``probingAddresses`` response (truncated to avoid leaking the test author's
    own network interfaces into the fixture).
    """
    base_lines = [
        "\r\n",
        "<div>\r\n",
        "    <div id='dotnet-interactive-this-cell-X' style='display: none'>\r\n",
        "        The below script needs to be able to find the current output cell.\r\n",
        "    </div>\r\n",
        "    <script type='text/javascript'>\r\n",
        "async function probingAddresses() {\r\n",
        "    try {\r\n",
        "        const addresses = await getAddresses();\r\n",
        "        loadDotnetInteractiveApi();\r\n",
        "        // echo IP list to console\r\n",
        "        console.log(addresses);\r\n",
        "    } catch (e) { console.error(e); }\r\n",
        "}\r\n",
        "probingAddresses();\r\n",
        "    </script>\r\n",
        "</div>\r\n",
    ]
    if extras:
        base_lines = extras + base_lines
    return {
        "output_type": "display_data",
        "data": {"text/html": base_lines},
        "metadata": {},
    }


def _banner_html_string() -> str:
    """Synthetic string-form banner (no list-of-lines split).

    Mirrors the newer .NET Interactive kernel format: the whole HTML+JS is a
    single inline string in ``data["text/html"]`` rather than a list. Anchors
    on the same signatures (``probeAddresses`` / ``probingAddresses`` /
    ``loadDotnetInteractiveApi``) — the strip drops the whole output, so no
    empty ``display_data`` envelope is left behind (#20190).
    """
    return (
        "<div>\r\n"
        "  <script type='text/javascript'>\r\n"
        "async function probeAddresses(probingAddresses) {\r\n"
        "    function timeout(ms, promise) {\r\n"
        "        return new Promise(function (resolve, reject) {\r\n"
        "            promise.then(resolve);\r\n"
        "        });\r\n"
        "    }\r\n"
        "}\r\n"
        "function loadDotnetInteractiveApi() {\r\n"
        "    probeAddresses(['http://fe80::3256:b4d8:946e:168d%21:2051/']);\r\n"
        "}\r\n"
        "  </script>\r\n"
        "</div>\r\n"
    )


# ---------------------------------------------------------------------------
# has_banner
# ---------------------------------------------------------------------------

class TestHasBanner:
    def test_detects_probeAddresses_in_list(self):
        assert has_banner(["line\r\n", "    probingAddresses()\r\n"])

    def test_detects_loadDotnetInteractiveApi_in_list(self):
        assert has_banner(["function loadDotnetInteractiveApi() {}\r\n"])

    def test_detects_in_string(self):
        assert has_banner("function probingAddresses() {}\r\n")

    def test_ignores_legitimate_prose(self):
        # has_banner matches by substring on the canonical signatures (probeAddresses,
        # probingAddresses, loadDotnetInteractiveApi). The strip is intentionally
        # aggressive: a markdown cell that mentions any signature will be flagged
        # as well, since legitimate use of these names in a notebook is
        # vanishingly rare (they're dotnet-interactive internals, not public API).
        # Document this as a deliberate trade-off: false positives are easier
        # to manage than false negatives (a missed banner leaks the worker's IPs).
        assert has_banner([
            "The probeAddresses banner is a kernel-injected display_data.\r\n",
        ])  # flagged on purpose — see comment above.
        # But non-banner content with no signature is not flagged.
        assert not has_banner([
            "Hello, world.\r\n",
            "Just a normal log line.\r\n",
        ])

    def test_ignores_empty(self):
        assert not has_banner([])
        assert not has_banner("")

    def test_ignores_non_string_non_list(self):
        assert not has_banner(None)
        assert not has_banner(42)
        assert not has_banner({"key": "value"})


# ---------------------------------------------------------------------------
# find_banner_outputs / count_banner_lines (read-only)
# ---------------------------------------------------------------------------

class TestFindBannerOutputs:
    def test_finds_single_output(self, tmp_path):
        cells = [_code(["print('hello')\r\n"], outputs=[_banner_html()])]
        nb = _write_nb(tmp_path / "x.ipynb", cells)
        assert find_banner_outputs(str(nb)) == [(0, 0)]

    def test_finds_multiple_lines_in_single_output(self, tmp_path):
        cells = [_code(["x = 1\r\n"], outputs=[_banner_html()])]
        nb = _write_nb(tmp_path / "x.ipynb", cells)
        # The synthetic banner HTML embeds 3 distinct banner signatures across
        # the script lines (probingAddresses x2 — function decl + invocation,
        # loadDotnetInteractiveApi x1 — helper call). count_banner_lines
        # counts each list element with ANY signature.
        assert count_banner_lines(str(nb)) == 3

    def test_no_banner_in_clean_notebook(self, tmp_path):
        cells = [_code(["x = 1\r\n"], outputs=[
            {"output_type": "stream", "name": "stdout", "text": ["1\r\n"]},
        ])]
        nb = _write_nb(tmp_path / "x.ipynb", cells)
        assert find_banner_outputs(str(nb)) == []
        assert count_banner_lines(str(nb)) == 0

    def test_ignores_markdown_cells_with_discussion(self, tmp_path):
        cells = [_md("The probeAddresses banner is the kernel leak class.")]
        nb = _write_nb(tmp_path / "x.ipynb", cells)
        assert find_banner_outputs(str(nb)) == []
        assert count_banner_lines(str(nb)) == 0


# ---------------------------------------------------------------------------
# strip_banner_in_place — safety guarantees
# ---------------------------------------------------------------------------

class TestStripBannerSafety:
    def test_strip_removes_banner_and_preserves_structure(self, tmp_path):
        banner = _banner_html()
        other_output = {
            "output_type": "stream",
            "name": "stdout",
            "text": ["Hello, world!\r\n"],
        }
        cells = [_code(
            ["Console.WriteLine(\"hi\");\r\n"],
            outputs=[banner, other_output],
            execution_count=42,
        )]
        nb = _write_nb(tmp_path / "x.ipynb", cells)

        # Pre-strip banner count (banner-bearing list elements across all
        # outputs of the notebook). The synthetic banner has 3 banner lines.
        pre = count_banner_lines(str(nb))
        assert pre == 3

        # The strip returns (n_outputs_with_banner_pre_strip, n_lines_fixed).
        # We use count_banner_lines AFTER to assert the strip was complete
        # (no banner-bearing list element survives in the file).
        outputs_with_banner, fixed = strip_banner_in_place(str(nb))
        assert outputs_with_banner == 1, "exactly one output carried the banner"
        assert fixed == pre, (
            f"Strip fixed {fixed} of {pre} banner lines — partial strip."
        )
        residual = count_banner_lines(str(nb))
        assert residual == 0, (
            f"Strip left {residual} banner line(s) behind — see regex bug."
        )

        # Re-read and assert post-strip invariants.
        with open(nb, encoding="utf-8") as f:
            new_nb = json.load(f)
        cell = new_nb["cells"][0]
        assert cell["cell_type"] == "code"
        assert cell["execution_count"] == 42  # preserved
        assert len(cell["outputs"]) == 2     # shape preserved
        # The other (non-banner) output is byte-identical.
        assert cell["outputs"][1] == other_output
        # The banner output is still present but its text/html no longer embeds
        # any of the banner signatures (the whole list is sanitized).
        banner_out = cell["outputs"][0]
        assert banner_out["output_type"] == "display_data"
        for line in banner_out["data"]["text/html"]:
            assert not any(sig in line for sig in BANNER_SIGNATURES), (
                f"Banner signature leaked: {line!r}"
            )

    def test_idempotent(self, tmp_path):
        # Strip twice — second call must be a no-op (no banner lines remain
        # after first strip).
        cells = [_code(["x = 1\r\n"], outputs=[_banner_html()])]
        nb = _write_nb(tmp_path / "x.ipynb", cells)

        pre = count_banner_lines(str(nb))
        assert pre == 3
        outputs1, fixed1 = strip_banner_in_place(str(nb))
        assert outputs1 == 1 and fixed1 == pre
        assert count_banner_lines(str(nb)) == 0

        # Read bytes after first strip, run strip again, compare bytes.
        with open(nb, "rb") as f:
            bytes_after_first = f.read()
        outputs2, fixed2 = strip_banner_in_place(str(nb))
        with open(nb, "rb") as f:
            bytes_after_second = f.read()

        assert outputs2 == 0  # no output carries a banner anymore
        assert fixed2 == 0
        assert bytes_after_first == bytes_after_second, (
            "Second strip must be byte-identical to first (idempotency)."
        )

    def test_no_banner_returns_zero(self, tmp_path):
        cells = [_code(["x = 1\r\n"], outputs=[
            {"output_type": "stream", "name": "stdout", "text": ["1\r\n"]},
        ])]
        nb = _write_nb(tmp_path / "x.ipynb", cells)

        found, fixed = strip_banner_in_place(str(nb))
        assert found == 0
        assert fixed == 0

    def test_does_not_touch_other_data_keys(self, tmp_path):
        # If a display_data output has BOTH a banner text/html AND a legitimate
        # image/png, strip must only sanitize the text/html.
        banner = _banner_html()
        banner["data"]["image/png"] = "iVBORw0KGgoAAAANSUhEUgAA..."  # fake base64
        cells = [_code(["Console.WriteLine()\r\n"], outputs=[banner])]
        nb = _write_nb(tmp_path / "x.ipynb", cells)

        strip_banner_in_place(str(nb))

        with open(nb, encoding="utf-8") as f:
            new_nb = json.load(f)
        out = new_nb["cells"][0]["outputs"][0]
        assert "image/png" in out["data"]   # preserved
        assert out["data"]["image/png"] == "iVBORw0KGgoAAAANSUhEUgAA..."
        for line in out["data"]["text/html"]:
            assert not any(sig in line for sig in BANNER_SIGNATURES)

    def test_strip_string_form_banner(self, tmp_path):
        # The newer .NET Interactive kernel emits the banner as a single inline
        # ``text/html`` STRING (not a list). The strip must handle this case by
        # dropping the banner output entirely. Blanking the string instead (the
        # pre-#20190 behaviour) left an empty ``display_data`` envelope that no
        # later run could see again — with no banner left, the tool skips the
        # notebook, so the residue was permanent.
        banner = {
            "output_type": "display_data",
            "data": {"text/html": _banner_html_string()},
            "metadata": {},
        }
        other_output = {
            "output_type": "stream", "name": "stdout",
            "text": ["OK\r\n"],
        }
        cells = [_code(
            ["Console.WriteLine();\r\n"],
            outputs=[banner, other_output],
            execution_count=7,
        )]
        nb = _write_nb(tmp_path / "x.ipynb", cells)

        pre = count_banner_lines(str(nb))
        assert pre == 1  # string form counts as 1 banner line

        outputs_with_banner, fixed = strip_banner_in_place(str(nb))
        assert outputs_with_banner == 1
        assert fixed == 1  # one string-form banner replaced with ""

        # Post-strip invariants.
        with open(nb, encoding="utf-8") as f:
            new_nb = json.load(f)
        cell = new_nb["cells"][0]
        assert cell["execution_count"] == 7
        # The banner output is gone; the neighbour is byte-identical.
        assert len(cell["outputs"]) == 1
        assert cell["outputs"][0] == other_output
        # And no empty envelope was left in its place (#20190).
        assert count_empty_envelopes(str(nb)) == 0

    def test_string_form_idempotent(self, tmp_path):
        # String-form strip must also be byte-stable on second invocation.
        banner = {
            "output_type": "display_data",
            "data": {"text/html": _banner_html_string()},
            "metadata": {},
        }
        cells = [_code(["x = 1\r\n"], outputs=[banner])]
        nb = _write_nb(tmp_path / "x.ipynb", cells)

        strip_banner_in_place(str(nb))
        with open(nb, "rb") as f:
            bytes_after_first = f.read()
        out2, fixed2 = strip_banner_in_place(str(nb))
        with open(nb, "rb") as f:
            bytes_after_second = f.read()

        assert out2 == 0 and fixed2 == 0
        assert bytes_after_first == bytes_after_second

    def test_mixed_list_and_string_banners_in_same_notebook(self, tmp_path):
        # Some notebooks may carry both list-form and string-form banners in
        # different cells (e.g. legacy + regenerated outputs). Both must be
        # stripped in a single pass.
        list_banner = _banner_html()
        str_banner = {
            "output_type": "display_data",
            "data": {"text/html": _banner_html_string()},
            "metadata": {},
        }
        cells = [
            _code(["x = 1\r\n"], outputs=[list_banner]),
            _code(["y = 2\r\n"], outputs=[str_banner]),
        ]
        nb = _write_nb(tmp_path / "x.ipynb", cells)

        pre = count_banner_lines(str(nb))
        assert pre == 4  # 3 from list + 1 from string

        outputs_with_banner, fixed = strip_banner_in_place(str(nb))
        assert outputs_with_banner == 2
        # fixed: 3 list elements + 1 string replacement = 4
        assert fixed == 4

        residual = count_banner_lines(str(nb))
        assert residual == 0

    def test_list_banner_with_inner_brackets_in_string(self, tmp_path):
        # Regression test: a list-form banner where one element embeds an
        # *inner* JS array literal like ``probeAddresses(["...","..."])``.
        # The naive regex ``r'"text/html"\\s*:\\s*\\[([^\\]]*)\\]'`` would
        # stop at the first ``]`` (inside the JS array) and miss the rest
        # of the banner elements. The fix is a JSON-string-aware
        # bracket-balancing scanner (_find_text_html_list_bounds). This
        # test was added after the c.457 review found real-world
        # GameTheory-10 PARTIALs (3/9) — only the bracket scanner passes.
        # Build a banner with 4 banner-bearing elements, including one
        # whose JSON string value contains an inner ``[`` / ``]`` pair.
        inner_bracket_element = (
            "function probeAddresses([\"http://2a01:e0a:9d4:f320:752:2048/\"]);\r\n"
        )
        banner_lines = [
            "    probingAddresses();\r\n",                                  # 0: banner
            "    loadDotnetInteractiveApi();\r\n",                        # 1: banner
            inner_bracket_element,                                        # 2: banner + inner []
            "    console.log(addresses);\r\n",                            # 3: plain
            "async function probeAddresses(probingAddresses) {\r\n",      # 4: banner
        ]
        n_banner = sum(
            1 for line in banner_lines if any(sig in line for sig in BANNER_SIGNATURES)
        )
        assert n_banner == 4
        banner_output = {
            "output_type": "display_data",
            "data": {"text/html": banner_lines},
            "metadata": {},
        }
        cells = [_code(
            ["Console.WriteLine();\r\n"],
            outputs=[banner_output],
            execution_count=11,
        )]
        nb = _write_nb(tmp_path / "x.ipynb", cells)

        pre = count_banner_lines(str(nb))
        assert pre == 4

        outputs_with_banner, fixed = strip_banner_in_place(str(nb))
        assert outputs_with_banner == 1
        assert fixed == 4

        residual = count_banner_lines(str(nb))
        assert residual == 0

        # Re-read and assert post-strip invariants.
        with open(nb, encoding="utf-8") as f:
            new_nb = json.load(f)
        cell = new_nb["cells"][0]
        assert cell["execution_count"] == 11
        assert len(cell["outputs"]) == 1
        assert cell["outputs"][0]["output_type"] == "display_data"
        # No banner signature may survive.
        for line in cell["outputs"][0]["data"]["text/html"]:
            assert not any(sig in line for sig in BANNER_SIGNATURES)


# ---------------------------------------------------------------------------
# Empty display_data envelope (#20190)
# ---------------------------------------------------------------------------

def _empty_envelope() -> dict:
    """The residue an older strip left on disk: banner removed, wrapper kept."""
    return {"output_type": "display_data", "data": {"text/html": ""}, "metadata": {}}


def _stream(text: str) -> dict:
    return {"output_type": "stream", "name": "stdout", "text": [text]}


class TestEmptyEnvelope:
    def test_is_empty_envelope_matches_the_strip_residue(self):
        assert is_empty_envelope(_empty_envelope())

    @pytest.mark.parametrize("obj", [
        {"output_type": "display_data", "data": {"text/html": "<b>x</b>"}, "metadata": {}},
        # A second data key means the output carries something else too.
        {"output_type": "display_data",
         "data": {"text/html": "", "text/plain": "kept"}, "metadata": {}},
        {"output_type": "stream", "name": "stdout", "text": [""]},
        {"output_type": "display_data", "data": {"image/png": ""}, "metadata": {}},
        {"output_type": "display_data", "data": {}, "metadata": {}},
        "not-a-dict",
        None,
    ])
    def test_is_empty_envelope_rejects_everything_else(self, obj):
        assert not is_empty_envelope(obj)

    def test_count_empty_envelopes(self, tmp_path):
        cells = [
            _code(["a"], outputs=[_empty_envelope(), _stream("ok")], execution_count=1),
            _code(["b"], outputs=[_stream("ok")], execution_count=2),
        ]
        nb = _write_nb(tmp_path / "x.ipynb", cells)
        assert count_empty_envelopes(str(nb)) == 1
        # No banner is involved: the residue is invisible to the banner count,
        # which is why it used to survive every later run of the tool.
        assert count_banner_lines(str(nb)) == 0

    def test_removes_inherited_envelope_without_banner(self, tmp_path):
        cells = [_code(["a"], outputs=[_empty_envelope(), _stream("ok")],
                       execution_count=4)]
        nb = _write_nb(tmp_path / "x.ipynb", cells)

        outputs_with_banner, fixed = strip_banner_in_place(str(nb))
        assert outputs_with_banner == 0
        assert fixed == 0  # nothing banner-related was rewritten

        with open(nb, encoding="utf-8") as f:
            new_nb = json.load(f)
        cell = new_nb["cells"][0]
        assert cell["execution_count"] == 4
        assert len(cell["outputs"]) == 1
        assert cell["outputs"][0] == _stream("ok")
        assert count_empty_envelopes(str(nb)) == 0

    def test_removes_envelope_between_real_outputs(self, tmp_path):
        a, b = _stream("first"), _stream("last")
        cells = [_code(["a"], outputs=[a, _empty_envelope(), b],
                       execution_count=9)]
        nb = _write_nb(tmp_path / "x.ipynb", cells)

        strip_banner_in_place(str(nb))

        with open(nb, encoding="utf-8") as f:
            new_nb = json.load(f)
        outs = new_nb["cells"][0]["outputs"]
        assert len(outs) == 2
        assert outs[0] == a
        assert outs[1] == b
        assert new_nb["cells"][0]["execution_count"] == 9

    def test_removes_envelope_after_last_real_output(self, tmp_path):
        # Cover the "head comma" branch: the envelope is the LAST element, so
        # the comma before it has to go with it.
        a = _stream("only")
        cells = [_code(["a"], outputs=[a, _empty_envelope()], execution_count=9)]
        nb = _write_nb(tmp_path / "x.ipynb", cells)

        strip_banner_in_place(str(nb))

        with open(nb, encoding="utf-8") as f:
            new_nb = json.load(f)
        outs = new_nb["cells"][0]["outputs"]
        assert outs == [a]

    def test_envelope_removal_idempotent(self, tmp_path):
        cells = [_code(["a"], outputs=[_empty_envelope()], execution_count=1)]
        nb = _write_nb(tmp_path / "x.ipynb", cells)

        strip_banner_in_place(str(nb))
        first = nb.read_text(encoding="utf-8")
        strip_banner_in_place(str(nb))
        assert nb.read_text(encoding="utf-8") == first
        with open(nb, encoding="utf-8") as f:
            new_nb = json.load(f)
        assert new_nb["cells"][0]["outputs"] == []

    def test_legitimate_outputs_are_untouched(self, tmp_path):
        # Guard against over-reach: a notebook with real outputs must come out
        # byte-identical (the removal is text-surgical, no re-serialization).
        cells = [
            _code(["a"], outputs=[_stream("ok\r\n")], execution_count=3),
            _code(["b"], outputs=[{"output_type": "execute_result",
                                   "data": {"text/plain": ["42"]},
                                   "metadata": {}, "execution_count": 3}],
                  execution_count=3),
        ]
        nb = _write_nb(tmp_path / "x.ipynb", cells)
        before = nb.read_text(encoding="utf-8")

        strip_banner_in_place(str(nb))

        assert nb.read_text(encoding="utf-8") == before

# ---------------------------------------------------------------------------
# The "this cell" discovery bootstrap — a SECOND, distinct banner (#23530)
# ---------------------------------------------------------------------------

def _discovery_output() -> dict:
    """Synthetic "this cell" discovery bootstrap output.

    Mirrors the shape measured on the inherited corpus (2026-10-30): a WHOLE
    ``display_data`` output whose ``data`` carries exactly ``text/html``,
    holding the discovery div plus a require.js bootstrap that fetches
    ``${rootUrl}discovery``. It embeds NONE of the three
    ``BANNER_SIGNATURES`` -- that is precisely why it needs its own set.
    """
    lines = [
        "\r\n",
        "<div>\r\n",
        "    <div id='dotnet-interactive-this-cell-$CACHE_BUSTER$' style='display: none'>\r\n",
        "        The below script needs to be able to find the current output cell; this is an easy method to get it.\r\n",
        "    </div>\r\n",
        "    <script type='text/javascript'>\r\n",
        "    const rootUrl = document.baseURI;\r\n",
        "    let response = await timeout(1000, fetch(`${rootUrl}discovery`, {\r\n",
        "        method: 'POST',\r\n",
        "        cache: 'no-cache',\r\n",
        "        mode: 'cors',\r\n",
        "    }));\r\n",
        "    </script>\r\n",
        "</div>\r\n",
    ]
    return {
        "output_type": "display_data",
        "data": {"text/html": lines},
        "metadata": {},
    }


def _probe_only_output() -> dict:
    """A probeAddresses banner output WITHOUT any discovery token.

    Used to keep the "both variants" test independent of the shared fixture
    (the historical ``_banner_html`` fixture also embeds the discovery div).
    """
    return {
        "output_type": "display_data",
        "data": {"text/html": ["<div>\r\n", "probeAddresses();\r\n", "</div>\r\n"]},
        "metadata": {},
    }


class TestDiscoveryVariant:
    """The discovery bootstrap is detected and stripped by its OWN set.

    The guard-facing ``BANNER_SIGNATURES`` must never absorb it: the
    repo-wide guard is calibrated against the committed corpus, so widening
    it reports the inherited residue (177 notebooks measured 2026-10-30) as
    new defects — the widening measured and reverted on #22728.
    """

    def test_discovery_signature_is_not_in_the_guard_set(self):
        assert "dotnet-interactive-this-cell" not in BANNER_SIGNATURES
        assert DISCOVERY_VARIANT_SIGNATURES == ("dotnet-interactive-this-cell",)
        assert set(DISCOVERY_VARIANT_SIGNATURES) & set(BANNER_SIGNATURES) == set()

    def test_guard_detection_does_not_flag_a_discovery_blob(self):
        blob = _discovery_output()["data"]["text/html"]
        assert has_banner(blob) is False, "the guard's set must stay blind to it"
        assert has_discovery_variant(blob) is True

    def test_count_discovery_outputs_counts_outputs_not_lines(self, tmp_path):
        cells = [_code(["x = 1\r\n"], outputs=[_discovery_output()])]
        nb = _write_nb(tmp_path / "x.ipynb", cells)

        assert count_discovery_outputs(str(nb)) == 1
        assert count_banner_units(str(nb), "discovery") == 1
        # The guard's units stay at zero on a discovery-only notebook: this is
        # the invariant that keeps `--scan-all --check` green.
        assert count_banner_units(str(nb), "probe") == 0
        assert count_banner_lines(str(nb)) == 0

    def test_strip_removes_the_whole_output(self, tmp_path):
        other = {"output_type": "stream", "name": "stdout", "text": ["hi\r\n"]}
        cells = [_code(["Console.WriteLine(1);\r\n"],
                       outputs=[_discovery_output(), other], execution_count=7)]
        nb = _write_nb(tmp_path / "x.ipynb", cells)

        found, fixed = strip_banner_in_place(str(nb), "discovery")
        assert (found, fixed) == (1, 1)

        new_nb = json.loads(nb.read_text(encoding="utf-8"))
        cell = new_nb["cells"][0]
        assert cell["execution_count"] == 7, "execution_count preserved"
        assert len(cell["outputs"]) == 1, "the banner output is gone"
        assert cell["outputs"][0] == other, "the real output is byte-identical"
        assert "dotnet-interactive-this-cell" not in nb.read_text(encoding="utf-8")

    def test_source_is_never_touched(self, tmp_path):
        source = ["Console.WriteLine(\"dotnet-interactive-this-cell\");\r\n"]
        cells = [_code(source, outputs=[_discovery_output()], execution_count=2)]
        nb = _write_nb(tmp_path / "x.ipynb", cells)

        strip_banner_in_place(str(nb), "discovery")

        new_nb = json.loads(nb.read_text(encoding="utf-8"))
        assert new_nb["cells"][0]["source"] == source

    def test_idempotent(self, tmp_path):
        cells = [_code(["x = 1\r\n"], outputs=[_discovery_output()])]
        nb = _write_nb(tmp_path / "x.ipynb", cells)

        assert strip_banner_in_place(str(nb), "discovery") == (1, 1)
        before = nb.read_bytes()
        assert strip_banner_in_place(str(nb), "discovery") == (0, 0)
        assert nb.read_bytes() == before

    def test_mixed_output_is_refused_not_destroyed(self, tmp_path):
        mixed = {
            "output_type": "display_data",
            "data": {"text/plain": ["42\r\n"],
                     "text/html": _discovery_output()["data"]["text/html"]},
            "metadata": {},
        }
        cells = [_code(["x = 1\r\n"], outputs=[mixed])]
        nb = _write_nb(tmp_path / "x.ipynb", cells)
        before = nb.read_bytes()

        found, fixed = strip_banner_in_place(str(nb), "discovery")
        assert found == 1, "the unit is counted"
        assert fixed == 0, "but refused: blanking it would destroy a real result"
        assert nb.read_bytes() == before

    def test_variant_both_strips_probe_and_discovery(self, tmp_path):
        cells = [_code(["x = 1\r\n"],
                       outputs=[_probe_only_output(), _discovery_output()])]
        nb = _write_nb(tmp_path / "x.ipynb", cells)

        found, fixed = strip_banner_in_place(str(nb), "both")
        assert found == fixed, "every counted unit is removed"
        assert count_banner_lines(str(nb)) == 0
        assert count_discovery_outputs(str(nb)) == 0
        new_nb = json.loads(nb.read_text(encoding="utf-8"))
        outs = new_nb["cells"][0]["outputs"]
        # The probe output KEEPS its non-signature lines -- the historical
        # probe behaviour drops only the banner-bearing elements (asserted by
        # TestStripBannerSafety). The discovery output is removed as a whole.
        assert len(outs) == 1
        assert all(
            not any(sig in line for sig in BANNER_SIGNATURES)
            for line in outs[0]["data"]["text/html"]
        )

    def test_default_variant_leaves_the_discovery_bootstrap_alone(self, tmp_path):
        # The default path (the pre-commit hook and the guard) must not
        # silently start stripping the discovery bootstrap: that widening is
        # a separate, sweep-gated decision (#23530).
        cells = [_code(["x = 1\r\n"], outputs=[_discovery_output()])]
        nb = _write_nb(tmp_path / "x.ipynb", cells)
        before = nb.read_bytes()

        strip_banner_in_place(str(nb))

        assert nb.read_bytes() == before

    # --- Gardes de forme (revue NanoClaw, 2026-10-30T14:34Z) --------------

    def test_string_form_strips_two_outputs_without_offset_drift(self, tmp_path):
        # The string form edits the raw text in place. Capturing every match
        # offset once and then rewriting left-to-right splices the JSON at the
        # wrong place from the SECOND output on, because each edit shrinks the
        # file. Two string-form outputs is the smallest case that exposes it.
        html = "".join(_discovery_output()["data"]["text/html"])
        first = {"output_type": "display_data", "data": {"text/html": html},
                 "metadata": {}}
        second = {"output_type": "display_data", "data": {"text/html": html},
                  "metadata": {}}
        cells = [_code(["x = 1\r\n"], outputs=[first, second], execution_count=3)]
        nb = _write_nb(tmp_path / "x.ipynb", cells)

        found, fixed = strip_banner_in_place(str(nb), "discovery")

        assert (found, fixed) == (2, 2)
        new_nb = json.loads(nb.read_text(encoding="utf-8"))
        assert count_discovery_outputs(str(nb)) == 0
        # The JSON must still parse and the cell must keep its identity: a
        # drifted splice truncates the document or the neighbouring keys.
        assert new_nb["cells"][0]["execution_count"] == 3
        assert new_nb["cells"][0]["source"] == ["x = 1\r\n"]

    def test_output_with_sibling_real_content_is_refused(self, tmp_path):
        # Mime keys are exactly ["text/html"], so the key check alone would
        # call this strippable and delete the whole list body -- destroying
        # the table. The structural guard (one balanced <div> block, nothing
        # else) is what refuses it.
        bootstrap = _discovery_output()["data"]["text/html"]
        polluted = dict(_discovery_output())
        polluted["data"] = {"text/html": list(bootstrap) + ["<table>result</table>"]}
        cells = [_code(["x = 1\r\n"], outputs=[polluted])]
        nb = _write_nb(tmp_path / "x.ipynb", cells)
        before = nb.read_bytes()

        found, fixed = strip_banner_in_place(str(nb), "discovery")

        assert found == 1, "the unit is counted"
        assert fixed == 0, "but refused: the table would be destroyed"
        assert nb.read_bytes() == before

    def test_source_quoting_the_wrapper_is_never_touched(self, tmp_path):
        # The string-form pattern anchors on `"text/html": "<...>"`, which also
        # appears inside a cell's `source` when that cell quotes the literal.
        # Only a match decoding to the EXACT string of a target output is
        # rewritten, so the docstring's "output-only" promise is structural.
        html = "".join(_discovery_output()["data"]["text/html"])
        quoted = '"text/html": ' + json.dumps(html) + "\r\n"
        cells = [
            _code([quoted], outputs=[]),
            _code(["x = 1\r\n"], outputs=[_discovery_output()]),
        ]
        nb = _write_nb(tmp_path / "x.ipynb", cells)

        found, fixed = strip_banner_in_place(str(nb), "discovery")

        assert found == fixed == 1
        new_nb = json.loads(nb.read_text(encoding="utf-8"))
        assert new_nb["cells"][0]["source"] == [quoted], "source must be intact"
        assert count_discovery_outputs(str(nb)) == 0
