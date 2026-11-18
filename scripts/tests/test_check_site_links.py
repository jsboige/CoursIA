"""Tests du garde post-deploiement des liens du site publie (#21628)."""

from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

SCRIPT = Path(__file__).resolve().parents[1] / "ci" / "check_site_links.py"

BASE = "https://example.test/CoursIA"


def _load():
    sys.path.insert(0, str(SCRIPT.parent))
    import check_site_links as mod  # noqa: WPS433
    return mod


def test_extract_internal_hrefs_resolves_and_filters() -> None:
    """Relative hrefs resolve against the page; external/anchor/mailto dropped."""
    mod = _load()
    html = """
    <a href="GenAI/README.html">serie</a>
    <a href="../parcours.html#top">parcours</a>
    <a href="#section">ancre pure</a>
    <a href="mailto:x@y.z">mail</a>
    <a href="javascript:void(0)">js</a>
    <a href="https://github.com/jsboige/CoursIA">externe</a>
    <a href="GenAI/README.html">doublon</a>
    """
    page = BASE + "/MyIA.AI.Notebooks/index.html"
    out = mod.extract_internal_hrefs(html, page)
    assert out == sorted({
        BASE + "/MyIA.AI.Notebooks/GenAI/README.html",
        BASE + "/parcours.html",
    })


def test_extract_keeps_query_out_and_strips_fragment() -> None:
    """Fragments and query strings are dropped: the resource is what is probed."""
    mod = _load()
    html = '<a href="page.html?a=1#frag">x</a>'
    page = BASE + "/"
    out = mod.extract_internal_hrefs(html, page)
    assert out == [BASE + "/page.html"]


def test_run_check_ok_when_all_links_200(monkeypatch) -> None:
    """Healthy site: every extracted link returns 2xx -> no broken entry."""
    mod = _load()
    monkeypatch.setattr(mod, "fetch_text",
                        lambda url, timeout=None: '<a href="/a.html">a</a>'
                                                  '<a href="/b.html">b</a>')
    monkeypatch.setattr(mod, "probe_status", lambda url, timeout=None: 200)
    result = mod.run_check(BASE, ("/",))
    assert result.instrument_errors == []
    assert result.broken == []
    assert result.checked == 2
    assert result.ok == 2


def test_run_check_reports_broken_404(monkeypatch) -> None:
    """Negative control: one 404 link is reported and fails the pass."""
    mod = _load()
    monkeypatch.setattr(mod, "fetch_text",
                        lambda url, timeout=None: '<a href="good.html">g</a>'
                                                  '<a href="gone.html">g</a>')
    monkeypatch.setattr(mod, "probe_status",
                        lambda url, timeout=None: 404 if url.endswith("gone.html") else 200)
    result = mod.run_check(BASE, ("/",))
    assert result.instrument_errors == []
    assert result.checked == 2
    assert result.ok == 1
    assert result.broken == [{
        "url": BASE + "/gone.html",
        "status": 404,
        "source_pages": [BASE + "/"],
    }]


def test_run_check_keeps_every_source_and_probes_target_once(monkeypatch) -> None:
    """Two referrers of one broken target survive URL deduplication."""
    mod = _load()
    pages = {
        BASE + "/": '<a href="gone.html">g</a>',
        BASE + "/parcours.html": '<a href="gone.html">g</a>',
    }
    probed = []
    monkeypatch.setattr(mod, "fetch_text", lambda url, timeout=None: pages[url])
    monkeypatch.setattr(mod, "probe_status",
                        lambda url, timeout=None: probed.append(url) or 404)
    result = mod.run_check(BASE, ("/", "/parcours.html"))
    assert result.broken == [{
        "url": BASE + "/gone.html",
        "status": 404,
        "source_pages": [BASE + "/", BASE + "/parcours.html"],
    }]
    assert probed == [BASE + "/gone.html"]


def test_main_names_sources_in_text_and_json(monkeypatch, capsys) -> None:
    """Both operator-facing reports carry the same source attribution."""
    mod = _load()
    monkeypatch.setattr(mod, "fetch_text",
                        lambda url, timeout=None: '<a href="gone.html">g</a>')
    monkeypatch.setattr(mod, "probe_status", lambda url, timeout=None: 404)
    argv = ["--base-url", BASE, "--page", "/", "--page", "/parcours.html"]

    assert mod.main(argv) == 1
    text = capsys.readouterr().out
    assert f"(source: {BASE}/, {BASE}/parcours.html)" in text

    assert mod.main([*argv, "--json"]) == 1
    report = json.loads(capsys.readouterr().out)
    assert report["broken"][0]["source_pages"] == [
        BASE + "/", BASE + "/parcours.html",
    ]


def test_run_check_instrument_error_when_critical_page_unreachable(monkeypatch) -> None:
    """A critical page that cannot be fetched is an instrument failure, never rc 1."""
    import urllib.error

    mod = _load()

    def boom(url, timeout=None):
        raise urllib.error.URLError("connection refused")

    monkeypatch.setattr(mod, "fetch_text", boom)
    result = mod.run_check(BASE, ("/",))
    assert len(result.instrument_errors) == 1
    assert result.checked == 0


def test_run_check_instrument_error_when_probe_network_fails(monkeypatch) -> None:
    """A network error mid-probe is an instrument failure, never a broken link."""
    import urllib.error

    mod = _load()
    monkeypatch.setattr(mod, "fetch_text",
                        lambda url, timeout=None: '<a href="a.html">a</a>')

    def boom(url, timeout=None):
        raise urllib.error.URLError("timed out")

    monkeypatch.setattr(mod, "probe_status", boom)
    result = mod.run_check(BASE, ("/",))
    assert len(result.instrument_errors) == 1
    assert "probe failed" in result.instrument_errors[0]
    assert result.checked == 0
    assert result.broken == []


def test_run_check_signals_truncation_beyond_max_links(monkeypatch) -> None:
    """Beyond max_links the verdict is incomplete: signalled, not silent."""
    mod = _load()
    monkeypatch.setattr(mod, "fetch_text",
                        lambda url, timeout=None: '<a href="a.html">a</a>'
                                                  '<a href="b.html">b</a>')
    monkeypatch.setattr(mod, "probe_status", lambda url, timeout=None: 200)
    result = mod.run_check(BASE, ("/",), max_links=1)
    assert any(err.startswith("truncated:") for err in result.instrument_errors)
    assert result.checked == 1
    assert result.broken == []


def test_main_exit_codes(monkeypatch) -> None:
    """main() maps the three states to 0 / 1 / 2."""
    mod = _load()
    monkeypatch.setattr(mod, "fetch_text",
                        lambda url, timeout=None: '<a href="x.html">x</a>')
    monkeypatch.setattr(mod, "probe_status", lambda url, timeout=None: 200)
    assert mod.main(["--base-url", BASE]) == 0

    monkeypatch.setattr(mod, "probe_status", lambda url, timeout=None: 404)
    assert mod.main(["--base-url", BASE]) == 1

    import urllib.error

    def boom(url, timeout=None):
        raise urllib.error.URLError("down")

    monkeypatch.setattr(mod, "fetch_text", boom)
    assert mod.main(["--base-url", BASE]) == 2


def test_raw_ipynb_detected_without_http_probe(monkeypatch) -> None:
    """Positive control (#25055): an internal .ipynb href fails the pass
    even when the probe would return 200 (the JSON-source case)."""
    mod = _load()
    html = ('<a href="MyIA.AI.Notebooks/SymbolicAI/SymbolicLearning/'
            'SL-11-Capstone-NeuroSymbolic.ipynb">capstone</a>'
            '<a href="ok.html">ok</a>')
    monkeypatch.setattr(mod, "fetch_text", lambda url, timeout=None: html)
    # Surtout : la sonde repond 200 PARTOUT -- le defaut est structurel,
    # pas de statut.
    monkeypatch.setattr(mod, "probe_status", lambda url, timeout=None: 200)
    result = mod.run_check(BASE, ("/",))
    assert result.broken == []
    assert result.raw_ipynb == [{
        "href": "MyIA.AI.Notebooks/SymbolicAI/SymbolicLearning/"
                "SL-11-Capstone-NeuroSymbolic.ipynb",
        "source_page": BASE + "/",
    }]
    assert mod.main(["--base-url", BASE, "--page", "/"]) == 1


def test_raw_ipynb_dedup_and_external_ignored(monkeypatch) -> None:
    """Duplicate hrefs collapse to one entry; external .ipynb links ignored."""
    mod = _load()
    href = "Notebooks/Dup.ipynb"
    html = (f'<a href="{href}">a</a><a href="{href}">b</a>'
            '<a href="https://else.where/x.ipynb">ext</a>')
    monkeypatch.setattr(mod, "fetch_text", lambda url, timeout=None: html)
    monkeypatch.setattr(mod, "probe_status", lambda url, timeout=None: 200)
    result = mod.run_check(BASE, ("/",))
    assert len(result.raw_ipynb) == 1
    assert result.raw_ipynb[0]["href"] == href


def test_raw_ipynb_names_page_in_text_report(monkeypatch, capsys) -> None:
    """The text report names the href and its source page (RAW-IPYNB)."""
    mod = _load()
    monkeypatch.setattr(mod, "fetch_text",
                        lambda url, timeout=None: '<a href="nb.ipynb">x</a>')
    monkeypatch.setattr(mod, "probe_status", lambda url, timeout=None: 200)
    assert mod.main(["--base-url", BASE, "--page", "/"]) == 1
    text = capsys.readouterr().out
    assert "RAW-IPYNB nb.ipynb" in text
    assert f"(source: {BASE}/)" in text


def test_json_report_carries_raw_ipynb(monkeypatch, capsys) -> None:
    """The JSON report carries the raw_ipynb entries for automation."""
    import json as jsonlib

    mod = _load()
    monkeypatch.setattr(mod, "fetch_text",
                        lambda url, timeout=None: '<a href="nb.ipynb">x</a>')
    monkeypatch.setattr(mod, "probe_status", lambda url, timeout=None: 200)
    assert mod.main(["--base-url", BASE, "--page", "/",
                     "--json"]) == 1
    report = jsonlib.loads(capsys.readouterr().out)
    assert report["raw_ipynb"][0]["href"] == "nb.ipynb"


def test_default_pages_include_catalog() -> None:
    """The catalog page is part of the default coverage (#25055)."""
    mod = _load()
    assert any("COURSE_CATALOG" in page for page in mod.DEFAULT_PAGES)


def test_concurrent_probes_cover_all_links(monkeypatch) -> None:
    """Parallel probing keeps every candidate's verdict (no link skipped)."""
    mod = _load()
    html = "".join(f'<a href="p{i}.html">x</a>' for i in range(30))
    monkeypatch.setattr(mod, "fetch_text", lambda url, timeout=None: html)

    def flaky(url, timeout=None):
        # Un tiers des sondes echouent reseau : l'ecart doit rester
        # instrument, et les 2/3 restants doivent porter leur verdict.
        if url.endswith(("p3.html", "p9.html", "p17.html")):
            raise OSError("connection reset")
        return 200

    monkeypatch.setattr(mod, "probe_status", flaky)
    result = mod.run_check(BASE, ("/",), max_links=30)
    assert result.checked == 27
    assert result.ok == 27
    assert len(result.instrument_errors) == 3

def test_raw_ipynb_internal_absolute_query_and_fragment(monkeypatch) -> None:
    """Les sources internes restent interdites avec URL absolue ou ancre."""
    mod = _load()
    hrefs = [
        'https://example.test/CoursIA/a.ipynb',
        '//example.test/CoursIA/b.ipynb?download=1',
        'c.ipynb#cellule',
        'd.ipynb?download=1#cellule',
    ]
    html = ''.join(f'<a href="{href}">x</a>' for href in hrefs)
    html += '<a href="https://else.where/a.ipynb?download=1">externe</a>'
    monkeypatch.setattr(mod, 'fetch_text', lambda url, timeout=None: html)
    monkeypatch.setattr(mod, 'probe_status', lambda url, timeout=None: 200)
    result = mod.run_check(BASE, ('/',))
    assert {entry['href'] for entry in result.raw_ipynb} == set(hrefs)
    assert result.broken == []
    assert mod.main(['--base-url', BASE, '--page', '/']) == 1


def test_raw_ipynb_origin_normalisation_and_encoded_extension(monkeypatch) -> None:
    """Meme origine canonique et extension encodee, sans faux positif externe."""
    mod = _load()
    positives = [
        'https://EXAMPLE.TEST/CoursIA/a.ipynb',
        'https://example.test:443/CoursIA/b.ipynb',
        '/CoursIA/c.%69pynb?download=1',
    ]
    negatives = [
        'https://example.test:444/CoursIA/externe.ipynb',
        'https://example.test:0/CoursIA/externe.ipynb',
        'https://example.test:bad/CoursIA/externe.ipynb',
        'https://else.where/CoursIA/externe.ipynb',
        '/CoursIA/page.html?nom=faux.ipynb',
        '/CoursIA/d.%2569pynb',
    ]
    html = ''.join(f'<a href="{href}">x</a>' for href in positives + negatives)
    monkeypatch.setattr(mod, 'fetch_text', lambda url, timeout=None: html)
    monkeypatch.setattr(mod, 'probe_status', lambda url, timeout=None: 200)
    result = mod.run_check(BASE, ('/',))
    assert {entry['href'] for entry in result.raw_ipynb} == set(positives)
    internal = mod.extract_internal_hrefs(html, BASE + '/')
    assert len(internal) == 5
    assert all(':444/' not in url and ':0/' not in url and ':bad/' not in url
               and 'else.where' not in url for url in internal)
    assert mod.main(['--base-url', BASE, '--page', '/']) == 1


def test_origine_http_port_par_defaut() -> None:
    """HTTP:80 est local, HTTP:443 est une autre origine."""
    mod = _load()
    html = ('<a href="http://EXAMPLE.TEST:80/a.ipynb">local</a>'
            '<a href="http://example.test:443/b.ipynb">autre port</a>')
    assert mod.extract_internal_hrefs(html, 'http://example.test/') == [
        'http://EXAMPLE.TEST:80/a.ipynb'
    ]
