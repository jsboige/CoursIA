"""Tests for detect_svg_html_only.py — SVG emitted only in text/html.

Pinne le contrat #26783 : une sortie dont le `<svg>` ne vit qu'en `text/html`
(sans `image/svg+xml` ni `image/png` dans le meme mime bundle) est flaggee ;
toute sortie doubled d'une representation native (`image/svg+xml`) ou d'un
fallback (`image/png`) est exempte. Le ratchet base-vs-PR juge les AJOUTS
seuls : le stock de main n'est pas re-flagge (clause de l'issue), un carnet
nouveau compte toutes ses occurrences comme ajouts.

Cas fondateur : #26613 — les quatre figures de Z3-20 C# (cellules 13/20/25/28,
`HistogramSvg`/`HeatSvg` StringBuilder -> `display(HTML(svg))`), capturees a
4/4 par l'organe sur la tete reelle de la PR (controle integre dans le body de
la PR de l'organe). L'etape 0 de #26783 a REFUTE l'invisibilite sur la surface
viewer : le garde est branche ADVISORY, pas bloquant.

La logique testee est pure (`svg_html_only_outputs` + cle d'ajout du ratchet)
-- pas de git, pas de kernel.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from detect_svg_html_only import (  # noqa: E402
    _SVG,
    _nb,
    _out,
    self_test,
    svg_html_only_outputs,
)


def _hits(outputs_by_cell):
    return svg_html_only_outputs(_nb(outputs_by_cell))


def test_positive_control_text_html_only_svg_fires():
    """Le cas fondateur : SVG seulement en text/html -> flagge."""
    hits = _hits({"c13": [_out({"text/html": _SVG})]})
    assert len(hits) == 1
    assert hits[0]["cell_id"] == "c13"
    assert hits[0]["output_type"] == "display_data"


def test_doubled_image_svg_plus_xml_exempt():
    """Le fix cible (image/svg+xml doubled) doit etre invisible au detecteur."""
    assert _hits({"c1": [_out({"text/html": _SVG,
                               "image/svg+xml": _SVG})]}) == []


def test_image_png_fallback_exempt():
    """Contrat #26783 : un fallback image/png exempte la sortie."""
    assert _hits({"c1": [_out({"text/html": _SVG,
                               "image/png": "iVBORw0KGgo="})]}) == []


def test_native_image_svg_plus_xml_alone_exempt():
    """Un SVG emis nativement en image/svg+xml seul est la forme saine."""
    assert _hits({"c1": [_out({"image/svg+xml": _SVG})]}) == []


def test_text_html_without_svg_not_flagged():
    """text/html sans <svg> : hors scope (pas une figure)."""
    assert _hits({"c1": [_out({"text/html": "<p>table</p>"})]}) == []


def test_escaped_svg_markup_not_flagged():
    """Un &lt;svg&gt; echappe (source montree en HTML) n'est pas un SVG emis."""
    assert _hits({"c1": [_out({"text/html":
                               "<code>&lt;svg&gt;...&lt;/svg&gt;</code>"})]}) == []


def test_stream_output_not_flagged():
    """stream n'est pas un mime bundle riche : hors jugement."""
    assert _hits({"c1": [{"output_type": "stream", "text": _SVG}]}) == []


def test_execute_result_flagged_like_display_data():
    """execute_result porte le meme mime bundle -> meme verdict."""
    assert len(_hits({"c1": [_out({"text/html": _SVG},
                                  "execute_result")]})) == 1


def test_list_serialized_payload_flagged():
    """Payload nbformat fragmente (liste de str) : meme verdict qu'un str."""
    assert len(_hits({"c1": [_out({"text/html": ["<div>", _SVG,
                                                 "</div>"]})]})) == 1


def test_markdown_cell_ignored():
    """Une cellule markdown n'a pas d'outputs jugeables."""
    nb = {"cells": [{"cell_type": "markdown", "id": "m",
                     "source": _SVG, "outputs": []}]}
    assert svg_html_only_outputs(nb) == []


def test_multiple_outputs_per_cell_counted():
    """Deux sorties html-only dans la meme cellule : deux occurrences."""
    hits = _hits({"c1": [_out({"text/html": _SVG}),
                         _out({"text/html": _SVG.replace("800", "400")})]})
    assert len(hits) == 2
    assert {h["svg_sha1"] for h in hits} or True  # signatures distinctes
    assert len({h["svg_sha1"] for h in hits}) == 2


def test_ratchet_added_only_keying():
    """Ajouts seuls : l'occurrence de base n'est pas re-flaggee, la nouvelle oui.

    Clause #26783 « le stock de main n'est pas juge » : le diff base/head se
    fait par signature (cell_id, svg_sha1), pas par position.
    """
    base_nb = _nb({"a": [_out({"text/html": _SVG})]})
    head_nb = _nb({"a": [_out({"text/html": _SVG})],
                   "b": [_out({"text/html": _SVG.replace("800", "400")})]})
    base_keys = {(h["cell_id"], h["svg_sha1"])
                 for h in svg_html_only_outputs(base_nb)}
    head_hits = svg_html_only_outputs(head_nb)
    added = [h for h in head_hits
             if (h["cell_id"], h["svg_sha1"]) not in base_keys]
    assert [h["cell_id"] for h in added] == ["b"]


def test_ratchet_stock_only_silent():
    """Base et head identiques (stock inchange) : zero ajout."""
    nb = _nb({"a": [_out({"text/html": _SVG})]})
    keys = {(h["cell_id"], h["svg_sha1"])
            for h in svg_html_only_outputs(nb)}
    added = [h for h in svg_html_only_outputs(nb)
             if (h["cell_id"], h["svg_sha1"]) not in keys]
    assert added == []


def test_founding_shape_csharp_stringbuilder_flagged():
    """Forme #26613 : SVG genere par StringBuilder C# dans display(HTML(...))."""
    z3_shape = ("<svg xmlns='http://www.w3.org/2000/svg' width='800'"
                " height='360'>generated by HistogramSvg</svg>")
    assert len(_hits({"c20": [_out({"text/html": z3_shape})]})) == 1


def test_self_test_passes():
    """Le self-test embarque (controles CI du garde) doit rendre 0 echec."""
    assert self_test() == []
