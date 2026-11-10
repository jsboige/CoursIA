"""Relevé des polices réellement utilisées par Chromium pour les glyphes."""

import pytest

from scripts.notebook_tools.scan_slidev_composition import (
    font_signature,
    probe_font_environment,
    rendered_fonts,
    rendering_conditions,
)


def test_releve_detecte_fallback_et_variation_apres_le_titre():
    sync_api = pytest.importorskip("playwright.sync_api")
    with sync_api.sync_playwright() as playwright:
        try:
            browser = playwright.chromium.launch()
        except sync_api.Error as exc:
            pytest.skip(f"Chromium Playwright indisponible : {exc}")
        page = browser.new_page()
        cdp = page.context.new_cdp_session(page)
        cdp.send("DOM.enable")
        cdp.send("CSS.enable")
        observations = []
        for family in ("serif", "monospace"):
            page.set_content(
                '<div id="slide-content"><h1 style="font-family:sans-serif">Titre</h1>'
                f'<p style="font-family:PoliceInexistante, {family}">Exemple</p></div>'
            )
            observations.append((font_signature(probe_font_environment(page)),
                                 rendered_fonts(cdp)))
        browser.close()

    ancienne_a, premier = observations[0]
    ancienne_b, second = observations[1]
    assert ancienne_a == ancienne_b  # La première sonde ne voit que le titre.
    assert "error" not in premier and "error" not in second
    assert premier["fonts"] != second["fonts"]
    assert all(f["glyphs"] > 0 for f in premier["fonts"] + second["fonts"])
    assert all(f["family"] != "PoliceInexistante" for f in premier["fonts"])
    a = rendering_conditions("Chromium", [980, 552], [{"slide": 1, **premier}])
    b = rendering_conditions("Chromium", [980, 552], [{"slide": 1, **second}])
    assert a["signature"] != b["signature"]
    assert a["signature"] != rendering_conditions("Chromium", [800, 600],
                                                   [{"slide": 1, **premier}])["signature"]


def test_sonde_indisponible_ne_produit_pas_une_empreinte():
    mesure = rendered_fonts(None)
    assert "error" in mesure
    conditions = rendering_conditions("Chromium", [980, 552], [{"slide": 1, **mesure}])
    assert conditions["signature"] == "indisponible"
