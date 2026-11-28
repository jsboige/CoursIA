"""Épinglage des polices de rendu Slidev (#24171).

Deux familles de tests : le verrou et la feuille (purs, sans navigateur), puis
les propriétés que seuls un moteur de rendu peut dire — boîtes de ligne de la
référence, identité des largeurs entre noms masqués, réparation des génériques.
"""

import functools
import http.server
import json
import pathlib
import re
import socketserver
import threading

import pytest

from scripts.notebook_tools import slidev_font_pin as pinmod

FACE = re.compile(r"@font-face \{ (.*?) \}\n", re.S)


def _faces(css: str) -> list[dict]:
    return [dict(part.split(": ", 1) for part in bloc.split("; "))
            for bloc in FACE.findall(css)]


def _by_family(css: str) -> dict[str, list[dict]]:
    familles: dict[str, list[dict]] = {}
    for face in _faces(css):
        familles.setdefault(face["font-family"].strip('"'), []).append(face)
    return familles


# --- verrou, plages, feuille -------------------------------------------------

def test_les_octets_livres_correspondent_au_verrou():
    manifest = pinmod.font_manifest()
    assert set(manifest) == set(pinmod.LOCK)
    for cle, entree in manifest.items():
        assert entree["bytes"] == pinmod.LOCK[cle][1]
        assert entree["sha256"] == pinmod.LOCK[cle][2]
        assert entree["upstream"]


def test_une_police_alteree_rend_le_pin_inapplicable(tmp_path, monkeypatch):
    (tmp_path / "selawik-regular.ttf").write_bytes(b"pas une police")
    monkeypatch.setattr(pinmod, "FONT_DIR", tmp_path)
    with pytest.raises(pinmod.FontPinError, match="altérée"):
        pinmod.FontPin()


def test_les_plages_livrees_sont_le_cmap_des_polices():
    pytest.importorskip("fontTools.ttLib")
    ranges = pinmod.load_ranges()
    assert set(ranges) == set(pinmod.RANGE_FONTS)
    for cle, police in pinmod.RANGE_FONTS.items():
        attendu = pinmod.cmap_of(pinmod.FONT_DIR / pinmod.LOCK[police][0])
        assert pinmod.parse_ranges(ranges[cle]) == attendu


def test_chaque_famille_masquee_porte_des_faces_a_poids_unique():
    familles = _by_family(pinmod.build_css())
    assert set(familles) == set(pinmod.shadow_names())
    # Par poids, dans l'ordre de déclaration : la face porte-t-elle une plage ?
    # Le repli est déclaré SANS plage AVANT la principale : c'est l'ordre qui
    # restreint le repli au complément du cmap principal.
    attendus = {}
    for nom in pinmod.SANS_NAMES:
        attendus[nom] = {"400": [False, True], "700": [False, True]}
    for nom in pinmod.MONO_NAMES:
        attendus[nom] = {"400": [False], "700": [False]}
    for nom in pinmod.SERIF_NAMES:
        attendus[nom] = {"400": [False, True, True], "700": [False, True, True]}
    for nom, faces in familles.items():
        par_poids: dict[str, list[bool]] = {}
        for face in faces:
            poids = face["font-weight"]
            assert re.fullmatch(r"\d+", poids), (
                f"`{nom}` : une face porte une plage de poids {poids!r} — sur une police "
                "variable elle prive la famille de ses autres faces")
            par_poids.setdefault(poids, []).append("unicode-range" in face)
            assert {"ascent-override", "descent-override", "line-gap-override"} <= set(face)
        assert par_poids == attendus[nom], nom


def test_les_generiques_repares_sont_des_noms_masques():
    for mot_cle in ("sans-serif", "system-ui", "ui-sans-serif", "monospace", "ui-monospace",
                    "serif", "ui-serif", "-apple-system", "blinkmacsystemfont"):
        assert mot_cle in pinmod.GENERIC_REPAIR, mot_cle
        remplacement = pinmod.GENERIC_REPAIR[mot_cle].strip('"')
        assert remplacement in pinmod.shadow_names(), mot_cle


def test_install_font_pin_ne_route_que_les_polices():
    """Le document du deck n'est JAMAIS intercepté ni réécrit.

    Un document renvoyé par une route Playwright perd son espace d'adressage :
    Chromium refuse alors ses scripts de module (« blocked by CORS policy: The
    request client is not a secure context and the resource is in more-private
    address space `local` ») dès que l'origine n'est pas un contexte sûr.
    Mesuré : deck entier en rc 2 sur 172.24.240.1, le même deck servi sur
    `localhost` passant. La feuille entre donc par `adoptedStyleSheets`, posée
    par un script d'initialisation avant tout script du deck.
    """
    vu = {}

    class _Page:
        def add_init_script(self, script=None, path=None):
            vu["init"] = script

        def route(self, pattern, handler):
            vu["route"] = (pattern, handler)

    pin = pinmod.install_font_pin(_Page())
    assert vu["route"][0] == "**" + pinmod.URL_PREFIX + "**"
    assert vu["route"][1] == pin.handle
    assert "@font-face" in vu["init"], "la feuille doit voyager dans le script d'initialisation"
    assert "adoptedStyleSheets" in vu["init"]


def test_hors_de_son_prefixe_la_route_ne_decide_de_rien():
    """`handle` laisse passer toute URL hors du préfixe du pin.

    Sous la route enregistrée (`**/__slidev_font_pin/**`) cette branche n'est
    pas atteignable ; elle vaut pour un appel direct — le jour où la route
    s'élargit, un document ou un module du deck attrapé par le pin doit
    continuer vers son serveur, jamais recevoir un 404 : un document intercepté
    est la panne mesurée (rc 2, scripts de module refusés)."""
    class _Requete:
        def __init__(self, url):
            self.url = url

    class _Route:
        def __init__(self, url):
            self.request = _Requete(url)
            self.gestes = []

        def continue_(self):
            self.gestes.append("continue")

        def fulfill(self, **kwargs):
            self.gestes.append(("fulfill", kwargs["status"]))

    pin = pinmod.FontPin()
    for url in ("http://hote/index.html",
                "http://hote/@fs/D:/deck/node_modules/@slidev/client/main.ts",
                "http://hote/__slidev_font_pin_inconnu/selawik-regular.ttf"):
        route = _Route(url)
        pin.handle(route)
        assert route.gestes == ["continue"], url
    assert pin.font_requests == 0
    route = _Route("http://hote" + pinmod.URL_PREFIX + "selawik-regular.ttf?x=1")
    pin.handle(route)
    assert route.gestes == [("fulfill", 200)] and pin.font_requests == 1
    route = _Route("http://hote" + pinmod.URL_PREFIX + "pas-une-police.ttf")
    pin.handle(route)
    assert route.gestes == [("fulfill", 404)] and pin.font_requests == 1


def test_la_signature_suit_les_octets_des_polices():
    manifest = pinmod.font_manifest()
    css = pinmod.build_css()
    reference = pinmod.signature(css, manifest)
    assert reference == pinmod.signature(css, manifest)
    altere = json.loads(json.dumps(manifest))
    altere["selawik"]["sha256"] = "0" * 64
    assert pinmod.signature(css, altere) != reference


def test_classify_fonts_distingue_epingle_deck_et_systeme():
    releve = {"fonts": [
        {"family": "Selawik", "postscript": "Selawik", "custom": True, "glyphs": 40},
        {"family": "KaTeX_Main", "postscript": "KaTeX_Main", "custom": True, "glyphs": 3},
        {"family": "Segoe UI Emoji", "postscript": "", "custom": False, "glyphs": 2},
    ]}
    verdict = pinmod.classify_fonts(releve)
    assert verdict["pinned"] == 40 and verdict["deck"] == 3
    assert verdict["escaped"] == [{"family": "Segoe UI Emoji", "glyphs": 2}]


def test_le_rapport_nomme_la_slide_de_chaque_glyphe_echappe():
    pin = pinmod.FontPin()
    rapport = pin.report({}, [{"slide": 3, "fonts": [
        {"family": "Selawik", "postscript": "Selawik", "custom": True, "glyphs": 9},
        {"family": "Segoe UI Emoji", "postscript": "", "custom": False, "glyphs": 1},
    ]}])
    assert rapport["enabled"] is True
    assert rapport["verified"] is False
    assert rapport["escaped"] == [{"slide": 3, "family": "Segoe UI Emoji", "glyphs": 1}]
    assert rapport["glyphs_pinned"] == 9
    assert rapport["signature"] == pin.signature
    assert rapport["borne"] and rapport["normalisation"]["sans"]
    # `applied` est une CONCLUSION sur un relevé, pas une constante : feuille
    # adoptée et toutes les faces chargées, rien de moins.
    charge = {"injected": True, "unloaded": []}
    assert pin.report(charge, [])["applied"] is True
    assert pin.report({**charge, "unloaded": ["Segoe UI 700"]}, [])["applied"] is False
    assert pin.report({**charge, "injected": False}, [])["applied"] is False
    assert pin.report({}, [])["applied"] is False


# --- propriétés de rendu -----------------------------------------------------

def test_les_arguments_de_lancement_font_partie_du_pin():
    """Sous Linux, Chromium hinte les avancées (largeurs entières) : sans
    `--font-render-hinting=none`, une MÊME police livrée s'écarte de Windows de
    −2,1 % à +8,7 % selon la taille (mesuré). Les arguments entrent donc dans
    l'empreinte du pin — les changer change la signature — et le rapport les
    nomme."""
    pin = pinmod.FontPin()
    assert pin.launch_args == list(pinmod.LAUNCH_ARGS) == ["--font-render-hinting=none"]
    assert pin.report({}, [])["launch_args"] == list(pinmod.LAUNCH_ARGS)
    manifest = pinmod.font_manifest()
    css = pinmod.build_css()
    assert pinmod.signature(css, manifest) != pinmod.signature(css, manifest, ())


@pytest.fixture(scope="module")
def browser():
    sync_api = pytest.importorskip("playwright.sync_api")
    playwright = sync_api.sync_playwright().start()
    try:
        # Les arguments du pin : sur Linux, sans eux, les avancées sont hintées
        # (arrondies au pixel) et les largeurs attendues ci-dessous (105,47 px…)
        # n'ont plus cours. Sur Windows, no-op mesuré.
        instance = playwright.chromium.launch(args=list(pinmod.LAUNCH_ARGS))
    except sync_api.Error as exc:  # binaire absent : le test le dit, ne ment pas
        playwright.stop()
        pytest.skip(f"Chromium Playwright indisponible : {exc}")
    yield instance
    instance.close()
    playwright.stop()


DOC = """<!doctype html><html><head><meta charset="utf-8"><style>
  body { margin: 0 } #slide-content { width: 900px }
</style></head><body><div id="slide-content">
  <p id="sans" style="font-family: 'Segoe UI', 'Calibri', Arial, sans-serif; font-size: 18px">Apprentissage supervisé</p>
  <p id="sans2" style="font-family: Verdana; font-size: 18px">Apprentissage supervisé</p>
  <p id="sans3" style="font-family: 'Trebuchet MS'; font-size: 18px">Apprentissage supervisé</p>
  <p id="mono" style="font-family: 'Cascadia Code', 'Consolas', monospace; font-size: 18px">iiiiiMMMMM</p>
  <p id="serif" style="font-family: Georgia, 'Times New Roman', serif; font-size: 18px">Le modèle apprend</p>
  <p id="serif2" style="font-family: Georgia, 'Times New Roman', serif; font-size: 18px; font-weight: 700">Le modèle apprend</p>
  <p id="genmono" style="font-family: monospace; font-size: 18px">iiiiiMMMMM</p>
  <p id="gensans" style="font-family: sans-serif; font-size: 18px">Apprentissage supervisé</p>
  <p id="genabs" style="font-family: 'Police Absente Xy', monospace; font-size: 18px">iiiiiMMMMM</p>
  <p id="hors" style="font-size: 18px">OK &#128512; &#20013;</p>
</div></body></html>"""

MEASURE = """
(ids) => ids.map(id => {
  const el = document.getElementById(id);
  const box = el.getBoundingClientRect();
  const range = document.createRange();
  range.selectNodeContents(el);
  let largeur = 0;
  for (const rect of range.getClientRects()) largeur = Math.max(largeur, rect.width);
  const sonde = document.createElement('span');
  sonde.style.cssText = 'display:inline-block;width:0;height:0;vertical-align:baseline';
  el.appendChild(sonde);
  const base = sonde.getBoundingClientRect().top - box.top;
  sonde.remove();
  return [id, Math.round(largeur * 100) / 100, Math.round(box.height * 100) / 100,
          Math.round(base * 100) / 100, getComputedStyle(el).fontFamily,
          el.dataset.slidevFontPin || null, el.style.getPropertyPriority('font-family')];
})
"""


def _mesures(browser):
    page = browser.new_page()
    # Route du document d'abord, pin ENSUITE : la route la plus récemment
    # enregistrée passe en premier, et celle du pin ne matche que les polices.
    page.route("**/*", lambda route: route.fulfill(
        status=200, content_type="text/html; charset=utf-8", body=DOC))
    pin = pinmod.install_font_pin(page)
    page.goto("http://pin.test/", wait_until="load")
    loaded = pin.ensure_loaded(page)
    assert loaded["injected"] is True and loaded["unloaded"] == []
    assert loaded["declared"] == pin.n_faces, (
        f"le contrôle doit couvrir les {pin.n_faces} faces du pin, pas "
        f"{loaded['declared']} — comparaison de familles sensible à la casse ?")
    page.evaluate("""async () => {
        for (const f of document.fonts) { try { await f.load(); } catch (e) {} }
        await document.fonts.ready;
    }""")
    avant = {ligne[0]: ligne[1:] for ligne in page.evaluate(MEASURE, ["sans", "mono", "serif", "genmono"])}
    pin.apply(page)
    apres = {ligne[0]: ligne[1:] for ligne in page.evaluate(
        MEASURE, ["sans", "sans2", "sans3", "mono", "serif", "serif2", "genmono", "gensans",
                  "genabs", "hors"])}
    cdp = page.context.new_cdp_session(page)
    cdp.send("DOM.enable")
    cdp.send("CSS.enable")
    root = cdp.send("DOM.getDocument", {"depth": 0})["root"]["nodeId"]
    polices = {}
    for cible in ("sans", "mono", "serif", "genmono", "gensans", "genabs", "hors"):
        noeud = cdp.send("DOM.querySelector", {"nodeId": root, "selector": "#" + cible})["nodeId"]
        polices[cible] = [(f["familyName"], f["isCustomFont"], f["glyphCount"])
                          for f in cdp.send("CSS.getPlatformFontsForNode", {"nodeId": noeud})["fonts"]]
    page.close()
    return avant, apres, polices


def test_le_pin_reproduit_les_boites_de_ligne_de_reference(browser):
    avant, apres, polices = _mesures(browser)
    # 18 px : Segoe UI 24/19, Cascadia Code 21/17, Georgia 21/17 (mesuré système).
    assert apres["sans"][1:3] == [24, 19]
    assert apres["mono"][1:3] == [21, 17]
    assert apres["serif"][1:3] == [21, 17]
    assert apres["serif2"][1:3] == [21, 17]
    assert avant["sans"][1:3] == [24, 19]  # la référence système, à l'identique
    assert all(f[0] in pinmod.PINNED_FAMILIES or not f[1] for f in polices["sans"])


def test_les_noms_masques_rendent_la_meme_largeur(browser):
    _, apres, _ = _mesures(browser)
    assert apres["sans"][0] == apres["sans2"][0] == apres["sans3"][0], (
        "trois noms différents (Segoe UI / Verdana / Trebuchet MS) doivent mesurer "
        "la même largeur sous le pin — c'est la normalisation")


def test_l_avance_mono_est_celle_de_la_reference(browser):
    _, apres, polices = _mesures(browser)
    # 10 glyphes × 1200/2048 em × 18 px = 105,47 px (résidu d'arrondi < 0,1 px).
    assert abs(apres["mono"][0] - 105.47) < 0.1
    assert [f[0] for f in polices["mono"]] == ["DejaVu Sans Mono"]


def test_les_piles_a_generique_en_tete_sont_reparees(browser):
    _, apres, polices = _mesures(browser)
    assert "Consolas" in apres["genmono"][3]
    assert "Segoe UI" in apres["gensans"][3]
    assert [f[0] for f in polices["genmono"]] == ["DejaVu Sans Mono"]
    assert [f[0] for f in polices["gensans"]] == ["Selawik"]
    # La réparation laisse une marque (elle sert à sauter l'élément au passage
    # suivant) et un style inline en `!important`.
    assert apres["genmono"][4:] == ["monospace", "important"]
    assert apres["gensans"][4:] == ["sans-serif", "important"]


def test_un_generique_apres_une_famille_absente_est_repare(browser):
    """La réparation lit la première famille RÉSOLUE, pas la première écrite :
    dans `'Police Absente Xy', monospace` le moteur saute la famille absente et
    emploie le générique, que `@font-face` ne peut pas masquer."""
    _, apres, polices = _mesures(browser)
    assert "Consolas" in apres["genabs"][3]
    assert [f[0] for f in polices["genabs"]] == ["DejaVu Sans Mono"]


DOC_SYSTEME = """<!doctype html><html><head><meta charset="utf-8"></head><body><div id="slide-content">
  <p id="sys" style="font-family: 'Segoe Print', monospace; font-size: 18px">iiiii</p>
</div></body></html>"""

# La sonde de disponibilité du réparateur (même mesure que `_JS_REPAIR`).
SONDE = """
(name) => {
  const ctx = document.createElement('canvas').getContext('2d');
  const regle = 'MMMMMWWWWWiiilli|@~';
  ctx.font = '32px "__slidev_font_pin_absent__"';
  const base = ctx.measureText(regle).width;
  ctx.font = '32px "' + name + '", "__slidev_font_pin_absent__"';
  return Math.abs(ctx.measureText(regle).width - base) > 0.01;
}
"""


def test_une_famille_systeme_non_masquee_en_tete_arrete_la_reparation(browser):
    """La première famille RÉSOLUE décide — y compris une police du SYSTÈME
    qu'aucune face ne masque (« Segoe Print », sur le siège Windows) : elle
    sert, le générique qui la suit n'a jamais servi, la pile n'est pas réécrite
    (le relit nommera cette police dans `escaped`).

    Le test LIT la sonde de disponibilité au lieu de supposer la machine : là
    où la famille manque (le conteneur ubuntu), le générique décide et la pile
    est réparée. Témoin négatif de la sonde : une famille absente."""
    page = browser.new_page()
    page.route("**/*", lambda route: route.fulfill(
        status=200, content_type="text/html; charset=utf-8", body=DOC_SYSTEME))
    pin = pinmod.install_font_pin(page)
    page.goto("http://pin.test/", wait_until="load")
    assert pin.ensure_loaded(page)["injected"] is True
    assert page.evaluate(SONDE, "Police Absente Xy") is False
    presente = page.evaluate(SONDE, "Segoe Print")
    pin.apply(page)
    pile = page.evaluate("""() => {
        const el = document.getElementById('sys');
        return [getComputedStyle(el).fontFamily, el.dataset.slidevFontPin || null,
                el.style.getPropertyPriority('font-family')];
    }""")
    page.close()
    if presente:
        # Servie par le système, non réécrite : le générique de queue survit,
        # ni marque ni priorité de réparation.
        assert "monospace" in pile[0] and "Consolas" not in pile[0], pile
        assert pile[1:] == [None, ""], pile
    else:
        assert "Consolas" in pile[0] and "monospace" not in pile[0], pile
        assert pile[1:] == ["monospace", "important"], pile


def test_les_piles_sans_generique_ne_sont_pas_reecrites(browser):
    """Une pile de familles NOMMÉES est masquée par `@font-face` : la réécrire
    en style inline serait une écriture inutile, et sur `!important` elle
    écraserait une intention du deck. Seul le générique en tête est réparé.

    Ce qui distingue une pile réécrite : le générique de QUEUE y serait
    remplacé, et l'élément porterait la marque et la priorité de réparation.
    La forme citée d'un nom (`"Calibri"`) ne le distingue pas : Chromium ne
    cite pas ce nom dans `getComputedStyle` — un réparateur qui réécrivait
    TOUT passait l'assertion (mesuré : mutant M14 survivant)."""
    _, apres, _ = _mesures(browser)
    for ident, queue in (("sans", "sans-serif"), ("mono", "monospace"), ("serif", "serif")):
        assert apres[ident][3].endswith(", " + queue), (ident, apres[ident][3])
        assert apres[ident][4:] == [None, ""], (ident, apres[ident][4:])


def test_la_feuille_retiree_est_vue_par_le_relit(browser):
    """`injected` est une LECTURE, pas une constante : un script du deck qui
    réécrirait `adoptedStyleSheets` ferait disparaître la feuille, et le relit
    doit le dire (c'est ce qui rend `font_pin.applied` opposable)."""
    page = browser.new_page()
    page.route("**/*", lambda route: route.fulfill(
        status=200, content_type="text/html; charset=utf-8", body=DOC))
    pin = pinmod.install_font_pin(page)
    page.goto("http://pin.test/", wait_until="load")
    assert pin.ensure_loaded(page)["injected"] is True
    page.evaluate("""() => {
        document.adoptedStyleSheets = [...document.adoptedStyleSheets].filter(
            s => s !== window.__slidevFontPin.sheet);
    }""")
    assert pin.ensure_loaded(page)["injected"] is False
    page.close()


PAGES_DOC = """<!doctype html><html><head><meta charset="utf-8"><style>
  body { margin: 0 } #slide-content { width: 900px }
</style></head><body><div id="slide-content"><div id="slideshow">
  <div class="slidev-page"><p style="font-family: monospace; font-size: 18px">iiiii</p></div>
  <div class="slidev-page" style="display: none"><p style="font-family: ui-sans-serif, sans-serif; font-size: 18px">Texte</p></div>
  <div class="slidev-page" style="display: none"><pre style="font-family: ui-monospace, Menlo, monospace; font-size: 11.52px">code</pre></div>
</div><div class="hors-page" style="font-family: system-ui; font-size: 14px">hors</div></div></body></html>"""


def test_les_reparations_sont_attribuees_a_leur_page(browser):
    """Slidev garde le deck ENTIER dans `#slide-content` (un `.slidev-page` par
    slide, une seule affichée) : le premier passage répare toutes les pages d'un
    coup — mesuré sur S8, 1 901 éléments à la slide 1 comme à la 30. Le rapport
    attribue donc chaque élément à SA page (index du `.slidev-page`, `hors-page`
    sinon), jamais à la slide pendant laquelle le passage a eu lieu."""
    page = browser.new_page()
    page.route("**/*", lambda route: route.fulfill(
        status=200, content_type="text/html; charset=utf-8", body=PAGES_DOC))
    pin = pinmod.install_font_pin(page)
    page.goto("http://pin.test/", wait_until="load")
    first = pin.apply(page)
    assert first["by_page"] == {"1": 1, "2": 1, "3": 1, "hors-page": 1}, first
    second = pin.apply(page)  # tout est marqué : rien de neuf à réparer
    assert second["repaired"] == 0
    # Un élément que le deck RECÉE (navigation, clic) porte un générique non
    # réparé : le passage suivant l'attrape, et son compte S'ADDITIONNE à
    # celui de sa page au lieu de le remplacer.
    page.evaluate("""() => {
        const p = document.createElement('p');
        p.style.cssText = 'font-family: sans-serif; font-size: 18px';
        p.textContent = 'recréé';
        document.querySelectorAll('.slidev-page')[1].appendChild(p);
    }""")
    third = pin.apply(page)
    assert third["by_page"] == {"2": 1}, third
    assert pin.report({}, [])["repaired_by_slide"] == {"1": 1, "2": 2, "3": 1, "hors-page": 1}
    page.close()


def test_le_controle_de_chargement_couvre_toutes_les_faces(browser):
    """`ensure_loaded` compare les familles SANS LA CASSE, des deux côtés.

    Mesuré avant correctif : `declared: 16` sur 144 faces — la comparaison
    cherchait un nom déjà en minuscules, donc seules les faces nommées en
    minuscules (`ui-monospace`, `ui-serif`, …) étaient contrôlées, et `applied`
    affirmait « toutes les faces chargées » en en vérifiant 16.
    """
    page = browser.new_page()
    page.route("**/*", lambda route: route.fulfill(
        status=200, content_type="text/html; charset=utf-8", body=DOC))
    pin = pinmod.install_font_pin(page)
    page.goto("http://pin.test/", wait_until="load")
    loaded = pin.ensure_loaded(page)
    assert pin.n_faces == 144
    assert loaded == {"declared": 144, "unloaded": [], "injected": True, "error": None}, loaded
    page.close()


def test_le_relit_voit_un_glyphe_hors_couverture(browser):
    _, _, polices = _mesures(browser)
    # 中 n'est dans aucune police livrée : il échappe au pin, et le relit le voit.
    # (😀, lui, est couvert par DejaVu Sans : épinglé, en monochrome.)
    assert any(not custom for _, custom, _ in polices["hors"])


class _Silencieux(http.server.SimpleHTTPRequestHandler):
    def log_message(self, *args):  # le journal HTTP polluerait la sortie pytest
        pass


def _serve(root: pathlib.Path) -> tuple[socketserver.TCPServer, str]:
    handler = functools.partial(_Silencieux, directory=str(root))
    httpd = socketserver.TCPServer(("127.0.0.1", 0), handler)
    threading.Thread(target=httpd.serve_forever, daemon=True).start()
    return httpd, f"http://127.0.0.1:{httpd.server_address[1]}/"


DOC_PREMIER_SCRIPT = """<!doctype html><html><head><meta charset="utf-8"><script>
  // Premier script du deck, classique et synchrone : que voit-il déjà ?
  window.__vu = {
    adoptee: [...document.adoptedStyleSheets].some(
      s => [...s.cssRules].some(r => r.type === CSSRule.FONT_FACE_RULE)),
    faces_segoe: [...document.fonts].filter(
      f => f.family.replace(/^["']|["']$/g, '') === 'Segoe UI').length,
  };
</script></head><body><div id="slide-content">
  <p id="sans" style="font-family: 'Segoe UI'; font-size: 18px">Apprentissage supervisé</p>
</div></body></html>"""


def test_la_feuille_est_en_place_avant_le_premier_script_du_deck(browser, tmp_path):
    """Mermaid mesure son texte à l'insertion : un pin posé après le rendu
    arrive trop tard. La feuille doit donc exister quand le PREMIER script
    du document s'exécute."""
    (tmp_path / "index.html").write_text(DOC_PREMIER_SCRIPT, encoding="utf-8")
    httpd, base = _serve(tmp_path)
    try:
        ctx = browser.new_context()
        page = ctx.new_page()
        pin = pinmod.install_font_pin(page)
        page.goto(base + "index.html", wait_until="load")
        vu = page.evaluate("() => window.__vu")
        assert vu == {"adoptee": True, "faces_segoe": 4}, vu  # 4 faces par nom sans, 2 poids × repli/principale
        loaded = pin.ensure_loaded(page)
        assert loaded["injected"] is True and loaded["unloaded"] == [] and loaded["error"] is None
        ctx.close()
    finally:
        httpd.shutdown()
        httpd.server_close()


def test_install_font_pin_ne_reecrit_pas_le_document_servi(browser, tmp_path):
    # `newline="\n"` : le fichier servi est octet pour octet le document attendu.
    (tmp_path / "index.html").write_text(DOC, encoding="utf-8", newline="\n")
    httpd, base = _serve(tmp_path)
    try:
        ctx = browser.new_context()
        page = ctx.new_page()
        pin = pinmod.install_font_pin(page)
        response = page.goto(base + "index.html", wait_until="load")
        assert response.body().decode("utf-8") == DOC  # servi par son serveur, tel quel
        loaded = pin.ensure_loaded(page)
        assert loaded["injected"] is True and loaded["unloaded"] == [] and loaded["error"] is None
        assert pin.font_requests >= 1
        ctx.close()
    finally:
        httpd.shutdown()
        httpd.server_close()
