# Reproduire les 12 captures du Tour de la plateforme AI Engine.
#
# Cible : l'instance jetable "Maison Valmont" (corpus 100% synthetique),
# decrite dans ../instance-jetable/README.md. JAMAIS une instance reelle :
# les captures sont publiees dans un depot public, elles ne montrent donc
# que ce cadre neutre.
#
# Prerequis :
#   1. instance jetable demarree (conteneurs valmont-*) ;
#   2. ../instance-jetable/.env renseigne (VALMONT_BASE_URL,
#      VALMONT_ADMIN_USER, VALMONT_ADMIN_SESSION_PASSWORD) ;
#   3. python + playwright (pip install playwright && playwright install chromium).
#
# Usage : python capturer-le-tour.py   (depuis ce dossier)

import time
from pathlib import Path

from playwright.sync_api import sync_playwright

HERE = Path(__file__).resolve().parent
ENV = HERE.parent / "instance-jetable" / ".env"
OUT = HERE / "assets"
OUT.mkdir(exist_ok=True)

vals = {}
for line in ENV.read_text(encoding="utf-8").splitlines():
    line = line.strip()
    if line and not line.startswith("#") and "=" in line:
        key, value = line.split("=", 1)
        vals[key.strip()] = value.strip()

BASE = vals.get("VALMONT_BASE_URL", "http://localhost:8093").rstrip("/")
USER = vals.get("VALMONT_ADMIN_USER", "valmont-admin")
PASSWORD = vals.get("VALMONT_ADMIN_SESSION_PASSWORD", "")
if not PASSWORD:
    raise SystemExit("VALMONT_ADMIN_SESSION_PASSWORD absent de instance-jetable/.env")

VIEWPORT = {"width": 1400, "height": 900}


def shot(page, name):
    path = OUT / (name + ".png")
    page.screenshot(path=str(path), full_page=False)
    print("capture :", path.name)


with sync_playwright() as p:
    browser = p.chromium.launch()

    # ---- Phase 1 : face administrateur (session wp-admin) ------------------
    ctx = browser.new_context(viewport=VIEWPORT, device_scale_factor=1)
    page = ctx.new_page()
    page.goto(BASE + "/wp-login.php", wait_until="domcontentloaded")
    page.fill("#user_login", USER)
    page.fill("#user_pass", PASSWORD)
    page.click("#wp-submit")
    page.wait_for_url("**/wp-admin/**", timeout=30000)
    page.wait_for_load_state("networkidle")

    def open_admin(path_qs, settle=1.5):
        page.goto(BASE + path_qs, wait_until="domcontentloaded")
        page.wait_for_load_state("networkidle")
        time.sleep(settle)

    # 7. Workspace : le chat plein ecran dans wp-admin. Capture EN PREMIER :
    #    l'app de reglages (etapes 1, 2, 3, 5) force module_workspace a
    #    false au chargement quand la licence Pro n'est pas enregistree (le
    #    module figure dans la liste "Pro" du bundle JS, alors que le serveur
    #    livre le shell de base en Free). On active donc le module par l'API
    #    REST juste avant de visiter la page, sans ouvrir l'app de reglages ;
    #    l'etape 1 la remettra a false ensuite et l'instance retrouve son
    #    etat Free habituel. Le README documente cette limite honnetement.
    page.goto(BASE + "/wp-admin/index.php", wait_until="networkidle")
    enabled = page.evaluate(
        """async (base) => {
            const nonce = window.wpApiSettings && window.wpApiSettings.nonce;
            if (!nonce) return "no-nonce";
            const h = { "Content-Type": "application/json", "X-WP-Nonce": nonce };
            const r = await fetch(base + "/wp-json/mwai/v1/settings/options", { headers: h });
            const d = await r.json();
            const options = d.options || d;
            options.module_workspace = true;
            const u = await fetch(base + "/wp-json/mwai/v1/settings/update", {
                method: "POST", headers: h, body: JSON.stringify({ options }) });
            return u.ok ? "ok" : "http-" + u.status;
        }""",
        BASE,
    )
    print("activation module_workspace :", enabled)
    assert enabled == "ok", "echec de l'activation REST du module workspace"
    page.goto(BASE + "/wp-admin/admin.php?page=mwai_workspace", wait_until="domcontentloaded")
    page.wait_for_selector("#mwai-workspace > *", timeout=25000)
    time.sleep(3.0)
    shot(page, "tour-07-workspace")

    # 1. Tableau de bord du plugin : etapes de prise en main, modules actifs.
    open_admin("/wp-admin/admin.php?page=mwai_settings&nekoTab=dashboard", 2.5)
    shot(page, "tour-01-tableau-de-bord")

    # 2. Catalogue des modules : 6 familles, une vingtaine d'entrees.
    open_admin("/wp-admin/admin.php?page=mwai_settings&nekoTab=modules")
    shot(page, "tour-02-modules")

    # 3. Editeur de chatbot : 3 chatbots seedes, reglages AI et apparence.
    open_admin("/wp-admin/admin.php?page=mwai_settings&nekoTab=chatbots", 2.0)
    shot(page, "tour-03-chatbots")

    # 4. Apercu live du chatbot, integre en bas de l'editeur.
    page.get_by_text("This is the actual chatbot").scroll_into_view_if_needed()
    time.sleep(1.0)
    shot(page, "tour-04-chatbots-apercu")

    # 5. Environnements par defaut (7 types d'usage). La carte "Environments
    #    for AI" au-dessus affiche la cle API et l'endpoint du serveur de
    #    modeles en clair : on aligne le titre en haut du viewport pour que
    #    cette carte reste hors cadre (rien de tout ca dans un depot public).
    open_admin("/wp-admin/admin.php?page=mwai_settings&nekoTab=settings", 2.0)
    page.evaluate(
        """() => {
            const h = [...document.querySelectorAll('h1,h2,h3,h4')]
                .find(e => e.textContent.includes('Default Environments for AI'));
            h.scrollIntoView({block: 'start'});
            window.scrollBy(0, -48);
        }"""
    )
    time.sleep(0.8)
    shot(page, "tour-05-environnements-defaut")

    # 6. Playground : banc d'essai de prompts.
    open_admin("/wp-admin/tools.php?page=mwai_dashboard", 2.0)
    shot(page, "tour-06-playground")

    # 8. Generateur de contenu (module Generators).
    open_admin("/wp-admin/tools.php?page=mwai_content_generator", 2.0)
    shot(page, "tour-08-generateur-contenu")

    # 9. Generateur d'images (module Generators).
    open_admin("/wp-admin/tools.php?page=mwai_images_generator", 2.0)
    shot(page, "tour-09-generateur-images")

    ctx.close()

    # ---- Phase 2 : face visiteur (contexte vierge, aucune session) ---------
    ctx2 = browser.new_context(viewport=VIEWPORT, device_scale_factor=1)
    page = ctx2.new_page()

    # 10. Accueil public du site.
    page.goto(BASE + "/", wait_until="networkidle")
    assert page.locator("#wpadminbar").count() == 0, "toolbar admin visible sur le front"
    shot(page, "tour-10-accueil-visiteur")

    # 11. Page Assistant : chatbot inline pose par shortcode.
    page.goto(BASE + "/assistant/", wait_until="networkidle")
    assert page.locator("#wpadminbar").count() == 0, "toolbar admin visible sur le front"
    shot(page, "tour-11-assistant")

    # 12. Conversation reelle : question visiteur, reponse du modele local.
    page.locator(".mwai-chatbot-container textarea").fill(
        "Quels genres la maison publie-t-elle ?")
    page.locator(".mwai-input-submit").click()
    page.wait_for_function(
        """() => {
            const reps = document.querySelectorAll(
                '.mwai-conversation .mwai-reply.mwai-ai');
            return reps.length >= 2
                && reps[reps.length - 1].textContent.trim().length > 40;
        }""",
        timeout=240000,
    )
    page.locator(".mwai-conversation .mwai-reply.mwai-ai").last.scroll_into_view_if_needed()
    time.sleep(0.8)
    shot(page, "tour-12-conversation")

    ctx2.close()
    browser.close()

print("OK : 12 captures dans", OUT)
