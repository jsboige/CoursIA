/**
 * Module 01 — Decouverte de Playwright & Open WebUI
 *
 * Ce premier module vous fait decouvrir Playwright en testant
 * une application reelle : Open WebUI, une plateforme de chat IA.
 *
 * CONCEPTS COUVERTS :
 * - Navigation (page.goto)
 * - Localisation d'elements (locator, getByRole, getByText)
 * - Assertions (expect, toBeVisible, toContain)
 * - Screenshots et artefacts
 * - Reutilisation de session authentifiee (storageState)
 *
 * PRE-REQUIS :
 * - .env configure avec OWUI_URL, OWUI_EMAIL, OWUI_PASSWORD
 * - npm install + npx playwright install chromium
 */
import { test, expect } from '@playwright/test';
import { MODEL } from '../helpers/selectors';
import { dismissModals } from '../helpers/chat';

test.describe('01 — Decouverte : Premiers pas avec Playwright', () => {

  /**
   * HOOK beforeEach : Fermer les modales eventuelles
   *
   * Open WebUI peut afficher un dialogue "Quoi de neuf" (changelog)
   * a la premiere visite. Ce modal bloque TOUS les clics sur la page.
   * On le ferme systematiquement avant chaque test.
   */
  test.beforeEach(async ({ page }) => {
    await page.goto('/');
    await dismissModals(page);
  });

  /**
   * TEST 1 : Verifier que la connexion fonctionne
   *
   * Grace au setup d'authentification (fixtures/auth.setup.ts),
   * on est deja connecte quand ce test demarre.
   * Le storageState contient les cookies/tokens de la session.
   *
   * On verifie simplement que la page principale se charge
   * et affiche le selecteur de modeles (signe que tout fonctionne).
   */
  test('connexion reussie — la page principale se charge', async ({ page }) => {
    // La navigation est faite dans beforeEach — on verifie juste le resultat

    // Attendre que le selecteur de modeles soit visible
    // C'est le premier element interactif qui apparait apres le chargement
    await expect(page.locator(MODEL.selectorButton)).toBeVisible({ timeout: 15_000 });

    // EXERCICE : Ajoutez une assertion pour verifier le titre de la page
    // Indice : await expect(page).toHaveTitle(/Open WebUI/);
  });

  /**
   * TEST 2 : Explorer le selecteur de modeles
   *
   * Open WebUI permet de choisir parmi de nombreux modeles LLM.
   * Ce test ouvre le dropdown et compte les modeles disponibles.
   *
   * CONCEPTS :
   * - click() pour interagir avec un element
   * - locator() pour cibler des elements dans le DOM
   * - count() pour compter les elements trouves
   */
  test('le selecteur de modeles liste les modeles disponibles', async ({ page }) => {
    await expect(page.locator(MODEL.selectorButton)).toBeVisible({ timeout: 15_000 });

    // Ouvrir le selecteur de modeles
    await page.locator(MODEL.selectorButton).click();

    // Attendre que la liste des modeles apparaisse
    await expect(page.locator(MODEL.modelListbox)).toBeVisible({ timeout: 10_000 });

    // Compter les modeles disponibles
    const modelOptions = page.locator(MODEL.modelOption);
    await expect(modelOptions.first()).toBeVisible({ timeout: 10_000 });
    const count = await modelOptions.count();

    // Il devrait y avoir au moins quelques modeles
    expect(count).toBeGreaterThan(0);
    console.log(`  → ${count} modeles disponibles sur cette instance`);

    // EXERCICE : Listez les noms des 5 premiers modeles
    // Indice : const text = await modelOptions.nth(i).innerText();
  });

  /**
   * TEST 3 : Naviguer dans le menu utilisateur
   *
   * Ce test montre comment interagir avec des menus deroulants
   * et gerer les labels multilingues (francais/anglais).
   *
   * CONCEPTS :
   * - getByRole() : Selecteur semantique recommande par Playwright
   * - .or() : Combiner des locators pour gerer plusieurs langues
   * - Regex : /menu/i pour un matching case-insensitive
   */
  test('le menu utilisateur est accessible', async ({ page }) => {
    await expect(page.locator(MODEL.selectorButton)).toBeVisible({ timeout: 15_000 });

    // Trouver le bouton menu utilisateur
    // En francais : "Menu utilisateur", en anglais : "User Menu"
    // On utilise une regex pour matcher les deux
    const userMenu = page.getByRole('button', { name: /menu/i }).last();
    await expect(userMenu).toBeVisible({ timeout: 10_000 });

    // Cliquer pour ouvrir le menu
    await userMenu.click();

    // Verifier qu'une option "Reglages" ou "Settings" apparait
    await expect(
      page.getByText('Réglages').or(page.getByText('Settings')).first()
    ).toBeVisible({ timeout: 10_000 });

    // EXERCICE : Verifiez qu'une option "Deconnexion" / "Sign Out" existe aussi
  });

  /**
   * TEST 4 : Capturer un screenshot de la page
   *
   * Les screenshots sont essentiels pour :
   * - Documenter l'etat de l'application
   * - Debugger des tests qui echouent
   * - Creer des rapports visuels
   *
   * CONCEPTS :
   * - page.screenshot() : Capture la page entiere
   * - testInfo.attach() : Attache des fichiers au rapport
   */
  test('capturer un screenshot de la page principale', async ({ page }, testInfo) => {
    await expect(page.locator(MODEL.selectorButton)).toBeVisible({ timeout: 15_000 });

    // Capturer un screenshot
    const screenshot = await page.screenshot({ fullPage: true });

    // L'attacher au rapport Playwright (visible dans le HTML report)
    await testInfo.attach('page-principale', {
      body: screenshot,
      contentType: 'image/png',
    });

    // Le screenshot est aussi sauvegarde automatiquement en cas d'echec
    // grace a la config : screenshot: 'only-on-failure'

    // EXERCICE : Capturez un screenshot de seulement le selecteur de modeles
    // Indice : await page.locator(MODEL.selectorButton).screenshot()
  });
});
