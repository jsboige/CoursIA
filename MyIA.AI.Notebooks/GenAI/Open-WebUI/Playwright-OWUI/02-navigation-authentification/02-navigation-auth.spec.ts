/**
 * Module 02 — Navigation & Authentification
 *
 * Ce module approfondit la navigation dans Open WebUI et explore
 * le mecanisme d'authentification Playwright.
 *
 * CONCEPTS COUVERTS :
 * - Authentification par storageState (session reutilisable)
 * - Navigation entre pages (goto, waitForURL)
 * - Assertions localisees (francais/anglais)
 * - Routes et structure de l'application SvelteKit
 *
 * NOTE : Tous les tests demarrent deja authentifies grace au setup
 * (fixtures/auth.setup.ts). Le fichier .auth/owui.json contient
 * les cookies et tokens de session.
 */
import { test, expect } from '@playwright/test';
import { MODEL, AUTH } from '../helpers/selectors';
import { dismissModals } from '../helpers/chat';

test.describe('02 — Navigation & Authentification', () => {

  /**
   * TEST 1 : Verifier que la session authentifiee persiste
   *
   * Ce test illustre le pattern storageState de Playwright :
   * on ne se reconnecte pas, on reutilise la session sauvegardee.
   *
   * Si ce test echoue, c'est que :
   * - Le token JWT a expire (duree de vie courte)
   * - Le serveur a ete redemarré (sessions invalidees)
   * - Les cookies ne sont pas correctement sauvegardes
   */
  test('la session authentifiee est valide et persistante', async ({ page }) => {
    await page.goto('/');
    await dismissModals(page);

    // Si la session est valide, on arrive directement sur la page de chat
    // (pas de redirection vers /auth)
    await expect(page.locator(MODEL.selectorButton)).toBeVisible({ timeout: 15_000 });

    // Verifier qu'on n'est PAS sur la page de login
    await expect(page.locator(AUTH.authPage)).not.toBeVisible();
  });

  /**
   * TEST 2 : Naviguer vers le panneau d'administration
   *
   * La page /admin est reservee aux administrateurs.
   * Elle affiche la liste des utilisateurs de l'instance.
   *
   * CONCEPT : Gestion des labels multilingues
   * Open WebUI affiche "Utilisateurs" en FR, "Users" en EN.
   * On utilise .or() pour accepter les deux.
   */
  test('acceder au panneau admin — liste des utilisateurs', async ({ page }) => {
    await page.goto('/admin');

    // Attendre le chargement de la page admin
    await expect(
      page.getByText('Utilisateurs').or(page.getByText('Users')).first()
    ).toBeVisible({ timeout: 15_000 });

    // La table des utilisateurs devrait etre visible
    await expect(page.locator('table')).toBeVisible({ timeout: 15_000 });

    // EXERCICE : Comptez le nombre d'utilisateurs dans la table
    // Indice : const rows = await page.locator('table tbody tr').count();
  });

  /**
   * TEST 3 : Naviguer vers les reglages admin
   *
   * La page /admin/settings contient la configuration globale
   * de l'instance Open WebUI.
   */
  test('acceder aux reglages admin', async ({ page }) => {
    await page.goto('/admin/settings');

    // Le lien "Reglages" / "Settings" devrait etre actif dans la navigation
    await expect(
      page.getByRole('link', { name: /réglages|settings/i }).first()
    ).toBeVisible({ timeout: 15_000 });
  });

  /**
   * TEST 4 : Parcourir le Workspace — Knowledge Bases
   *
   * Le Workspace contient les ressources de l'instance :
   * modeles, prompts, knowledge bases, fonctions.
   *
   * CONCEPT : Navigation SvelteKit
   * Les pages sous /workspace/ utilisent le routage SvelteKit.
   * La navigation est cote client (pas de rechargement complet).
   */
  test('workspace — lister les bases de connaissances', async ({ page }) => {
    await page.goto('/workspace/knowledge');

    // Attendre que la page charge et affiche du contenu
    await expect(page.locator('body')).toBeVisible({ timeout: 15_000 });

    // EXERCICE : Verifiez qu'au moins une knowledge base est listee
    // Indice : Cherchez un element contenant le nom d'une KB connue
  });

  /**
   * TEST 5 : Parcourir le Workspace — Modeles custom
   *
   * Open WebUI permet de creer des "personas" : des modeles
   * avec des instructions systeme et des parametres personnalises.
   */
  test('workspace — lister les modeles personnalises', async ({ page }) => {
    await page.goto('/workspace/models');

    await expect(
      page.getByText('Modèles').or(page.getByText('Models')).first()
    ).toBeVisible({ timeout: 15_000 });

    // EXERCICE : Cliquez sur un modele pour voir ses details
  });

  /**
   * TEST 6 : Parcourir le Workspace — Prompts sauvegardes
   */
  test('workspace — lister les prompts', async ({ page }) => {
    await page.goto('/workspace/prompts');

    await expect(
      page.getByText('Prompts').first()
    ).toBeVisible({ timeout: 15_000 });
  });

  /**
   * TEST 7 : Parcourir le Workspace — Fonctions installees
   *
   * Open WebUI supporte des "fonctions" (plugins) : filtres,
   * actions, outils. Elles sont gerees par l'admin.
   */
  test('workspace — lister les fonctions', async ({ page }) => {
    await page.goto('/admin/functions');

    await expect(
      page.getByText('Fonctions').or(page.getByText('Functions')).first()
    ).toBeVisible({ timeout: 15_000 });
  });

  /**
   * TEST 8 : Naviguer vers les canaux (Channels)
   *
   * Les canaux sont des espaces de discussion de groupe,
   * similaires a Slack/Discord.
   */
  test('acceder a la section Channels', async ({ page }) => {
    await page.goto('/');
    await dismissModals(page);
    await expect(page.locator(MODEL.selectorButton)).toBeVisible({ timeout: 15_000 });

    // Essayer de trouver le lien Channels dans la navigation
    const channelsLink = page.getByRole('link', { name: /channels|canaux/i }).first();
    if (await channelsLink.isVisible({ timeout: 5_000 }).catch(() => false)) {
      await channelsLink.click();
      await expect(page).toHaveURL(/channel/i, { timeout: 10_000 });
    } else {
      // Navigation directe si le lien n'est pas visible
      await page.goto('/channels');
      await expect(page.locator('body')).toBeVisible({ timeout: 15_000 });
    }
  });
});
