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
import { MODEL, AUTH, SETTINGS } from '../helpers/selectors';
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
   * CONCEPT : un test qui passe n'est pas forcement un test JUSTE.
   *
   * Jusqu'a la v0.10, /admin/settings etait une PAGE, avec un lien "Reglages"
   * dans sa navigation. On assertait donc :
   *
   *     page.getByRole('link', { name: /réglages|settings/i }).first()
   *
   * La v0.11 a refondu l'interface : les reglages sont devenus des ONGLETS
   * (role=tab) dans une fenetre unique, et /admin/settings REDIRIGE vers /.
   *
   * Le piege : cette ancienne assertion continuait de passer par moments.
   * Mesure firsthand (2026-08-07, instance de cours en v0.11.0) :
   *
   *     t=4.3s  goto termine, url=/admin/settings, 0 correspondance
   *     t=7.5s  <a href="/admin/settings">Reglages</a> APPARAIT (vestige)
   *     t=10.7s l'app redirige vers /, le lien DISPARAIT
   *
   * L'ancienne assertion attrapait donc une fenetre transitoire d'environ 3
   * secondes : verte sur une machine, rouge sur une autre (c'est exactement ce
   * qui s'est produit entre deux suites lancees contre le MEME serveur).
   * C'est un FAUX VERT — la pire categorie de test, car il ne signale rien.
   *
   * La regle : asserter l'etat STABILISE, jamais un etat de passage.
   * Ici, on attend la redirection puis on cible un onglet d'administration.
   *
   * PIEGE (mode strict) : l'onglet "General" existe dans les deux groupes
   * (utilisateur ET admin) -> 2 correspondances -> "strict mode violation".
   * On vise "Authentification", qui n'existe que cote admin.
   */
  test('acceder aux reglages admin', async ({ page }) => {
    await page.goto('/admin/settings');

    // 1. Attendre l'etat STABILISE : la v0.11 redirige vers / en ouvrant la
    //    fenetre de reglages. On tolere l'absence de redirection (versions
    //    anterieures) pour que le test reste lisible sur une instance v0.10.
    await page.waitForURL((url) => !url.pathname.startsWith('/admin/settings'), {
      timeout: 30_000,
    }).catch(() => {});

    // 2. Asserter un onglet propre a l'administration (1 seule correspondance).
    await expect(
      page.getByRole('tab', { name: SETTINGS.adminAuthTab })
    ).toBeVisible({ timeout: 15_000 });

    // EXERCICE : verifiez que getByRole('tab', { name: /^général$/i }) renvoie
    // DEUX elements, et expliquez pourquoi .first() est alors obligatoire.
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
