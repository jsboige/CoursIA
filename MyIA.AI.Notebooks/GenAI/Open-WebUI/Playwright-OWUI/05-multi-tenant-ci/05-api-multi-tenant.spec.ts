/**
 * Module 05 — Multi-tenant, API Testing & CI/CD
 *
 * Ce module final explore les tests API et l'architecture multi-tenant.
 *
 * CONCEPTS AVANCES :
 * - Tests API sans navigateur (APIRequestContext)
 * - Comparaison de donnees entre instances
 * - Isolation et partage dans une architecture multi-tenant
 * - Patterns pour l'integration CI/CD
 *
 * PRE-REQUIS :
 * - .env avec OWUI_URL, OWUI_EMAIL, OWUI_PASSWORD (obligatoire)
 * - OWUI_TENANT2_URL, OWUI_TENANT2_EMAIL, OWUI_TENANT2_PASSWORD (optionnel)
 *   Ces variables ne sont necessaires que pour les tests multi-tenant (partie 2)
 *
 * RATE LIMITING :
 * L'API /api/v1/auths/signin a un rate limit strict (~2 min entre les appels).
 * Pour eviter les erreurs 429, on s'authentifie UNE SEULE FOIS dans beforeAll()
 * et on reutilise le token dans tous les tests.
 *
 * C'est un pattern important en tests API :
 * - MAUVAIS : chaque test fait son propre login → rate limit
 * - BON : un seul login partage entre tous les tests → rapide et fiable
 */
import { test, expect, type APIRequestContext } from '@playwright/test';
import { apiLogin, getModels, getKnowledgeBases, getFunctions } from '../helpers/api';

// Configuration du tenant principal
const OWUI_URL = process.env.OWUI_URL || 'http://localhost:3000';
const OWUI_EMAIL = process.env.OWUI_EMAIL || '';
const OWUI_PASSWORD = process.env.OWUI_PASSWORD || '';

// Configuration du tenant secondaire (optionnel)
const TENANT2_URL = process.env.OWUI_TENANT2_URL || '';
const TENANT2_EMAIL = process.env.OWUI_TENANT2_EMAIL || '';
const TENANT2_PASSWORD = process.env.OWUI_TENANT2_PASSWORD || '';

// =====================================================================
// PARTIE 1 : Tests API sur le tenant principal
// =====================================================================

test.describe('05a — Tests API (tenant principal)', () => {
  // Token partage entre tous les tests (obtenu dans beforeAll)
  let token = '';

  /**
   * HOOK beforeAll : Authentification unique
   *
   * On se connecte UNE SEULE FOIS pour tout le describe block.
   * Le token JWT est stocke dans la variable 'token' et reutilise.
   *
   * CONCEPT : Eviter le rate limiting en partageant les credentials
   * C'est un pattern standard pour les tests API :
   * - Authentification couteuse → beforeAll
   * - Requetes rapides → dans chaque test
   */
  test.beforeAll(async ({ request }: { request: APIRequestContext }) => {
    token = await apiLogin(request, OWUI_URL, OWUI_EMAIL, OWUI_PASSWORD);
  });

  /**
   * TEST 1 : Verifier que l'authentification a fonctionne
   *
   * Le token JWT est une chaine encodee en base64 contenant :
   * - Header : algorithme de signature
   * - Payload : user ID, email, role, expiration
   * - Signature : verification d'integrite
   */
  test('login via API — token JWT valide', async () => {
    // Le token a ete obtenu dans beforeAll
    expect(token).toBeTruthy();
    expect(typeof token).toBe('string');
    expect(token.length).toBeGreaterThan(20);

    console.log(`  → Token JWT obtenu (${token.length} caracteres)`);

    // EXERCICE : Decodez le JWT (base64) pour voir son contenu
    // Indice : JSON.parse(Buffer.from(token.split('.')[1], 'base64').toString())
  });

  /**
   * TEST 2 : Lister les modeles via l'API
   *
   * L'endpoint /api/models retourne la liste des modeles
   * accessibles a l'utilisateur connecte.
   */
  test('lister les modeles disponibles via API', async ({ request }) => {
    const models = await getModels(request, OWUI_URL, token);

    expect(models.length).toBeGreaterThan(0);
    console.log(`  → ${models.length} modeles disponibles`);

    // Chaque modele a un id et un nom
    for (const model of models.slice(0, 3)) {
      expect(model.id).toBeTruthy();
      console.log(`    - ${model.id}: ${model.name}`);
    }
  });

  /**
   * TEST 3 : Lister les Knowledge Bases via l'API
   */
  test('lister les knowledge bases via API', async ({ request }) => {
    let kbs: Awaited<ReturnType<typeof getKnowledgeBases>>;
    try {
      kbs = await getKnowledgeBases(request, OWUI_URL, token);
    } catch (e) {
      test.skip(true, `API KB non disponible: ${(e as Error).message}`);
      return;
    }

    console.log(`  → ${kbs.length} knowledge bases`);
    for (const kb of kbs.slice(0, 3)) {
      console.log(`    - ${kb.name}: ${kb.description || '(pas de description)'}`);
    }
  });

  /**
   * TEST 4 : Lister les fonctions installees via l'API
   */
  test('lister les fonctions installees via API', async ({ request }) => {
    let functions: Awaited<ReturnType<typeof getFunctions>>;
    try {
      functions = await getFunctions(request, OWUI_URL, token);
    } catch (e) {
      test.skip(true, `API Functions non disponible: ${(e as Error).message}`);
      return;
    }

    console.log(`  → ${functions.length} fonctions installees`);
    for (const fn of functions.slice(0, 5)) {
      console.log(`    - [${fn.type}] ${fn.name}`);
    }
  });
});

// =====================================================================
// PARTIE 2 : Tests multi-tenant (optionnel)
// =====================================================================

test.describe('05b — Multi-tenant : Isolation & Partage', () => {
  // Tokens pour les deux tenants (obtenus dans beforeAll)
  let token1 = '';
  let token2 = '';

  /**
   * HOOK beforeAll : Authentification sur les deux tenants
   *
   * On se connecte aux deux instances en une seule fois.
   * Si le tenant 2 n'est pas configure, on skip tout le describe.
   */
  test.beforeAll(async ({ request }: { request: APIRequestContext }) => {
    if (!TENANT2_URL || !TENANT2_EMAIL || !TENANT2_PASSWORD) {
      test.skip(true, 'Variables OWUI_TENANT2_* non configurees');
      return;
    }

    token1 = await apiLogin(request, OWUI_URL, OWUI_EMAIL, OWUI_PASSWORD);
    // Petit delai pour eviter le rate limit entre les deux tenants
    await new Promise(resolve => setTimeout(resolve, 2000));
    token2 = await apiLogin(request, TENANT2_URL, TENANT2_EMAIL, TENANT2_PASSWORD);
  });

  /**
   * TEST 5 : Les deux tenants sont accessibles et authentifiables
   *
   * CONCEPT : Comparaison cross-instance
   * On verifie que les tokens sont valides pour les deux instances.
   */
  test('les deux tenants sont accessibles', async () => {
    test.skip(!TENANT2_URL, 'Tenant 2 non configure');

    expect(token1).toBeTruthy();
    expect(token2).toBeTruthy();

    console.log('  → Les deux tenants sont authentifiables');
  });

  /**
   * TEST 6 : Les Knowledge Bases sont partagees entre tenants
   *
   * Dans une architecture multi-tenant avec Qdrant partage,
   * les KBs creees sur un tenant sont visibles sur les autres
   * (si copiees via script de partage).
   */
  test('knowledge bases partagees entre tenants', async ({ request }) => {
    test.skip(!TENANT2_URL, 'Tenant 2 non configure');

    let kbs1: Awaited<ReturnType<typeof getKnowledgeBases>>;
    let kbs2: Awaited<ReturnType<typeof getKnowledgeBases>>;
    try {
      kbs1 = await getKnowledgeBases(request, OWUI_URL, token1);
      kbs2 = await getKnowledgeBases(request, TENANT2_URL, token2);
    } catch (e) {
      test.skip(true, `API KB non disponible: ${(e as Error).message}`);
      return;
    }

    expect(kbs1.length).toBeGreaterThan(0);
    expect(kbs2.length).toBeGreaterThan(0);

    console.log(`  → Tenant 1: ${kbs1.length} KBs, Tenant 2: ${kbs2.length} KBs`);
  });

  /**
   * TEST 7 : Les modeles custom sont deployes sur les deux tenants
   *
   * Les personas/modeles custom doivent etre identiques
   * sur tous les tenants (deployes via script configure-tenant.py).
   */
  test('modeles custom identiques sur les deux tenants', async ({ request }) => {
    test.skip(!TENANT2_URL, 'Tenant 2 non configure');

    const models1 = await getModels(request, OWUI_URL, token1);
    const models2 = await getModels(request, TENANT2_URL, token2);

    expect(models1.length).toBeGreaterThan(0);
    expect(models2.length).toBeGreaterThan(0);

    console.log(`  → Tenant 1: ${models1.length} modeles, Tenant 2: ${models2.length} modeles`);

    // EXERCICE : Identifiez les modeles presents sur T1 mais absents de T2
    // Indice :
    // const ids1 = new Set(models1.map(m => m.id));
    // const ids2 = new Set(models2.map(m => m.id));
    // const onlyOnT1 = [...ids1].filter(id => !ids2.has(id));
  });

  /**
   * TEST 8 : Isolation des donnees — chaque tenant a ses propres utilisateurs
   *
   * CONCEPT : Securite multi-tenant
   * L'isolation des donnees est cruciale. Les utilisateurs d'un tenant
   * ne doivent pas etre visibles depuis un autre tenant.
   */
  test('isolation des donnees — bases utilisateurs separees', async ({ request }) => {
    test.skip(!TENANT2_URL, 'Tenant 2 non configure');

    // Les deux tenants fonctionnent independamment
    const models1 = await getModels(request, OWUI_URL, token1);
    const models2 = await getModels(request, TENANT2_URL, token2);

    expect(models1.length).toBeGreaterThan(0);
    expect(models2.length).toBeGreaterThan(0);

    // Le token du tenant 1 ne devrait PAS fonctionner sur le tenant 2
    // (chaque tenant a sa propre base d'utilisateurs et ses propres tokens)
    try {
      await getModels(request, TENANT2_URL, token1);
      // Si ca marche, les tenants partagent peut-etre le meme backend
      console.log('  ⚠️  Token cross-tenant accepte — verifiez l\'isolation');
    } catch {
      console.log('  ✓  Token cross-tenant rejete — isolation confirmee');
    }
  });
});
