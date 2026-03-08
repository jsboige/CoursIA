/**
 * Client API pour interagir directement avec le backend Open WebUI.
 *
 * QUAND UTILISER L'API vs LE NAVIGATEUR ?
 * ========================================
 * - Navigateur (page.*) : Tester l'experience utilisateur, le rendu, les interactions
 * - API (request.*) : Verifier les donnees, preparer l'etat, tests multi-tenant
 *
 * L'API est plus rapide et plus fiable pour les assertions sur les donnees.
 * Le navigateur est indispensable pour tester le comportement visuel.
 *
 * ENDPOINTS PRINCIPAUX (Open WebUI v0.8.x) :
 * - POST /api/v1/auths/signin → { token: "jwt..." }
 * - GET  /api/models → { data: [{ id, name }] }
 * - GET  /api/v1/knowledge → { items: [{ id, name }] }
 * - GET  /api/v1/users → { users: [{ id, name, email, role }] }
 * - GET  /api/v1/functions → [{ id, name, type }]
 */
import { type APIRequestContext } from '@playwright/test';

/**
 * Authentification via l'API — retourne un token JWT.
 */
export async function apiLogin(
  request: APIRequestContext,
  baseUrl: string,
  email: string,
  password: string,
): Promise<string> {
  const response = await request.post(`${baseUrl}/api/v1/auths/signin`, {
    data: { email, password },
  });
  if (!response.ok()) {
    throw new Error(`Login failed (${response.status()}): ${await response.text()}`);
  }
  const body = await response.json();
  return body.token;
}

/**
 * Recupere la liste des modeles visibles pour l'utilisateur connecte.
 */
export async function getModels(
  request: APIRequestContext,
  baseUrl: string,
  token: string,
): Promise<Array<{ id: string; name: string }>> {
  const response = await request.get(`${baseUrl}/api/models`, {
    headers: { Authorization: `Bearer ${token}` },
  });
  if (!response.ok()) {
    throw new Error(`Failed to fetch models: ${response.status()}`);
  }
  const body = await response.json();
  return body.data || body;
}

/**
 * Recupere la liste des bases de connaissances (Knowledge Bases).
 */
export async function getKnowledgeBases(
  request: APIRequestContext,
  baseUrl: string,
  token: string,
): Promise<Array<{ id: string; name: string; description: string }>> {
  const response = await request.get(`${baseUrl}/api/v1/knowledge`, {
    headers: { Authorization: `Bearer ${token}` },
  });
  if (!response.ok()) {
    throw new Error(`Failed to fetch KBs: ${response.status()}`);
  }
  const body = await response.json();
  return body.items || body;
}

/**
 * Recupere la liste des utilisateurs (admin uniquement).
 */
export async function getUsers(
  request: APIRequestContext,
  baseUrl: string,
  token: string,
): Promise<Array<{ id: string; name: string; email: string; role: string }>> {
  const response = await request.get(`${baseUrl}/api/v1/users`, {
    headers: { Authorization: `Bearer ${token}` },
  });
  if (!response.ok()) {
    throw new Error(`Failed to fetch users: ${response.status()}`);
  }
  const body = await response.json();
  return body.users || body;
}

/**
 * Recupere la liste des fonctions/outils installes.
 */
export async function getFunctions(
  request: APIRequestContext,
  baseUrl: string,
  token: string,
): Promise<Array<{ id: string; name: string; type: string }>> {
  const response = await request.get(`${baseUrl}/api/v1/functions`, {
    headers: { Authorization: `Bearer ${token}` },
  });
  if (!response.ok()) {
    throw new Error(`Failed to fetch functions: ${response.status()}`);
  }
  return await response.json();
}
