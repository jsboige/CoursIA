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
  // IMPORTANT: trailing slash required — IIS reverse proxy redirects to SvelteKit HTML without it
  const response = await request.get(`${baseUrl}/api/v1/knowledge/`, {
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
  // IMPORTANT: trailing slash required — IIS reverse proxy redirects to SvelteKit HTML without it
  const response = await request.get(`${baseUrl}/api/v1/functions/`, {
    headers: { Authorization: `Bearer ${token}` },
  });
  if (!response.ok()) {
    throw new Error(`Failed to fetch functions: ${response.status()}`);
  }
  // L'API peut retourner du HTML si redirigee par le reverse proxy
  const text = await response.text();
  if (text.startsWith('<!') || text.startsWith('<html')) {
    throw new Error('Functions API returned HTML instead of JSON (reverse proxy issue)');
  }
  return JSON.parse(text);
}

/**
 * Recupere la liste des channels (canaux de discussion).
 */
export async function getChannels(
  request: APIRequestContext,
  baseUrl: string,
  token: string,
): Promise<Array<{ id: string; name: string; description: string }>> {
  // IMPORTANT: trailing slash required — IIS reverse proxy redirects to SvelteKit HTML without it
  const response = await request.get(`${baseUrl}/api/v1/channels/`, {
    headers: { Authorization: `Bearer ${token}` },
  });
  if (!response.ok()) {
    throw new Error(`Failed to fetch channels: ${response.status()}`);
  }
  const body = await response.json();
  return body.items || body;
}

// =====================================================================
// Nouveautes v0.10 — Memoire & Dossiers (utilises par le module 06)
// =====================================================================

/**
 * Un souvenir (memory). Depuis la refonte memoire v0.10, chaque souvenir
 * porte un `type` ("context" = long terme, ou lie a une conversation) et un
 * `path` optionnel — deux champs qui n'existaient PAS avant v0.10.
 */
export interface Memory {
  id: string;
  content: string;
  type?: string;
  path?: string | null;
  created_at?: number;
  updated_at?: number;
}

/**
 * Liste les souvenirs (memories) de l'utilisateur connecte.
 * Fonctionnalite stabilisee en v0.10 (Memories sort officiellement de beta).
 */
export async function getMemories(
  request: APIRequestContext,
  baseUrl: string,
  token: string,
): Promise<Memory[]> {
  // IMPORTANT: trailing slash required — IIS reverse proxy redirects to SvelteKit HTML without it
  const response = await request.get(`${baseUrl}/api/v1/memories/`, {
    headers: { Authorization: `Bearer ${token}` },
  });
  if (!response.ok()) {
    throw new Error(`Failed to fetch memories: ${response.status()}`);
  }
  return await response.json();
}

/**
 * Ajoute un souvenir. La reponse inclut le champ `type` (nouveaute v0.10),
 * "context" par defaut.
 *
 * ATTENTION : les souvenirs sont injectes dans les prompts du modele. En test,
 * TOUJOURS nettoyer avec deleteMemory() ensuite — surtout sur une instance
 * partagee, pour ne pas polluer les conversations reelles.
 */
export async function addMemory(
  request: APIRequestContext,
  baseUrl: string,
  token: string,
  content: string,
): Promise<Memory> {
  const response = await request.post(`${baseUrl}/api/v1/memories/add`, {
    headers: { Authorization: `Bearer ${token}` },
    data: { content },
  });
  if (!response.ok()) {
    throw new Error(`Failed to add memory: ${response.status()}`);
  }
  return await response.json();
}

/**
 * Supprime un souvenir par son id. Retourne true si la suppression a reussi.
 */
export async function deleteMemory(
  request: APIRequestContext,
  baseUrl: string,
  token: string,
  memoryId: string,
): Promise<boolean> {
  const response = await request.delete(`${baseUrl}/api/v1/memories/${memoryId}`, {
    headers: { Authorization: `Bearer ${token}` },
  });
  return response.ok();
}

/**
 * Un dossier (folder). Les dossiers d'equipe v0.10 peuvent etre partages avec
 * des permissions lecture/ecriture pour des utilisateurs ou des groupes.
 */
export interface Folder {
  id: string;
  name: string;
  parent_id?: string | null;
  items?: unknown;
  meta?: unknown;
  data?: unknown;
}

/**
 * Liste les dossiers de l'utilisateur connecte.
 */
export async function getFolders(
  request: APIRequestContext,
  baseUrl: string,
  token: string,
): Promise<Folder[]> {
  // IMPORTANT: trailing slash required — IIS reverse proxy redirects to SvelteKit HTML without it
  const response = await request.get(`${baseUrl}/api/v1/folders/`, {
    headers: { Authorization: `Bearer ${token}` },
  });
  if (!response.ok()) {
    throw new Error(`Failed to fetch folders: ${response.status()}`);
  }
  return await response.json();
}

/**
 * Cree un dossier. En test, penser a le supprimer (deleteFolder) ensuite.
 */
export async function createFolder(
  request: APIRequestContext,
  baseUrl: string,
  token: string,
  name: string,
): Promise<Folder> {
  // IMPORTANT: trailing slash required — IIS reverse proxy redirects to SvelteKit HTML without it
  const response = await request.post(`${baseUrl}/api/v1/folders/`, {
    headers: { Authorization: `Bearer ${token}` },
    data: { name },
  });
  if (!response.ok()) {
    throw new Error(`Failed to create folder: ${response.status()}`);
  }
  return await response.json();
}

/**
 * Supprime un dossier par son id. Retourne true si la suppression a reussi.
 */
export async function deleteFolder(
  request: APIRequestContext,
  baseUrl: string,
  token: string,
  folderId: string,
): Promise<boolean> {
  const response = await request.delete(`${baseUrl}/api/v1/folders/${folderId}`, {
    headers: { Authorization: `Bearer ${token}` },
  });
  return response.ok();
}
