# Explorer une longue conversation / un export ChatGPT via Playwright (lecture par tranches)

**Problème.** Une conversation ChatGPT stratégique longue (audit, discussion vocale transcrite) fait souvent
plusieurs dizaines de milliers de tokens. Un `browser_snapshot` unique, un `Read` du HTML exporté, ou un
copier-coller intégral **déborde le contexte** et écrase le reste de la session. Il faut la lire **par tranches
bornées**, en ne ramenant que le texte utile (jamais le HTML brut, très coûteux en tokens).

**Principe.** Ouvrir la conversation dans le navigateur Playwright, **compter d'abord** le nombre de tours, puis
**paginer** : extraire les tours `[i .. i+k]` en `innerText` seul, un appel `browser_evaluate` par tranche. On
digère tranche par tranche (résumé incrémental) au lieu de tout charger d'un coup.

## Source de la conversation

Trois cas selon ce que fournit le user :
- **Lien de partage** `https://chatgpt.com/share/<uuid>` → `browser_navigate` directement dessus (rendu statique, pas d'auth).
- **Export de données** (`chat.html` / `conversations.json` du zip « Export data ») → ouvrir le HTML local :
  `browser_navigate` vers `file:///D:/.../chat.html` (Playwright peut charger `file://`).
- **Conversation live** (chatgpt.com/c/<uuid>, nécessite la session loggée du user) → n'utiliser que si le user
  a déjà une fenêtre authentifiée ; sinon préférer le lien de partage.

## Étape 1 — compter les tours (une seule fois)

ChatGPT rend chaque tour comme un élément portant `data-message-author-role` (`user` / `assistant`), souvent
dans un conteneur `[data-testid^="conversation-turn"]`. Sélecteur robuste (fallback en cascade) :

```js
// browser_evaluate — retourne juste le compte + un aperçu des rôles
() => {
  const nodes = document.querySelectorAll('[data-message-author-role]');
  const turns = nodes.length
    ? [...nodes]
    : [...document.querySelectorAll('[data-testid^="conversation-turn"]')];
  return {
    total: turns.length,
    roles: turns.slice(0, 8).map(n => n.getAttribute('data-message-author-role') || '?'),
  };
}
```

Si `total` est 0, la page n'est pas encore rendue (SPA) → `browser_wait_for({ time: 2 })` puis relancer, ou
scroller pour forcer le lazy-render (voir Étape 3).

## Étape 2 — extraire une tranche `[start .. start+count)`

Un appel par tranche. **`innerText` uniquement** (pas `outerHTML`). Garder `count` petit (4–6 tours) pour rester
sous ~2–3k tokens par tranche.

```js
// browser_evaluate({ function: `(...) ...` })  — paramétrer start/count en éditant les 2 constantes
() => {
  const START = 0, COUNT = 5;
  const nodes = document.querySelectorAll('[data-message-author-role]');
  const turns = nodes.length
    ? [...nodes]
    : [...document.querySelectorAll('[data-testid^="conversation-turn"]')];
  return turns.slice(START, START + COUNT).map((n, i) => ({
    idx: START + i,
    role: n.getAttribute('data-message-author-role') || '?',
    text: (n.innerText || '').trim().slice(0, 6000), // borne dure par tour
  }));
}
```

Puis itérer : `START = 0`, `5`, `10`, … jusqu'à `total`. Résumer chaque tranche avant de charger la suivante
(digestion incrémentale — c'est ce qui évite l'explosion de contexte).

## Étape 3 — pages qui lazy-load (virtualisation)

Certaines vues ne montent dans le DOM que les tours visibles. Si `total` plafonne sous le vrai nombre, forcer le
rendu en scrollant par pas avant de re-compter :

```js
() => { window.scrollTo(0, document.body.scrollHeight); return document.body.scrollHeight; }
```

Alterner scroll + `browser_wait_for({ time: 1 })` jusqu'à stabilisation de `scrollHeight`, puis Étape 1/2.
Pour un export HTML statique (cas le plus fréquent), tout le DOM est présent d'emblée — pas de scroll nécessaire.

## Alternative sans navigateur (export JSON)

Si le user fournit `conversations.json` (export de données), **pas besoin de Playwright** : c'est un fichier
local. Extraire par tranches en shell plutôt qu'en chargeant tout :

```bash
# nombre de messages
jq '.[0].mapping | length' conversations.json
# titres des conversations
jq -r '.[] | .title' conversations.json
# messages d'une conversation, texte seul, par tranche (ex. 0..20)
jq -r '[.[0].mapping[] | select(.message) | .message.content.parts[]?] | .[0:20][]' conversations.json
```

Préférer le JSON quand il est disponible : plus fiable et scriptable que le DOM rendu.

## Checklist d'usage

- [ ] Compter d'abord (`total`), ne jamais deviner la longueur.
- [ ] `innerText` seul, jamais `outerHTML` ; borne dure par tour (`.slice(0, 6000)`).
- [ ] Tranches de 4–6 tours ; résumer avant la tranche suivante.
- [ ] Lien de partage > conversation live (pas d'auth) ; export JSON > DOM quand dispo.
- [ ] `browser_close` en fin d'exploration.

## Contexte

Méthode utilisée pour la consolidation planification ICT (Epic #4588) depuis les transcripts stratégiques du
user. Mémoire liée : `chatgpt-export-playwright-method`, `ict-transcript-planning-2026-07-19`.
