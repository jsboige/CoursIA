# Module 05 - Multi-tenant, API Testing & CI/CD

> **Format** : Fichier TypeScript `.spec.ts` avec tests commentes. Ouvrez `05-api-multi-tenant.spec.ts` dans VS Code. Ce module utilise l'API REST (pas le navigateur) pour la plupart des tests. Configurez `OWUI_TENANT2_*` dans `.env` pour activer les tests multi-tenant.

## Objectifs pedagogiques

A la fin de ce module, vous serez capable de :

- Tester des APIs REST directement avec Playwright (sans navigateur)
- Comprendre l'architecture multi-tenant d'Open WebUI
- Verifier l'isolation des donnees entre tenants
- Valider le partage de ressources (KBs, modeles) entre instances
- Integrer les tests Playwright dans un pipeline CI/CD

## Duree estimee

**3 a 4 heures**

## Contenu du module

### Partie theorique

**Tests API vs Tests UI :**
Playwright n'est pas limite aux interactions navigateur.
Sa classe `APIRequestContext` permet de faire des requetes HTTP directes.

```typescript
// Test UI (lent, mais teste l'experience utilisateur)
await page.goto('/admin');
await expect(page.getByText('Users')).toBeVisible();

// Test API (rapide, teste les donnees et la logique metier)
const response = await request.get('/api/v1/users');
const users = await response.json();
expect(users.length).toBeGreaterThan(0);
```

**Quand utiliser l'API vs le navigateur :**
| Scenario | Approche |
|----------|----------|
| Verifier un rendu visuel | Navigateur (page) |
| Comparer des donnees entre instances | API (request) |
| Tester l'authentification | Les deux |
| Verifier la performance | API + metrics |

**Architecture multi-tenant :**
Chaque "tenant" est une instance independante d'Open WebUI :
- Base de donnees PostgreSQL separee
- Configuration independante (modeles, fonctions, users)
- Certaines ressources partagees (KBs via Qdrant, modeles LLM)

### Partie pratique

| Test | Description | Concepts |
|------|-------------|----------|
| Auth API | Login via API, obtenir un token JWT | `request.post()`, JWT |
| Modeles API | Lister les modeles via API | `request.get()`, headers |
| KBs API | Lister les knowledge bases via API | Pagination API |
| Multi-tenant auth | Authentification sur deux instances | Isolation |
| KB partagees | Verifier le partage de KBs | Comparison cross-tenant |
| Modeles identiques | Verifier la parite des modeles | Assertions en boucle |
| Isolation donnees | Verifier l'isolation des users | Securite multi-tenant |

## Commandes

```bash
npm run test:module5
npx playwright test --grep "05" --headed
```

## Pour aller plus loin : CI/CD

### GitHub Actions

```yaml
# .github/workflows/e2e-tests.yml
name: E2E Tests
on: [push, pull_request]
jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: actions/setup-node@v4
        with:
          node-version: 20
      - run: npm ci
      - run: npx playwright install --with-deps chromium
      - run: npx playwright test
        env:
          OWUI_URL: ${{ secrets.OWUI_URL }}
          OWUI_EMAIL: ${{ secrets.OWUI_EMAIL }}
          OWUI_PASSWORD: ${{ secrets.OWUI_PASSWORD }}
      - uses: actions/upload-artifact@v4
        if: always()
        with:
          name: playwright-report
          path: playwright-report/
```

### Bonnes pratiques CI/CD

1. **Secrets** : Ne jamais hardcoder les credentials — utiliser les secrets CI
2. **Retries** : Activer 1-2 retries en CI (reseaux instables)
3. **Rapports** : Toujours uploader le rapport HTML comme artefact
4. **Timeouts** : Augmenter les timeouts en CI (machines plus lentes)
5. **Screenshots** : `only-on-failure` pour le debogage post-mortem
