# Module 05 - Multi-tenant, API Testing & CI/CD

> **Format** : deux artefacts. Le fichier TypeScript `05-api-multi-tenant.spec.ts` (tests commentés) est le **moteur de test** ; le notebook `05-Multi-Tenant-CI-QA-OWUI.ipynb` (section ci-dessous) en est la **couche pédagogique**. Ouvrez le `.spec.ts` dans VS Code. Ce module utilise l'API REST (pas le navigateur) pour la plupart des tests. Configurez `OWUI_TENANT2_*` dans `.env` pour activer les tests multi-tenant.

## Objectifs pédagogiques

À la fin de ce module, vous serez capable de :

- Tester des APIs REST directement avec Playwright (sans navigateur)
- Comprendre l'architecture multi-tenant d'Open WebUI
- Vérifier l'isolation des données entre tenants
- Valider le partage de ressources (KBs, modèles) entre instances
- Intégrer les tests Playwright dans un pipeline CI/CD

## Durée estimée

**3 à 4 heures**

## Contenu du module

### Partie théorique

**Tests API vs Tests UI :**
Playwright n'est pas limité aux interactions navigateur.
Sa classe `APIRequestContext` permet de faire des requêtes HTTP directes.

```typescript
// Test UI (lent, mais teste l'expérience utilisateur)
await page.goto('/admin');
await expect(page.getByText('Users')).toBeVisible();

// Test API (rapide, teste les données et la logique métier)
const response = await request.get('/api/v1/users');
const users = await response.json();
expect(users.length).toBeGreaterThan(0);
```

**Quand utiliser l'API vs le navigateur :**

| Scénario | Approche |
|----------|----------|
| Vérifier un rendu visuel | Navigateur (page) |
| Comparer des données entre instances | API (request) |
| Tester l'authentification | Les deux |
| Vérifier la performance | API + metrics |

**Architecture multi-tenant :**
Chaque "tenant" est une instance indépendante d'Open WebUI :
- Base de données PostgreSQL séparée
- Configuration indépendante (modèles, fonctions, users)
- Certaines ressources partagées (KBs via Qdrant, modèles LLM)

### Partie pratique

| Test | Description | Concepts |
|------|-------------|----------|
| Auth API | Login via API, obtenir un token JWT | `request.post()`, JWT |
| Modèles API | Lister les modèles via API | `request.get()`, headers |
| KBs API | Lister les knowledge bases via API | Pagination API |
| Multi-tenant auth | Authentification sur deux instances | Isolation |
| KB partagées | Vérifier le partage de KBs | Comparison cross-tenant |
| Modèles identiques | Vérifier la parité des modèles | Assertions en boucle |
| Isolation données | Vérifier l'isolation des users | Sécurité multi-tenant |

## Couche pédagogique (notebook)

Le notebook [`05-Multi-Tenant-CI-QA-OWUI.ipynb`](05-Multi-Tenant-CI-QA-OWUI.ipynb) est la cinquième et dernière étape de la mission (voir le notebook chapeau [`00-Parcours-QA-OWUI.ipynb`](../00-Parcours-QA-OWUI.ipynb)). Il quitte le navigateur pour l'API REST, explique l'architecture multi-tenant (isolation et partage des données entre tenants) et ouvre sur l'industrialisation CI/CD. Il lit `05-api-multi-tenant.spec.ts`, en dresse l'inventaire (`npx playwright test --list`, sans exécution) et propose des exercices en Python : décodage du payload d'un JWT, modèles présents sur un tenant et absents de l'autre, choix entre API et navigateur. Il explique aussi comment lire un rapport où la seconde partie du module (05b) est sautée sur une instance mono-tenant.

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
2. **Retries** : Activer 1-2 retries en CI (réseaux instables)
3. **Rapports** : Toujours uploader le rapport HTML comme artefact
4. **Timeouts** : Augmenter les timeouts en CI (machines plus lentes)
5. **Screenshots** : `only-on-failure` pour le débogage post-mortem
