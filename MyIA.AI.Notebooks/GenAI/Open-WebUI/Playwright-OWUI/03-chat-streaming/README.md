# Module 03 - Tests de Chat & Streaming LLM

> **Format** : Fichier TypeScript `.spec.ts` avec tests commentés. Ouvrez `03-chat-streaming.spec.ts` dans VS Code. C'est le module le plus riche — il couvre les defis uniques du test d'applications d'IA générative.

## Objectifs pédagogiques

A la fin de ce module, vous serez capable de :

- Tester une interface de chat avec un éditeur rich text (TipTap)
- Gérer le streaming de réponses LLM (tokens progressifs)
- Implementer des patterns d'attente adaptes aux IA génératives
- Écrire des assertions sur du contenu généré par IA (non deterministe)
- Utiliser `test.skip()` pour gérer les services indisponibles

## Durée estimée

**3 heures**

## Contenu du module

### Partie théorique

**Le defi du test E2E avec des LLMs :**
Tester une application d'IA générative pose des defis uniques :

1. **Non-determinisme** : Le même prompt peut donner des réponses differentes
2. **Latence variable** : De 2s (GPT-4.1-mini) a 2min (modèle local en reflexion)
3. **Streaming** : Les tokens arrivent progressivement, le DOM change en continu
4. **Disponibilite** : Les services LLM peuvent être temporairement indisponibles

**Solutions implementees :**
- Assertions souples : `toContain('hello')` au lieu de `toBe('Hello from GPT')`
- Timeouts généreux : 120s par test, polling toutes les secondes
- Skip gracieux : `test.skip(!response, 'Service indisponible')`
- Helper `waitForResponse()` : Attend que le contenu soit stable

**L'éditeur TipTap :**
Open WebUI utilise TipTap (un éditeur ProseMirror) au lieu d'un `<textarea>`.
Consequence : `fill()` ne fonctionne pas ! Il faut utiliser `keyboard.type()`.

```typescript
// FAUX — ne declenche pas les evenements TipTap
await page.locator('#chat-input').fill('Bonjour');

// CORRECT — simule une vraie saisie clavier
await page.locator('#chat-input').click();
await page.keyboard.type('Bonjour', { delay: 10 });
await page.keyboard.press('Enter');
```

### Partie pratique

| Test | Description | Concepts |
|------|-------------|----------|
| Chat cloud | Envoyer un message a un modèle cloud | `keyboard.type()`, TipTap |
| Chat local | Tester un modèle local (vLLM) | `test.skip()`, resilience |
| Streaming | Vérifier que le texte apparait progressivement | `waitForFunction()`, polling |
| Markdown | Vérifier le rendu des blocs de code | Sélecteurs CSS imbriques |
| Régénérer | Tester le bouton "Régénérer la réponse" | Boutons localises, regex |
| Éditer | Modifier un message envoyé | Workflow multi-étapes |

## Commandes

```bash
npm run test:module3
npx playwright test --grep "03" --headed
```

## Points cles a retenir

- TipTap = `keyboard.type()`, JAMAIS `fill()` pour le chat input
- Les réponses LLM sont non-deterministes → assertions souples
- `test.skip()` est votre ami pour gérer les services down
- Le polling (`waitForFunction()`) est préférable a `waitForTimeout()`
