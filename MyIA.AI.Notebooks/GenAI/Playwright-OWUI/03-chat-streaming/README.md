# Module 03 - Tests de Chat & Streaming LLM

> **Format** : Fichier TypeScript `.spec.ts` avec tests commentes. Ouvrez `03-chat-streaming.spec.ts` dans VS Code. C'est le module le plus riche — il couvre les defis uniques du test d'applications d'IA generative.

## Objectifs pedagogiques

A la fin de ce module, vous serez capable de :

- Tester une interface de chat avec un editeur rich text (TipTap)
- Gerer le streaming de reponses LLM (tokens progressifs)
- Implementer des patterns d'attente adaptes aux IA generatives
- Ecrire des assertions sur du contenu genere par IA (non deterministe)
- Utiliser `test.skip()` pour gerer les services indisponibles

## Duree estimee

**3 heures**

## Contenu du module

### Partie theorique

**Le defi du test E2E avec des LLMs :**
Tester une application d'IA generative pose des defis uniques :

1. **Non-determinisme** : Le meme prompt peut donner des reponses differentes
2. **Latence variable** : De 2s (GPT-4.1-mini) a 2min (modele local en reflexion)
3. **Streaming** : Les tokens arrivent progressivement, le DOM change en continu
4. **Disponibilite** : Les services LLM peuvent etre temporairement indisponibles

**Solutions implementees :**
- Assertions souples : `toContain('hello')` au lieu de `toBe('Hello from GPT')`
- Timeouts genereux : 120s par test, polling toutes les secondes
- Skip gracieux : `test.skip(!response, 'Service indisponible')`
- Helper `waitForResponse()` : Attend que le contenu soit stable

**L'editeur TipTap :**
Open WebUI utilise TipTap (un editeur ProseMirror) au lieu d'un `<textarea>`.
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
| Chat cloud | Envoyer un message a un modele cloud | `keyboard.type()`, TipTap |
| Chat local | Tester un modele local (vLLM) | `test.skip()`, resilience |
| Streaming | Verifier que le texte apparait progressivement | `waitForFunction()`, polling |
| Markdown | Verifier le rendu des blocs de code | Selecteurs CSS imbriques |
| Regenerer | Tester le bouton "Regenerer la reponse" | Boutons localises, regex |
| Editer | Modifier un message envoye | Workflow multi-etapes |

## Commandes

```bash
npm run test:module3
npx playwright test --grep "03" --headed
```

## Points cles a retenir

- TipTap = `keyboard.type()`, JAMAIS `fill()` pour le chat input
- Les reponses LLM sont non-deterministes → assertions souples
- `test.skip()` est votre ami pour gerer les services down
- Le polling (`waitForFunction()`) est preferable a `waitForTimeout()`
