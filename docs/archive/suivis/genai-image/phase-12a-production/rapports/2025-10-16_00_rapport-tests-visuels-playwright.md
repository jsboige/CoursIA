# Rapport Tests Visuels Playwright - Phase 12A

**Date**: 2025-10-16 02:24 UTC+2  
**Durée**: ~16 minutes  
**Approche**: Hybride (Script automatisé + MCP manuel)

---

## 🎯 Objectif

Valider visuellement les deux interfaces en production (ComfyUI + Forge) avec une approche hybride combinant automatisation et validation manuelle interactive.

---

## 📊 Méthode Hybride

### Approche 1: Script Automatisé Playwright

**Fichier**: [`docs/suivis/genai-image/2025-10-15_13_test-playwright-ui.ps1`](2025-10-15_13_test-playwright-ui.ps1)

**Résultats**:
- ✅ Installation: Node.js v23.11.0 détecté
- ✅ Dépendances: Playwright installé
- ✅ Navigateurs: Chromium installé
- ✅ Exécution: Tests lancés avec succès
- ⚠️ Screenshots générés: 2 fichiers (qualité limitée)
- **Taille totale**: 28.75 KB

**Problèmes détectés**:
- ❌ Canvas ComfyUI non détecté
- ❌ Bouton Queue non détecté
- ❌ Bouton Generate Forge non détecté
- ❌ Zone de prompt Forge non détectée

**Analyse**: Les sélecteurs automatiques ne trouvent pas les éléments UI, probablement car :
1. Le chargement async n'est pas complété
2. Les délais d'attente (5s) sont insuffisants
3. Les éléments sont dans des shadow DOM ou iframes

---

### Approche 2: MCP Playwright (Manuel)

**Résultats**:
- ✅ ComfyUI testé interactivement
- ✅ Forge testé (page de login détectée)
- ✅ Screenshots MCP: 2 fichiers (haute qualité)
- ✅ Validations interactives: Console, snapshots, observations directes
- **Taille totale**: 190.04 KB

**Avantages**:
- Screenshots beaucoup plus détaillés (19x plus gros pour ComfyUI)
- Observation directe des erreurs console
- Navigation interactive
- Capacité à attendre le chargement complet

---

## 🖼️ Résultats ComfyUI

### Interface Principale

**URL**: https://qwen-image-edit.myia.io  
**Statut**: ✅ Accessible (sans authentification)

#### Screenshot Script Automatisé
- **Fichier**: [`comfyui-ui.png`](screenshots/comfyui-ui.png)
- **Taille**: 8.31 KB
- **Qualité**: ⚠️ Très limitée (capture incomplète)

#### Screenshot MCP Manuel
- **Fichier**: [`comfyui-interface-mcp.png`](screenshots/comfyui-interface-mcp.png)
- **Taille**: 156.56 KB
- **Qualité**: ✅ Excellente (capture complète full-page)

### Vérifications Interface

| Élément | Script Auto | MCP Manuel | Commentaire |
|---------|-------------|------------|-------------|
| Page charge | ✅ | ✅ | Délai: ~5-8 secondes |
| Titre page | ✅ | ✅ | "ComfyUI" puis "*Unsaved Workflow - ComfyUI" |
| Menu principal | ❌ Non détecté | ✅ Visible | Logo, navigation, onglets |
| Canvas workflow | ❌ Non détecté | ✅ Visible | Zone principale d'édition |
| Panneau nodes | ❌ Non détecté | ✅ Visible | Bibliothèque de nodes accessible |
| Bouton Run | ❌ Non détecté | ✅ Visible | Avec batch count spinner |
| Console JS | N/A | ⚠️ Warnings | Voir section erreurs |

### Logs Console Observés (MCP)

**✅ Messages positifs**:
```
- Running on qwen-image-edit.myia.io
- ComfyUI Front-end version: 1.27.10
- [workflowStore] open workflow workflows/Unsaved Workflow.json
```

**⚠️ Warnings JavaScript**:
```
- JavaScript Warning: "unreachable code after return statement" (14 occurrences)
  → Non bloquant, problème de code legacy
```

**❌ Erreurs critiques**:
```
- TypeError: can't access property "id", setting is undefined at CORE_SETTINGS
  → Erreur de configuration, impact inconnu
  
- JavaScript Error: "Firefox can't establish a connection to wss://qwen-image-edit.myia.io"
  → WebSocket backend inaccessible (7 occurrences)
  → Impact: Backend ComfyUI non accessible, génération d'images impossible
```

### Éléments UI Détectés (MCP Snapshot)

Via le snapshot accessibility, voici les éléments principaux identifiés :

```yaml
✅ Logo ComfyUI (cliquable)
✅ Navigation "Graph navigation"
✅ Lien "Unsaved Workflow" (workflow actif)
✅ Bouton "Run" avec icône
✅ Spinbutton "Batch Count" (valeur: 1)
✅ Bouton "Cancel current run" (disabled)
✅ Bouton "Clear Pending Tasks" (disabled)
✅ Boutons latéraux:
   - Queue (q)
   - Node Library (n)
   - Model Library (m)
   - Workflows (w)
   - Templates
   - Help Center
   - Toggle Bottom Panel
   - Keyboard Shortcuts
✅ Onglets de workflows (créer nouveau workflow)
✅ Outils: Select (V), Hand (H), Fit View (.), Zoom (100%), Focus Mode (F), Hide Links
✅ Textboxes de prompt visibles:
   - "text, watermark"
   - "beautiful scenery nature glass bottle landscape, , purple galaxy bottle,"
```

### Custom Nodes Qwen

**Statut**: ⚠️ Non vérifiable sans accès backend

**Raison**: Les erreurs WebSocket indiquent que le backend ComfyUI n'est pas accessible. Impossible de vérifier si les custom nodes Qwen sont chargés car :
1. La connexion au serveur WebSocket échoue
2. Le menu nodes nécessite le backend pour lister les nodes disponibles
3. Aucune génération d'image ne peut être testée

**Action requise**: Diagnostic backend ComfyUI pour résoudre les erreurs WebSocket.

### Performance

| Métrique | Valeur | Statut |
|----------|--------|--------|
| Temps chargement initial | ~5-8 secondes | ⚠️ Moyen |
| Réactivité UI | ✅ Fluide | Frontend opérationnel |
| Backend accessible | ❌ Non | Erreurs WebSocket critiques |
| VRAM observée | N/A | Backend inaccessible |

---

## 🖼️ Résultats Forge

### Interface Principale

**URL**: https://turbo.stable-diffusion-webui-forge.myia.io  
**Statut**: 🔒 Authentification requise

#### Screenshot Script Automatisé
- **Fichier**: [`forge-ui.png`](screenshots/forge-ui.png)
- **Taille**: 20.44 KB
- **Qualité**: ⚠️ Page de login (non authentifié)

#### Screenshot MCP Manuel
- **Fichier**: [`forge-login-mcp.png`](screenshots/forge-login-mcp.png)
- **Taille**: 33.48 KB
- **Qualité**: ✅ Page de login claire

### Vérifications Interface

| Élément | Script Auto | MCP Manuel | Commentaire |
|---------|-------------|------------|-------------|
| Page charge | ✅ | ✅ | Rapide (<2s) |
| Titre page | ❌ Vide | ❌ Vide | Pas de titre défini |
| Page de login | ✅ Visible | ✅ Visible | Champs username/password |
| Bouton "Login" | ✅ Visible | ✅ Visible | Cliquable |
| Scripts chargés | ⚠️ Échecs | ⚠️ Échecs | Nombreux scripts non chargés |

### Logs Console Observés (MCP)

**⚠️ Warnings critiques**:
```
- JavaScript Warning: "Loading failed for the <script> with source https://turbo.stable-di..." 
  (41 occurrences)
  → La plupart des scripts JS de l'interface ne se chargent pas
  → Probable cause: Authentification requise avant d'accéder aux assets
```

### Éléments UI Détectés (MCP Snapshot)

```yaml
✅ Heading "Login" (niveau 2)
✅ Textbox "username" (placeholder: Type here...)
✅ Textbox "password" (placeholder: Type here...)
✅ Bouton "Login" (cliquable)
```

### Observations Importantes

1. **Authentification obligatoire**: Contrairement à ComfyUI, Forge nécessite des credentials
2. **Protection des assets**: Les scripts JS ne sont pas accessibles sans authentification
3. **Interface minimaliste**: Page de login simple et fonctionnelle
4. **Pas d'impact visible**: Le déploiement ComfyUI n'a pas cassé la page de login

### API Documentation

**URL testée**: https://turbo.stable-diffusion-webui-forge.myia.io/docs  
**Statut**: ❌ Non testé (authentification requise)

**Prochaine étape**: Fournir des credentials pour tester l'interface complète et l'API.

### Impact Déploiement ComfyUI

**Verdict**: ✅ Aucun impact négatif détecté

- Service Forge répond toujours
- Page de login fonctionnelle
- Pas d'erreur de routage ou de conflit de port
- Les deux services semblent isolés correctement

---

## 🔄 Comparaison Script vs MCP

| Critère | Script Auto | MCP Manuel | Gagnant |
|---------|-------------|------------|---------|
| **Reproductibilité** | ✅ Haute | ⚠️ Manuelle | **Script** |
| **Qualité screenshots** | ⚠️ 8-20 KB | ✅ 33-156 KB | **MCP** |
| **Détection éléments** | ❌ Échec | ✅ Succès | **MCP** |
| **Logs console** | ❌ Aucun | ✅ Complets | **MCP** |
| **Confiance visuelle** | ⚠️ Indirecte | ✅ Directe | **MCP** |
| **Vitesse exécution** | ✅ ~30s | ⚠️ ~10min | **Script** |
| **Détection bugs UI** | ⚠️ Limitée | ✅ Excellente | **MCP** |
| **CI/CD intégration** | ✅ Automatisable | ❌ Non | **Script** |
| **Debugging** | ❌ Limité | ✅ Interactif | **MCP** |
| **Snapshots accessibility** | ❌ Non | ✅ Oui | **MCP** |

### Analyse Comparative

#### Forces du Script Automatisé
- Parfait pour la CI/CD et les tests de non-régression
- Exécution rapide et reproductible
- Pas d'intervention humaine nécessaire

#### Faiblesses du Script Automatisé
- Screenshots de faible qualité (captures incomplètes)
- Sélecteurs UI fragiles (aucun élément détecté)
- Pas d'accès aux logs console
- Délais d'attente fixes inadaptés au chargement async

#### Forces du MCP Manuel
- Screenshots haute résolution et complets
- Logs console détaillés pour le debugging
- Snapshots accessibility pour l'analyse UI
- Observation directe des erreurs critiques
- Navigation interactive adaptative

#### Faiblesses du MCP Manuel
- Processus manuel et plus lent
- Non automatisable dans une CI/CD
- Nécessite intervention humaine

---

## 🎯 Recommandations

### Approche Hybride Optimale

1. **CI/CD (Production)**: Script automatisé pour tests de smoke rapides
   - Vérifier que les pages chargent (status 200)
   - Détecter les régressions majeures
   - Exécution après chaque déploiement

2. **Validation Approfondie**: MCP manuel pour phases critiques
   - Après modifications majeures d'architecture
   - Pour investiguer des bugs complexes
   - Validation visuelle avant release importante

3. **Améliorer le Script Automatisé**:
   - Augmenter les délais d'attente (15-30s au lieu de 5s)
   - Utiliser `waitUntil: 'networkidle'` et des sélecteurs spécifiques
   - Ajouter capture des logs console
   - Implémenter retry logic pour éléments async

---

## 📁 Screenshots Archivés

Tous les screenshots sont disponibles dans [`docs/suivis/genai-image/screenshots/`](screenshots/):

### ComfyUI
- [`comfyui-ui.png`](screenshots/comfyui-ui.png) - 8.31 KB (script auto)
- [`comfyui-interface-mcp.png`](screenshots/comfyui-interface-mcp.png) - 156.56 KB (MCP manuel) ⭐

### Forge
- [`forge-ui.png`](screenshots/forge-ui.png) - 20.44 KB (script auto)
- [`forge-login-mcp.png`](screenshots/forge-login-mcp.png) - 33.48 KB (MCP manuel) ⭐

**Taille totale**: 218.79 KB

---

## ✅ Validation Finale

### ComfyUI (qwen-image-edit.myia.io)

| Critère | Statut | Détails |
|---------|--------|---------|
| Interface complète et fonctionnelle | ✅ | Frontend chargé, UI réactive |
| Custom nodes Qwen accessibles | ⚠️ | Non vérifiable (backend inaccessible) |
| Pas d'erreurs bloquantes frontend | ✅ | Warnings uniquement |
| Backend accessible | ❌ | **Erreurs WebSocket critiques** |
| Performances optimales | ⚠️ | Frontend OK, backend HS |

**Verdict ComfyUI**: 🔶 **Interface frontend opérationnelle mais backend inaccessible**

### Forge (turbo.stable-diffusion-webui-forge.myia.io)

| Critère | Statut | Détails |
|---------|--------|---------|
| Non impacté par déploiement ComfyUI | ✅ | Service répond normalement |
| Page de login accessible | ✅ | Formulaire fonctionnel |
| Authentification requise | ✅ | Protection active |
| Scripts chargés correctement | ⚠️ | Bloqués avant auth |
| Performances optimales | ✅ | Chargement rapide |

**Verdict Forge**: ✅ **Service opérationnel, authentification obligatoire**

---

## 🚨 Problèmes Critiques Identifiés

### 1. ComfyUI Backend Inaccessible ⚠️ CRITIQUE

**Symptôme**: 
```
JavaScript Error: "Firefox can't establish a connection to wss://qwen-image-edit.myia.io"
```

**Impact**:
- ❌ Impossible de générer des images
- ❌ Impossible de lister les custom nodes
- ❌ Impossible de sauvegarder/charger des workflows
- ❌ Backend ComfyUI totalement inaccessible

**Cause probable**:
- Le serveur WebSocket ComfyUI n'est pas démarré
- Ou le reverse proxy IIS ne route pas correctement le WebSocket
- Ou un firewall bloque les connexions WebSocket

**Action requise**: 
1. Vérifier que le service ComfyUI backend est démarré
2. Vérifier la configuration IIS pour le support WebSocket
3. Tester la connexion WebSocket directement

### 2. Forge Nécessite Authentification 🔒 INFO

**Symptôme**: Page de login affichée

**Impact**:
- ❌ Impossible de tester l'interface complète sans credentials
- ❌ Impossible de tester l'API `/docs`
- ❌ Tests visuels complets bloqués

**Action requise**: 
1. Fournir des credentials de test
2. Ou désactiver temporairement l'authentification pour les tests
3. Relancer les tests MCP avec authentification

---

## 📋 Prochaines Étapes

### Priorité 1: Résoudre Backend ComfyUI

1. **Diagnostic backend** (CRITIQUE):
   ```powershell
   # Vérifier si le service ComfyUI tourne
   docker ps | Select-String comfyui
   
   # Vérifier les logs du container
   docker logs comfyui-container-name
   
   # Tester connexion WebSocket directe
   Test-NetConnection qwen-image-edit.myia.io -Port 8188
   ```

2. **Configuration IIS WebSocket**:
   - Vérifier que le module WebSocket est installé
   - Vérifier la configuration du reverse proxy
   - Tester avec wscat ou autre outil WebSocket

### Priorité 2: Tests Forge Authentifiés

1. Obtenir des credentials de test
2. Relancer tests MCP avec authentification
3. Capturer screenshots de l'interface complète
4. Tester l'API `/docs`

### Priorité 3: Améliorer Script Automatisé

1. Implémenter délais d'attente plus longs
2. Ajouter capture des logs console
3. Utiliser sélecteurs plus robustes
4. Ajouter tests de connectivité WebSocket

---

## 📊 Statistiques Globales

| Métrique | Valeur |
|----------|--------|
| Durée totale | ~16 minutes |
| Screenshots générés | 4 fichiers |
| Taille totale screenshots | 218.79 KB |
| URLs testées | 2 |
| Tests automatisés | 2 |
| Tests manuels MCP | 2 |
| Erreurs critiques détectées | 2 |
| Warnings détectés | 55+ |

---

## 🏁 Conclusion

### Infrastructure ComfyUI + Forge: ⚠️ PARTIELLEMENT OPÉRATIONNELLE

**Points Positifs** ✅:
- Frontend ComfyUI complètement fonctionnel et réactif
- Interface moderne et intuitive chargée
- Forge non impacté par le déploiement ComfyUI
- Isolation correcte des deux services
- Page de login Forge opérationnelle
- Screenshots haute qualité capturés

**Points Critiques** ❌:
- **Backend ComfyUI inaccessible** (WebSocket en erreur)
- Aucune génération d'images possible sur ComfyUI
- Custom nodes Qwen non vérifiables
- Tests Forge bloqués par authentification

**Recommandation Finale**:

🚨 **Infrastructure NON production-ready pour ComfyUI**

Le frontend est excellent mais sans backend fonctionnel, le service est inutilisable. Priorité absolue : réparer la connexion WebSocket backend.

✅ **Forge reste opérationnel** - Aucune régression détectée

**Prochaine étape**: Sous-tâche de diagnostic et réparation backend ComfyUI avant de passer à la Phase 12B.

---

**Rapport généré par**: Roo Code (Mode Code)  
**Scripts créés**:
- [`2025-10-16_00_copier-screenshots-playwright.ps1`](2025-10-16_00_copier-screenshots-playwright.ps1)
- [`2025-10-16_00_copier-screenshots-mcp.ps1`](2025-10-16_00_copier-screenshots-mcp.ps1)

**Tests executés**:
- Script automatisé Playwright via [`2025-10-15_13_test-playwright-ui.ps1`](2025-10-15_13_test-playwright-ui.ps1)
- Tests manuels MCP Playwright (interactifs)