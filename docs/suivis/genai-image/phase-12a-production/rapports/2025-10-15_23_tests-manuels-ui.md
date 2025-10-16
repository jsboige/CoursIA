# Tests Manuels UI - Checklist Complète Phase 12A

**Date**: 2025-10-15 23:56 UTC  
**Objectif**: Validation visuelle exhaustive des interfaces ComfyUI et Forge après déploiement SSL

---

## ComfyUI - https://qwen-image-edit.myia.io

### 🔐 Sécurité SSL

- [ ] **Certificat SSL valide** - Cadenas vert dans la barre d'adresse
- [ ] **Pas d'avertissement de sécurité** - Chargement direct sans warning
- [ ] **HTTPS forcé** - Redirection automatique depuis HTTP
- [ ] **Informations certificat** - Cliquer sur cadenas → Vérifier émetteur Let's Encrypt

### 🎨 Interface Principale

- [ ] **Page charge complètement** - Pas d'erreurs de chargement
- [ ] **Temps de chargement < 5 secondes** - Interface réactive
- [ ] **Pas d'erreurs JavaScript** - Ouvrir Console (F12) → Onglet Console → Vérifier 0 erreurs rouges
- [ ] **Style CSS appliqué** - Interface avec design complet (pas de texte brut)

### 📊 Panneau Workflow (Canvas)

- [ ] **Canvas visible et interactif** - Zone de workflow centrale présente
- [ ] **Zoom fonctionnel** - Molette souris ou boutons +/- 
- [ ] **Pan fonctionnel** - Déplacement avec clic molette ou Shift+clic
- [ ] **Grille visible** - Fond quadrillé du canvas

### 🔧 Panneau Nodes (Gauche)

- [ ] **Menu Add Node accessible** - Clic droit sur canvas → Menu s'ouvre
- [ ] **Catégories visibles** - Liste hiérarchique des types de nodes
- [ ] **Custom nodes Qwen présents** - Chercher "Qwen" dans la liste
  - [ ] QwenVL nodes visibles
  - [ ] Pas d'erreurs "Failed to load" pour Qwen nodes
- [ ] **Nodes par défaut présents** - CheckpointLoader, KSampler, etc.

### ⚙️ Panneau Propriétés (Droite)

- [ ] **Panneau propriétés visible** - Sélectionner un node → Propriétés s'affichent à droite
- [ ] **Champs éditables** - Possibilité de modifier les valeurs
- [ ] **Widgets fonctionnels** - Sliders, dropdowns, text inputs répondent

### 🚀 Fonctionnalités Core

- [ ] **Bouton "Queue Prompt" visible** - Bouton principal de génération
- [ ] **Bouton "Queue Prompt" cliquable** - Pas d'état disabled
- [ ] **Historique accessible** - Onglet History chargeable
- [ ] **Queue Management visible** - Vue de la file d'attente

### 🔌 Custom Nodes Qwen

- [ ] **Qwen2-VL-Instruct disponible** - Dans liste des models si configuré
- [ ] **Image Analysis node** - Node d'analyse d'image Qwen présent
- [ ] **Vision nodes fonctionnels** - Pas d'erreurs au chargement

### 🎯 Test Fonctionnel Rapide

- [ ] **Créer un node simple** - Clic droit → Add Node → CheckpointLoaderSimple
- [ ] **Node s'affiche** - Node apparaît sur le canvas
- [ ] **Connecter des nodes** - Drag & drop de sorties vers entrées
- [ ] **Sauvegarder workflow** - Menu → Save → Pas d'erreur

### 📱 Performance

- [ ] **Interface fluide** - Pas de lag lors de déplacements
- [ ] **Réactivité boutons** - Clics instantanés
- [ ] **Scroll smooth** - Défilement des menus fluide
- [ ] **Mémoire stable** - Utilisation CPU/RAM normale (Gestionnaire des tâches)

---

## Forge - https://turbo.stable-diffusion-webui-forge.myia.io

### 🔐 Sécurité SSL

- [ ] **Certificat SSL valide** - Cadenas vert
- [ ] **Pas d'avertissement** - Chargement direct
- [ ] **HTTPS forcé** - Redirection depuis HTTP
- [ ] **Certificat vérifié** - Émetteur Let's Encrypt correct

### 🎨 Interface Principale

- [ ] **Page charge complètement** - Tous les éléments présents
- [ ] **Temps de chargement < 5 secondes** - Réponse rapide
- [ ] **Console sans erreurs critiques** - F12 → Console → Max warnings, pas d'erreurs bloquantes
- [ ] **Style Gradio appliqué** - Interface moderne avec thème

### 📑 Onglets Principaux

- [ ] **txt2img visible** - Onglet génération texte vers image
- [ ] **img2img visible** - Onglet image vers image
- [ ] **Extras visible** - Upscaling et post-processing
- [ ] **PNG Info visible** - Lecture métadonnées
- [ ] **Settings accessible** - Configuration générale

### 🖼️ Onglet txt2img

- [ ] **Zone de prompt visible** - Champ texte principal
- [ ] **Negative prompt visible** - Champ texte négatif
- [ ] **Sampling steps slider** - Curseur steps ajustable
- [ ] **Width/Height sliders** - Dimensions configurables
- [ ] **CFG Scale slider** - Configuration présente
- [ ] **Seed input** - Champ seed visible
- [ ] **Bouton "Generate" visible et actif** - Pas d'état disabled

### 🎛️ Paramètres Avancés

- [ ] **Accordéon paramètres déplié** - Clic sur "Show" fonctionne
- [ ] **Sampler dropdown** - Liste samplers accessible
- [ ] **Checkpoint selector** - Sélection modèle fonctionnelle
- [ ] **VAE selector** - Si applicable
- [ ] **LoRA section** - Addons disponibles

### 🖼️ Galerie

- [ ] **Zone galerie visible** - Grid d'images
- [ ] **Images précédentes chargées** - Si historique existe
- [ ] **Boutons download fonctionnels** - Téléchargement images
- [ ] **Preview images cliquables** - Zoom sur image

### 🔧 Onglet Settings

- [ ] **Settings page charge** - Pas d'erreur 404
- [ ] **Sections dépliables** - Accordéons fonctionnels
- [ ] **Save settings button** - Bouton sauvegarde présent
- [ ] **Restart button** - Option restart visible (ne pas cliquer!)

### 📚 API Documentation

- [ ] **Route /docs accessible** - `https://turbo.stable-diffusion-webui-forge.myia.io/docs`
- [ ] **Swagger UI chargé** - Interface interactive API
- [ ] **Endpoints listés** - Liste complète des routes API
- [ ] **Try it out fonctionnel** - Boutons de test présents

### 🎯 Test Fonctionnel Rapide (OPTIONNEL)

⚠️ **Attention**: Ce test génère une image (consomme ressources GPU)

- [ ] **Entrer prompt simple** - Ex: "a red apple"
- [ ] **Steps = 1** - Réduire au minimum pour test rapide
- [ ] **Cliquer Generate** - Lancer génération
- [ ] **Pas d'erreur immédiate** - Pas de popup d'erreur
- [ ] **Progress bar visible** - Barre de progression apparaît
- [ ] **Image générée** - Résultat s'affiche dans galerie

### 📱 Performance

- [ ] **Interface fluide** - Scrolling smooth
- [ ] **Réactivité** - Clics instantanés
- [ ] **Pas de freeze** - Interface ne se bloque pas
- [ ] **Ressources stables** - CPU/RAM normaux

---

## Comparaison ComfyUI vs Forge

### ⚖️ Tests de Non-Régression

- [ ] **Forge toujours accessible** - Pas impacté par déploiement ComfyUI
- [ ] **Performances similaires** - Pas de ralentissement notable
- [ ] **Deux services simultanés** - Les deux URL accessibles en parallèle
- [ ] **Pas d'interférence GPU** - Génération sur un n'impacte pas l'autre

### 🔄 Tests de Basculement

- [ ] **Passer de ComfyUI à Forge** - Changer d'onglet navigateur
- [ ] **Passer de Forge à ComfyUI** - Navigation fluide
- [ ] **Deux fenêtres simultanées** - Ouvrir les deux en même temps
- [ ] **Pas de conflit de port** - Chaque service sur son port

---

## Tests Certificat SSL Détaillés

### 🔍 Inspection Manuelle

1. **Ouvrir DevTools** (F12)
2. **Onglet Security**
3. **Vérifier**:
   - [ ] Connection is secure
   - [ ] Certificate is valid
   - [ ] Issued by: Let's Encrypt Authority X3
   - [ ] Valid from/to dates correctes
   - [ ] No mixed content warnings

### 🌐 Tests Navigateurs Multiples

- [ ] **Chrome/Edge** - Fonctionne sans warning
- [ ] **Firefox** - Fonctionne sans warning
- [ ] **Safari** (si disponible) - Fonctionne sans warning

### 📱 Tests Mobile (Optionnel)

- [ ] **Responsive design** - Interface adaptée mobile
- [ ] **Touch controls** - Fonctionnels sur écran tactile
- [ ] **SSL valide** - Pas d'avertissement mobile

---

## Résolution de Problèmes

### ❌ Si erreurs trouvées

**Erreurs SSL**:
- Vérifier binding IIS avec script validation
- Vérifier date système Windows
- Regénérer certificat avec win-acme si nécessaire

**Erreurs JavaScript**:
- Ouvrir Console (F12) → Noter messages d'erreur
- Vérifier logs IIS
- Vérifier reverse proxy configuration

**Performance dégradée**:
- Vérifier utilisation GPU avec `nvidia-smi`
- Vérifier logs Windows Event Viewer
- Redémarrer service si nécessaire

**Interface incomplète**:
- Vider cache navigateur (Ctrl+Shift+Delete)
- Rafraîchir avec Ctrl+F5
- Vérifier fichiers statiques servis par IIS

---

## Logs de Test

### Format de Reporting

Pour chaque test effectué, noter:

```
[✅/❌] Test Name
Date/Heure: YYYY-MM-DD HH:MM
Navigateur: Chrome/Firefox/Edge
Résultat: Succès/Échec
Notes: Détails éventuels
```

### Exemple

```
✅ ComfyUI - Certificat SSL valide
Date/Heure: 2025-10-15 23:56
Navigateur: Chrome 120
Résultat: Succès
Notes: Cadenas vert, émetteur Let's Encrypt, valide jusqu'au 2026-01-15
```

---

## Validation Finale

### Critères de Succès

Pour considérer la validation UI comme réussie:

- **Minimum 95% des tests passés** sur chaque service
- **0 erreur bloquante** dans les consoles
- **Certificats SSL valides** sur les deux services
- **Performances acceptables** (< 5s chargement initial)
- **Aucune régression** sur service Forge existant

### Signature Validation

```
Testé par: ___________________
Date: 2025-10-15 23:56 UTC
Statut: [ ] VALIDÉ  [ ] ÉCHEC  [ ] PARTIEL

Commentaires:
_________________________________
_________________________________
_________________________________
```

---

**Version**: 1.0  
**Dernière mise à jour**: 2025-10-15 23:56 UTC  
**Prochaine révision**: Après chaque changement infrastructure