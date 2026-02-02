# Migration des scripts et de la documentation

Ce document décrit les changements effectués pour rendre la démo Roo autonome tout en maintenant son intégration avec le dépôt principal.

## Changements effectués

### 1. Déplacement des scripts

Les scripts suivants ont été déplacés du répertoire `scripts/demo-scripts/` vers le répertoire racine de la démo :

- `install-demo.ps1` : Script d'installation unifié
- `prepare-workspaces.ps1` : Script de préparation des espaces de travail
- `clean-workspaces.ps1` : Script de nettoyage des espaces de travail

### 2. Adaptation des chemins relatifs

Les chemins relatifs dans les scripts ont été adaptés pour qu'ils fonctionnent correctement depuis le répertoire de la démo :

- Les références au répertoire racine du projet ont été remplacées par des références au répertoire courant
- Les chemins vers les répertoires de démo ont été adaptés pour fonctionner depuis le répertoire de la démo

### 3. Déplacement de la documentation

La documentation suivante a été déplacée du répertoire `docs/guides/` vers le répertoire `demo-roo-code/docs/` :

- `demo-maintenance.md` : Guide de maintenance de la démo

### 4. Mise à jour des références

Les références dans les documents ont été mises à jour pour refléter la nouvelle structure :

- Les liens vers les scripts dans le README principal ont été mis à jour
- Les références aux chemins de fichiers dans le guide de maintenance ont été adaptées

## Objectifs atteints

- ✅ **Autonomie fonctionnelle** : La démo peut maintenant fonctionner de manière autonome, sans dépendre du reste du dépôt
- ✅ **Cohérence des chemins** : Tous les chemins relatifs fonctionnent correctement depuis le répertoire de la démo
- ✅ **Documentation adaptée** : La documentation a été mise à jour pour refléter la nouvelle structure
- ✅ **Intégration préservée** : La démo reste intégrée au dépôt principal via des références et des liens

## Tests effectués

- ✅ Script d'installation (`install-demo.ps1`)
- ✅ Script de préparation des espaces de travail (`prepare-workspaces.ps1`)
- ✅ Script de nettoyage des espaces de travail (`clean-workspaces.ps1`)

## Remarques

- Les problèmes d'encodage des caractères accentués dans la sortie des scripts n'affectent pas leur fonctionnement
- Les scripts ont été simplifiés pour éviter les erreurs de syntaxe PowerShell

---

*Dernière mise à jour : 21 mai 2025*