# Version de la démo d'initiation à Roo

## Version actuelle: 1.0.0 (21 mai 2025)

Ce fichier documente la version actuelle de la démo d'initiation à Roo ainsi que l'historique des modifications apportées au projet.

## Système de versionnement

Le système de versionnement suit le format standard MAJEUR.MINEUR.CORRECTIF:

- **MAJEUR**: Changements incompatibles avec les versions précédentes
- **MINEUR**: Ajouts de fonctionnalités rétrocompatibles
- **CORRECTIF**: Corrections de bugs rétrocompatibles

## Historique des versions

### 1.0.0 (21 mai 2025)

**Première version stable**

- Finalisation de l'intégration de la démo dans le dépôt principal
- Ajout du script d'installation unifié `scripts/demo-scripts/install-demo.ps1`
- Création du système de versionnement (ce fichier)
- Documentation du processus de maintenance
- Correction des chemins relatifs pour assurer la compatibilité avec le dépôt principal
- Tests complets de toutes les démos dans l'environnement intégré

### 0.9.0 (15 mai 2025)

**Version de pré-lancement**

- Intégration initiale dans le dépôt principal
- Migration des scripts de préparation et de nettoyage vers `scripts/demo-scripts/`
- Adaptation des références aux MCPs pour utiliser l'organisation du dépôt principal
- Mise à jour des chemins relatifs dans tous les scripts et références

### 0.8.0 (10 mai 2025)

**Version de test**

- Finalisation de la structure des 5 répertoires thématiques
- Ajout des démos pour chaque section thématique
- Création des scripts de préparation et de nettoyage des workspaces
- Documentation complète avec guides d'utilisation

### 0.7.0 (5 mai 2025)

**Version de développement**

- Création de la structure initiale du projet
- Implémentation des premières démos (découverte et assistant pro)
- Mise en place de l'architecture des répertoires workspace et ressources

## Processus de mise à jour

Pour mettre à jour la version de la démo:

1. Apporter les modifications nécessaires au code et à la documentation
2. Mettre à jour ce fichier VERSION.md avec:
   - Le nouveau numéro de version
   - La date de la mise à jour
   - Une description des changements
3. Mettre à jour les références à la version dans les autres fichiers si nécessaire
4. Créer un commit avec un message décrivant clairement la mise à jour

## Compatibilité

- **VS Code**: Compatible avec les versions 1.60.0 et ultérieures
- **Extension Roo**: Compatible avec les versions 2.0.0 et ultérieures
- **Python**: Compatible avec les versions 3.8 et ultérieures
- **Node.js**: Compatible avec les versions 14.0.0 et ultérieures

## Notes importantes

- Les mises à jour majeures (changement du premier chiffre) peuvent nécessiter des modifications dans la configuration ou l'utilisation de la démo.
- Les mises à jour mineures (changement du deuxième chiffre) ajoutent généralement de nouvelles fonctionnalités sans casser la compatibilité.
- Les correctifs (changement du troisième chiffre) sont des corrections de bugs et n'affectent pas l'utilisation générale.

Pour plus d'informations sur la maintenance et les mises à jour, consultez le [guide de maintenance](../docs/guides/demo-maintenance.md).