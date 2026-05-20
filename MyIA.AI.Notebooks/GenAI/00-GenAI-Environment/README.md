# 00-GenAI-Environment - Setup et Configuration

[← Documentation GenAI](../README.md) | [↑ ..](../README.md) | [→ Docker Services](00-2-Docker-Services-Management.ipynb)

## Introduction : Pourquoi cet setup est crucial

Avant de plonger dans l'univers des modèles de génération IA, prenez un moment pour comprendre pourquoi une configuration rigoureuse évite 80% des problèmes techniques. Les notebooks GenAI font appel à des services externes, des conteneurs Docker et des modèles complexes – une seule variable d'environnement manquante peut bloquer toute votre exploration. Ce module vous guide pas à pas pour créer une base solide, vous permettant de vous concentrer sur l'essentiel : apprendre et expérimenter avec l'IA.

## Vue d'Ensemble
[GREEN] Setup et Configuration

**Validation: 100% (6/6 notebooks)**

## Notebooks du Module

| # | Notebook | Description | Validation |
|---|----------|-------------|------------|
| 1 | [00-1-Environment-Setup](00-1-Environment-Setup.ipynb) | Configuration environnement complet | OK |
| 2 | [00-2-Docker-Services-Management](00-2-Docker-Services-Management.ipynb) | Gestion services conteneurises | OK |
| 3 | [00-3-API-Endpoints-Configuration](00-3-API-Endpoints-Configuration.ipynb) | Configuration endpoints API | OK |
| 4 | [00-4-Environment-Validation](00-4-Environment-Validation.ipynb) | Tests et validation setup | OK |
| 5 | [00-5-ComfyUI-Local-Test](00-5-ComfyUI-Local-Test.ipynb) | Test local des services ComfyUI | OK |
| 6 | [00-6-Local-Docker-Deployment](00-6-Local-Docker-Deployment.ipynb) | Deploiement Docker local complet | OK |

## Prérequis
- Configuration .env avec clés API
- Python 3.11+ avec dépendances
- Variables d'environnement OpenRouter

## Ce que vous saurez faire

À l'issue de ce module, vous serez capable de :
- Configurer un environnement Python complet pour le développement GenAI
- Gérer des services Docker conteneurisés (ComfyUI, modèles de langue)
- Paramétrer les endpoints API pour les services IA
- Valifier que chaque composant fonctionne correctement
- Déployer localement l'ensemble de l'infrastructure GenAI
- Résoudre les problèmes courants de configuration

## Utilisation

1. Configurer l'environnement selon 00-GenAI-Environment
2. Exécuter les notebooks dans l'ordre numérique
3. Vérifier les outputs dans /outputs/
