# Captures du Tour de la plateforme

[← Tour de la plateforme](../README.md) | [Script de capture →](../capture/README.md)

Ce dossier contient les **captures d'écran** du [tour](../README.md). Elles sont
produites de façon reproductible par le script
[`tour-captures.spec.ts`](../capture/README.md), contre une instance réelle,
avec un **compte non-administrateur neuf** et le **masquage** des zones
d'identité. Chaque image est relue avant d'être versionnée.

## Captures présentes

| Fichier | Section du tour | Ce que l'image montre |
|---------|-----------------|-----------------------|
| `01-connexion.png` | 1 — Connexion & première vue | Le formulaire de connexion, champs vides |
| `01-premiere-vue.png` | 1 — Connexion & première vue | L'écran de départ d'une conversation : assistant sélectionné, zone de saisie, suggestions d'invites, panneau « Fichiers » ouvert à droite |
| `02-chat-streaming.png` | 2 — Le chat IA | La réponse d'un assistant à une invite fictive, un court poème suivi de son commentaire |
| `05-parametres.png` | 5 — Notes & autres surfaces | Les réglages personnels, onglet « Général » |
| `05-memoire.png` | 5 — Notes & autres surfaces | L'onglet « Personnalisation » des réglages : mémoire activée, aucun souvenir enregistré |
| `03-dossier-equipe.png` | Aucune : le tour ne l'affiche pas | L'écran de départ d'une conversation, avec le champ « Nom du dossier » du panneau « Fichiers » |

Deux précisions de lecture.

- **`03-dossier-equipe.png` ne montre pas un dossier d'équipe.** Le script
  clique le premier bouton de création de dossier qu'il trouve sur la page, et
  c'est celui du panneau « Fichiers » qui répond. Le dossier de conversations
  partagé avec un groupe, que décrit la section 3 du tour, reste donc à
  capturer.
- **Le nom de l'assistant sélectionné reste lisible** sur les images prises à
  l'écran de conversation. Ce que le script ne capture pas par défaut, c'est la
  liste complète des modèles de l'instance.

## Surfaces non capturées

Le script saute ces captures tant que la condition n'est pas remplie ; le tour
les signale par la mention **Surface non capturée**.

| Fichier attendu | Section du tour | Condition de capture |
|-----------------|-----------------|----------------------|
| `02-selecteur-modele.png` | 2 — liste des modèles | `DEMO_OWUI_CAPTURE_REAL_CONTENT=1`, sur une instance à données fictives : la liste porte les noms des modèles de l'instance |
| `02-raisonnement-direct.png` | 2 — raisonnement affiché en direct | `DEMO_OWUI_REASONING_MODEL` renseigné avec le nom d'un modèle de raisonnement |
| `03-workspace-modele.png` | 3 — modèle personnalisé | `DEMO_OWUI_CAPTURE_REAL_CONTENT=1`, sur une instance à données fictives |
| `03-base-connaissances.png` | 3 — base de connaissances | `DEMO_OWUI_CAPTURE_REAL_CONTENT=1`, sur une instance à données fictives |
| `04-canal.png` | 4 — fil de discussion d'un canal | `DEMO_OWUI_CAPTURE_REAL_CONTENT=1`, sur une instance à données fictives |

Les variables se renseignent dans le fichier `.env` du dossier
[`capture/`](../capture/README.md), qui n'est jamais versionné.

## Règles

- **Aucune** capture ne doit montrer d'URL de tenant réel, d'e-mail nominatif, de
  clé d'API, de jeton ni de mot de passe.
- Chaque image est **relue** avant d'être versionnée, puis en revue de
  contribution.
- Régénérer les images après toute montée de version de l'interface (voir
  [`../capture/README.md`](../capture/README.md)).
