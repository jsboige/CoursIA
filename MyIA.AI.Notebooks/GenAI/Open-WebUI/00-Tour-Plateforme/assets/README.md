# Captures du Tour de la plateforme

[← Tour de la plateforme](../README.md)

Ce dossier accueille les **captures d'écran annotées** du
[tour](../README.md), générées de façon reproductible par le script
[`../capture/tour-captures.spec.ts`](../capture/).

> **Statut : gabarit.** Les images ne sont pas encore présentes : elles seront
> produites une fois le **tenant de démonstration** en ligne (compte non-admin,
> données fictives, masquage des zones sensibles). En attendant, le tour indique
> chaque emplacement par `📷 Capture à venir`.

## Fichiers attendus

| Fichier | Section du tour |
|---------|-----------------|
| `01-connexion.png` | 1 — page de connexion (champs masqués) |
| `01-premiere-vue.png` | 1 — écran de chat |
| `02-selecteur-modele.png` | 2 — liste des modèles |
| `02-chat-streaming.png` | 2 — réponse en streaming |
| `03-workspace-modele.png` | 3 — modèle personnalisé |
| `03-base-connaissances.png` | 3 — base de connaissances (RAG) |
| `04-canal.png` | 4 — fil de discussion d'un canal |
| `05-parametres.png` | 5 — paramètres personnels |

## Règles

- **Aucune** capture ne doit montrer d'URL de tenant réel, d'e-mail nominatif, de
  clé d'API, de jeton ni de mot de passe.
- Chaque PNG est **relu en revue de PR** avant fusion.
- Régénérer les images après toute montée de version de l'interface (voir
  [`../capture/README.md`](../capture/README.md)).

---

*Assets — Tour de la plateforme (Epic #4433, sous #4427). FR-first. Gabarit en
attente du tenant de démonstration.*
