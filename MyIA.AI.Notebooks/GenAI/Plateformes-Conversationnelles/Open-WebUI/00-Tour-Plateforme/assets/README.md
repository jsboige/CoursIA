# Captures du Tour de la plateforme

[← Tour de la plateforme](../README.md)

Ce dossier accueille les **captures d'écran annotées** du
[tour](../README.md), générées de façon reproductible par le script
[`../capture/tour-captures.spec.ts`](../capture/).

> **Statut.** Les captures sont produites contre une **instance réelle** via un
> **compte non-administrateur neuf**, avec **masquage** des zones sensibles et
> **revue anti-fuite de chaque image**. Les surfaces qui exposeraient du contenu
> réel d'un établissement (listes de modèles/bases internes, canaux) restent
> volontairement **schématisées** dans [`../architecture.md`](../architecture.md)
> et signalées `📷 Capture à venir` dans le tour.
>
> **Sous-ensemble sûr livré** (2026-07, contre une instance v0.10.2) : les trois
> captures **sans contenu réel** — `01-connexion.png`, `02-raisonnement-direct.png`
> *(v0.10)* et `05-memoire.png` *(v0.10)* — sont présentes et relues. Les entrées
> ⚠️ restent en attente d'un jeu de données fictives.

## Fichiers attendus

| Fichier | Section du tour | Peut être capturé sans contenu réel ? |
|---------|-----------------|:---:|
| `01-connexion.png` | 1 — page de connexion (champs masqués) | ✅ (pré-auth) |
| `01-premiere-vue.png` | 1 — écran de chat vide | ✅ (compte neuf) |
| `02-selecteur-modele.png` | 2 — liste des modèles | ⚠️ (noms de modèles) |
| `02-chat-streaming.png` | 2 — réponse en streaming (invite fictive) | ✅ |
| `02-raisonnement-direct.png` | 2 — raisonnement en direct *(v0.10)* | ✅ (invite fictive) |
| `03-workspace-modele.png` | 3 — modèle personnalisé | ⚠️ (contenu établissement) |
| `03-base-connaissances.png` | 3 — base de connaissances (RAG) | ⚠️ (contenu établissement) |
| `03-dossier-equipe.png` | 3 — dossier d'équipe *(v0.10)* | ✅ (compte neuf) |
| `04-canal.png` | 4 — fil de discussion d'un canal | ⚠️ (contenu établissement) |
| `05-parametres.png` | 5 — paramètres personnels | ✅ (identité masquée) |
| `05-memoire.png` | 5 — gestion de la mémoire *(v0.10)* | ✅ (compte neuf, vide) |

Les entrées ⚠️ exposent du contenu réel d'un établissement : elles restent
schématisées dans [`../architecture.md`](../architecture.md) tant qu'un jeu de
**données fictives** dédié n'est pas disponible.

## Règles

- **Aucune** capture ne doit montrer d'URL de tenant réel, d'e-mail nominatif, de
  clé d'API, de jeton ni de mot de passe.
- Chaque PNG est **relu en revue de PR** avant fusion.
- Régénérer les images après toute montée de version de l'interface (voir
  [`../capture/README.md`](../capture/README.md)).

---

*Assets — Tour de la plateforme (Epic #4433, sous #4427). FR-first.*
