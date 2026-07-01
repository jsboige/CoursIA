# Génération reproductible des captures du Tour

[← Tour de la plateforme](../README.md)

Ce dossier contient le script qui **génère** les captures d'écran du
[tour](../README.md), de façon **reproductible** et **sans fuite de secret**.
Les images produites atterrissent dans [`../assets/`](../assets/).

> **Statut.** Le script cible une **instance réelle** via un **compte
> non-administrateur** (de préférence neuf, sans donnée réelle visible). Tant que
> les variables d'environnement ne sont pas renseignées, il se **met en pause
> automatiquement** (`test.skip`) — il ne s'exécute donc jamais, et n'échoue
> jamais, en intégration continue.

## Pourquoi un script plutôt que des captures à la main ?

- **Reproductibilité** : on régénère toutes les images d'un coup quand
  l'interface change (montée de version, refonte UI).
- **Anti-fuite par construction** : le masquage (`mask` de Playwright) est appliqué
  à *chaque* capture, plutôt que de compter sur un floutage manuel a posteriori.
- **Cohérence** : même fenêtre, même zoom, mêmes conditions partout.

## Principe anti-fuite

1. **Compte non-administrateur**, de préférence **neuf** — la session de capture
   n'a pas les droits d'admin, et un compte neuf ne voit **aucune donnée réelle**
   d'établissement.
2. **Surfaces sans contenu réel uniquement** — on ne capture que la connexion, un
   chat neuf sur invite fictive, et des panneaux de réglages vides. Les surfaces
   qui exposeraient du contenu (listes de modèles/bases internes, canaux) restent
   **schématisées** dans [`../architecture.md`](../architecture.md), pas capturées.
3. **Masquage** (`mask`) des zones sensibles (identité, e-mail) sur chaque image.
4. **Revue anti-fuite de chaque PNG en PR** avant fusion — relecture humaine des
   images générées.
5. **Aucune URL réelle dans l'image** : Playwright capture le *contenu de la page*,
   pas la barre d'adresse du navigateur.

## Configuration

Les identifiants et l'URL vivent dans un fichier `.env` **non commité** (le dépôt
ignore `*.env`). Copiez le gabarit et renseignez-le localement :

```bash
cp .env.example .env
# puis éditez .env avec l'URL de l'instance et le compte non-admin de capture
```

Variables attendues (voir [`.env.example`](.env.example)) :

| Variable | Rôle |
|----------|------|
| `DEMO_OWUI_URL` | URL de l'instance ciblée |
| `DEMO_OWUI_EMAIL` | E-mail du compte **non-admin** de capture |
| `DEMO_OWUI_PASSWORD` | Mot de passe de ce compte |
| `DEMO_OWUI_REASONING_MODEL` | *(optionnel)* nom d'un modèle « thinking » pour la capture du raisonnement en direct (v0.10) ; vide → capture sautée |

## Exécution

Depuis la racine du projet Playwright de la série QA (qui fournit déjà
`@playwright/test`) :

```bash
# charge le .env puis lance uniquement le script de capture
npx playwright test 00-Tour-Plateforme/capture/tour-captures.spec.ts
```

Les images sont écrites dans [`../assets/`](../assets/). **Vérifiez chaque image
visuellement** (revue anti-fuite) avant de la commiter.

> **Note sélecteurs.** Les sélecteurs du script sont volontairement robustes
> (rôles ARIA, libellés multilingues) mais devront être **confirmés contre la
> version live** de l'instance — comme pour la série QA, l'interface peut dériver
> d'une version à l'autre.

---

*Capture — Tour de la plateforme (Epic #4433, sous #4427). FR-first. 0 secret commité.*
