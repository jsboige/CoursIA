# Génération reproductible des captures du Tour

[← Tour de la plateforme](../README.md)

Ce dossier contient le script qui **génère** les captures d'écran du
[tour](../README.md), de façon **reproductible** et **sans fuite de secret**.
Les images produites atterrissent dans [`../assets/`](../assets/).

> **Statut.** Le script vise un **tenant de démonstration** dédié, qui n'est pas
> encore en ligne au moment où ce chapitre est écrit (en attente de
> provisionnement). Tant que les variables d'environnement ne sont pas
> renseignées, le script se **met en pause automatiquement** (`test.skip`) — il ne
> s'exécute donc jamais, et n'échoue jamais, en intégration continue.

## Pourquoi un script plutôt que des captures à la main ?

- **Reproductibilité** : on régénère toutes les images d'un coup quand
  l'interface change (montée de version, refonte UI).
- **Anti-fuite par construction** : le masquage (`mask` de Playwright) est appliqué
  à *chaque* capture, plutôt que de compter sur un floutage manuel a posteriori.
- **Cohérence** : même fenêtre, même zoom, mêmes données fictives partout.

## Principe anti-fuite

1. **Tenant de démonstration** dédié — jamais une instance de production.
2. **Compte non-administrateur** — la session de capture n'a pas les droits
   d'admin (les vues admin sensibles restent schématisées dans
   [`../architecture.md`](../architecture.md), pas capturées).
3. **Données fictives** uniquement dans le tenant de démonstration.
4. **Masquage** (`mask`) des zones sensibles (identité, e-mail) sur chaque image.
5. **Revue des PNG en PR** avant fusion — relecture humaine des images générées.

## Configuration

Les identifiants et l'URL du tenant de démonstration vivent dans un fichier
`.env` **non commité** (le dépôt ignore `*.env`). Copiez le gabarit et
renseignez-le localement :

```bash
cp .env.example .env
# puis éditez .env avec l'URL et le compte non-admin du tenant de démo
```

Variables attendues (voir [`.env.example`](.env.example)) :

| Variable | Rôle |
|----------|------|
| `DEMO_OWUI_URL` | URL du tenant de démonstration |
| `DEMO_OWUI_EMAIL` | E-mail du compte **non-admin** de démonstration |
| `DEMO_OWUI_PASSWORD` | Mot de passe de ce compte |

## Exécution (une fois le tenant de démo en ligne)

Depuis la racine du projet Playwright de la série QA (qui fournit déjà
`@playwright/test`) :

```bash
# charge le .env puis lance uniquement le script de capture
npx playwright test 00-Tour-Plateforme/capture/tour-captures.spec.ts
```

Les images sont écrites dans [`../assets/`](../assets/). Vérifiez-les visuellement
avant de les commiter.

> **Note sélecteurs.** Les sélecteurs du script sont volontairement robustes
> (rôles ARIA, libellés multilingues) mais devront être **confirmés contre la
> version live** du tenant de démonstration — comme pour la série QA, l'interface
> peut dériver d'une version à l'autre. Cette confirmation fait partie de l'étape
> « captures live » (différée).

---

*Capture — Tour de la plateforme (Epic #4433, sous #4427). FR-first. 0 secret commité.*
