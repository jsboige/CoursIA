# Sécurité et méthode

[← README AI-Engine-WordPress](../../README.md)

La sécurité n'est pas une section de plus : c'est une contrainte de méthode qui
s'applique à tout ce dossier. Elle regroupe la politique « pas de secret dans
les supports », le notebook qui mesure ce que les tests structurels ne voient
pas, et le renvoi à la posture PII du dépôt.

## Pas de secret dans les supports

Comme pour le dossier Open-WebUI voisin :

- **Aucun secret exposé** : pas d'URL d'admin, pas de clé d'API, pas
  de token MCP, pas de credentials WordPress.
- **Aucune capture d'écran**, ce qui est le moyen le plus sûr de
  tenir la ligne précédente. Un écran de `wp-admin` expose son
  contexte — compte connecté, domaines, extensions installées —
  indépendamment de la page affichée, et une capture retouchée n'est
  pas vérifiable par le lecteur. La
  [note de méthode](../04-Cas-Usage-livresagites/livresagites-parcours.md#note-de-méthode--pourquoi-il-ny-a-aucune-capture)
  détaille l'arbitrage et ce qu'illustrer proprement supposerait.
- **Aucun contenu privé livresagités** : le cas d'usage est décrit à
  un niveau architectural (structures, comptages, familles d'outils),
  jamais avec les contenus réels du site — ni texte de manuscrit, ni
  nom de personne, ni titre d'ouvrage.
- **Documentation de patterns, pas de credentials** : les exemples
  PHP dans ce dossier utilisent des *constantes de substitution*
  (`YOUR_OPENAI_API_KEY`, `YOUR_VECTOR_STORE_ID`), jamais des
  valeurs réelles.

Les fichiers `.env` réels ne sont jamais commités (`*.env` est
gitignoré) — seuls les `*.env.example` documentent les variables
attendues.

## Posture PII du dépôt

Ce dossier applique localement la règle du dépôt public tout entier —
aucune donnée étudiante, aucun identité, aucun artifact nominatif —
décrite dans [`PRIVACY.md`](../../../../../PRIVACY.md) (§1) à la racine
du dépôt.

## Notebooks

- [`auditer-la-conformite-visuelle.ipynb`](auditer-la-conformite-visuelle.ipynb) —
  smoke test structurel vs conformité visuelle : contraste WCAG, primaires
  Bootstrap, affordance des CTA. Quatre pages synthétiques portant une
  violation délibérée chacune, trois détecteurs dédiés, et la démonstration
  que le smoke test est aveugle aux trois classes de défauts. C'est la classe
  *visuelle* du motif « la sonde ment » documenté pour la classe *système*
  dans
  [`verification-verte-systeme-casse.md`](../../../../../docs/reference/verification-verte-systeme-casse.md).

## Voir aussi

- [Note de méthode du parcours livresagités](../04-Cas-Usage-livresagites/livresagites-parcours.md#note-de-méthode--pourquoi-il-ny-a-aucune-capture) — pourquoi une capture de `wp-admin` n'est pas assainissable
- [`verification-verte-systeme-casse.md`](../../../../../docs/reference/verification-verte-systeme-casse.md) — le motif général « une vérification qui passe n'établit pas l'état qu'elle prétend »
