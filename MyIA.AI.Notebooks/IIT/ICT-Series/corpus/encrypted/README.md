# Tier chiffré — cas historiques

Ce répertoire porte le blob `historical_cases.json.gz.enc` du tier **chiffré**
de la strate 6 : les transcriptions de l'**Anschluss (1938)** et de **Matsui
(1933)** — les deux seules sources historiques nommables dans ce dépôt
(verrou nominatif #7742). Provenance : extraits du corpus d'analyse
argumentative (dépôt EPITA), avec l'accord du mainteneur.

**Le texte en clair ne vit jamais dans le dépôt** — seule la forme chiffrée
`*.json.gz.enc` y est versionnée. La passphrase, elle, est **publiée par
design** dans [`.env.example`](../../.env.example) (décision user #7742) :
le but du chiffrement est la **non-indexabilité**, pas la confidentialité —
le texte n'apparaît ni dans la recherche GitHub ni dans un scrape naïf, et
son ouverture devient un geste délibéré. Voir le
[README du corpus](../README.md) pour la formulation qui fige cet arbitrage.

Un nouveau dépôt se fait hors dépôt — la garde du constructeur refuse une
source en clair suivie par git :

```python
from ict import extracts_tiers

# texte source hors dépôt (la garde refuse un fichier suivi par git)
resume = extracts_tiers.build_encrypted_tier(
    definitions,                     # schema extract_definition_v1
    "corpus/encrypted/historical_cases.json.gz.enc",
    passphrase,                      # jamais codée en dur dans le dépôt
    plaintext_sources=["/chemin/hors/depot/source.json"],
)
```

Le format du blob est le contrat EPITA (JSON UTF-8 → gzip → Fernet, clé
PBKDF2-HMAC-SHA256, 480 000 itérations, sel public constant) : un blob écrit
ici se déchiffre par le pipeline `argumentation_analysis` d'EPITA à passphrase
égale, et réciproquement.
