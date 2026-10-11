# Tier chiffré — cas historiques (dépôt en attente)

Ce répertoire reçoit les blobs `*.json.gz.enc` du tier **chiffré** de la
strate 6 : les transcriptions de l'**Anschluss (1938)** et de **Matsui
(1933)** — les deux seules sources historiques nommables dans ce dépôt
(verrou nominatif #7742).

**État : dépôt en attente.** La passphrase est distribuée au cours — c'est
une décision de cours, pas de lane. Le port S6-B livre la machinerie
complète ; le dépôt du blob est un geste à une commande une fois la
passphrase fixée :

```python
from ict import extracts_tiers

# texte source hors dépôt (la garde refuse un fichier suivi par git)
resume = extracts_tiers.build_encrypted_tier(
    definitions,                     # schema extract_definition_v1
    "encrypted/historical_cases.json.gz.enc",
    passphrase,                      # jamais dans le dépôt
    plaintext_sources=["/chemin/hors/depot/anschluss_1938.txt"],
)
```

Ce que le chiffrement achète ici : de la **non-indexabilité**, pas de la
confidentialité — voir le [README du corpus](../README.md).

Le format du blob est le contrat EPITA (JSON UTF-8 → gzip → Fernet, clé
PBKDF2-HMAC-SHA256, 480 000 itérations, sel public constant) : un blob écrit
ici se déchiffre par le pipeline `argumentation_analysis` d'EPITA à passphrase
égale, et réciproquement.
