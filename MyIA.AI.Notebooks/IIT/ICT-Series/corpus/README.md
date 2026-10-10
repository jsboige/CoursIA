# Corpus strate 6 — jambe C3 (issue #7742)

Répertoire de corpus du port S6-B : le système d'extracts à tiers de la strate 6.
Design et scaffold d'origine : `jsboigeEpita/2025-Epita-Intelligence-Symbolique`
(`docs/coursia_contrib/s6_b_port_extracts_design.md`), dont le différement était
conditionné à l'acceptation de S6-A1 — PR EPITA #1516, mergée le 2026-07-24.
Code porté : [`ict/extracts_tiers.py`](../ict/extracts_tiers.py) ; validation :
[`ict/validate_extracts_tiers.py`](../ict/validate_extracts_tiers.py).

## Les quatre tiers (source d'autorité : body #7742)

| Tier | Contenu | Forme dans le dépôt |
|---|---|---|
| **Public en clair** (`public/`) | œuvres du domaine public — La Fontaine, tier fables | texte versionné |
| **Chiffré** (`encrypted/`) | Anschluss 1938, Matsui 1933 (transcriptions circulant librement) | blob `*.json.gz.enc`, passphrase distribuée au cours |
| **Référence + fetch runtime** (`references/`) | les deux items Chaplin | **jamais vendorés** — droits Roy Export S.A.S. ; `fetch_method` + chemin, texte récupéré à l'exécution |
| **Hors CoursIA** | le reste du corpus EPITA | reste chez EPITA, chiffré, non énuméré |

## Ce que le chiffrement achète ici

> **Ce que le chiffrement achète ici** : de la **non-indexabilité**, pas de la
> confidentialité. Dans un dépôt de cours public, la passphrase doit atteindre
> les étudiants — elle devient donc de fait publique. Ce que le chiffrement
> obtient réellement : le texte n'apparaît ni dans la recherche GitHub ni dans
> un scrape naïf, et son ouverture devient un geste délibéré. C'est suffisant
> pour l'usage visé ; ça ne doit pas être vendu pour autre chose.

(Formulation à figer telle quelle — arbitrage #7742.)

## Verrou nominatif

Le détail nominatif du corpus est **hors dépôt public**, à **quatre exceptions
décidées le 2026-08-31** (#7742) : les discours de l'**Anschluss (1938)**, de
**Matsui (1933)**, et les deux items **Chaplin — *Le Dictateur* (1940)**. La
ligne de partage n'est pas « historique vs fictionnel » mais **charge
politique vivante** : ce qui a un enjeu actuel reste chez EPITA, chiffré, et
cette liste-là ne se cite pas. Le fragment de meeting de Hynkel n'a aucune
transcription canonique : il est étiqueté **« fragment, pas reconstitution »**
partout où il va — c'est précisément ce qui en fait un contrôle honnête.

## Vie privée — invariants portés par le code

1. Le loader public (`ict.extracts_tiers.load_public_definitions`) ne sert que
   le tier public, vérifie des ids opaques (`fable_*`, `myth_*`, `legend_*`)
   et retire toute trace d'URL.
2. Le tier références ne porte **jamais** de texte (le loader le vérifie et
   refuse une fiche qui en porterait).
3. Tout artefact émis (summaries, stdout de validation) est opaque-id-only :
   `strip_text_fields` retire `text` et `full_text` avant émission.
4. Le constructeur de blob (`build_encrypted_tier`) **refuse** une source en
   clair suivie par git : le texte historique ne vit jamais en clair dans le
   dépôt.

## Usage

```python
from ict import extracts_tiers

# Tier public (fables, domaine public) — ids opaques, texte en clair
defs = extracts_tiers.load_public_definitions("corpus")

# Tier référence (fiches Chaplin — jamais de texte)
refs = extracts_tiers.load_fetch_references("corpus")

# Tier chiffré — passphrase par argument ou variable d'environnement
# ICT_S6B_PASSPHRASE (aucune valeur par défaut, jamais dans le dépôt)
hist = extracts_tiers.load_encrypted_definitions(
    "encrypted/historical_cases.json.gz.enc", passphrase="…")

# Toute émission passe par le summary opaque
print(extracts_tiers.opaque_summary(hist))
```

Dépôt du tier chiffré (une fois la passphrase de cours fixée) :

```bash
python -m ict.validate_extracts_tiers            # validation + round-trip
```

La passphrase se transmet par canal privé, jamais dans le dépôt, jamais sur
un dashboard (cf. règle secrets-hygiene).

## Provenance des textes publics

- **Le Loup et l'Agneau** (Fables, I.10) et **Le Loup et le Chien** (I.5),
  Jean de La Fontaine — transcription modernisée (ſ→s, accents) de l'édition
  Barbin 1678 relue sur Wikisource (`Fables de La Fontaine (éd. Barbin)/1/…`,
  texte validé). Domaine public. Codage AF expert des deux spécimens :
  notebook `ICT-Argumentation-BeliefTrajectories.ipynb` §8bis/§8ter.
