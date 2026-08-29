# Datasets du pipeline audiobook (EPIC #1028, passe P7)

Livrables de la passe P7 : des textes sources **arbitraires** pour valider le
contrat « livre arbitraire » du pipeline (P6, `scripts/audiobook_pipeline.py --book`)
sans dépendre du seul texte de développement (Boule de Suif).

## Contenu

| Fichier | Nature | Provenance |
|---|---|---|
| `le_horla_1887.txt` | Livre réel #2 — recueil complet *Le Horla* (1887), 251 Ko | [Project Gutenberg #10775](https://www.gutenberg.org/ebooks/10775), domaine public |
| `mlle_fifi_nouveaux_contes.txt` | Livre réel #3 — recueil *Mlle Fifi: Nouveaux Contes* (18 contes), 215 Ko | [Project Gutenberg #11597](https://www.gutenberg.org/ebooks/11597) (édition du 28/10/2024), domaine public |
| `synthetic/persona_test_book.txt` | Mini-livre **100 % synthétique** (conte court, 4 locuteurs, dialogues français standard `--`) | Écrit pour ce dataset — aucun personnage réel |
| `synthetic/persona_catalog.json` | Catalogue de personas synthétiques, validé contre le schéma Pydantic `v4.schemas.SpeakerCatalog` | Écrit pour ce dataset |

## Statut de droits

- **Guy de Maupassant est mort en 1893** : les deux recueils sont dans le
  domaine public en France et dans l'Union européenne (vie + 70 ans), et les
  éditions Project Gutenberg citées sont déclarées libres aux États-Unis. Les
  textes committés sont le corps littéraire seul, **boilerplate Project
  Gutenberg retiré** — *Le Horla* : en-tête `*** START ***` et back-matter
  `TABLE` + licence supprimés ; *Mlle Fifi* : en-tête `*** START ***` et table
  des matières de l'édition (18 titres nus) supprimés (cette édition ne porte
  pas de back-matter `TABLE`).
- Les personnages du mini-livre synthétique (`Mahaut Reverdy`, `Évariste
  Bonneau`, `Léonie Charpentre`, village de `Bréhal-sous-les-Saules`) sont
  entièrement fictifs et inventés pour ce dataset.

## Utilisation

```bash
# Segmentation déterministe réelle (aucun service appelé)
python scripts/audiobook_pipeline.py --dry-run \
    --book MyIA.AI.Notebooks/GenAI/Audio/04-Applications/datasets/le_horla_1887.txt

# Mesuré au 2026-08-22 : le_horla_1887 -> 1503 paragraphes, 251 chunks
#                      persona_test_book -> 21 paragraphes, 4 chunks
# Mesuré au 2026-08-29 : mlle_fifi_nouveaux_contes -> 1090 paragraphes, 182 chunks
```

## Mesures comparées (p2 dry-run, 2026-08-29)

| Texte | Paragraphes | Chunks | Taille | Lignes `--` | Occ. `--` | `«` |
|---|---|---|---|---|---|---|
| `boule_de_suif_full.txt` (texte de développement, défaut) | 385 | 64 | 109 Ko | 54 | 128 | 198 |
| `le_horla_1887.txt` | 1503 | 251 | 251 Ko | 452 | 596 | 350 |
| `mlle_fifi_nouveaux_contes.txt` | 1090 | 182 | 215 Ko | 47 | 101 | 483 |
| `synthetic/persona_test_book.txt` | 21 | 4 | — | — | — | — |

Tailles en octets du fichier ; `--` = marqueur de dialogue tiré en tête de
ligne ; `«` = guillemet ouvrant (discours rapporté). *Mlle Fifi* apporte un
profil distinct du *Horla* : narration dominante avec un fort discours
rapporté (`«` 483, le plus élevé du dataset) mais peu de dialogues tirés
(47 lignes `--`), là où le *Horla* (forme journal) en est riche (452). Deux
mix dialogue/narration différents pour exercer la segmentation p2 — et 18
contes indépendants pour des reprises partielles (`--from-pass`).

Le catalogue `persona_catalog.json` est consommable par la passe P3 (contexte
dramatique) et la passe de casting : champs `voice_register`, `prosody_defaults`,
`emotional_arc` alignés sur `CharacterProfile` du schéma v4.
