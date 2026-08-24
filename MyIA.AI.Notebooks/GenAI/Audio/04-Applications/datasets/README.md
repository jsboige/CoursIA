# Datasets du pipeline audiobook (EPIC #1028, passe P7)

Livrables de la passe P7 : des textes sources **arbitraires** pour valider le
contrat « livre arbitraire » du pipeline (P6, `scripts/audiobook_pipeline.py --book`)
sans dépendre du seul texte de développement (Boule de Suif).

## Contenu

| Fichier | Nature | Provenance |
|---|---|---|
| `le_horla_1887.txt` | Livre réel #2 — recueil complet *Le Horla* (1887), 251 Ko | [Project Gutenberg #10775](https://www.gutenberg.org/ebooks/10775), domaine public |
| `synthetic/persona_test_book.txt` | Mini-livre **100 % synthétique** (conte court, 4 locuteurs, dialogues français standard `--`) | Écrit pour ce dataset — aucun personnage réel |
| `synthetic/persona_catalog.json` | Catalogue de personas synthétiques, validé contre le schéma Pydantic `v4.schemas.SpeakerCatalog` | Écrit pour ce dataset |

## Statut de droits

- **Guy de Maupassant est mort en 1893** : l'œuvre est dans le domaine public
  worldwide (vie + 70 ans révolus depuis longtemps). Le texte committé est le
  corps littéraire seul, **boilerplate Project Gutenberg retiré** (en-tête
  `*** START ***` et back-matter `TABLE` + licence supprimés).
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
```

Le catalogue `persona_catalog.json` est consommable par la passe P3 (contexte
dramatique) et la passe de casting : champs `voice_register`, `prosody_defaults`,
`emotional_arc` alignés sur `CharacterProfile` du schéma v4.
