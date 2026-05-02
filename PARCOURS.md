# Parcours Pedagogiques CoursIA

Cinq parcours de formation en intelligence artificielle, du fondamentaux aux sujets avances.
Chaque parcours reference des notebooks tries par serie et maturite.

| # | Parcours | Notebooks | Focus |
|---|----------|-----------|-------|
| 1 | [IA Classique](docs/parcours/ia-classique.md) | 13 | Recherche, CSP, Sudoku |
| 2 | [IA Symbolique](docs/parcours/ia-symbolique.md) | 82 | Lean, Tweety, SemanticWeb, Planning |
| 3 | [GenAI Multimodale](docs/parcours/genai.md) | 68 | Image, Audio, Video, Texte |
| 4 | [Trading Algoritmique](docs/parcours/trading.md) | 56 | QuantConnect, ML, Probas |
| 5 | [Recherche Avancee](docs/parcours/recherche.md) | 51 | Infer.NET, Pyro, IIT, RL, GameTheory |

## Legend Maturite

| Statut | Description |
|--------|-------------|
| PRODUCTION | Complets, executes, structure pedagogique finalisee |
| BETA | Fonctionnels, outputs presents, structure partielle |
| ALPHA | En cours de developpement, outputs partiels |
| DRAFT | Non executes ou structure minimale |

## Niveaux de difficulte

- **Debutant** : PRODUCTION/BETA sans prerequis techniques (pas d'API/GPU/cloud)
- **Intermediaire** : BETA/ALPHA avec configuration requise (API keys, Docker)
- **Avance** : ALPHA/RESEARCH avec infrastructure specialisee (GPU, QC Cloud, WSL)

## Comment utiliser un parcours

1. Ouvrir la page du parcours (liens ci-dessus)
2. Commencer par les notebooks PRODUCTION (maturite la plus elevee)
3. Progresser vers les BETA puis ALPHA
4. Installer les prerequis indiques dans le premier notebook de chaque serie

## Generation

Les pages de parcours sont generees automatiquement via :

```bash
python scripts/notebook_tools/generate_parcours.py          # Generer tout
python scripts/notebook_tools/generate_parcours.py --check   # Verifier couverture
python scripts/notebook_tools/generate_parcours.py --dry-run # Apercu sans ecriture
```

Source : `COURSE_CATALOG.generated.json` (mis a jour par `generate_catalog.py`).
