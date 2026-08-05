# Parcours Pedagogiques CoursIA

Cinq parcours de formation en intelligence artificielle, des fondamentaux aux sujets avances.
Chaque parcours reference des notebooks tries par serie et maturite.

| # | Parcours | Focus |
|---|----------|-------|
| 1 | [IA Classique](docs/curriculum/ia-classique.md) | Recherche, CSP, Sudoku |
| 2 | [IA Symbolique](docs/curriculum/ia-symbolique.md) | Lean, Tweety, SemanticWeb, Planning |
| 3 | [GenAI Multimodale](docs/curriculum/genai.md) | Image, Audio, Video, Texte |
| 4 | [Trading Algorithmique](docs/curriculum/trading.md) | QuantConnect, ML, Probas |
| 5 | [Recherche Avancee](docs/curriculum/recherche.md) | Infer.NET, Pyro, IIT, RL, GameTheory |

> Les comptes de notebooks par parcours vivent dans les pages generees elles-memes
> (regenerees chaque jour depuis le catalogue par `catalog-cron.yml`) -- ils ne sont
> pas epingles ici, ou ils derivaient silencieusement (constat 2026-08-05 : la
> colonne manuelle etait fausse d'un ordre de grandeur, 13/82/68/56/51 pour des
> pages a 143/221/135/198/173).

## Legende maturite

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
