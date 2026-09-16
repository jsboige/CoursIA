# Parcours d'apprentissage CoursIA

Trois parcours narratifs — objectif, public, durée et sortie concrète — sont
livrés par l'équipe `docs/curriculum/`. Cinq autres pages listent les notebooks
par domaine thématique ; ce sont des **vues du catalogue**, pas des parcours
d'apprentissage, et elles sont régénérées chaque jour par `catalog-cron.yml`.

## Parcours narratifs

| # | Parcours | Public | Durée | Sortie |
|---|---------|--------|-------|--------|
| 1 | [Accéléré vers GenAI](docs/curriculum/genai-rush.md) | Développeur Python qui veut être opérationnel sur les APIs d'IA générative sans GPU | ~8-10 h | Boucle agentique texte, chaîne image, voix bidirectionnelle, agents `AgentGroupChat`, RAG Qdrant embarqué |
| 2 | [IA Symbolique et Formalisation](docs/curriculum/symbolic-formalization.md) | Étudiant ou ingénieur qui veut passer du symbolique « qui marche » à la formalisation vérifiée par machine | ~20 h | Quatre familles logiques Tweety, SMT Z3 avec capstone d'optimisation, planification Fast-Downward, trois preuves Lean 4 rejouées |
| 3 | [Recherche et Corpus (AIMA-inspired)](docs/curriculum/aima-walk.md) | Lecteur qui veut retraverser l'IA classique avec un manuel de référence (Russel & Norvig) et vérifier chaque concept sur du code | ~25-30 h | A*, CSP, logiques Tweety, Bayes PyMC, Nash, CFR, RL, pipeline LLM — plus la carte de ce que le corpus ajoute à AIMA |

Les trois pilotes suivent le modèle « Parcours alternatifs » du
[README GameTheory](MyIA.AI.Notebooks/GameTheory/README.md) : durée annoncée,
liste numérotée, clause de prérequis qui dit ce qui est supposé **et ce qui ne
l'est pas**. La matière première est l'inventaire des embryons de parcours
([`docs/curriculum/_inventory.md`](docs/curriculum/_inventory.md), EPIC
[#13844](https://github.com/jsboige/CoursIA/issues/13844)).

### Parcours par contraintes d'infrastructure

`[parcours.qmd](parcours.qmd)` répond à une question différente : *« avec quel
matériel puis-je avancer ? »*. Trois profils y sont documentés :

1. **Local sobre** — Python + Jupyter, sans GPU, sans Docker.
2. **ML.NET + symbolique** — ajout de .NET Interactive pour C# et Lean 4.
3. **GenAI complet** — Docker (ComfyUI, Qwen), GPU RTX 3090, services cloud.

C'est un axe orthogonal : les trois parcours narratifs ci-dessus sont chacun
réalisables dans le profil *Local sobre*, à l'exception de `genai-rush.md` qui
exige une clé OpenAI directe pour les étapes image et voix (deux endpoints non
relayés par les tiers).

## Vues du catalogue (par domaine)

Cinq pages listent les notebooks par thème. Elles sont **régénérées
automatiquement** chaque jour par
[`scripts/notebook_tools/generate_parcours.py`](scripts/notebook_tools/generate_parcours.py)
depuis `COURSE_CATALOG.generated.json`, et ne définissent aucun ordre
pédagogique : elles disent *ce qui existe*, pas *dans quel ordre le faire*.

| Page | Domaine |
|------|---------|
| [IA Classique](docs/curriculum/ia-classique.md) | Recherche, CSP, Sudoku |
| [IA Symbolique](docs/curriculum/ia-symbolique.md) | Lean, Tweety, SemanticWeb, Planning |
| [GenAI Multimodale](docs/curriculum/genai.md) | Image, Audio, Vidéo, Texte |
| [Trading Algorithmique](docs/curriculum/trading.md) | QuantConnect, ML, Probas |
| [Recherche Avancée](docs/curriculum/recherche.md) | Infer.NET, Pyro, IIT, RL, GameTheory |

Les comptes vivent dans les pages générées elles-mêmes — ils ne sont pas
épinglés ici, ou ils dériveraient silencieusement (constat 2026-08-05 : la
colonne manuelle était fausse d'un ordre de grandeur).

## Légende maturité

| Statut | Description |
|--------|-------------|
| PRODUCTION | Complets, exécutés, structure pédagogique finalisée |
| BETA | Fonctionnels, outputs présents, structure partielle |
| ALPHA | En cours de développement, outputs partiels |
| DRAFT | Non exécutés ou structure minimale |

## Niveaux de difficulté

- **Débutant** : PRODUCTION/BETA sans prérequis techniques (pas d'API/GPU/cloud)
- **Intermédiaire** : BETA/ALPHA avec configuration requise (clés API, Docker)
- **Avancé** : ALPHA/RESEARCH avec infrastructure spécialisée (GPU, QC Cloud, WSL)

## Comment choisir un parcours narratif

1. Lire la section « Public visé » du parcours pour vérifier que votre profil correspond.
2. Vérifier les prérequis : chaque pilote porte une table « Prérequis vérifiables en ~10 min » avec commande et succès attendu.
3. Suivre les étapes dans l'ordre : chaque étape porte explicitement ce qu'elle *suppose acquis* — la précédence n'est pas une convention, elle est lue sur la section Prérequis réelle du notebook (marquée « déclaré ») ou déduite de son contenu.
4. Si un parcours vous semble trop ambitieux ou pas assez, le tableau « Prolongements » à la fin de chaque pilote liste les briques voisines qui le prolongent.

## Génération des vues catalogue

Les pages `genai.md`, `ia-classique.md`, `ia-symbolique.md`, `trading.md` et `recherche.md` sont générées automatiquement via :

```bash
python scripts/notebook_tools/generate_parcours.py          # Générer tout
python scripts/notebook_tools/generate_parcours.py --check   # Vérifier couverture
python scripts/notebook_tools/generate_parcours.py --dry-run # Aperçu sans écriture
```

Source : `COURSE_CATALOG.generated.json` (mis à jour par `generate_catalog.py`).

Les pages narratives `genai-rush.md`, `symbolic-formalization.md`,
`aima-walk.md` et l'inventaire `_inventory.md` suivent la convention des pages
manuelles (préfixe underscore ou hors liste des cinq ids du générateur) : elles
n'appartiennent **pas** au catalogue et ne sont jamais écrasées par
`catalog-cron.yml`.

## Voir aussi

- [`README.md`](README.md) — racine du dépôt, section *Parcours recommandés*.
- [`index.md`](index.md) — index des thématiques, *« quelles thématiques ? »*.
- [`parcours.qmd`](parcours.qmd) — choix par contraintes d'infrastructure, *« avec quel matériel ? »*.
- [`COURSE_CATALOG.generated.md`](COURSE_CATALOG.generated.md) — catalogue vivant, *« quel notebook précis dans quelle série ? »*.
