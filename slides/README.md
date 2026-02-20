# Slides du cours Intelligence Artificielle

Presentations du cours IA 101 / CS 405, converties au format **Marp** (Markdown) pour edition et maintenance facilitees.

## Format et outils

Les slides sont au format [Marp](https://marp.app/) : du Markdown pur avec des directives de presentation. Cela permet a Claude (et a tout editeur) de lire et modifier le contenu et le layout directement en texte, sans passer par PowerPoint.

### Commandes Marp CLI

```bash
# Preview live dans le navigateur (hot-reload)
npx @marp-team/marp-cli --preview slides/08-ia-generative/slides.md

# Export HTML (un fichier par deck)
npx @marp-team/marp-cli slides/08-ia-generative/slides.md --html --allow-local-files -o slides/08-ia-generative/output/index.html

# Export PDF
npx @marp-team/marp-cli slides/08-ia-generative/slides.md --pdf --allow-local-files -o slides/08-ia-generative/output/slides.pdf

# Export PPTX (si besoin de revenir en PowerPoint)
npx @marp-team/marp-cli slides/08-ia-generative/slides.md --pptx --allow-local-files -o slides/08-ia-generative/output/slides.pptx

# Render tous les decks en HTML
for d in slides/*/slides.md; do
  out="$(dirname "$d")/output/index.html"
  mkdir -p "$(dirname "$out")"
  npx @marp-team/marp-cli "$d" --html --allow-local-files -o "$out"
done
```

### Theme personnalise

Le fichier `themes/ia101.css` definit le style visuel partage :
- Accent rouge-brique (#8B1A1A) sur fond gris clair (#F5F5F5)
- Classes : `title` (slide de titre), `section` (sommaire), `questions` (respiration), `crossref` (liens notebooks)
- Configuration Marp dans `.marprc.yml` (theme, HTML, fichiers locaux)

## Inventaire des decks

| # | Deck | Slides | Images | Lignes .md | Conversion |
|---|------|--------|--------|------------|------------|
| 01 | Introduction | 43 | 40 | 718 | Done |
| 02 | Resolution de problemes | 95 | 56 | 1423 | Done |
| 03 | Logique | 68 | 45 | 1201 | Done |
| 04 | Probabilites | 117 | 110 | 1370 | Done |
| 05 | Theorie des jeux | 42 | 54 | 729 | Done |
| 06 | Apprentissage | 126 | 140 | 2096 | Done |
| 07 | Elargissements | 42 | 2 | 644 | Done |
| 08 | IA Generative | 27 | 36 | 399 | Done |
| S1 | Argumentation | 50 | 9 | 656 | Done |
| S2 | IA exploratoire/symbolique | 58 | 54 | 909 | Done |
| S3 | Acculturation | 66 | 133 | 1383 | Done |
| S4 | Trading algorithmique | 81 | 0 | 1388 | Done |
| | **Total** | **815** | **679** | **12 916** | **12/12** |

Les decks 04, 05, S1 et 07 ont gagne des slides par eclatement de slides trop denses.

## Ameliorations appliquees

Chaque deck a beneficie d'une relecture qualitative (guidee par les `analysis/improvement_plan.md`) :

- **Hierarchie des puces** : sous-items indentes correctement (2 espaces)
- **Eclatement des slides denses** : les slides surchargees ont ete scindees en 2-3 slides
- **Cross-references notebooks** : liens vers les notebooks Jupyter pertinents en fin de section
- **Marqueurs TODO** : `<!-- TODO: ... -->` pour les visuels manquants a ajouter ulterieurement
- **Slides "Questions?"** : conservees comme pauses respiratoires entre sections

### Decks a ameliorer en priorite (visuels manquants)

1. **S4 - Trading algorithmique** : 81 slides, **0 images** - besoin complet de visuels
2. **07 - Elargissements** : 42 slides, **2 images** - quasi entierement textuel
3. **S1 - Argumentation** : 50 slides, **9 images** - ratio faible

## Structure par deck

```
slides/
  themes/
    ia101.css                # Theme Marp partage
  .marprc.yml                # Configuration Marp (theme, HTML, local files)
  .markdownlint.json         # Regles markdownlint adaptees a Marp
  _tools/
    pptx_to_marp.py          # Script de conversion PPTX -> Marp
    slide_tools.py           # Extraction PPTX (texte, images, inventaire)
    batch_extract_all.py     # Extraction batch des 12 decks
    slide_inventory.py       # Inventaire presentations etudiantes
  XX-nom-du-deck/
    slides.md                # Source Marp (livrable principal, commite)
    images/                  # Images referencees par slides.md (commite)
    output/                  # HTML/PDF generes par Marp CLI [.gitignore]
    original/                # PPTX de reference [.gitignore]
    extracted/
      content.md             # Texte markdown extrait du PPTX
      inventory.json         # Metadonnees (layout, mots, images par slide)
      renders/               # PNG de chaque slide PPTX [.gitignore]
      images/                # Images extraites du PPTX [.gitignore]
    analysis/
      improvement_plan.md    # Diagnostic qualitatif + plan d'amelioration
```

## Cross-references slides <-> notebooks

| Deck | Repertoire notebooks | Nb notebooks | Type |
|------|---------------------|--------------|------|
| 01 Introduction | (transversal) | - | Vue d'ensemble |
| 02 Resolution | `Search/`, `Sudoku/` | ~15 | Demo directe |
| 03 Logique | `SymbolicAI/`, `Lean/` | ~35 | Demo directe |
| 04 Probabilites | `Probas/`, `Infer/` | ~22 | Demo directe |
| 05 Theorie des jeux | `GameTheory/` | ~26 | Demo directe |
| 06 Apprentissage | `ML/`, `RL/` | ~8 | Demo partielle |
| 07 Elargissements | (transversal) | - | References |
| 08 IA Generative | `GenAI/` | ~58 | Demo riche |
| S1 Argumentation | `SymbolicAI/Argument_Analysis/` | 5 | Demo directe |
| S2 IA exploratoire | `Search/`, `Sudoku/`, `SymbolicAI/` | ~35 | TP pratique |
| S3 Acculturation | (transversal) | - | Vulgarisation |
| S4 Trading algo | `QuantConnect/` | ~27 | Demo directe |

## Pipeline de conversion

La conversion depuis les PPTX originaux s'est faite en plusieurs etapes :

1. **Extraction** : `slide_tools.py full-extract` -> `content.md`, `inventory.json`, images
2. **Conversion** : `pptx_to_marp.py` -> `slides.md` brut avec images migrees
3. **Relecture qualitative** : amelioration manuelle (hierarchie, splits, cross-refs, TODOs)
4. **Verification** : rendu Marp CLI sans erreur pour les 12 decks

## Decisions de conception

- **Format Marp** (Markdown) : lisible et editable en texte pur, versionnable dans git
- **Slides "Questions?"** conservees comme pauses respiratoires entre sections
- **Theme partage** (`ia101.css`) : coherence visuelle entre tous les decks
- **Images migrees depuis PPTX** : conservees dans `images/` par deck
- **PPTX originaux en .gitignore** : servent de reference mais ne sont pas edites
