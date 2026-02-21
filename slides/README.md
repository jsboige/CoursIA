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

| # | Deck | Slides | Images | Lignes .md | Statut |
|---|------|--------|--------|------------|--------|
| 01 | Introduction | 46 | 40 | 706 | Corrige |
| 02 | Resolution de problemes | 100 | 56 | 1552 | Corrige |
| 03 | Logique | 100 | 45 | 1399 | Corrige |
| 04 | Probabilites | 118 | 110 | 1763 | Corrige |
| 05 | Theorie des jeux | 43 | 54 | 782 | Corrige |
| 06 | Apprentissage | 127 | 140 | 2206 | Corrige |
| 07 | Elargissements | 42 | 9 | 683 | Enrichi |
| 08 | IA Generative | 28 | 36 | 432 | Corrige |
| S1 | Argumentation | 51 | 20 | 693 | Enrichi |
| S2 | IA exploratoire/symbolique | 58 | 54 | 1025 | Corrige |
| S3 | Acculturation | 72 | 133 | 2037 | Corrige |
| S4 | Trading algorithmique | 128 | 14 | 1873 | Enrichi |
| | **Total** | **913** | **711** | **15 151** | **12/12** |

Les decks marques "Enrichi" ont recu des images libres de droits (Wikimedia Commons, CC BY-SA / CC0) en plus des corrections de contenu.

## Ameliorations appliquees

Chaque deck a beneficie d'une relecture qualitative (guidee par les `analysis/improvement_plan.md`) :

- **Hierarchie des puces** : sous-items indentes correctement (2 espaces)
- **Eclatement des slides denses** : les slides surchargees ont ete scindees en 2-3 slides
- **Cross-references notebooks** : liens vers les notebooks Jupyter pertinents en fin de section
- **Enrichissement textuel** : reformulation des fragments telegraphiques, ajout d'exemples et de contexte
- **Slides "Questions?"** : conservees comme pauses respiratoires entre sections
- **Images libres de droits** : ajout d'illustrations Wikimedia Commons (CC BY-SA, CC0) pour les decks pauvres en visuels

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
