# Slides du cours Intelligence Artificielle

Presentations du cours IA 101 / CS 405 au format **Slidev** (Markdown + Vue), editables en texte pur et versionnees dans git.

## Format et outils

Les slides sont ecrits en Slidev ([slidev.antfu.me](https://sli.dev/)) : du Markdown avec directives de layout, composants Vue optionnels, et hot-reload via `@slidev/cli`. Chaque deck est un fichier `slides.md` isole dans son dossier, avec son propre `package.json` au niveau racine `slides/` qui installe l'environnement commun.

### Installation une fois

```bash
cd slides
npm install
```

### Commandes Slidev

```bash
# Preview live dans le navigateur (hot-reload), depuis le dossier du deck
cd slides/01-introduction && npx slidev slides.md

# Port personnalise pour servir plusieurs decks en parallele
cd slides/02-resolution-problemes && npx slidev slides.md --port 3032
cd slides/03-logique && npx slidev slides.md --port 3030

# Export HTML statique (SPA)
cd slides/08-ia-generative && npx slidev build

# Export PDF
cd slides/08-ia-generative && npx slidev export --output slides.pdf
```

Scripts raccourcis (`slides/package.json`) : `npm run dev`, `npm run build`, `npm run export`.

### Theme personnalise

Le dossier `theme-ia101/` contient le theme Slidev partage par tous les decks :
- Accent rouge-brique (`#8B1A1A`) sur fond gris clair (`#F5F5F5`)
- Layouts custom (`cover`, `section`, `questions`, `image-overlay`, `dense`, `two-cols`)
- Reference dans le frontmatter : `theme: ../theme-ia101`

Les images pleine-largeur utilisent le layout **`image-overlay`** (fond d'image + texte par-dessus), jamais en colonne droite — convention validee pour la coherence visuelle.

## Inventaire des decks

| # | Deck | Dossier | Ligne `slides.md` | Images | Sessions |
|---|------|---------|-------------------|--------|----------|
| 01 | Introduction a l'IA | `01-introduction/` | ~772 | 40 | EPITA, ECE, EPF |
| 02 | Resolution de problemes | `02-resolution-problemes/` | ~1551 | 56 | EPITA, EPF |
| 03 | Logique | `03-logique/` | ~1969 | 45 | EPITA, EPF |
| 04 | Probabilites | `04-probabilites/` | ~1945 | 110 | EPITA, ECE, EPF |
| 05 | Theorie des jeux | `05-theorie-des-jeux/` | ~705 | 54 | EPITA, EPF |
| 06 | Apprentissage | `06-apprentissage/` | ~2394 | 140 | EPITA, ECE, EPF |
| 07 | Elargissements | `07-elargissements/` | ~642 | 9 | EPITA, EPF |
| 08 | IA Generative | `08-ia-generative/` | ~464 | 36 | EPITA, ECE, EPF |
| S1 | Argumentation | `S1-argumentation/` | ~791 | 20 | Sessions avancees |
| S2 | IA exploratoire/symbolique | `S2-ia-exploratoire-symbolique/` | ~1112 | 54 | Sessions avancees |
| S3 | Acculturation IA | `S3-acculturation/` | ~2039 | 133 | Sessions avancees |
| S4 | Trading algorithmique | `S4-trading-algorithmique/` | ~2761 | 15 | ESGF |
| S4 | Trading exercices | `S4-trading-exercices/` | ~871 | 0 | ESGF |

Le decompte exact de slides se fait au runtime Slidev (les separateurs `---` incluent aussi les frontmatter locaux des layouts custom). Lancer le serveur pour voir le compteur pagine.

## Cross-references slides <-> notebooks

Chaque deck pointe vers les notebooks Jupyter pertinents dans `MyIA.AI.Notebooks/` :

| Deck | Notebooks references | Type |
|------|----------------------|------|
| 01 Introduction | (transversal) | Vue d'ensemble |
| 02 Resolution | `Search/`, `Sudoku/` | Demo directe |
| 03 Logique | `SymbolicAI/`, `Lean/` | Demo directe |
| 04 Probabilites | `Probas/`, `Infer/` | Demo directe |
| 05 Theorie des jeux | `GameTheory/` | Demo directe |
| 06 Apprentissage | `ML/`, `RL/` | Demo partielle |
| 07 Elargissements | (transversal) | References |
| 08 IA Generative | `GenAI/` | Demo riche |
| S1 Argumentation | `SymbolicAI/Argument_Analysis/` | Demo directe |
| S2 IA exploratoire | `Search/`, `Sudoku/`, `SymbolicAI/` | TP pratique |
| S3 Acculturation | (transversal) | Vulgarisation |
| S4 Trading algo | `QuantConnect/` | Demo directe (27 notebooks + 89 strategies) |

## Structure par deck

```
slides/
  package.json               # Slidev CLI + theme-default + playwright-chromium
  theme-ia101/               # Theme Slidev partage (layouts, styles, composants Vue)
    index.ts
    layouts/                 # cover, section, questions, image-overlay, dense, two-cols
    styles/
    package.json
  _tools/                    # Scripts conversion PPTX (historique)
    pptx_to_marp.py          # Etape 1 : PPTX -> Markdown brut
    marp_to_slidev.py        # Etape 2 : normalisation Slidev + layouts
    slide_tools.py           # Extraction PPTX (texte, images, inventaire)
    batch_extract_all.py     # Extraction batch des 12 decks
    compare_marp_pptx.py     # Diff visuel PPTX <-> rendu Slidev
  analysis/                  # Rapports audits visuels cross-deck
  XX-nom-du-deck/
    slides.md                # Source Slidev (livrable principal, commite)
    images/                  # Images referencees par slides.md (commite)
    pptx-reference/          # Renders PNG du PPTX d'origine pour audit visuel (commite)
    analysis/                # Audits PPTX<->Slidev, mapping, vision compare
      mapping-YYYYMMDD.md
      visual-audit-deckNN.md
    public/                  # Assets statiques Slidev (optionnel)
```

## Pipeline de conversion (historique)

Les decks 01-08 et S1-S4 ont ete convertis depuis des PPTX originaux en deux temps :

1. **PPTX -> Marp** via `_tools/pptx_to_marp.py` (extraction texte + images + inventaire)
2. **Marp -> Slidev** via `_tools/marp_to_slidev.py` (normalisation frontmatter, conversion layouts, migration theme `ia101.css` vers `theme-ia101/`)
3. **Relecture qualitative** : hierarchie des puces, eclatement des slides denses, cross-references notebooks, enrichissement textuel
4. **Audits visuels PPTX <-> Slidev** : mapping manuel + verification sk-agent glm-4.6v + screenshots Playwright par slide

Le format Marp n'est plus utilise pour editer les slides — les scripts de conversion restent disponibles pour d'eventuels nouveaux decks PPTX a importer.

## Audits visuels

Chaque deck critique (cours imminent) fait l'objet d'un audit visuel strict :
- **Mapping PPTX <-> Slidev** : paires de titres, SPLIT/MERGE/MISSING/EXTRA
- **Vision compare** : `mcp__sk-agent__call_agent` (model `glm-4.6v`) avec screenshots cote-a-cote
- **Screenshots Playwright** : `?clicks=99` pour capturer le contenu complet apres toutes les animations
- **Rapport** : `<deck>/analysis/visual-audit-deck<NN>.md` avec verdict par slide (MATCH / PARTIAL / DIFFERENT)

Regles de base pour les images et le layout :
- Zero image mal taillee (ratio respecte, pas d'ecrasement ni d'etirement)
- Zero superposition texte/image
- Zero overflow (contenu coupe en bas = rejet)
- Positionnement explicite (top/right/width documentes, jamais par defaut)
- Coherence visuelle inter-slides

## Decisions de conception

- **Slidev** (Markdown + Vue) : hot-reload, layouts custom, composants Vue pour interactivite, export HTML/PDF
- **Theme-ia101 partage** : coherence visuelle entre tous les decks (13 au total)
- **Images en overlay** : layout `image-overlay` pour les slides image-dominantes, jamais en colonne droite (convention issue #221, confirmee 5+ fois)
- **Slides "Questions?"** conservees comme pauses respiratoires entre sections
- **PPTX-reference en `.gitignore` ou committe** selon le deck : les renders PNG servent a l'audit visuel
- **Cross-references notebooks** : chaque deck termine ses sections par un lien vers le notebook Jupyter correspondant
