# Mise en forme visuelle des notebooks — directives + verification de rendu

Source : mandat user 2026-06-23 (EPIC #3966). Les agents editent le markdown/code **sans voir le rendu**, ce qui laisse passer des pathologies de mise en forme invisibles a l'edition. Ce document donne (1) les **directives de formatage** et (2) le **pipeline de verification visuelle**.

## 1. Directives de formatage (HARD)

### 1.1 Hierarchie des titres
- **Un seul `#` (H1) par notebook = le titre**, dans le premier cell markdown. Tout le reste commence a `##`.
- Hierarchie **monotone** : pas de `###` (H3) suivi d'un `#` (H1) plus bas. Les sections = `##`, les sous-sections = `###`, etc.
- **Symptome a bannir** (`MULTI-H1`, `H1-DEEP`) : plusieurs H1 -> le vrai titre n'est plus visuellement distinct (« les titres sont difficilement visibles »).

### 1.2 Asides d'exercice : JAMAIS un heading
Un **indice / objectif / étape / conseil / note / remarque / attention / TODO** ne doit **jamais** etre ecrit en `#` ou `##` : il apparaitrait dans la **plus grande police** alors qu'il doit etre discret (« les indices apparaissent comme les elements de police la plus grande alors que ca devrait etre l'inverse »).

| A bannir | A utiliser |
|----------|-----------|
| `# Indice` / `## Objectif` / `# Etape 1` | **gras inline** `**Indice :**`, `**Objectif :**`, `**Etape 1 —**` |
| heading pour un aside court | liste a puces, ou blockquote `>` |
| (si vraie sous-section necessaire) | au plus `####`/`#####` (H4/H5), petit |

### 1.3 Grilles (Sudoku...) et sorties texte alignees
- Une grille en ASCII / texte aligne **doit etre dans un bloc code** (clotures triple-backtick) ou un `<pre>` — **jamais** du markdown ordinaire (la police proportionnelle casse l'alignement).
- Si la grille est une **sortie de cellule** mal alignee : corriger le **code d'affichage** (largeur fixe, separateurs, monospace) puis **re-executer** (C.2 Stop&Repair — jamais hand-editer la sortie, cf [secrets-hygiene.md](../../.claude/rules/secrets-hygiene.md) regle 6).

## 2. Detecteur source-level — `scan_md_hierarchy.py`

`scripts/notebook_tools/scan_md_hierarchy.py` parse le JSON notebook (render-agnostic) et flague :
- `HINT-AS-HEADING` — un aside ecrit en heading.
- `H1-DEEP` — un H1 hors du premier cell markdown.
- `MULTI-H1` — plus d'un H1 dans le notebook.

```bash
# Une famille
python scripts/notebook_tools/scan_md_hierarchy.py MyIA.AI.Notebooks/Sudoku
# Tout l'arbre
python scripts/notebook_tools/scan_md_hierarchy.py MyIA.AI.Notebooks
```

Etat initial (2026-06-23) : **261/676 notebooks flagges** (GenAI 71, QuantConnect 47, SymbolicAI 43, Sudoku 28, ML 23, Probas 17, GameTheory 14, Search 11, RL 5, CaseStudies 2).

## 3. Pipeline de verification VISUELLE (obligatoire apres fix)

Le scanner detecte ; **la verification finale est visuelle** (exigence user). Le rendu fidele :

```bash
# 1. Rendre le notebook en HTML (env mcp-jupyter)
conda run -n mcp-jupyter python -m nbconvert --to html \
  --output-dir /tmp/nbrender "MyIA.AI.Notebooks/Sudoku/Sudoku-1-Backtracking-Python.ipynb"
# 2. Servir en localhost (file:// est bloque dans Playwright MCP)
cd /tmp/nbrender && python -m http.server 8899 --bind 127.0.0.1 &
```

Puis dans Playwright MCP :
- `browser_navigate` -> `http://127.0.0.1:8899/<notebook>.html`
- `browser_evaluate` pour **mesurer** : `[...document.querySelectorAll('h1,h2,h3,h4,h5,h6')].map(h => ({tag:h.tagName, px:getComputedStyle(h).fontSize, text:h.textContent}))` — verifie qu'aucun aside n'est plus gros qu'une section.
- `browser_take_screenshot` pour la preuve visuelle (avant/apres).

### Pourquoi pas le blob GitHub directement
Le rendu notebook de `github.com/.../blob/...ipynb` est **React-virtualise** : seules les cellules visibles sont dans le DOM, et le scraping `querySelectorAll` ne voit que le chrome GitHub. Utile pour un **spot-check humain a l'oeil**, **pas** pour une mesure DOM fiable. Le rendu **nbconvert local** est deterministe et fidele.

## 4. Garde-fous (rollout)
- **Scope typo strict** : changer le **niveau** d'un heading n'est pas changer le **contenu** pedagogique. Ne jamais en profiter pour resoudre/stubber/relabeler un exercice (cf [exercise-example-labeling.md](../../.claude/rules/exercise-example-labeling.md), [anti-regression.md](../../.claude/rules/anti-regression.md)).
- **C.2** : modif markdown seule -> outputs precedents valides ; cellule code modifiee -> re-exec réelle, jamais scrub.
- **1 sujet par PR** (G.4/G.5) : rollout par famille / sous-lot, pas de composite.
- **Verifier visuellement** apres fix, pas seulement relancer le scanner.

## Voir aussi
- EPIC #3966 (mise en forme) ; #3967 (cet outillage) ; #3968 (rollout typo) ; #3969 (grilles Sudoku).
- [scripts-reference.md](scripts-reference.md) — catalogue scripts notebook.
- [.claude/rules/notebook-conventions.md](../../.claude/rules/notebook-conventions.md) — C.1/C.2/C.3.
