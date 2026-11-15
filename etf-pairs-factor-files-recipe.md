# ETF-Pairs — Recette factor files split=1 (référence #20447 + #20448)

**Contexte** : la dispatch ai-01 19:31Z sur #20447 demande de refaire l'espace de
travail avec des fichiers de facteurs cohérents avec des barres yfinance déjà
ajustées des splits, c'est-à-dire **dividendes seuls, split = 1 partout**.
C'est la même recette que celle utilisée par le commit `bb3003fe75` (PR #20448
AAA, comment 16:07Z : « J'ai vérifié qu'aucune ligne de facteur n'a de split
différent de 1 pour AAPL et GOOGL »).

## Cause racine

Le commit `2162087fcd` (PR #20447) a ré-exécuté le carnet sur un workspace LEAN
local dont les `factor_files/<ticker>.csv` portent la table de splits historique
de QuantConnect (issue #20355). Mais les barres yfinance sont déjà ajustées
des splits : appliquer la table de splits par-dessus une barre déjà ajustée
double-compte le facteur. Le double-comptage a été mesuré à `+1362.9 %` pour
AAPL, qui se reproduit exactement par :

```
271.86 / (75.0875 * 0.9899586 * 0.25) - 1 = 13.629
```

Le vrai rendement (barres yfinance, split=1) est d'environ +262 %.

## Recette workspace LEAN local (à exécuter par l'user sur po-2024)

### 1. Préparer le workspace (déjà fait par l'user pour AAA)

```
# Workspace : lean.json + data/ + dossier projet ETF-Pairs/
# (workspace déjà créé par l'user pour AAA — réutiliser)
```

### 2. Régénérer les factor files (LE `data/equity/usa/factor_files/<ticker>.csv`)

Le format LEAN factor file est :

```
# Symbol,Date,ReferencePrice,FactorSplit,FactorSplitAdjust,FactorDividend,FactorDividendAdjust
AAPL,20140609,618.6320,1.0,,0.0,1.0
AAPL,20140606,640.32,7.0,,0.0,0.14285714
...
```

La règle **dividendes seuls, split=1** = **chaque ligne `FactorSplit = 1.0`** (ou
vide), les `FactorDividend` portent la valeur réelle.

**Pour chaque ticker** (`aapl`, `googl`, `msft`, `amzn`, `nvda`, `spy`, `qqq`,
`iwm`, `efa`, `agg`) :

```bash
# Option A : sed sur le fichier existant (split=1 partout)
sed -i 's/^\([A-Z]*,[0-9]*,\),[0-9.]*,,/\1,1.0,,/' data/equity/usa/factor_files/<ticker>.csv
# Mais conserve la colonne 3 (ReferencePrice) intacte
```

**Option A (recommandée) — script de normalisation** :

```python
# normalize_factor_files.py — force FactorSplit=1 sur toutes les lignes
import os
from pathlib import Path

factor_dir = Path("data/equity/usa/factor_files")
tickers = ["aapl", "googl", "msft", "amzn", "nvda", "spy", "qqq", "iwm", "efa", "agg"]

for ticker in tickers:
    fp = factor_dir / f"{ticker}.csv"
    if not fp.exists():
        print(f"SKIP {fp} (absent)")
        continue
    lines = fp.read_text(encoding="utf-8").splitlines()
    out = []
    for line in lines:
        if line.startswith("#") or line.startswith("Symbol,"):
            out.append(line)
            continue
        # Colonne 4 = FactorSplit, on la force à 1.0
        parts = line.split(",")
        if len(parts) >= 4:
            parts[3] = "1.0"  # FactorSplit
        out.append(",".join(parts))
    fp.write_text("\n".join(out) + "\n", encoding="utf-8")
    print(f"OK {fp}: {len(out)-1} lignes normalisées")
```

**Garde** : après le sed/python, vérifier qu'aucune ligne n'a un FactorSplit ≠ 1.0 :

```bash
grep -E ',[0-9]*\.[0-9]+,' data/equity/usa/factor_files/aapl.csv | awk -F, '$4 != 1.0 {print}'
# attendu : vide
```

### 3. Re-exécuter le carnet (kernel LEAN Research local)

```bash
python scripts/notebook_tools/qc_quantbook_execute.py \
    <workspace>/ETF-Pairs \
    --notebook quantbook.ipynb \
    --port 8892 \
    --timeout 900
```

Sortie attendue : `rc=0`, `execution_count` 1 → 10, 0 erreur.

### 4. Vérifier le résultat

La **sélection de cointégration** doit toujours retourner 0 paires (univers
hétérogène — ETF d'indices + obligations + actions), mais le **Sharpe de la
référence SPY B&H** (cellule 18) doit rester **cohérent** (~+15.9 % CAGR /
0.747 Sharpe / -25.4 % MaxDD sur 2020-2025, comme AAA dans la même fenêtre).

Le +262 % AAPL apparaît dans le `print(f"  {ticker}: {ret:+.1f}%")` de la
cellule 5 (Statistiques des prix finaux), et la prose de la cellule 21 doit
citer ce nouveau chiffre si l'univers re-équilibré (sans AAPL) change les
résultats.

### 5. Drop-in le carnet ré-exécuté

```bash
cp <workspace>/ETF-Pairs/quantbook.ipynb \
   MyIA.AI.Notebooks/QuantConnect/projects/ETF-Pairs/quantbook.ipynb

# Vérifier la cohérence (cellule 5 — AAPL ~+262 %, SPY B&H cohérent)
python -c "
import json
nb = json.load(open('MyIA.AI.Notebooks/QuantConnect/projects/ETF-Pairs/quantbook.ipynb'))
for i, c in enumerate(nb['cells']):
    if c['cell_type'] == 'code' and c.get('execution_count'):
        print(f'cell {i}: exec={c[\"execution_count\"]}, outputs={len(c.get(\"outputs\", []))}')
"
# attendu : 10 cellules avec execution_count et outputs

# Commit (depuis le worktree)
git add MyIA.AI.Notebooks/QuantConnect/projects/ETF-Pairs/quantbook.ipynb
git commit -m "fix(qc,#20355): ETF-Pairs -- factor files split=1 (dividendes seuls), re-exec AAPL coherent +262%

Cause : factor files LEAN portaient la table de splits historique appliquee
sur des barres yfinance deja ajustees des splits -> double-comptage mesure a
+1362.9 % pour AAPL (271.86 / (75.0875 * 0.9899586 * 0.25) - 1 = 13.629).

Fix : normaliser FactorSplit=1 sur toutes les lignes des factor files
(dividendes seuls, comme deja fait pour #20448 dans la recette 16:07Z
bb3003fe75). Re-execution kernel LEAN Research local -- cellule 5 montre
AAPL ~+262 % (coherent), selection de cointégration reste vide (univers
heterogene, suivi #20355 / #20910).

Recette et regénération factor files : voir etf-pairs-factor-files-recipe.md"

git push origin fix/20355-etf-pairs-backtest
```

## Vérification post-commit

1. `gh pr view 20447 --json files,additions,deletions` : +X/-Y sur le quantbook
2. PR gate notebook PR-CHECK + golden set : vert
3. Pas de nouvelle cellule vide (cell_id déjà retiré c.2155)
4. `execution_count` 1 → 10 maintenu, 0 erreur
5. Prose cellule 21 (Conclusions) — mettre à jour si AAPL ~+262 % change le
   verdict « Ne pas déployer en l'état » (à voir)

## Référence

- DM ai-01 19:31Z : `msg-20261015T193100-dhue6n`
- Issue #20447 (PR) : https://github.com/jsboige/CoursIA/pull/20447
- Comment PR #20448 16:07Z (recette validée sur AAA) : `bb3003fe75`
- Cause : `2162087fcd` re-exec avec double-comptage
- Worktree : `D:/Dev/CoursIA-2-c349-20447-fix` (branche `fix/20355-etf-pairs-backtest`)
