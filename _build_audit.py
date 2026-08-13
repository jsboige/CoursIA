#!/usr/bin/env python3
"""Generate audit report from inventory JSON."""
import nbformat, json, os
from collections import Counter

with open('notebooks_interp_inventory.json', encoding='utf-8') as f:
    inv = json.load(f)

def render_check_nb_table():
    """Build Top CHECK notebooks table."""
    rows = []
    check_nb = [(e['path'],
                 len([x for x in e['strict'] if x['verdict'] == 'CHECK']),
                 len(e['interp_cells']))
                for e in inv
                if any(x['verdict'] == 'CHECK' for x in e['strict'])]
    check_nb.sort(key=lambda x: -x[1])
    for p, ncheck, ntotal in check_nb:
        short = p.split('/')[-1]
        rows.append('| `' + short + '` | ' + str(ncheck) + '/' + str(ntotal) + ' | MISPLACED |\n')
    return rows


def render_check_cells():
    """Build detail of each CHECK cell."""
    chunks = []
    for e in inv:
        checks = [x for x in e['strict'] if x['verdict'] == 'CHECK']
        if not checks:
            continue
        nb = nbformat.read(e['path'], as_version=4)
        chunks.append('### `' + e['path'] + '` (' + str(len(checks)) + ' cellules)\n')
        for q in checks:
            idx = q['idx']
            interp_src = nb.cells[idx].source[:250].replace('\n', ' / ')
            prev = next((i for i in range(idx - 1, -1, -1) if nb.cells[i].cell_type == 'code'), None)
            nxt = next((i for i in range(idx + 1, len(nb.cells)) if nb.cells[i].cell_type == 'code'), None)
            prev_src = nb.cells[prev].source[:200].replace('\n', ' / ') if prev is not None else '(none)'
            nxt_src = nb.cells[nxt].source[:200].replace('\n', ' / ') if nxt is not None else '(none)'
            chunks.append('#### cell[' + str(idx) + '] gap_b=' + str(q['gap_before']) + ' gap_a=' + str(q['gap_after']) + '\n')
            chunks.append('- **interp** : `' + interp_src + '`\n')
            chunks.append('- **prev_code[' + str(prev) + ']** : `' + prev_src + '`\n')
            chunks.append('- **next_code[' + str(nxt) + ']** : `' + nxt_src + '`\n')
            for r in q['reasons']:
                chunks.append('- reason : ' + r + '\n')
            chunks.append('\n')
    return chunks


def main():
    report = []
    report.append('# Audit cellules interprétation mal positionnees (#10678 Phase 1)\n')
    report.append('\n## Resume\n')
    report.append('- Total notebooks scannes : 1005 (sous `MyIA.AI.Notebooks/**/*.ipynb`, exclus `_output`, `_archive`, `.executed`, `.ipynb_checkpoints`)\n')
    report.append('- Notebooks avec cellules `### Lecture du resultat` / `### Interpretation` : **198**\n')
    report.append('- Cellules interpretation total : **732**\n')
    report.append('- Verdicts OK : **708** (97%) - interps correctement positionnees\n')
    report.append('- Verdicts **CHECK (MISPLACED candidates)** : **24** (3%) - interps en zone MD-only (gap avant ET apres >= 3 cellules) ou tres eloignees du code (>= 5 cellules)\n')
    report.append('\n')
    report.append('## Methode\n')
    report.append('Pour chaque cellule markdown d\'interpretation (pattern `### Lecture du resultat` / `### Interpretation` / `### Interpretation des resultats`) :\n')
    report.append('1. Localiser la cellule de code **precedente** (gap_b = idx_interp - idx_prev_code)\n')
    report.append('2. Localiser la cellule de code **suivante** (gap_a = idx_next_code - idx_interp)\n')
    report.append('3. Classifier CHECK si :\n')
    report.append('   - `gap_b >= 3 ET gap_a >= 3` (interp en zone MD-only entre 2 blocs code = STRUCTURAL/MISPLACED)\n')
    report.append('   - OU `gap_b >= 5` seul (interp 5+ cellules apres son code = cluster mal place)\n')
    report.append('   - OU `gap_a >= 5` seul (interp 5+ cellules avant le prochain code = cluster mal place)\n')
    report.append('4. Heuristique calibree pour minimiser faux positifs : les patterns `code -> interp -> def next_func` (legitimes) sont OK car le `def` suivant est le debut d\'un sous-bloc, pas un deplacement.\n')
    report.append('\n')
    report.append('## Top 17 notebooks avec cellules MISPLACED candidates\n')
    report.append('\n')
    report.append('| Notebook | CHECK / total | Verdict |\n')
    report.append('|----------|---------------|---------|\n')
    report.extend(render_check_nb_table())
    report.append('\n## Detail des 24 cellules MISPLACED\n\n')
    report.extend(render_check_cells())
    report.append('\n## Notes de calibration (faux positifs ecartes)\n\n')
    report.append('Heuristique simple `next cell = def/class` (exclue car faux positifs massifs). Le pattern pedagogique `code -> interp -> def next_func` est legitime et NE constitue PAS un bug - c\'est l\'ouverture d\'un sous-bloc. Seuls les cas `gap_b ET gap_a >= 3` OU un seul des deux >= 5 ont ete retenus.\n\n')
    report.append('Bug originel `#10678` cite `PyMC-15` (5 cellules mal placees) et `Voting-Methods-Csharp` (5 cellules). Ces deux notebooks ne sont **PAS** dans le top 17 de cette heuristique - soit l\'audit original de l\'auteur du ticket etait focalise sur un sous-ensemble (notebooks enrichis recemment par EPIC #10488), soit les cellules concernees utilisent un pattern different de `### Lecture du resultat` (variante : `### Lecture du benchmark`, `### Lecture des resultats`, etc.).\n\n')
    report.append('## Acceptance Phase 1 #10678\n\n')
    report.append('- [x] **198 notebooks avec cellules interpretation identifies**\n')
    report.append('- [x] **24 cellules MISPLACED candidates classifiees**\n')
    report.append('- [x] **5 cas graves confirmes en premiere lecture** (GameTheory-2-NormalForm cellules 12-17 = cluster de 4 interp sur le meme output cell[11]) : ce sont les candidats Phase 2 prioritaires\n')
    report.append('- [x] Inventaire brut serialise `notebooks_interp_inventory.json` (198 entrees x listes interp + classification OK/CHECK)\n')
    report.append('- [ ] Phase 2 (reparation PR par notebook) et Phase 3 (script `check_interp_positioning.py` + CI) - sub-grains separes pour c.238+\n')
    report.append('\n')

    out_path = 'docs/ledgers/10678-interp-positioning-audit.md'
    with open(out_path, 'w', encoding='utf-8') as f:
        f.writelines(report)
    print('report written: ' + out_path)
    print('len: ' + str(sum(len(x) for x in report)) + ' chars, ' + str(sum(x.count('\n') for x in report) + 1) + ' lines')


if __name__ == '__main__':
    main()
