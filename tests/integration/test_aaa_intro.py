"""Integration test: verify AdaptiveAssetAllocation quantbook intro/code alignment.

Closes the 3-confirmation audit-reassessment from issue #20354:
  1. Cell 0 intro must say 5 ETFs US large-cap (not 10 multi-asset)
  2. Cell 0 intro must state the period printed by the executed cell 5
     (not the 2008-2026 promise)
  3. Cell 3 code must load 5 tickers (the 5 that dropna() preserves)
  4. Cell 12 must NOT include Top N=6 (degenerate on 5 assets)
  5. Cell 21 conclusions must not say "10 ETFs multi-asset classes"
  6. Cell 21 conclusions must cite the Sharpe printed by the executed cell 12

The notebook runs in the LEAN Research container (QuantBook). The tests read
the committed outputs: the prose must quote the values of the execution that
is committed with it, so a re-execution that changes them fails here until
the prose is updated.

Run from repo root:
    python tests/integration/test_aaa_intro.py
"""
import json
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
NB_PATH = REPO_ROOT / 'MyIA.AI.Notebooks' / 'QuantConnect' / 'projects' / 'AdaptiveAssetAllocation' / 'quantbook.ipynb'


def get_cell_src(nb, idx: int) -> str:
    c = nb['cells'][idx]
    s = c.get('source', [])
    return ''.join(s) if isinstance(s, list) else s


def get_cell_text_output(nb, idx: int) -> str:
    """Concatenate the stream text and text/plain outputs of a code cell."""
    parts = []
    for o in nb['cells'][idx].get('outputs', []):
        if 'text' in o:
            t = o['text']
        else:
            t = o.get('data', {}).get('text/plain', '')
        parts.append(''.join(t) if isinstance(t, list) else t)
    return ''.join(parts)


# Module-level globals (set by setUpModule)
nb = None
cell0_src = None
cell2_src = None
cell3_src = None
cell12_src = None
cell21_src = None


def setUpModule():
    global nb, cell0_src, cell2_src, cell3_src, cell12_src, cell21_src
    if not NB_PATH.exists():
        raise unittest.SkipTest(f'Notebook not found: {NB_PATH}')
    nb = json.load(open(NB_PATH, 'r', encoding='utf-8'))
    cell0_src = get_cell_src(nb, 0)
    cell2_src = get_cell_src(nb, 2)
    cell3_src = get_cell_src(nb, 3)
    cell12_src = get_cell_src(nb, 12)
    cell21_src = get_cell_src(nb, 21)


class TestIntroCodeAlignment(unittest.TestCase):

    def test_intro_says_five_etfs_not_ten(self):
        """Cell 0 must say 5 ETFs (the effective count), not 10."""
        self.assertIn('5 ETFs', cell0_src,
                      'Cell 0 intro must state 5 ETFs (effective count after dropna)')
        # Old claim was 10 ETFs multi-asset -- must be gone from the intro
        self.assertNotIn('10 ETFs', cell0_src,
                         'Cell 0 intro must NOT say 10 ETFs (contradicts effective data)')

    def test_intro_period_matches_executed_output(self):
        """Cell 0 must state the period printed by the executed cell 5."""
        import re
        out = get_cell_text_output(nb, 5)
        m = re.search(r'P\S*riode: (\d{4}-\d\d-\d\d) \S+ (\d{4}-\d\d-\d\d)', out)
        self.assertIsNotNone(m, 'Cell 5 must carry its executed output (period line)')
        start, end = m.groups()
        self.assertIn(start, cell0_src,
                      f'Cell 0 must state the executed start date {start}')
        self.assertIn(end, cell0_src,
                      f'Cell 0 must state the executed end date {end}')
        self.assertNotIn('2008-2026', cell0_src,
                         'Cell 0 must NOT claim 2008-2026 (not the executed period)')

    def test_intro_mentions_dropna_or_docker_constraint(self):
        """Cell 0 must explain WHY the universe/period is limited."""
        # Acceptable mentions: Docker, dropna, disponible
        self.assertTrue(
            any(word in cell0_src for word in ('Docker', 'dropna', 'disponibilit')),
            'Cell 0 must explain the universe/period constraint (Docker/dropna/disponibilite)'
        )

    def test_chargement_says_five_etfs_not_ten(self):
        """Cell 2 (Chargement des donnees) must say 5 ETFs, not 10.

        Closes the gap flagged by NanoClaw review: the intro/cell 0 said 5 ETFs
        but cell 2 still said 'On charge les 10 ETFs', a contradiction that
        no test previously caught.
        """
        self.assertIn('5 ETFs', cell2_src,
                      'Cell 2 must say 5 ETFs (effective count after dropna)')
        self.assertNotIn('10 ETFs', cell2_src,
                         'Cell 2 must NOT say 10 ETFs (contradicts effective 5-asset universe)')

    def test_code_loads_five_tickers(self):
        """Cell 3 must load exactly 5 tickers (the effective count)."""
        # Tickers list literal in cell 3
        import re
        # Match list literal like ["SPY", "QQQ", ...]
        m = re.search(r'tickers\s*=\s*\[(.*?)\]', cell3_src, re.DOTALL)
        self.assertIsNotNone(m, 'Cell 3 must define a tickers list')
        tickers_str = m.group(1)
        # Count quoted strings
        tickers = re.findall(r'"([A-Z]+)"', tickers_str)
        self.assertEqual(len(tickers), 5,
                         f'Cell 3 must load exactly 5 tickers (got {len(tickers)}: {tickers})')
        # Must NOT load 10 tickers (the original claim)
        self.assertNotEqual(len(tickers), 10,
                            'Cell 3 must NOT load 10 tickers (contradicts effective 5-asset universe)')

    def test_top_n_test_excludes_six(self):
        """Cell 12 must NOT include Top N=6 (degenerate on 5 assets)."""
        import re
        m = re.search(r'top_n_values\s*=\s*\[(.*?)\]', cell12_src)
        self.assertIsNotNone(m, 'Cell 12 must define top_n_values list')
        values = [int(x.strip()) for x in m.group(1).split(',') if x.strip()]
        self.assertNotIn(6, values,
                         f'Cell 12 must NOT include Top N=6 (degenerate on 5 assets), got {values}')

    def test_top_n_test_acknowledges_constraint(self):
        """Cell 12 must explain WHY Top N is bounded by N assets available."""
        self.assertTrue(
            any(phrase in cell12_src for phrase in ('5 --', '5 actifs', 'N actifs', '3 a 5')),
            'Cell 12 must explain Top N bounded by 5 assets (comment or string)'
        )

    def test_conclusions_dont_claim_multi_asset(self):
        """Cell 21 must not claim 10 ETFs as the CURRENT implementation's universe.

        Mentions of 10 ETFs are allowed in forward-looking context
        ("would test", cloud migration, Prochaines etapes, original article).
        They are FORBIDDEN in "Points forts" / current scope.
        """
        # Find the "Points forts" section
        idx_pf = cell21_src.find('### Points forts')
        idx_lim = cell21_src.find('### Limites')
        end = idx_lim if idx_lim > 0 else len(cell21_src)
        if idx_pf > 0:
            scope = cell21_src[idx_pf:end]
        else:
            scope = cell21_src

        self.assertNotIn('10 ETFs', scope,
                         'Cell 21 "Points forts" must NOT claim 10 ETFs (effective is 5)')

        self.assertTrue(
            any(phrase in cell21_src for phrase in ('5 large-cap', '5 actifs', 'Limites', 'limite')),
            'Cell 21 must acknowledge the 5-asset limit (Limites or Diversification section)'
        )

    def test_conclusions_cite_executed_sharpe(self):
        """Cell 21 must quote the best Top N Sharpe printed by the executed cell 12."""
        import re
        out = get_cell_text_output(nb, 12)
        m = re.search(r'Meilleur Top N: (\d) \(Sharpe=([0-9.]+)\)', out)
        self.assertIsNotNone(m, 'Cell 12 must carry its executed output (best Top N line)')
        self.assertIn(m.group(2), cell21_src,
                      f'Cell 21 must cite the executed Sharpe {m.group(2)} (Top {m.group(1)})')


if __name__ == '__main__':
    unittest.main(verbosity=2)
