"""Integration test: verify AdaptiveAssetAllocation quantbook intro/code alignment.

Closes the 3-confirmation audit-reassessment from issue #20354:
  1. Cell 0 intro must say 5 ETFs US large-cap (not 10 multi-asset)
  2. Cell 0 intro must say 2011-2025 period (not 2008-2026)
  3. Cell 3 code must load 5 tickers (the 5 that dropna() preserves)
  4. Cell 12 must NOT include Top N=6 (degenerate on 5 assets)
  5. Cell 21 conclusions must not say "10 ETFs multi-asset classes"

The notebook uses QuantBook which can't run locally -- this test only verifies
the source code is internally consistent (markdown promises match code loads
and code load sizes). Re-execution is via QuantConnect Cloud (per CLAUDE.md
QuantConnect section).

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


def get_cell_outputs(nb, idx: int):
    c = nb['cells'][idx]
    return c.get('outputs', [])


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

    def test_intro_says_2011_2025_not_2008_2026(self):
        """Cell 0 must state the effective 2011-2025 period."""
        self.assertIn('2011', cell0_src,
                      'Cell 0 must mention 2011 (start of effective period)')
        self.assertIn('2025', cell0_src,
                      'Cell 0 must mention 2025 (end of effective period)')
        self.assertNotIn('2008-2026', cell0_src,
                         'Cell 0 must NOT claim 2008-2026 (period is truncated)')

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

    def test_dependent_outputs_cleared(self):
        """QuantBook-dependent outputs (cells 5, 7, 10, 12, 14, 16, 18, 20) must
        be cleared since the intro/code changed and re-execution is via QC Cloud."""
        for idx in [5, 7, 10, 12, 14, 16, 18, 20]:
            c = nb['cells'][idx]
            if c.get('cell_type') != 'code':
                continue
            outputs = c.get('outputs', [])
            self.assertEqual(len(outputs), 0,
                             f'Cell {idx} outputs must be cleared (re-execution via QC Cloud required), got {len(outputs)} output(s)')


if __name__ == '__main__':
    unittest.main(verbosity=2)
