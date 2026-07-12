# region imports
from operator import attrgetter

from AlgorithmImports import *
# endregion


class PiotroskiFactors:

    field_map = {
        "roa": "operation_ratios.roa.one_year",
        "operating_cash_flow": "financial_statements.cash_flow_statement.cash_flow_from_continuing_operating_activities.twelve_months",
        "current_ratio": "operation_ratios.current_ratio.one_year",
        "ordinary_shares_number": "financial_statements.balance_sheet.ordinary_shares_number.twelve_months",
        "gross_margin": "operation_ratios.gross_margin.one_year",
        "assets_turnover": "operation_ratios.assets_turnover.one_year",
        "total_assets": "financial_statements.balance_sheet.total_assets.twelve_months",
        "long_term_debt": "financial_statements.balance_sheet.long_term_debt.twelve_months",
    }

    def __init__(self, f):
        for name, path in self.field_map.items():
            setattr(self, name, attrgetter(path)(f))

    @staticmethod
    def are_available(f):
        return all(
            not np.isnan(attrgetter(path)(f))
            for path in PiotroskiFactors.field_map.values()
        )
