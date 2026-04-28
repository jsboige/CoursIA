# region imports
from AlgorithmImports import *
# endregion


class PiotroskiScore:

    # Source: https://www.anderson.ucla.edu/documents/areas/prg/asam/2019/F-Score.pdf

    def get_score(self, factors):
        return (
            self.roa_score(factors)   # ROA
            + self.operating_cash_flow_score(factors)  # CFO
            + self.roa_change_score(factors)  # ROA Change
            + self.accruals_score(factors)  # ACCRUAL
            + self.leverage_score(factors)  # Leverage Change
            + self.liquidity_score(factors)  # Liquidity Change
            + self.share_issued_score(factors)  # Equity Offer
            + self.gross_margin_score(factors)  # Margin Change
            + self.asset_turnover_score(factors)  # Turnover Change
        )

    def roa_score(self, factors):
        '''Profitability - Return of Asset sub-score'''
        return int(factors[0].roa > 0)

    def operating_cash_flow_score(self, factors):
        '''Profitability - Operating Cash Flow sub-score'''
        return int(factors[0].operating_cash_flow > 0)

    def roa_change_score(self, factors):
        '''Profitability - Change in Return of Assets sub-score'''
        return int(factors[0].roa > factors[1].roa)

    def accruals_score(self, factors):
        '''Profitability - Accruals sub-score'''
        operating_cashflow = factors[0].operating_cash_flow
        roa = factors[0].roa
        total_assets = factors[1].total_assets
        return int(operating_cashflow / total_assets > roa)

    def leverage_score(self, factors):
        '''Leverage, Liquidity and Source of Funds - Change in Leverage sub-score'''
        lt_t = factors[0].long_term_debt
        lt_t1 = factors[1].long_term_debt
        a_t = factors[0].total_assets
        a_t1 = factors[1].total_assets
        a_t2 = factors[2].total_assets

        avg_assets_t  = (a_t  + a_t1) / 2.0
        avg_assets_t1 = (a_t1 + a_t2) / 2.0

        leverage_t  = lt_t  / avg_assets_t
        leverage_t1 = lt_t1 / avg_assets_t1

        return int(leverage_t < leverage_t1)

    def liquidity_score(self, factors):
        '''Change in current ratio between current and prior year'''
        return int(factors[0].current_ratio > factors[1].current_ratio)

    def share_issued_score(self, factors):
        '''Whether firm did not issue common equity'''
        return int(factors[0].ordinary_shares_number <= factors[1].ordinary_shares_number)

    def gross_margin_score(self, factors):
        '''Change in gross margin ratio'''
        return int(factors[0].gross_margin > factors[1].gross_margin)

    def asset_turnover_score(self, factors):
        '''Change in asset turnover ratio'''
        return int(factors[0].assets_turnover > factors[1].assets_turnover)
