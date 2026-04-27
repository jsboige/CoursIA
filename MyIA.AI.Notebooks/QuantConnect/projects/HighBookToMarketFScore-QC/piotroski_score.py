# region imports
from AlgorithmImports import *
# endregion


class PiotroskiScore:

    # Source: https://www.anderson.ucla.edu/documents/areas/prg/asam/2019/F-Score.pdf

    def get_score(self, factors):
        return (
            self.roa_score(factors)   # ROA
            + self.operating_cash_flow_score(factors)  # CFO
            + self.roa_change_score(factors)  # ΔROA
            + self.accruals_score(factors)  # ACCRUAL
            + self.leverage_score(factors)  # ΔLEVER
            + self.liquidity_score(factors)  # ΔLIQUID
            + self.share_issued_score(factors)  # EQ_OFFER
            + self.gross_margin_score(factors)  # ΔMARGIN
            + self.asset_turnover_score(factors)  # ΔTURN
        )

    def roa_score(self, factors):
        '''Get the Profitability - Return of Asset sub-score of Piotroski F-Score

        "I define ROA ... as net income before extraordinary items ..., scaled by
        beginning of the year total assets." (p. 7)

        "Net income before extraordinary items for the fiscal year preceding
        portfolio formation scaled by total assets at the beginning of year t."
        (p. 13)
        '''
        return int(factors[0].roa > 0)

    def operating_cash_flow_score(self, factors):
        '''Get the Profitability - Operating Cash Flow sub-score of Piotroski F-Score

        "I define ... CRO as ... cash flow from operations ..., scaled by
        beginning of the year total assets." (p. 7)

        "Cash flow from operations scaled by total assets at the beginning
        of year t". (p. 13)
        '''
        return int(factors[0].operating_cash_flow > 0)

    def roa_change_score(self, factors):
        '''Get the Profitability - Change in Return of Assets sub-score of Piotroski F-Score

        "I define ΔROA as the current year's ROA less the prior year's ROA. If ΔROA > 0,
        the indicator variable F_ΔROA equals one, zero otherwise." (p. 7)

        "Change in annual ROA for the year preceding portfolio formation. ΔROA is
        calculated as ROA for year t less the firm's ROA for year t-1." (p. 13)
        '''
        return int(factors[0].roa > factors[1].roa)

    def accruals_score(self, factors):
        '''Get the Profitability - Accruals sub-score of Piotroski F-Score

        "I define the variable ACCRUAL as current year's net income before
        extraordinary items less cash flow from operations, scaled by
        beginning of the year total assets. The indicator variable
        F_ACCRUAL equals one if CFO > ROA, zero otherwise." (p. 7)

        "Net income before extraordinary items less cash flow from
        operations, scaled by total assets at the beginning of year t." (p. 13)
        '''
        # Nearest Operating Cash Flow and ROA as current year data.
        operating_cashflow = factors[0].operating_cash_flow
        roa = factors[0].roa
        total_assets = factors[1].total_assets  # Beginning of year t.
        return int(operating_cashflow / total_assets > roa)

    def leverage_score(self, factors):
        '''Get the Leverage, Liquidity and Source of Funds - Change in Leverage sub-score of Piotroski F-Score

        "I measure ΔLEVER as the historical change in the ratio of total
        long-term debt to average total assets, and view an increase (decrease)
        in financial leverage as a negative (positive) signal.... I define the
        indicator variable F_ΔLEVER to equal one (zero) if the firm's leverage
        ratio fell (rose) in the year preceding portfolio formation." (p. 8)

        "Change in the firm's debt-to-assets ratio between the end of year t
        and year t-1. The debt-to-asset ratio is defined as the firm's total
        long-term debt (including the portion of long-term debt classified
        as current) scaled by average total assets." (p. 13)
        '''
        lt_t = factors[0].long_term_debt
        lt_t1 = factors[1].long_term_debt
        a_t = factors[0].total_assets
        a_t1 = factors[1].total_assets
        a_t2 = factors[2].total_assets

        avg_assets_t  = (a_t  + a_t1) / 2.0
        avg_assets_t1 = (a_t1 + a_t2) / 2.0

        leverage_t  = lt_t  / avg_assets_t
        leverage_t1 = lt_t1 / avg_assets_t1

        # Score 1 if leverage decreased
        return int(leverage_t < leverage_t1)

    def liquidity_score(self, factors):
        '''Get the Liquidity score

        "The variable ΔLIQUID measures the historical change in the firm's
        current ratio between the current and prior year, where I define the
        current ratio as the ratio of current assets to current liabilities
        at fiscal year-end. I assume that an improvement in liquidity (i.e.,
        ΔLIQUID > 0) is a good signal about the firm's ability to service
        current debt obligations. The indicator variable F_ΔLIQUID equals
        one if the firm's liquidity improved, zero otherwise." (p. 8)

        "Change in the firm's current ratio between the end of year t and
        year t-1. Current ratio is defined as total current assets divided
        by total current liabilities." (p. 13)
        '''
        return int(factors[0].current_ratio > factors[1].current_ratio)

    def share_issued_score(self, factors):
        '''Get the share issued score

        "I define the indicator variable EQ_OFFER to equal one if the firm
        did not issue common equity in the year preceding portfolio formation,
        zero otherwise." (p. 8)
        '''
        return int(factors[0].ordinary_shares_number <= factors[1].ordinary_shares_number)

    def gross_margin_score(self, factors):
        '''Get the gross margin score

        "I define ΔMARGIN as the firm's current gross margin ratio (gross
        margin scaled by total sales) less the prior year's gross margin
        ratio.... The indicator variable F_ΔMARGIN equals one if ΔMARGIN
        is positive, zero otherwise." (p. 8)

        "Gross margin (net sales less cost of good sold) for the year
        preceding portfolio formation, scaled by net sales for the year,
        less the firm's gross margin (scaled by net sales) from year t-1."
        (p. 13)
        '''
        return int(factors[0].gross_margin > factors[1].gross_margin)

    def asset_turnover_score(self, factors):
        '''Get the asset turnover score

        "I define ΔTURN as the firm's current year asset turnover ratio
        (total sales scaled by beginning of the year total assets) less
        the prior year's asset turnover ratio.... The indicator variable
        F_ΔTURN equals one if ΔTURN is positive, zero otherwise." (p. 8)

        "Change in the firm's asset turnover ratio between the end of
        year t and year t-1. The asset turnover ratio is defined as net
        sales scaled by average total assets for the year" (p. 13)
        '''
        return int(factors[0].assets_turnover > factors[1].assets_turnover)
