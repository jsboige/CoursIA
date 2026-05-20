#region imports
from AlgorithmImports import *
import numpy as np
# endregion
# Hands-On AI Trading - Ex19: FinBERT Sentiment Analysis
# Uses the ProsusAI/finbert model to analyze financial news
# sentiment from Tiingo articles. Trades the most volatile
# asset based on aggregated news sentiment scores.
# Source: HandsOnAITradingBook, Section 06, Example 19


class FinBERTSentimentAlgorithm(QCAlgorithm):
    """
    FinBERT News Sentiment Trading Strategy.

    This strategy uses the FinBERT model (ProsusAI/finbert) to
    classify financial news articles as positive, negative, or
    neutral. It selects the most volatile asset from a tech
    universe and trades it based on aggregated sentiment.

    Reference: Hands-On AI Trading with Python, QuantConnect, and AWS
    Chapter 06 - Applied Machine Learning, Example 19

    How it works:
    1. Select top tech stocks by market cap
    2. Identify the most volatile asset as trading vehicle
    3. Subscribe to Tiingo news for that asset
    4. Use FinBERT to classify each news article
    5. Aggregate sentiment over rolling window
    6. Go long when sentiment is positive, liquidate when negative

    Parameters:
    - universe_size: Number of tech stocks (default: 10)
    - sentiment_window: Articles for aggregation (default: 5)
    - vol_lookback: Days for volatility calculation (default: 30)
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_end_date(2026, 1, 1)
        self.set_cash(100_000)

        # Model parameters
        self._universe_size = self.get_parameter(
            'universe_size', 10
        )
        self._sentiment_window = self.get_parameter(
            'sentiment_window', 5
        )
        self._vol_lookback = self.get_parameter(
            'vol_lookback', 30
        )
        self._sentiment_threshold = 0.2

        # Load FinBERT model
        self._tokenizer = None
        self._model = None
        self._model_loaded = False
        self._load_model()

        # Universe selection - top tech by market cap
        self.universe_settings.data_normalization_mode = (
            DataNormalizationMode.RAW
        )
        schedule_symbol = Symbol.create(
            "SPY", SecurityType.EQUITY, Market.USA
        )
        date_rule = self.date_rules.week_start(schedule_symbol)
        self.universe_settings.schedule.on(date_rule)
        self._universe = self.add_universe(self._select_assets)

        # Schedule weekly rebalance
        self.schedule.on(
            date_rule,
            self.time_rules.after_market_open(schedule_symbol, 30),
            self._select_target_and_trade
        )

        # Sentiment storage
        self._sentiment_scores = []
        self._articles_processed = 0
        self._target_symbol = None
        self._news_symbol = None

    def _load_model(self):
        """Load FinBERT model for sentiment analysis."""
        try:
            from transformers import AutoTokenizer
            from transformers import (
                AutoModelForSequenceClassification
            )

            self._tokenizer = AutoTokenizer.from_pretrained(
                "ProsusAI/finbert"
            )
            self._model = (
                AutoModelForSequenceClassification.from_pretrained(
                    "ProsusAI/finbert"
                )
            )
            self._model_loaded = True
            self.log("FinBERT model loaded successfully")
        except Exception as e:
            self.log(
                f"FinBERT not available: {e}. "
                "Using keyword-based fallback."
            )
            self._model_loaded = False

    def _select_assets(self, fundamental):
        """Select largest tech stocks by market cap."""
        tech_stocks = [
            f for f in fundamental
            if f.asset_classification.morningstar_sector_code
            == MorningstarSectorCode.TECHNOLOGY
        ]
        sorted_by_mc = sorted(
            tech_stocks, key=lambda x: x.market_cap
        )
        return [
            x.symbol for x in sorted_by_mc[-self._universe_size:]
        ]

    def on_securities_changed(self, changes):
        """Handle universe changes."""
        for security in changes.removed_securities:
            if self._news_symbol and security.symbol == self._news_symbol:
                self.subscription_manager.remove_consolidator(
                    security.symbol,
                    getattr(security, 'consolidator', None)
                )

    def _select_target_and_trade(self):
        """Select most volatile asset and execute trade."""
        selected = list(self._universe.selected)
        if len(selected) == 0:
            return

        # Find most volatile asset
        most_volatile = self._find_most_volatile(selected)
        if most_volatile is None:
            return

        # Update target if changed
        if most_volatile != self._target_symbol:
            self._target_symbol = most_volatile
            self._sentiment_scores = []

            # Add Tiingo news for the new target
            ticker = str(most_volatile.value)
            try:
                self._news_symbol = self.add_data(
                    TiingoNews, ticker, Resolution.DAILY
                ).symbol
            except Exception:
                self._news_symbol = None

        # Aggregate and trade
        self._trade()

    def _find_most_volatile(self, symbols):
        """Find the most volatile symbol by trailing std."""
        best_vol = 0
        best_symbol = None

        for symbol in symbols:
            history = self.history(
                symbol, self._vol_lookback + 5, Resolution.DAILY,
                data_normalization_mode=DataNormalizationMode.SCALED_RAW
            )
            if history.empty or 'close' not in history:
                continue

            if isinstance(history.index, pd.MultiIndex):
                history = history.loc[symbol]

            closes = history['close'].values
            if len(closes) < self._vol_lookback:
                continue

            returns = np.diff(closes[-self._vol_lookback:])
            vol = float(np.std(returns))
            if vol > best_vol:
                best_vol = vol
                best_symbol = symbol

        return best_symbol

    def on_data(self, data):
        """Process incoming news articles."""
        if self._news_symbol is None:
            return
        if self._news_symbol not in data:
            return

        news_item = data[self._news_symbol]

        # Extract text
        article_text = ''
        for attr in ['title', 'description']:
            val = getattr(news_item, attr, None)
            if val and str(val).strip():
                article_text += ' ' + str(val).strip()
        article_text = article_text.strip()

        if len(article_text) < 10:
            return

        # Analyze sentiment
        sentiment = self._analyze_sentiment(article_text)
        if sentiment is not None:
            self._sentiment_scores.append(sentiment)
            self._sentiment_scores = self._sentiment_scores[
                -self._sentiment_window * 3:
            ]
            self._articles_processed += 1

    def _analyze_sentiment(self, text):
        """
        Analyze sentiment using FinBERT or keyword fallback.

        Returns a score between -1 (bearish) and 1 (bullish).
        """
        if self._model_loaded:
            result = self._finbert_sentiment(text)
            if result is not None:
                return result
        return self._keyword_sentiment(text)

    def _finbert_sentiment(self, text):
        """Use FinBERT model for sentiment classification."""
        try:
            import torch

            inputs = self._tokenizer(
                text, return_tensors="pt", truncation=True,
                max_length=512, padding=True
            )

            with torch.no_grad():
                outputs = self._model(**inputs)

            probs = torch.nn.functional.softmax(
                outputs.logits, dim=-1
            ).numpy()[0]

            # FinBERT labels: positive(0), negative(1), neutral(2)
            positive = float(probs[0])
            negative = float(probs[1])
            neutral = float(probs[2])

            return positive - negative
        except Exception:
            return None

    def _keyword_sentiment(self, text):
        """Keyword-based sentiment fallback."""
        positive = [
            'surge', 'rally', 'gain', 'profit', 'growth', 'beat',
            'exceed', 'strong', 'bullish', 'upgrade', 'outperform',
            'raise', 'buy', 'positive', 'record', 'high', 'soar',
            'jump', 'climb', 'advance', 'recover', 'boost'
        ]
        negative = [
            'decline', 'drop', 'loss', 'fall', 'crash', 'miss',
            'weak', 'bearish', 'downgrade', 'sell', 'negative',
            'concern', 'risk', 'fear', 'recession', 'low', 'slump',
            'plunge', 'tumble', 'cut', 'reduce', 'warning'
        ]

        text_lower = text.lower()
        pos_count = sum(1 for w in positive if w in text_lower)
        neg_count = sum(1 for w in negative if w in text_lower)

        total = pos_count + neg_count
        if total == 0:
            return 0.0
        return (pos_count - neg_count) / total

    def _trade(self):
        """Execute trade based on aggregated sentiment."""
        if self._target_symbol is None:
            return
        if len(self._sentiment_scores) < 3:
            return

        # Average recent sentiment
        recent = self._sentiment_scores[-self._sentiment_window:]
        avg_sentiment = float(np.mean(recent))

        self.plot('FinBERT', 'Average Sentiment', avg_sentiment)
        self.plot(
            'FinBERT', 'Articles Processed',
            self._articles_processed
        )

        # Trading logic
        if avg_sentiment > self._sentiment_threshold:
            self.set_holdings(self._target_symbol, 1.0)
        elif avg_sentiment < -self._sentiment_threshold:
            self.liquidate(self._target_symbol)
