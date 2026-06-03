#region imports
from AlgorithmImports import *
import numpy as np
# endregion
# Hands-On AI Trading - Ex16: LLM Summarization of Tiingo News Articles
# Uses Tiingo news data and sentiment analysis to trade SPY.
# Supports optional OpenAI API for advanced LLM summarization,
# with keyword-based sentiment as fallback.
# Source: HandsOnAITradingBook, Section 06, Example 16


class LLMNewsSentimentAlgorithm(QCAlgorithm):
    """
    LLM-Based News Sentiment Trading Strategy.

    This strategy uses financial news sentiment to predict market
    direction. News articles are analyzed for sentiment using either
    an LLM (OpenAI API, if key provided) or keyword-based analysis.

    Reference: Hands-On AI Trading with Python, QuantConnect, and AWS
    Chapter 06 - Applied Machine Learning, Example 16

    How it works:
    1. Subscribe to SPY equity and Tiingo news feed
    2. Process incoming news articles for sentiment
    3. Aggregate sentiment over a rolling window
    4. Weekly rebalance: long SPY when sentiment positive,
       liquidate when negative

    Parameters:
    - openai_api_key: OpenAI API key for LLM sentiment (optional)
    - sentiment_window: Number of recent articles for aggregation
    - sentiment_threshold: Minimum average sentiment to go long
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_end_date(2026, 1, 1)
        self.set_cash(100_000)

        # Trading vehicle
        self._spy = self.add_equity("SPY", Resolution.DAILY).symbol

        # Model parameters
        self._sentiment_window = self.get_parameter(
            'sentiment_window', 10
        )
        self._sentiment_threshold = self.get_parameter(
            'sentiment_threshold', 0.15
        )
        self._openai_api_key = self.get_parameter(
            'openai_api_key', ''
        )

        # Sentiment storage
        self._sentiment_scores = []
        self._articles_processed = 0

        # Add Tiingo news feed
        self._news_symbol = self.add_data(
            TiingoNews, "SPY", Resolution.DAILY
        ).symbol

        # Schedule weekly trading
        self.schedule.on(
            self.date_rules.week_start(self._spy),
            self.time_rules.after_market_open(self._spy, 30),
            self._trade
        )

    def on_data(self, data):
        """Process incoming news articles for sentiment."""
        if self._news_symbol not in data:
            return

        news_item = data[self._news_symbol]

        # Extract article text
        article_text = self._extract_text(news_item)
        if not article_text or len(article_text) < 10:
            return

        # Analyze sentiment
        sentiment = self._analyze_sentiment(article_text)
        if sentiment is not None:
            self._sentiment_scores.append(sentiment)
            self._sentiment_scores = self._sentiment_scores[
                -self._sentiment_window * 3:
            ]
            self._articles_processed += 1

    def _extract_text(self, news_item):
        """Extract text content from TiingoNews data item."""
        parts = []
        for attr in ['title', 'description']:
            val = getattr(news_item, attr, None)
            if val and str(val).strip():
                parts.append(str(val).strip())
        return ' '.join(parts) if parts else ''

    def _analyze_sentiment(self, text):
        """
        Analyze sentiment of news text.

        Uses LLM (OpenAI) if API key provided, otherwise
        falls back to keyword-based analysis.
        """
        if self._openai_api_key:
            llm_result = self._llm_sentiment(text)
            if llm_result is not None:
                return llm_result
        return self._keyword_sentiment(text)

    def _llm_sentiment(self, text):
        """Use OpenAI API for sentiment analysis."""
        try:
            import requests

            headers = {
                'Authorization': f'Bearer {self._openai_api_key}',
                'Content-Type': 'application/json'
            }

            prompt = (
                "Analyze the financial sentiment of this text. "
                "Reply with ONLY a number between -1.0 and 1.0 "
                "where -1.0 is very bearish and 1.0 is very "
                f"bullish.\n\nText: {text[:500]}"
            )

            payload = {
                'model': 'gpt-3.5-turbo',
                'messages': [
                    {
                        'role': 'system',
                        'content': 'You analyze financial sentiment.'
                    },
                    {'role': 'user', 'content': prompt}
                ],
                'temperature': 0.0,
                'max_tokens': 10
            }

            response = requests.post(
                'https://api.openai.com/v1/chat/completions',
                headers=headers, json=payload, timeout=10
            )

            if response.status_code == 200:
                content = response.json()[
                    'choices'][0]['message']['content'].strip()
                return max(-1.0, min(1.0, float(content)))
        except Exception:
            pass
        return None

    def _keyword_sentiment(self, text):
        """
        Keyword-based sentiment analysis fallback.

        Uses financial domain-specific positive/negative word
        lists to compute a sentiment score between -1 and 1.
        """
        positive = [
            'surge', 'rally', 'gain', 'profit', 'growth', 'beat',
            'exceed', 'strong', 'bullish', 'upgrade', 'outperform',
            'raise', 'buy', 'positive', 'record', 'high', 'soar',
            'jump', 'climb', 'advance', 'recover', 'boost', 'optim'
        ]
        negative = [
            'decline', 'drop', 'loss', 'fall', 'crash', 'miss',
            'weak', 'bearish', 'downgrade', 'sell', 'negative',
            'concern', 'risk', 'fear', 'recession', 'low', 'slump',
            'plunge', 'tumble', 'cut', 'reduce', 'warning', 'pessim'
        ]

        text_lower = text.lower()
        pos_count = sum(1 for w in positive if w in text_lower)
        neg_count = sum(1 for w in negative if w in text_lower)

        total = pos_count + neg_count
        if total == 0:
            return 0.0
        return (pos_count - neg_count) / total

    def _trade(self):
        """Trade based on aggregated sentiment."""
        if len(self._sentiment_scores) < 3:
            return

        # Average recent sentiment
        recent = self._sentiment_scores[-self._sentiment_window:]
        avg_sentiment = float(np.mean(recent))

        self.plot('Sentiment', 'Average', avg_sentiment)
        self.plot(
            'Sentiment', 'Articles Processed',
            self._articles_processed
        )

        # Trading logic
        if avg_sentiment > self._sentiment_threshold:
            self.set_holdings(self._spy, 1.0)
        elif avg_sentiment < -self._sentiment_threshold:
            self.liquidate(self._spy)
