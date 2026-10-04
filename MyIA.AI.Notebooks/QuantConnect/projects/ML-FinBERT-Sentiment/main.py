#region imports
from AlgorithmImports import *
import numpy as np
import torch
from transformers import (
    AutoTokenizer,
    AutoModelForSequenceClassification,
    set_seed,
)
# endregion
# Hands-On AI Trading - Ex19 (06/19/01 Base Model) : FinBERT Sentiment
# Portage fidele du code du livre en PyTorch (le livre utilise la variante
# TFBertForSequenceClassification ; ProsusAI/finbert expose les deux).
# Source: QuantConnect/HandsOnAITradingBook, "06 Applied Machine Learning/
# 19 FinBERT Model/01 Base Model/main.py".
#
# Ecart documente n2 : abonnement SPY ajoute. Le livre cree le Symbol SPY
# sans l'abonner (il ne sert que de reference calendrier aux date_rules) ;
# sur les noeuds QC actuels, un date_rules.month_start(spy) non abonne
# tue l'algorithme en FATAL ~13 s apres initialize (reproduit 2x, corrige
# par l'abonnement -- v3, backtest 36a27f53014c16ebd72224c913fcc55c).


class FinbertBaseModelAlgorithm(QCAlgorithm):
    """
    Modele de base FinBERT du livre (Exemple 19, chapitre 06).

    Charge ProsusAI/finbert depuis le cache local des noeuds QC Cloud
    (``local_files_only=True``, comme le livre). L'univers mensuel garde
    les 10 actifs les plus liquides et n'en retient que le plus volatil
    (ecart-type des rendements quotidiens sur 365 jours). Au
    rebalancement, le sentiment des articles Tiingo des 10 derniers
    jours est agrege avec des poids exponentiels : long 100 % si le
    positif depasse le negatif, sinon short 25 %. Toujours investi.

    Ecarts documentes du portage : (1) PyTorch au lieu de TensorFlow
    pour l'inference (meme modele, meme tokenizer, memes poids ; TF
    importe aussi sur les noeuds -- sonde probe2, mask 31 -- mais la
    voie PyTorch est plus legere) ; (2) abonnement SPY explicite
    (cf. note v3 en tete de fichier).
    """

    def initialize(self):
        self.set_start_date(2022, 1, 1)
        self.set_end_date(2023, 1, 1)
        self.set_cash(100_000)

        # Reference calendrier : abonnee (ecart n2, cf. note en tete).
        spy = self.add_equity("SPY", Resolution.DAILY).symbol

        # Univers : top 10 liquidite -> le plus volatil, chaque debut de mois.
        self.universe_settings.resolution = Resolution.DAILY
        self.universe_settings.schedule.on(
            self.date_rules.month_start(spy)
        )
        self._universe = self.add_universe(
            lambda fundamental: [
                self.history(
                    [
                        f.symbol
                        for f in sorted(
                            fundamental,
                            key=lambda f: f.dollar_volume
                        )[-10:]
                    ],
                    timedelta(365),
                    Resolution.DAILY
                )['close'].unstack(0).pct_change().iloc[1:].std().idxmax()
            ]
        )

        # Reproductibilite (le livre : set_seed(1, True)).
        set_seed(1, True)

        model_path = "ProsusAI/finbert"
        self._tokenizer = AutoTokenizer.from_pretrained(
            model_path, local_files_only=True
        )
        self._model = AutoModelForSequenceClassification.from_pretrained(
            model_path, local_files_only=True
        )
        self._model.eval()

        # Rebalancements mensuels.
        self._last_rebalance_time = datetime.min
        self.schedule.on(
            self.date_rules.month_start(spy, 1),
            self.time_rules.midnight,
            self._trade
        )

        self.set_warm_up(timedelta(30))

    def on_warmup_finished(self):
        self._trade()

    def on_securities_changed(self, changes):
        for security in changes.removed_securities:
            self.remove_security(security.dataset_symbol)
        for security in changes.added_securities:
            security.dataset_symbol = self.add_data(
                TiingoNews, security.symbol
            ).symbol

    def _trade(self):
        if self.is_warming_up:
            return
        if self.time - self._last_rebalance_time < timedelta(14):
            return

        security = self.securities[list(self._universe.selected)[0]]

        articles = self.history[TiingoNews](
            security.dataset_symbol, 10, Resolution.DAILY
        )
        article_text = [article.description for article in articles]
        if not article_text:
            self.log(
                f"{self.time:%Y-%m-%d} : aucun article Tiingo sur "
                "10 jours, position inchangee"
            )
            return

        inputs = self._tokenizer(
            article_text, padding=True, truncation=True,
            return_tensors='pt'
        )
        with torch.no_grad():
            outputs = self._model(**inputs)
        scores = torch.nn.functional.softmax(
            outputs.logits, dim=-1
        ).numpy()

        self.log(
            f"{self.time:%Y-%m-%d} : {len(article_text)} articles, "
            f"cible {security.symbol.value}, "
            f"probas moyennes {scores.mean(axis=0).round(3)}"
        )

        scores = self._aggregate_sentiment_scores(scores)
        self.plot("Sentiment Probability", "Negative", scores[0])
        self.plot("Sentiment Probability", "Neutral", scores[1])
        self.plot("Sentiment Probability", "Positive", scores[2])

        weight = 1 if scores[2] > scores[0] else -0.25
        self.set_holdings(security.symbol, weight, True)
        self._last_rebalance_time = self.time

    def _aggregate_sentiment_scores(self, sentiment_scores):
        n = sentiment_scores.shape[0]
        weights = np.exp(np.linspace(0, 1, n))
        weights /= weights.sum()
        weighted_scores = sentiment_scores * weights[:, np.newaxis]
        return weighted_scores.sum(axis=0)
