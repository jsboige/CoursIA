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
# Ecarts documentes du livre :
# n1 - Blindage par etape. Le pipeline du livre, execute tel quel, n'a
#      jamais complete un backtest sur les noeuds QC actuels : les six
#      executions non blindees (v1-v6) n'en ont jamais produit un seul --
#      l'annee et le semestre meurent en FATAL natif ~12 s apres le
#      depart, le 2 mois echoue aussi (Runtime Error). Les executions
#      blindees de fenetres courtes (probe5 janvier, probe6/probe7
#      jan-fev, probe9 jan-fev complet, et ce livrable v7 qui complete
#      avec 2 ordres) completent toutes, la meme journee, sur le meme
#      noeud.
#      Le blindage (try/except par etape, position inchangee en cas
#      d'echec, echecs journalises) est donc une adaptation d'execution,
#      pas un choix de strategie : aucun stage ne change de semantique
#      quand il reussit.
# n2 - SPY est abonne, mais en FIN d'initialize (apres la creation des
#      date_rules). Le livre cree le Symbol SPY sans l'abonner ; ne jamais
#      l'abonner tue l'initialize sur les noeuds QC actuels (v1/v2,
#      hasInitializeError=true, reproduit 2x).
# n3 - Cash porte a 1 000 000 USD (le livre laisse le defaut 100 000) :
#      probe8 (annee, blindee, 1M) et v3/v4 (annee, 100k) meurent au meme
#      point, le cash n'est donc pas la cause -- c'est un choix de confort
#      de lecture des ordres.
# n4 - Fenetre 2022-01-01 -> 2022-03-01 (2 mois) au lieu de l'annee du
#      livre : sur les noeuds QC actuels (org FREE, noeud "Backtest
#      MyIA 1", projet 29936073), les fenetres longues meurent aussi
#      (annee ~0,15, semestre ~0,29) et les fenetres de 1-2 mois
#      completent l'integralite du pipeline, transition du 1er fevrier
#      incluse. 2 mois est la plus longue fenetre mesuree qui complete.


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

    Ecarts documentes du portage : (1) blindage par etape (adaptation
    d'execution, cf. note n1 en tete de fichier) ; (2) PyTorch au lieu de
    TensorFlow pour l'inference (meme modele, meme tokenizer, memes poids ;
    TF importe aussi sur les noeuds -- sonde probe2, mask 31) ;
    (3) abonnement SPY explicite en fin d'initialize ; (4) cash 1M ;
    (5) fenetre 2 mois (cf. note n4).
    """

    def _fail(self, stage, exc):
        """Journalise un etage en echec sans interrompre le backtest."""
        message = f"{type(exc).__name__}: {str(exc)[:300]}"
        self._stage_fails.append((stage, message))
        self.log(f"{self.time:%Y-%m-%d} : ETAGE EN ECHEC {stage} -> {message}")

    def initialize(self):
        self.set_start_date(2022, 1, 1)
        self.set_end_date(2022, 3, 1)
        self.set_cash(1_000_000)
        self._stage_fails = []

        # Reference calendrier (non abonnee ici -- ecart n2, cf. note
        # en tete : l'abonnement se fait en FIN d'initialize).
        spy = Symbol.create("SPY", SecurityType.EQUITY, Market.USA)

        # Univers : top 10 liquidite -> le plus volatil, chaque debut de mois.
        self.universe_settings.resolution = Resolution.DAILY
        self.universe_settings.schedule.on(
            self.date_rules.month_start(spy)
        )
        self._universe = self.add_universe(self._book_selector)

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

        # Ecart n2 (fin) : abonnement SPY ici, APRES la creation des
        # date_rules -- cf. note en tete de fichier.
        self._spy = self.add_equity("SPY", Resolution.DAILY)

    def _book_selector(self, fundamental):
        """Selecteur du livre : top 10 liquidite -> le plus volatil.

        En cas d'echec, repli sur le plus liquide (l'univers reste non
        vide, la strategie reste investie) -- blindage n1.
        """
        try:
            selected = [
                f.symbol
                for f in sorted(
                    fundamental, key=lambda f: f.dollar_volume
                )[-10:]
            ]
            target = self.history(
                selected, timedelta(365), Resolution.DAILY
            )['close'].unstack(0).pct_change().iloc[1:].std().idxmax()
            return [target]
        except Exception as e:
            self._fail("selecteur d'univers", e)
            return [
                sorted(
                    fundamental, key=lambda f: f.dollar_volume
                )[-1].symbol
            ]

    def on_securities_changed(self, changes):
        for security in changes.removed_securities:
            try:
                self.remove_security(security.dataset_symbol)
            except Exception as e:
                self._fail("remove_security", e)
        for security in changes.added_securities:
            try:
                security.dataset_symbol = self.add_data(
                    TiingoNews, security.symbol
                ).symbol
            except Exception as e:
                self._fail("add_data TiingoNews", e)

    def on_warmup_finished(self):
        self._trade()

    def _trade(self):
        if self.is_warming_up:
            return
        if self.time - self._last_rebalance_time < timedelta(14):
            return

        try:
            security = self.securities[list(self._universe.selected)[0]]
        except Exception as e:
            self._fail("securities[selected[0]]", e)
            return

        try:
            articles = self.history[TiingoNews](
                security.dataset_symbol, 10, Resolution.DAILY
            )
        except Exception as e:
            self._fail("history[TiingoNews]", e)
            return

        article_text = [article.description for article in articles]
        if not article_text:
            self.log(
                f"{self.time:%Y-%m-%d} : aucun article Tiingo sur "
                "10 jours, position inchangee"
            )
            return

        try:
            inputs = self._tokenizer(
                article_text, padding=True, truncation=True,
                return_tensors='pt'
            )
            with torch.no_grad():
                outputs = self._model(**inputs)
            scores = torch.nn.functional.softmax(
                outputs.logits, dim=-1
            ).numpy()
        except Exception as e:
            self._fail("tokenizer + inference", e)
            return

        self.log(
            f"{self.time:%Y-%m-%d} : {len(article_text)} articles, "
            f"cible {security.symbol.value}, "
            f"probas moyennes {scores.mean(axis=0).round(3)}"
        )

        try:
            scores = self._aggregate_sentiment_scores(scores)
        except Exception as e:
            self._fail("aggregate", e)
            return

        self.plot("Sentiment Probability", "Negative", scores[0])
        self.plot("Sentiment Probability", "Neutral", scores[1])
        self.plot("Sentiment Probability", "Positive", scores[2])

        try:
            weight = 1 if scores[2] > scores[0] else -0.25
            self.set_holdings(security.symbol, weight, True)
            self._last_rebalance_time = self.time
        except Exception as e:
            self._fail("set_holdings", e)

    def _aggregate_sentiment_scores(self, sentiment_scores):
        n = sentiment_scores.shape[0]
        weights = np.exp(np.linspace(0, 1, n))
        weights /= weights.sum()
        weighted_scores = sentiment_scores * weights[:, np.newaxis]
        return weighted_scores.sum(axis=0)

    def on_end_of_algorithm(self):
        if self._stage_fails:
            summary = " | ".join(
                f"{stage}: {message}" for stage, message in self._stage_fails
            )
            self.log(f"Ex19 : {len(self._stage_fails)} etage(s) en echec -> {summary}")
        else:
            self.log("Ex19 : aucun etage en echec sur la fenetre.")
