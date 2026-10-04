# region imports
from AlgorithmImports import *
import numpy as np
# endregion

# qc-research #18901 : Corrective AI (Hands-On AI Trading, ch. 08-02).
# Strategie primaire : saisonnalite intrajournaliere EUR/USD de Breedon et
# Ranaldo (2012) -- vente pendant les heures ouvrees europeennes (03:00-09:00
# ET), achat pendant les heures ouvrees americaines (11:00-15:00 ET), plat
# sinon. Le livre (OOS oct. 2021 - janv. 2023, barres 1 minute EBS) mesure
# Sharpe 0,88 pour la primaire seule.
# Corrective AI : le livre corrige la primaire trade par trade via un gradient
# boosting de +100 predicteurs (API payante predictnow.ai, Sharpe 1,29). Ce
# port implemente le PRINCIPE sans dependance payante, comme l'exige l'issue :
# meta-etiquetage (Lopez de Prado, 2018) -- un classifieur walk-forward
# entraine sur les fenetres passees predit la probabilite que le trade de la
# fenetre soit gagnant, et filtre (ou dimensionne) l'entree en consequence.
# Ecart declare au livre : ~16 predicteurs calculables ex-ante vs >100 chez
# predictnow.ai (proprietaire) ; le verdict BEATS/NO BEATS se mesure sur ce
# port, pas sur la promesse du livre.


class CorrectiveAIAlgorithm(QCAlgorithm):

    def initialize(self) -> None:
        # Periodes par defaut : fenetre du livre (oct. 2021 - janv. 2023).
        # Overridables par parametre (format YYYY-MM-DD) : fenetre longue
        # 2018-2026 et multi-seed sans recompilation.
        start = self._param_date("start", date(2021, 10, 1))
        end = self._param_date("end", date(2023, 1, 31))
        self.set_start_date(start.year, start.month, start.day)
        self.set_end_date(end.year, end.month, end.day)
        self.set_cash(100_000)

        self._eurusd = self.add_forex("EURUSD", Resolution.MINUTE, Market.OANDA)
        self.set_benchmark(self._eurusd.symbol)
        self.set_warm_up(timedelta(days=5))

        self._use_meta = self.get_parameter("use_meta", "true") == "true"
        self._threshold = float(self.get_parameter("threshold", "0.5"))
        self._seed = int(self.get_parameter("seed", "0"))
        self._retrain_days = int(self.get_parameter("retrain_days", "21"))
        self._min_train = int(self.get_parameter("min_train", "120"))
        self._sizing = self.get_parameter("sizing", "filter")  # filter | scale

        # Fenetres : (heure d'entree ET, heure de sortie ET, cote).
        # Convention par defaut = transcription de l'issue #18901 (vente UE,
        # achat US). swap_sides=true teste la convention du papier Breedon-
        # Ranaldo (achat UE, vente US) : mesuree en mirror du livre sur nos
        # donnees (Sharpe -0,881 vs +0,88 annonces), a trancher empiriquement.
        swap = self.get_parameter("swap_sides", "false") == "true"
        sign = -1.0 if swap else 1.0
        self._windows = [(3, 9, -1.0 * sign), (11, 15, 1.0 * sign)]

        # Buffers walk-forward du meta-modele.
        self._x_buf: list[list[float]] = []
        self._y_buf: list[int] = []
        self._entry_features: list[list[float]] = []
        self._entry_price: list[float] = []
        self._model = None
        self._last_fit = datetime.min

        # Comptes pour le rapport de fin d'execution.
        self._n_windows = 0
        self._n_taken = 0
        self._n_skipped = 0
        self._n_refits = 0

        for entry_h, exit_h, _ in self._windows:
            self.schedule.on(
                self.date_rules.every_day(self._eurusd.symbol),
                self.time_rules.at(entry_h, 0),
                self._make_entry(entry_h))
            self.schedule.on(
                self.date_rules.every_day(self._eurusd.symbol),
                self.time_rules.at(exit_h, 0),
                self._make_exit(entry_h))

    # -- Parametrage ------------------------------------------------------

    def _param_date(self, name: str, default: date) -> date:
        raw = self.get_parameter(name)
        return (
            datetime.strptime(raw, "%Y-%m-%d").date()
            if raw else default)

    # -- Ordonnancement ---------------------------------------------------

    def _make_entry(self, entry_hour: int):
        side = next(s for h, _, s in self._windows if h == entry_hour)

        def enter() -> None:
            # Le calendrier every_day tire aussi le dimanche (forex ferme) :
            # garde semaine uniquement, comme le livre (jours ouvrables).
            if self.is_warming_up or self.time.weekday() > 4:
                return
            features = self._compute_features(side)
            if features is None:
                # Fenetre sans historique minute exploitable (ex. 1er janvier,
                # marche ferme, warmup sans donnees pre-start) : sautee.
                return
            take, weight = self._meta_decision(features)
            self._n_windows += 1
            if not take:
                self._n_skipped += 1
            else:
                self._n_taken += 1
                self.set_holdings(self._eurusd.symbol, side * weight)
            # La fenetre est journalisee meme si sautee : le meta-modele
            # apprend des fenetres passees, prises ou non (le label mesure
            # ce que la primaire AURAIT fait, pas ce que le filtre a fait).
            self._entry_features.append(features)
            self._entry_price.append(float(
                self.securities[self._eurusd.symbol].price))
        return enter

    def _make_exit(self, entry_hour: int):
        def exit_window() -> None:
            if self.is_warming_up or self.time.weekday() > 4:
                return
            if self._entry_price:
                entry = self._entry_price.pop(0)
                features = self._entry_features.pop(0)
                exit_price = float(
                    self.securities[self._eurusd.symbol].price)
                if entry > 0 and exit_price > 0:
                    side = next(
                        s for h, _, s in self._windows if h == entry_hour)
                    pnl = (exit_price / entry - 1.0) * side
                    self._x_buf.append(features)
                    self._y_buf.append(1 if pnl > 0 else 0)
            if self.portfolio[self._eurusd.symbol].invested:
                self.liquidate(self._eurusd.symbol)
        return exit_window

    # -- Meta-etiquetage ---------------------------------------------------

    def _meta_decision(self, features: list[float]) -> tuple[bool, float]:
        """Verdict du filtre correctif : (prendre la fenetre, poids)."""
        if not self._use_meta:
            return True, 1.0
        self._maybe_refit()
        if self._model is None:
            # Warm-up walk-forward : pas d'entree tant que le meta-modele
            # n'a pas min_train fenetres passees (declare dans le README).
            return False, 0.0
        p = self._model.predict_proba([features])[0][1]
        if self._sizing == "scale":
            return p >= 0.5, min(1.0, max(0.05, 2.0 * p - 1.0))
        return p >= self._threshold, 1.0

    def _maybe_refit(self) -> None:
        if (self.time - self._last_fit).days < self._retrain_days:
            return
        if len(self._y_buf) < self._min_train:
            return
        from sklearn.ensemble import GradientBoostingClassifier
        # sub-sample 0.7 (stochastic GBM, Friedman 2002) : la graine pilote
        # le sous-echantillonnage -- sinon le classifieur est deterministe et
        # le multi-seed de la regle C n'a aucune variance a mesurer.
        self._model = GradientBoostingClassifier(
            n_estimators=80, max_depth=3, subsample=0.7,
            random_state=self._seed)
        self._model.fit(self._x_buf, self._y_buf)
        self._last_fit = self.time
        self._n_refits += 1

    # -- Predicteurs --------------------------------------------------------

    def _compute_features(self, side: float) -> list[float]:
        """~16 predicteurs ex-ante : la divergence vs les >100 du livre est
        declaree en tete de fichier (predictnow.ai = payant, proprietaire)."""
        hist = self.history(self._eurusd.symbol, 240, Resolution.MINUTE)
        if hist is None or hist.empty or "close" not in hist.columns:
            return None
        values = hist["close"].dropna().values
        if len(values) == 0:
            return None
        if len(values) < 240:
            # Filet defensif (le warm-up de 5 jours couvre deja 240 barres) :
            # borner a gauche au premier close evade l'index negatif bouclant.
            values = np.concatenate(
                [np.full(240 - len(values), values[0]), values])
        logs = np.log(values)
        rets = np.diff(logs)

        def ret(w: int) -> float:
            return float(logs[-1] - logs[-1 - w])

        def vol(w: int) -> float:
            return float(np.std(rets[-w:]))

        labels = self._y_buf
        win10 = np.mean(labels[-10:]) if labels else 0.0
        win20 = np.mean(labels[-20:]) if labels else 0.0
        pnl10 = [
            (1 if lab else -1) for lab in labels[-10:]]
        streak = 0
        if labels:
            last = labels[-1]
            for lab in reversed(labels):
                if lab != last:
                    break
                streak += 1

        return [
            ret(1), ret(5), ret(15), ret(30), ret(60), ret(120),
            vol(15), vol(30), vol(60),
            side, float(self.time.weekday()), ret(240 - 1),
            float(win10), float(win20), float(np.mean(pnl10)) if pnl10 else 0.0,
            float(streak),
        ]

    # -- Rapport -------------------------------------------------------------

    def on_end_of_algorithm(self) -> None:
        self.log(
            "corrective-ai: fenetres=" + str(self._n_windows)
            + " prises=" + str(self._n_taken)
            + " sautees=" + str(self._n_skipped)
            + " refits=" + str(self._n_refits)
            + " echantillon_train=" + str(len(self._y_buf)))
