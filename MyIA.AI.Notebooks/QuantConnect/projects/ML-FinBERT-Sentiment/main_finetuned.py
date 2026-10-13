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
# Hands-On AI Trading - Ex19 (06/19/02 Fine-Tuned Model) : FinBERT re-entraine
# Portage fidele du code du livre en PyTorch (le livre utilise la variante
# TFBertForSequenceClassification avec `from_pt=True`, c'est-a-dire les memes
# poids PyTorch convertis ; cf. note n6).
# Source: QuantConnect/HandsOnAITradingBook, "06 Applied Machine Learning/
# 19 FinBERT Model/02 Fine-Tuned Model/main.py" (commit e025f21).
#
# CE FICHIER N'EST PAS EXECUTABLE EN CI, ni sur un noeud QC ordinaire :
# le re-entrainement tourne DANS l'algorithme et demande un GPU. Le harnais
# `finetune/run_finetune_finbert.py` l'execute hors ligne et mesure l'ecart
# base / re-entraine ; ce fichier est le portage de reference.
#
# Ecarts documentes du livre :
# n1 - Blindage par etage. Le pipeline du livre, execute tel quel, n'a jamais
#      complete un backtest sur les noeuds QC actuels pour la variante de base
#      (six executions non blindees, aucune n'a produit un seul backtest ;
#      cf. note n1 de `main.py`). Le re-entrainement ajoute une etape lourde
#      (deux epoques sur 100 echantillons) : le blindage par etage est
#      conserve a l'identique. Un etage en echec laisse la position inchangee
#      et se journalise ; aucun etage ne change de semantique quand il reussit.
# n2 - SPY est abonne en FIN d'initialize (apres les date_rules), comme dans le
#      portage de base -- ne jamais l'abonner tue l'initialize sur les noeuds
#      QC actuels (reproduit 2x sur 06/19/01).
# n3 - Cash porte a 1 000 000 USD (le livre laisse le defaut 100 000) : choix
#      de confort de lecture des ordres, sans effet sur la semantique.
# n4 - Fenetre 2022-01-01 -> 2022-03-01 (2 mois) au lieu de l'annee du livre :
#      sur les noeuds QC actuels, les fenetres longues meurent en FATAL natif.
#      2 mois est la plus longue fenetre mesuree qui complete (cf. note n4 de
#      `main.py`).
# n5 - Convention d'indices de FinBERT. Le livre compare `scores[2] > scores[0]`
#      et etiquete ses trois plot Negative/Neutral/Positive sur les indices
#      0/1/2. Or il vient de re-etiqueter ses echantillons avec 0 = negatif et
#      2 = positif : sur le modele **re-entraine**, la comparaison est donc
#      celle qu'il annonce. Le portage conserve l'expression telle quelle.
#      (Sur le modele de base, `id2label` vaut {0: positive, 1: negative,
#      2: neutral} et la meme expression compare neutre > positif -- c'est la
#      note n5 de `main.py`, deja livree pour 06/19/01.)
# n6 - TensorFlow -> PyTorch. Le livre charge
#      `TFBertForSequenceClassification.from_pretrained(..., num_labels=3,
#      from_pt=True)` : les poids sont ceux du modele PyTorch, convertis. Le
#      portage entraine directement le modele PyTorch, avec la meme recette
#      (Adam, lr 3e-5, 2 epoques, entropie croisee sur les logits).
# n7 - `max_length` : le livre laisse la valeur par defaut du tokenizer (512)
#      avec `padding='max_length'`. Les titres d'articles font ~15 jetons ; le
#      portage passe `max_length=128`, qui les contient avec une marge large et
#      divise le temps de calcul du re-entrainement.
# n8 - Fenetre de reaction, et pourquoi le portage la GARDE telle quelle. Le
#      livre etiquette chaque article par la reaction du cours entre deux
#      parutions consecutives, mesuree a la SECONDE (`Resolution.SECOND`, cf.
#      `_collect_samples` ci-dessous). Cette regle est resolvable ici, parce
#      que l'algorithme tourne sur QC Cloud et dispose bien des clotures a la
#      seconde. Le harnais hors ligne `finetune/run_finetune_finbert.py`, lui,
#      ne dispose que de clotures quotidiennes : a cette resolution deux
#      parutions de la meme seance n'ont aucune reaction resolvable, et la
#      regle du livre y rend 63 % de labels exactement nuls (mesure : 410 des
#      680 paires consecutives tombent dans la meme seance), soit une classe
#      neutre artificiellement majoritaire a 75 %. Le harnais adapte donc sa
#      mecanique de mesure (reaction a la parution) et le documente ; le
#      portage de reference, lui, reste fidele au livre sans changement.
#      Divergence assumee et locale au harnais : les deux artefacts ne
#      mesurent pas la meme chose, et le disent chacun de leur cote.


class FinbertFineTunedModelAlgorithm(QCAlgorithm):
    """
    Modele FinBERT re-entraine du livre (Exemple 19-02, chapitre 06).

    Reprend l'algorithme de base et ajoute le re-entrainement decrit par le
    livre : a chaque rebalancement mensuel, les articles des 30 derniers jours
    de l'actif retenu sont etiquetes par la **reaction du cours** entre deux
    parutions consecutives, classes en trois groupes au 25/75, puis le modele
    est re-entraine deux epoques (Adam, lr 3e-5) avant de scorer les articles
    du mois.

    Le modele est rechargé **frais a chaque rebalancement** : le livre appelle
    `from_pretrained` dans `_trade`, l'apprentissage d'un mois ne s'accumule
    donc pas sur le suivant. Le portage reproduit ce point.
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

        # Reference calendrier (non abonnee ici -- ecart n2).
        spy = Symbol.create("SPY", SecurityType.EQUITY, Market.USA)

        self.universe_settings.resolution = Resolution.DAILY
        self.universe_settings.schedule.on(self.date_rules.month_start(spy))
        self._universe = self.add_universe(self._book_selector)

        # Reproductibilite (le livre : set_seed(1, True)).
        set_seed(1, True)

        self._model_name = "ProsusAI/finbert"
        self._tokenizer = AutoTokenizer.from_pretrained(
            self._model_name, local_files_only=True
        )

        self._last_rebalance_time = datetime.min
        self.schedule.on(
            self.date_rules.month_start(spy, 1),
            self.time_rules.midnight,
            self._trade
        )

        self.set_warm_up(timedelta(30))

        # Ecart n2 (fin) : abonnement SPY APRES la creation des date_rules.
        self._spy = self.add_equity("SPY", Resolution.DAILY)

    def _book_selector(self, fundamental):
        """Selecteur du livre : top 10 liquidite -> le plus volatil."""
        try:
            selected = [
                f.symbol
                for f in sorted(fundamental, key=lambda f: f.dollar_volume)[-10:]
            ]
            target = self.history(
                selected, timedelta(365), Resolution.DAILY
            )['close'].unstack(0).pct_change().iloc[1:].std().idxmax()
            return [target]
        except Exception as e:
            self._fail("selecteur d'univers", e)
            return [sorted(fundamental, key=lambda f: f.dollar_volume)[-1].symbol]

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

    def _collect_samples(self, security):
        """Etiquetage du livre : reaction du cours entre deux parutions."""
        samples = pd.DataFrame(columns=['text', 'label'])
        news_history = self.history(
            security.dataset_symbol, 30, Resolution.DAILY
        )
        if news_history.empty:
            return samples
        news_history = news_history.loc[security.dataset_symbol]['description']
        asset_history = self.history(
            security.symbol, timedelta(30), Resolution.SECOND
        ).loc[security.symbol]['close']
        for i in range(len(news_history.index) - 1):
            factor = news_history.iloc[i]
            if not factor:
                continue
            release_time = self._convert_to_eastern(news_history.index[i])
            next_release_time = self._convert_to_eastern(news_history.index[i + 1])
            reaction_period = asset_history[
                (asset_history.index > release_time)
                & (asset_history.index < next_release_time + timedelta(seconds=1))
            ]
            if reaction_period.empty:
                continue
            label = (
                (reaction_period.iloc[-1] - reaction_period.iloc[0])
                / reaction_period.iloc[0]
            )
            samples.loc[len(samples), :] = [factor, label]
        return samples.iloc[-100:]

    @staticmethod
    def _classify3(samples):
        """Trois classes au 25/75 -- logique du livre, recopiee telle quelle."""
        sorted_samples = samples.sort_values(
            by='label', ascending=False
        ).reset_index(drop=True)
        percent_signed = 0.75
        positive_cutoff = int(
            percent_signed * len(sorted_samples[sorted_samples.label > 0])
        )
        negative_cutoff = (
            len(sorted_samples)
            - int(percent_signed * len(sorted_samples[sorted_samples.label < 0]))
        )
        sorted_samples.loc[
            list(range(negative_cutoff, len(sorted_samples))), 'label'
        ] = 0
        sorted_samples.loc[
            list(range(positive_cutoff, negative_cutoff)), 'label'
        ] = 1
        sorted_samples.loc[list(range(0, positive_cutoff)), 'label'] = 2
        return sorted_samples

    def _finetune(self, samples):
        """Re-entraine une tete de classification fraiche (recette du livre)."""
        model = AutoModelForSequenceClassification.from_pretrained(
            self._model_name, num_labels=3, local_files_only=True
        )
        device = "cuda" if torch.cuda.is_available() else "cpu"
        model.to(device)
        model.train()

        encoded = self._tokenizer(
            list(samples['text'].values), padding='max_length', truncation=True,
            max_length=128, return_tensors='pt'
        )
        labels = torch.tensor(
            samples['label'].astype(int).values, dtype=torch.long
        )
        optimizer = torch.optim.AdamW(model.parameters(), lr=3e-5)
        loss_fn = torch.nn.CrossEntropyLoss()
        batch = 16
        for _ in range(2):
            for start in range(0, len(labels), batch):
                stop = start + batch
                ids = encoded['input_ids'][start:stop].to(device)
                mask = encoded['attention_mask'][start:stop].to(device)
                target = labels[start:stop].to(device)
                optimizer.zero_grad()
                loss = loss_fn(model(input_ids=ids, attention_mask=mask).logits, target)
                loss.backward()
                optimizer.step()
        model.eval()
        return model

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
            samples = self._collect_samples(security)
        except Exception as e:
            self._fail("collecte des echantillons", e)
            return

        if samples.shape[0] < 10:
            self.log(
                f"{self.time:%Y-%m-%d} : {samples.shape[0]} echantillon(s), "
                "sous le seuil du livre -- liquidation"
            )
            try:
                self.liquidate()
            except Exception as e:
                self._fail("liquidate", e)
            return

        try:
            samples = self._classify3(samples)
        except Exception as e:
            self._fail("classification 3 classes", e)
            return

        try:
            model = self._finetune(samples)
        except Exception as e:
            self._fail("re-entrainement", e)
            return

        try:
            inputs = self._tokenizer(
                list(samples['text'].values), padding=True, truncation=True,
                max_length=128, return_tensors='pt'
            )
            device = next(model.parameters()).device
            inputs = {k: v.to(device) for k, v in inputs.items()}
            with torch.no_grad():
                outputs = model(**inputs)
            scores = torch.nn.functional.softmax(
                outputs.logits, dim=-1
            ).cpu().numpy()
            scores = self._aggregate_sentiment_scores(scores)
        except Exception as e:
            self._fail("inference apres re-entrainement", e)
            return

        self.log(
            f"{self.time:%Y-%m-%d} : {samples.shape[0]} echantillons, "
            f"cible {security.symbol.value}, scores agreges "
            f"{np.round(scores, 3).tolist()}"
        )

        self.plot("Sentiment Probability", "Negative", scores[0])
        self.plot("Sentiment Probability", "Neutral", scores[1])
        self.plot("Sentiment Probability", "Positive", scores[2])

        try:
            weight = 1 if scores[2] > scores[0] else -0.25
            self.set_holdings(security.symbol, weight, True)
            self._last_rebalance_time = self.time
        except Exception as e:
            self._fail("set_holdings", e)

    def _convert_to_eastern(self, dt):
        return dt.astimezone(pytz.timezone('US/Eastern')).replace(tzinfo=None)

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
            self.log(f"Ex19-02 : {len(self._stage_fails)} etage(s) en echec -> {summary}")
        else:
            self.log("Ex19-02 : aucun etage en echec sur la fenetre.")
