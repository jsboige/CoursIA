#region imports
from AlgorithmImports import *

import os, random
from scipy.stats import norm
import torch as T
from torch import optim
import torch.distributions as D
import torch.nn as nn
import joblib
import plotly.graph_objects as go
from plotly.subplots import make_subplots

from policy import Policy
#endregion


class AIDeltaHedgeModel:

    _base_model_key = 'ai-hedging-base-model'
    _interest_rate_provider = InterestRateProvider()
    _earliest_options_date = datetime(2013, 1, 1)

    def __init__(
            self, algorithm, min_contract_duration=timedelta(30), 
            max_contract_duration=timedelta(120), 
            min_holding_period=timedelta(14), size=(10_000, 1), 
            commission=0.01):
        self._algorithm = algorithm
        self._min_contract_duration = min_contract_duration
        self._max_contract_duration = max_contract_duration
        self._min_holding_period = min_holding_period
        self._size = size
        self._commission = commission
        self._pos = 0
        self._policy = None
        self.enable_automatic_indicator_warm_up = True
        # Set the random seeds to enable reproducibility.
        seed_value = 1
        os.environ['PYTHONHASHSEED'] = str(seed_value)
        random.seed(seed_value)
        np.random.seed(seed_value)
        T.manual_seed(seed_value)
        # Set the default tensor type.
        T.set_default_dtype(T.float32)
        # Set the device type (CPU/GPU).
        self._device = 'cuda:0' if T.cuda.is_available() else 'cpu'

    def _get_vol_and_rf(self, symbol, start_date, end_date):
        # Calculate the asset volatility.
        vol = self._algorithm.history(
            symbol, start_date, end_date, Resolution.DAILY,
            data_normalization_mode=DataNormalizationMode.ADJUSTED
        ).loc[symbol]['close'].pct_change().std()     

        # Get the risk-free rate.
        rf = RiskFreeInterestRateModelExtensions.get_risk_free_rate(
            self._interest_rate_provider, start_date, end_date
        )
        return vol, rf

    def train_base_model(self, plot=True, epochs=1000):
        # Create the policy.
        self._policy = Policy(self._device)
        # Define the loss function.
        mse = nn.MSELoss()

        # Set the volatility and risk-free interest rate arguments.
        # The base model is trained with generated data, which doesn't
        # have a start and end date, so let's just use 2013-2018.
        vol, rf = self._get_vol_and_rf(
            Symbol.create("SPY", SecurityType.EQUITY, Market.USA), 
            self._earliest_options_date, datetime(2018, 1, 1)
        )

        # Train the model to replicate the underhedged Black-Scholes' 
        # delta.
        in_sample_loss_values = []
        oos_loss_values = []
        for E in range(epochs):
            # Get the data we need to run the network.
            ttm, moneyness, delta, position = self._generate_data(vol, rf)
            states, y, test_states, test_y = self._forge_batch(
                moneyness, ttm, delta, position
            )
            # Get the in-sample action and loss.
            action, _ = self._policy.sample(states)
            loss = mse(action, y)
            inloss = loss.item()
            # Update the network parameters.
            self._policy.optimizer.zero_grad()
            loss.backward()
            self._policy.optimizer.step()
            # Get the out-of-sample action and loss.
            action, _ = self._policy.sample(test_states)
            outloss = mse(action, test_y).item()
            # Record the loss value of this epoch.
            in_sample_loss_values.append(inloss)
            oos_loss_values.append(outloss)

        # Plot the training loss values of each epoch.
        if plot:
            x = list(range(1, epochs+1))
            go.Figure(
                [
                    go.Scatter(x=x, y=in_sample_loss_values, name='In-sample'),
                    go.Scatter(x=x, y=oos_loss_values, name='Out-of-sample')
                ],
                dict(
                    title='Training Loss of the Base Model', 
                    xaxis_title='Epoch', yaxis_title='Loss', showlegend=True
                )
            ).show()

        # Save the base model to the Object Store.
        joblib.dump(
            self._policy, 
            self._algorithm.object_store.get_file_path(self._base_model_key)
        )

    def train_asset_model(
            self, ticker, start_date, end_date, epochs=20, 
            save=False, in_research_env=False):
        # If there is no base model in the Object Store yet, add one.
        if not self._algorithm.object_store.contains_key(self._base_model_key):
            print("No base model in the Object Store. Let's create one first.")
            self.train_base_model()

        # Adjust the QuantBook date to avoid look-ahead bias.
        if in_research_env: 
            self._algorithm.set_start_date(end_date)
        # Add a security initializer so that `self._equity.price` 
        # isn't zero in research and so we can trade Option contracts 
        # right after we subscribe to them while trading.
        self._algorithm.set_security_initializer(
            BrokerageModelSecurityInitializer(
                self._algorithm.brokerage_model, 
                FuncSecuritySeeder(self._algorithm.get_last_known_prices)
            )
        )
        # Subscribe to the underlying Equity.
        self._equity = self._algorithm.add_equity(
            ticker, data_normalization_mode=DataNormalizationMode.RAW
        )
        # Create a member on the Equity object to track the current
        # Option contract.
        self._equity.option_contract = None

        self._asset_model_key = "ai-hedging-" + ticker
        epoch_penalties = self.refit(save, epochs)
        # Plot the training penalties.
        if in_research_env:
            go.Figure(
                go.Scatter(
                    x=list(range(1, epochs+1)), y=epoch_penalties, 
                    name='Total Penalty'
                ),
                dict(
                    title='Training Penalties of the Refined Model<br><sub>'
                        + f'Refined the base model for {ticker}</sub>', 
                    xaxis_title='Epoch', yaxis_title='Total Pentality', 
                    showlegend=True
                )
            ).show()

        if not in_research_env:
            return self._equity.symbol

    def _get_data(self, strike_level, start_date, end_date):
        # Get all the contracts that were trading at the start of the 
        # period.
        contract_symbols = self._algorithm.option_chain_provider.\
            get_option_contract_list(self._equity.symbol, start_date)

        # Filter the contracts.
        # (1) Select strikes near the underying price.
        strikes = sorted(list(set(
            [symbol.id.strike_price for symbol in contract_symbols]
        )))
        strikes_above = [s for s in strikes if s >= self._equity.price]
        strikes_below = [s for s in strikes if s < self._equity.price]
        if strike_level:
            if strike_level > 0:
                selected_strikes = [strikes_above[strike_level-1]]
            else:
                selected_strikes = [strikes_below[strike_level]]
        else:
            strikes_above = strikes_above[:3]
            strikes_below = strikes_below[-3:]
            selected_strikes = strikes_above + strikes_below
        # (2) Select call contracts that expire within n months.
        contract_symbols = [
            symbol 
            for symbol in contract_symbols 
            if (symbol.id.strike_price in selected_strikes and 
                symbol.id.option_right == OptionRight.CALL and
                symbol.id.date <= self._algorithm.time + self._max_contract_duration)
        ]
        selected_strikes = sorted(list(set(
            [symbol.id.strike_price for symbol in contract_symbols]
        )))
        # Create a DataFrame that contains history for the 
        # underlying Equity and all the selected contracts.
        option_history = self._algorithm.history(
            contract_symbols, start_date, end_date, Resolution.DAILY
        )
        equity_history = self._algorithm.history(
            self._equity.symbol, start_date, end_date, Resolution.DAILY, 
            data_normalization_mode=DataNormalizationMode.ScaledRaw
        )
        data = pd.merge(
            option_history.reset_index(), equity_history, 
            how="left", on='time', suffixes=("_option", "_underlying")
        ).set_index("time")
        
        return contract_symbols, selected_strikes, data

    def research_test(
            self, strike_level, start=datetime(2023,1,16), 
            end=datetime(2024,2,17)):
        contract_symbols, selected_strikes, data = self._get_data(
            strike_level, start, end
        )
        vol, rf = self._get_vol_and_rf(self._equity.symbol, start, end)
        ttm, moneyness, delta, position = self._generate_data(vol, rf)
        states, y, _, _ = self._forge_batch(
            moneyness, ttm, delta, position, ratio=1.
        )
        mu, sig = self._policy(states)

        mu = mu.detach()
        sig = sig.detach()
        score = T.abs((y - mu) / sig)
        alpha = T.quantile(score, 0.95).item()

        expiry = max([s.id.date for s in contract_symbols])
        K = contract_symbols[0].id.strike_price
        path = self._get_option_seq(data, K, expiry, start, end)
        ttm = np.array([path.shape[0] - i for i in range(path.shape[0])])/252
        S = np.array(path['close_underlying'])
        C = np.array(path['close_option'])
        moneyness = S[:-1] / K - 1
        deltaC = C[1:] - C[:-1]
        deltaS = S[1:] - S[:-1]
        delta = self._black_scholes_delta(S/K - 1, vol, rf, ttm).flatten()[:-1]
        ndelta = (deltaC / deltaS)[:-1]
        ndelta = np.insert(ndelta, 0, 0.5)

        pos = 0.
        mean = []
        std = []
        for i in range(path.shape[0]-1):
            states = T.tensor(
                [[moneyness[i], ttm[i], pos]], device=self._device
            ).float()
            mu, sig = self._policy(states)
            pos = mu
            mean.append(mu.item())
            std.append(sig.item())

        mu = np.array(mean)
        sig = np.array(std)
       
        x = path.index[1:]
        go.Figure(
            [
                go.Scatter(
                    x=x, y=np.maximum(mu - sig * alpha, 0.0), fill='tozeroy', 
                    fillcolor='rgba(255, 0, 0, 0)', line=dict(width=0), 
                    mode='lines', showlegend=False
                ),
                go.Scatter(
                    x=x, y=np.minimum(mu + sig * alpha, 1.0), fill='tonexty', 
                    fillcolor='rgba(255, 0, 0, 0.3)', line=dict(width=0), 
                    mode='lines', showlegend=False
                ),
                go.Scatter(
                    x=x, y=mu, mode='lines', 
                    line=dict(color='red', dash='dash'), name='AI hedging'
                ),
                go.Scatter(
                    x=x, y=delta, mode='lines', line=dict(color='blue'), 
                    name='Delta hedging'
                )
            ],
            dict(
                title=f'Decision Evolution<br><sub>Contract details: {K} strike, {expiry.date()} expiry</sub>', 
                xaxis_title='', yaxis_title='Value', 
                showlegend=True
            )
        ).show()

        fig = make_subplots(specs=[[{"secondary_y": True}]])
        fig.add_trace(
            go.Scatter(x=path.index, y=S.flatten(), name='Underlying', mode='lines+markers'),
            secondary_y=False,
        )
        for s in contract_symbols:
            contract_info = data[data['symbol'] == s]
            fig.add_trace(
                go.Scatter(
                    x=contract_info.index, y=contract_info['close_option'], 
                    name=f"Expiry {contract_info['expiry'].iloc[0].date()}", mode='lines'
                ),
                secondary_y=True,
            )
        fig.update_yaxes(title_text="Underlying Price", secondary_y=False)
        fig.update_yaxes(title_text="Contract Price", secondary_y=True)
        fig.update_xaxes(title_text="Date")
        fig.update_yaxes(showgrid=False, secondary_y=False)
        fig.update_yaxes(showgrid=False, secondary_y=True)
        fig.update_layout(
            title_text=f"Prices<br><sub>Underlying and contracts with a {K} strike price</sub>"
        )
        fig.update_xaxes(range=[data.index.min(), data.index.max()])
        fig.show()

        fee = self._commission * S[:-1]
        hold_change = (
            deltaS 
            - deltaC 
            - np.insert(np.zeros(deltaS.size-1), 0, 1.) * fee
        )
        ai_change = (
            deltaS * mu 
            - deltaC 
            - np.insert(np.diff(mu), 0, mu[0]) * fee
        )
        delta_change = (
            deltaS * delta 
            - deltaC 
            - np.insert(np.diff(delta), 0, delta[0]) * fee
        )
        ndelta_change = (
            deltaS * ndelta 
            - deltaC 
            - np.insert(np.diff(ndelta), 0, ndelta[0]) * fee
        )

        hold_wealth = np.cumsum(hold_change) + C[0]
        ai_wealth = np.cumsum(ai_change) + C[0]
        delta_wealth = np.cumsum(delta_change) + C[0]
        ndelta_wealth = np.cumsum(ndelta_change) + C[0]

        go.Figure(
            [
                go.Scatter(x=x, y=hold_wealth, name='Hold'),
                go.Scatter(x=x, y=ai_wealth, name='AI Hedging'),
                go.Scatter(x=x, y=delta_wealth, name='Delta Hedging'),
                go.Scatter(x=x, y=ndelta_wealth, name='Numerical Hedging')
            ],
            dict(
                title=f'Hedging Wealth<br><sub>Contract details: {K} strike, {expiry.date()} expiry</sub>', 
                xaxis_title='Date', yaxis_title='Value', 
                showlegend=True
            )
        ).show()

        go.Figure(
            [
                go.Scatter(x=x, y=hold_wealth - C[1:], name='Hold'),
                go.Scatter(x=x, y=ai_wealth - C[1:], name='AI Hedging'),
                go.Scatter(x=x, y=delta_wealth - C[1:], name='Delta Hedging'),
                go.Scatter(
                    x=x, y=ndelta_wealth - C[1:], name='Numerical Hedging'
                )
            ],
            dict(
                title=f'Hedging Performance<br><sub>Contract details: {K} strike, {expiry.date()} expiry</sub>', 
                xaxis_title='Date', 
                yaxis_title='Value', showlegend=True
            )
        ).show()

    def refit(self, save=False, epochs=20, lookback=timedelta(2*365)):
        # Load the base model from the Object Store.
        self._policy = joblib.load(
            self._algorithm.object_store.get_file_path(self._base_model_key)
        )
        contract_list_date = self._algorithm.time - lookback
        # Train the base model to be specific to this asset.
        contract_symbols, selected_strikes, data = self._get_data(
            None, contract_list_date, self._algorithm.time
        )
        # Reset the optimizer and run the epochs.
        self._policy.optimizer = optim.AdamW(self._policy.parameters(), lr=1e-5)
        epoch_penalties = []
        for E in range(epochs):
            total_pen = 0
            for k in selected_strikes:
                # Get the closest expiry.
                next_expiry = min(
                    [
                        symbol.id.date for symbol in contract_symbols 
                        if symbol.id.strike_price == k
                    ]
                )
                # Get the Option sequence data.
                path = self._get_option_seq(
                    data, k, next_expiry, contract_list_date, 
                    self._algorithm.time
                )
                s = path['close_underlying']
                c = path['close_option']
                if c.empty:
                    continue
                moneyness = s / k - 1
                ttm = np.array(
                    [path.shape[0] - i for i in range(path.shape[0])]
                ) / 252
                position = T.zeros([1], device=self._device, dtype=T.float32)
                wealth = c.iloc[0]

                self._policy.optimizer.zero_grad()
                
                for t in range(path.shape[0]-1):
                    state = T.cat(
                        (
                            T.tensor(
                                [moneyness.iloc[t], ttm[t]], 
                                device=self._device, dtype=T.float32
                            ), 
                            position
                        )
                    ).unsqueeze(0)
                    new_position, _ = self._policy.sample(state)
                    change = (
                        new_position * (s.iloc[t+1] - s.iloc[t]) 
                        - self._commission * (new_position - position) 
                        - (c.iloc[t+1] - c.iloc[t])
                    )
                    penalty =  T.relu( - change / wealth)
                    wealth += change.item()
                    (penalty).backward()
                    total_pen += penalty.item()

                self._policy.optimizer.step()
            epoch_penalties.append(total_pen)

        # Save the model to the Object store.
        if save or self._algorithm.live_mode:
            joblib.dump(
                self._policy, 
                self._algorithm.object_store.get_file_path(self._asset_model_key)
            )
        return epoch_penalties

    def trade(self, target_margin_usage):
        min_expiry_date = self._algorithm.time + self._min_contract_duration
        max_expiry_date = self._algorithm.time + self._max_contract_duration
        # If the current contract expires soon, liquidate it so we can 
        # roll-over to the next one.
        if (self._equity.option_contract is not None and 
            not (min_expiry_date <= self._equity.option_contract.id.date <= max_expiry_date)):
            self._algorithm.liquidate(self._equity.option_contract)
            self._algorithm.remove_option_contract(self._equity.option_contract)
            self._equity.option_contract = None

        # If not invested in a call Option contract, select one.
        if self._equity.option_contract is None:
            # Get all the contracts that are currently trading.
            contract_symbols = self._algorithm.option_chain_provider.\
                get_option_contract_list(
                    self._equity.symbol, self._algorithm.time
            )
            # Select an appropriate expiry date.
            expiry = min(
                [
                    symbol.id.date 
                    for symbol in contract_symbols 
                    if min_expiry_date + self._min_holding_period <= symbol.id.date <= max_expiry_date
                ]
            )
            # Select the ITM call contract with a strike price closest
            # to the underlying price.
            filtered_symbols = [
                symbol 
                for symbol in contract_symbols 
                if (symbol.id.date == expiry and 
                    symbol.id.option_right == OptionRight.CALL and 
                    symbol.id.strike_price < self._equity.price)
            ]
            self._equity.option_contract = sorted(
                filtered_symbols, key=lambda symbol: symbol.id.strike_price
            )[-1]
            # Subscribe to the new contract.
            self._algorithm.add_option_contract(self._equity.option_contract)
        
        # If we're not invested in the selected contract, buy it.
        if not self._algorithm.portfolio[self._equity.option_contract].invested:
            quantity = self._algorithm.calculate_order_quantity(
                self._equity.option_contract, target_margin_usage
            )
            if quantity == 0:
                self._algorithm.log(f"{self._algorithm.time} - zero quantity")
                self._algorithm.liquidate()
                return
            self._algorithm.market_order(
                self._equity.option_contract, 
                quantity
            )

        # If this method is running before `refit` has run at least once,
        # load the model from the Object Store.
        if self._algorithm.live_mode and self._policy is None:
            self._policy = joblib.load(
                self._algorithm.object_store.get_file_path(self._asset_model_key)
            )

        # Get the optimal Delta hedge from the neural network.
        moneyness = (
            self._equity.price 
            / self._equity.option_contract.id.strike_price
            - 1
        )
        ttm = (
            self._equity.option_contract.id.date - self._algorithm.time
        ).days / 365
        states = T.tensor(
            [[moneyness, ttm, self._pos]], device=self._device
        ).float()
        mu, _ = self._policy(states)
        self._pos = float(mu.detach()[0])
        # Plot the optimal Delta hedge.
        self._algorithm.plot(f"Delta", "AI Value", self._pos)
        vol, rf = self._get_vol_and_rf(self._equity.symbol, self._algorithm.time-timedelta(365), self._algorithm.time)
        training_delta = self._black_scholes_delta(moneyness, vol, rf, ttm)
        self._algorithm.plot(f"Delta", "Black Scholes", training_delta)

        # Adjust the underlying position to make the portfolio 
        # delta-neutral.
        contract_multiplier = self._algorithm.securities[
            self._equity.option_contract
        ].symbol_properties.contract_multiplier
        target_quantity = -int(
            self._pos 
            * self._algorithm.portfolio[self._equity.option_contract].quantity 
            * contract_multiplier
        )
        quantity = target_quantity - self._equity.holdings.quantity
        if quantity:
            self._algorithm.market_order(self._equity.symbol, quantity)

    def on_splits(self, splits, epochs, training_lookback):
        split = splits.get(self._equity.symbol)
        if split and split.type == SplitType.SPLIT_OCCURRED:
            # If you hold an Option contract for an underlying Equity 
            # when a split occurs, LEAN closes your Option contract 
            # position. Set the member to None so the algorithm buys 
            # a new contract when `_trade` is called next.
            self._equity.option_contract = None
            self.refit(self._algorithm.live_mode, epochs, training_lookback)

    def _black_scholes_delta(self, m, sig, r, t):
        d1 = np.log(m+1.) + (r+sig**2/2)*t
        return norm.cdf(d1)

    def _generate_data(self, vol, rf):
        ttm = np.random.uniform(size=self._size) * 31 / 252
        moneyness = np.random.uniform(size=self._size) * 2 - 1
        delta = self._black_scholes_delta(moneyness, vol, rf, ttm)
        position = np.random.uniform(size=self._size)
        return ttm, moneyness, delta, position

    def _forge_batch(self, moneyness, ttm, delta, position, ratio=0.75):
        cut = int(moneyness.size * ratio)
        tmp = delta * 0.9 + position * 0.1

        states = T.tensor(
            np.concatenate(
                (
                    moneyness.flatten()[:cut, np.newaxis], 
                    np.sqrt(ttm.flatten())[:cut, np.newaxis], 
                    position.flatten()[:cut, np.newaxis]
                ), 
                axis=1
            )
        ).float().to(self._device)

        y = T.tensor(tmp.flatten()[:cut, np.newaxis]).float().to(self._device)

        test_states = T.tensor(
            np.concatenate(
                (
                    moneyness.flatten()[cut:, np.newaxis], 
                    np.sqrt(ttm.flatten())[cut:, np.newaxis], 
                    position.flatten()[cut:, np.newaxis]
                ), 
                axis=1
            )
        ).float().to(self._device)

        test_y = T.tensor(
            tmp.flatten()[cut:, np.newaxis]
        ).float().to(self._device)
        
        return states, y, test_states, test_y

    def _get_option_seq(
            self, data, strike, expiry=datetime(2024,1,19), 
            start=datetime(2023,12,19), end=datetime(2024,1,20)):
        seq = data[
            (data['strike'] == strike) & 
            (data['expiry'] == expiry) & 
            (data['type'] == 'Call')
        ].iloc[:, 4:].interpolate(method='time')
        return seq[(seq.index > start) & (seq.index < end)]
    
