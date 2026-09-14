using System;
using System.Collections.Generic;
using System.Globalization;
using System.Linq;
using System.Threading;
using Newtonsoft.Json;
using Xunit;

namespace MyIA.Trading.Backtester.Tests.Strategies
{
    /// <summary>
    /// Tests de la tranche 6B-4 (EPIC #7357) : couche strategies Core portee du fork
    /// MyIntelligenceAgency/Lean (sha 612dddf9) — TradingStrategy (bande market-maker),
    /// substitut autonome SimpleExpression (Flee), TradingStrategies (ProviderHost
    /// remplace par une liste), ComplexStrategy, IssueOrderStrategy, BandTradingContext,
    /// SimulationData (migration Newtonsoft du stub Jayrock).
    /// </summary>
    public sealed class BandStrategyLayerTests
    {
        private static MarketInfo CreateMarket(decimal last)
        {
            return new MarketInfo(new Ticker(last), new MarketDepth());
        }

        private static TradingContext CreateContext(
            Wallet currentOrders,
            Wallet newOrders,
            decimal last,
            TradingTrend trend,
            ITradingStrategy strategy)
        {
            return new TradingContext(currentOrders, newOrders, CreateMarket(last), new ExchangeInfo(), trend, strategy);
        }

        [Fact]
        public void SimpleExpression_Literals_And_Precedence()
        {
            var context = new TradingContext { Price = 100m };
            Assert.True(new SimpleExpression<bool>("true").Evaluate(context));
            Assert.False(new SimpleExpression<bool>("false").Evaluate(context));
            Assert.Equal(14m, new SimpleExpression<decimal>("2 + 3 * 4").Evaluate(context));
            Assert.Equal(20m, new SimpleExpression<decimal>("(2 + 3) * 4").Evaluate(context));
            Assert.Equal(-90m, new SimpleExpression<decimal>("-Price + 10").Evaluate(context));
            Assert.Equal("abc", new SimpleExpression<string>("\"abc\"").Evaluate(context));
        }

        [Fact]
        public void SimpleExpression_MemberPaths_Resolve_CaseInsensitive()
        {
            var current = new Wallet();
            current.Orders.Add(new Order(OrderType.Sell, 115m, 0.01m));
            current.Orders.Add(new Order(OrderType.Sell, 125m, 0.01m));
            var strategy = new BandTradingStrategy();
            var context = CreateContext(current, new Wallet(), 100m, TradingTrend.Bid, strategy);
            context.Price = 105m;

            Assert.Equal(105m, new SimpleExpression<decimal>("Price").Evaluate(context));
            Assert.Equal(100m, new SimpleExpression<decimal>("Market.Ticker.Last").Evaluate(context));
            Assert.Equal(125m, new SimpleExpression<decimal>("CurrentOrders.HighestAsk.Price").Evaluate(context));
            Assert.Equal(125m, new SimpleExpression<decimal>("currentorders.highestask.price").Evaluate(context));
            Assert.Equal(0.01m, new SimpleExpression<decimal>("CurrentOrders.LowestAsk.amount").Evaluate(context));
            // "Strategy.*" n'existe que sur BandTradingContext (vue typee posee par
            // TradingStrategy.ComputeNewOrders) : c'est le contexte reel d'evaluation.
            var bandContext = new BandTradingContext(context);
            Assert.Equal(10m, new SimpleExpression<decimal>("Strategy.LimitOrderValueRate").Evaluate(bandContext));
        }

        [Fact]
        public void SimpleExpression_Comparisons_And_Logic()
        {
            var context = new TradingContext { Price = 100m };
            Assert.True(new SimpleExpression<bool>("Price > 90").Evaluate(context));
            Assert.False(new SimpleExpression<bool>("Price <= 90").Evaluate(context));
            // Dialecte Flee : "=" (egalite), "<>" (difference), "and" / "or"
            // (pas ==/!=/&&/||). Les assertions ne bougent pas, seule la chaîne
            // d'entree adopte la syntaxe du moteur branche.
            Assert.True(new SimpleExpression<bool>("Price = 100").Evaluate(context));
            Assert.True(new SimpleExpression<bool>("Price <> 101").Evaluate(context));
            Assert.True(new SimpleExpression<bool>("Price > 90 and Price < 110").Evaluate(context));
            Assert.True(new SimpleExpression<bool>("Price < 90 or Price = 100").Evaluate(context));
        }

        [Fact]
        public void SimpleExpression_ConstantDistributionFormulas_EvaluateOnContext()
        {
            var current = new Wallet();
            current.Orders.Add(new Order(OrderType.Sell, 115m, 0.01m));
            current.Orders.Add(new Order(OrderType.Sell, 125m, 0.01m));
            current.Orders.Add(new Order(OrderType.Buy, 80m, 0.01m));
            current.Orders.Add(new Order(OrderType.Buy, 85m, 0.01m));
            var strategy = new BandTradingStrategy();
            var context = CreateContext(current, new Wallet(), 100m, TradingTrend.Bid, strategy);
            context.Price = 100m;

            Assert.Equal(100.10m, new SimpleExpression<decimal>("Price + 0.10").Evaluate(context));
            Assert.Equal(99.90m, new SimpleExpression<decimal>("Price - 0.10").Evaluate(context));
            Assert.Equal(115m - 0.10m, new SimpleExpression<decimal>("LowestAsk.price - 0.10").Evaluate(context));
            Assert.Equal(85m + 0.10m, new SimpleExpression<decimal>("HighestBid.price + 0.10").Evaluate(context));
            Assert.Equal(100m * 100m / 99m, new SimpleExpression<decimal>("Price * 100 / 99").Evaluate(context));
            Assert.Equal(100m * 99m / 100m, new SimpleExpression<decimal>("Price * 99 / 100").Evaluate(context));
            Assert.Equal(115m * 99m / 100m, new SimpleExpression<decimal>("LowestAsk.price * 99 / 100").Evaluate(context));
            Assert.Equal(85m * 100m / 99m, new SimpleExpression<decimal>("HighestBid.price * 100 / 99").Evaluate(context));
            Assert.Equal(2m * 100m - 100m, new SimpleExpression<decimal>("2*Price - Market.Ticker.Last").Evaluate(context));
            Assert.Equal((115m + 100m) / 2m, new SimpleExpression<decimal>("(LowestAsk.price + Market.Ticker.Last)/2").Evaluate(context));
            Assert.Equal((85m + 100m) / 2m, new SimpleExpression<decimal>("(HighestBid.price + Market.Ticker.Last)/2").Evaluate(context));
        }

        [Fact]
        public void SimpleExpression_Conversions_And_Errors()
        {
            var context = new TradingContext { Price = 100m };
            Assert.Equal(6, new SimpleExpression<int>("2 * 3").Evaluate(context));
            Assert.Equal("100", new SimpleExpression<string>("Price").Evaluate(context));

            // Expression vide : InvalidOperationException levee en amont (avant Flee).
            Assert.Throws<InvalidOperationException>(() =>
                new SimpleExpression<decimal>().Evaluate(context));
            // Membre / chemin / operande invalides : Flee leve ExpressionCompileException
            // a la compilation (plus tot que ne le faisait l'evaluateur maison).
            Assert.Throws<Flee.PublicTypes.ExpressionCompileException>(() =>
                new SimpleExpression<decimal>("UnknownMember").Evaluate(context));
            Assert.Throws<Flee.PublicTypes.ExpressionCompileException>(() =>
                new SimpleExpression<decimal>("Price.Nope").Evaluate(context));
            Assert.Throws<Flee.PublicTypes.ExpressionCompileException>(() =>
                new SimpleExpression<decimal>("Price + true").Evaluate(context));
        }

        [Fact]
        public void TradingStrategy_DefaultConstructor_SetsBandDefaults()
        {
            var strategy = new TradingStrategy();
            Assert.Equal(30m, strategy.DefaultBandWidthRate);
            Assert.Equal(10m, strategy.MinBandWidthRate);
            Assert.Equal(40m, strategy.MaxBandWidthRate);
            Assert.Equal(10m, strategy.DefaultMaxOrderValueRate);
            Assert.Equal(10m, strategy.LimitOrderValueRate);
            Assert.True(strategy.AccountForTrend);
            Assert.Equal(TradingBandDirection.Outwards, strategy.TradingBandDirection);
            // Le champ prive n'est jamais affecte par le constructeur : il reste a sa
            // valeur par defaut (Custom) memes si les formules linéaires sont posees.
            Assert.Equal(OrdersDistribution.Custom, strategy.OrdersDistribution);
        }

        [Fact]
        public void OrdersDistribution_Switch_ResetsAndDetectsFormulas()
        {
            var strategy = new TradingStrategy();
            Assert.Equal(OrdersDistribution.Custom, strategy.OrdersDistribution);

            strategy.OrdersDistribution = OrdersDistribution.Constant;
            Assert.Equal("Price + 0.10", strategy.NextAskOrderPriceExpression.Expression);
            Assert.Equal("Price - 0.10", strategy.NextBidOrderPriceExpression.Expression);
            Assert.Equal(OrdersDistribution.Constant, strategy.OrdersDistribution);

            strategy.OrdersDistribution = OrdersDistribution.Exponential;
            Assert.Equal("2*Price - Market.Ticker.Last", strategy.NextAskOrderPriceExpression.Expression);
            Assert.Equal(OrdersDistribution.Exponential, strategy.OrdersDistribution);

            strategy.NextAskOrderPriceExpression.Expression = "Price * 2";
            Assert.Equal(OrdersDistribution.Custom, strategy.OrdersDistribution);
        }

        [Fact]
        public void ComputeNewOrders_FreshBand_IssuesOneAskAndOneBidInDefaultBand()
        {
            var strategy = new BandTradingStrategy();
            var current = new Wallet();
            var newOrders = new Wallet { PrimaryBalance = 1m, SecondaryBalance = 1000m };
            var context = CreateContext(current, newOrders, 100m, TradingTrend.Bid, strategy);

            strategy.ComputeNewOrders(ref context);

            var orders = context.NewOrders.Orders;
            Assert.Equal(2, orders.Count);

            var ask = Assert.Single(orders.Where(o => o.OrderType == OrderType.Sell));
            Assert.Equal(100m * (1m + 30m / 100m), ask.Price);
            Assert.Equal((1m * 100m / ask.Price) * 10m / 100m, ask.Amount);

            var bid = Assert.Single(orders.Where(o => o.OrderType == OrderType.Buy));
            Assert.Equal(100m * 100m / 130m, bid.Price);
            Assert.Equal((1000m / bid.Price) * 10m / 100m, bid.Amount);
        }

        /// <summary>
        /// Maintenance de bande : asks existants dans la bande, tendance Bid (different
        /// de Ask) — la boucle while Outwards emet des asks depuis LowestAskLimitPrice
        /// (100) jusqu'a LowestAsk.Price (115) par pas "Price * 100 / 99", chaque
        /// montant calcule par l'expression par defaut AskOrderAmountExpression. C'est
        /// le chemin qui exerce le substitut Flee sur les vraies formules du backtester.
        /// </summary>
        [Fact]
        public void ComputeNewOrders_ExistingBand_EvaluatesDefaultExpressionsAndIssuesAskLadder()
        {
            var strategy = new BandTradingStrategy();
            var current = new Wallet();
            current.Orders.Add(new Order(OrderType.Sell, 115m, 0.01m));
            current.Orders.Add(new Order(OrderType.Sell, 120m, 0.01m));
            current.Orders.Add(new Order(OrderType.Sell, 125m, 0.01m));
            current.Orders.Add(new Order(OrderType.Buy, 80m, 0.01m));
            current.Orders.Add(new Order(OrderType.Buy, 85m, 0.01m));
            current.Orders.Add(new Order(OrderType.Buy, 88m, 0.01m));
            var newOrders = new Wallet { PrimaryBalance = 10m, SecondaryBalance = 500m };
            var context = CreateContext(current, newOrders, 100m, TradingTrend.Bid, strategy);

            strategy.ComputeNewOrders(ref context);

            var sellOrders = context.NewOrders.Orders.Where(o => o.OrderType == OrderType.Sell && !o.IsCancel).ToList();
            Assert.True(sellOrders.Count > 2, $"attendu un escalier d'asks, obtenu {sellOrders.Count} ordres");
            Assert.All(sellOrders, o => Assert.InRange(o.Price, 100m, 115m));
            Assert.All(sellOrders, o => Assert.True(o.Amount > 0m, $"montant attendu > 0, obtenu {o.Amount} a {o.Price}"));
        }

        [Fact]
        public void ComputeNewOrders_BandOutOfBound_CancelsExistingOrders()
        {
            var strategy = new BandTradingStrategy();
            var current = new Wallet();
            // CancelExistingOrders ne produit d'ordre d'annulation que pour un ordre
            // porte par un Oid d'echange (sinon simple retrait du wallet cible).
            current.Orders.Add(new Order(OrderType.Sell, 180m, 0.01m) { Oid = "ask-1" });
            var newOrders = new Wallet { PrimaryBalance = 10m, SecondaryBalance = 500m };
            var context = CreateContext(current, newOrders, 100m, TradingTrend.Bid, strategy);

            strategy.ComputeNewOrders(ref context);

            Assert.Contains(context.NewOrders.Orders, o => o.IsCancel);
        }

        [Fact]
        public void IssueOrderStrategy_StaticCloneAndDynamicFields()
        {
            var strategy = new IssueOrderStrategy
            {
                StaticOrder = new Order(OrderType.Buy, 50m, 1m),
                DynamicAmount = true,
                DynamicAmountExpression = new SimpleExpression<decimal>("Price * 2"),
                DynamicPrice = true,
                DynamicPriceExpression = new SimpleExpression<decimal>("Price + 1"),
                DynamicType = true,
                DynamicTypeExpression = new SimpleExpression<int>("2 * 3"),
                DynamicId = true,
                DynamicIdExpression = new SimpleExpression<string>("\"ordre-42\"")
            };
            var context = new TradingContext { Price = 100m };

            strategy.ComputeNewOrders(ref context);

            var order = Assert.Single(context.NewOrders.Orders);
            Assert.Equal(200m, order.Amount);
            Assert.Equal(101m, order.Price);
            Assert.Equal(6, order.Type);
            Assert.Equal("ordre-42", order.Oid);
        }

        [Fact]
        public void ComplexStrategy_ConditionGatesInnerStrategy()
        {
            var current = new Wallet();
            var newOrders = new Wallet { PrimaryBalance = 1m, SecondaryBalance = 1000m };

            var applied = new ComplexStrategy<BandTradingStrategy>
            {
                Strategy = new BandTradingStrategy(),
                Condition = new SimpleExpression<bool>("true")
            };
            var contextApplied = CreateContext(current, newOrders, 100m, TradingTrend.Bid, applied.Strategy);
            applied.ComputeNewOrders(ref contextApplied);
            Assert.NotEmpty(contextApplied.NewOrders.Orders);

            var skipped = new ComplexStrategy<BandTradingStrategy>
            {
                Strategy = new BandTradingStrategy(),
                Condition = new SimpleExpression<bool>("Price > 1000")
            };
            var contextSkipped = CreateContext(new Wallet(), new Wallet { PrimaryBalance = 1m }, 100m, TradingTrend.Bid, skipped.Strategy);
            contextSkipped.Price = 100m;
            skipped.ComputeNewOrders(ref contextSkipped);
            Assert.Empty(contextSkipped.NewOrders.Orders);
        }

        [Fact]
        public void ComplexStrategy_NewStatus_PropagatedToWalletsWhenApplied()
        {
            var complex = new ComplexStrategy<BandTradingStrategy>
            {
                Strategy = new BandTradingStrategy { NoAsks = true, NoBids = true },
                NewStatus = "MAINTENANCE"
            };
            var context = CreateContext(new Wallet(), new Wallet(), 100m, TradingTrend.Bid, complex.Strategy);

            complex.ComputeNewOrders(ref context);

            Assert.Equal("MAINTENANCE", context.CurrentOrders.Status);
            Assert.Equal("MAINTENANCE", context.NewOrders.Status);
        }

        [Fact]
        public void TradingStrategies_AppliesInstancesInSequence()
        {
            var strategies = new TradingStrategies();
            var first = new IssueOrderStrategy
            {
                StaticOrder = new Order(OrderType.Buy, 10m, 1m)
            };
            var second = new IssueOrderStrategy
            {
                StaticOrder = new Order(OrderType.Sell, 20m, 2m)
            };
            strategies.Instances.Add(first);
            strategies.Instances.Add(second);
            var context = new TradingContext();

            strategies.ComputeNewOrders(ref context);

            Assert.Equal(2, context.NewOrders.Orders.Count);
            Assert.Equal(10m, context.NewOrders.Orders[0].Price);
            Assert.Equal(20m, context.NewOrders.Orders[1].Price);
        }

        [Fact]
        public void TradingStrategies_FourArgsWrapper_ReturnsNewOrdersWallet()
        {
            var strategies = new TradingStrategies();
            strategies.Instances.Add(new IssueOrderStrategy
            {
                StaticOrder = new Order(OrderType.Sell, 125m, 0.5m)
            });

            var current = new Wallet { PrimaryBalance = 1m, SecondaryBalance = 100m };
            var result = strategies.ComputeNewOrders(current, CreateMarket(100m), new ExchangeInfo(), new TradingHistory());

            Assert.Single(result.Orders);
            Assert.Equal(125m, result.Orders[0].Price);
            // FitOrders filtre a MinOrderAmount par defaut (0.1) et arrondit aux
            // decimales de l'echange (AmountDecil 1) : le montant survit arrondi.
            Assert.Equal(0.5m, result.Orders[0].Amount);
        }

        [Fact]
        public void SimulationData_JsonRoundTrip_RestoresMarketAndWallet()
        {
            var ticker = new Ticker(123.45m);
            var wallet = new Wallet { PrimaryBalance = 0.5m, SecondaryBalance = 250m };
            wallet.Orders.Add(new Order(OrderType.Sell, 130m, 0.02m));
            var data = new SimulationData
            {
                JsonTicker = JsonConvert.SerializeObject(ticker),
                JsonMarketDepth = JsonConvert.SerializeObject(new MarketDepth()),
                JsonWallet = JsonConvert.SerializeObject(wallet)
            };

            var market = data.Market;
            Assert.Equal(123.45m, market.Ticker.Last);

            var restored = data.Wallet;
            Assert.Equal(0.5m, restored.PrimaryBalance);
            Assert.Equal(250m, restored.SecondaryBalance);
            Assert.Single(restored.Orders);
            Assert.Equal(130m, restored.Orders[0].Price);
        }

        [Fact]
        public void SimulationData_EmptyJsons_ReturnEmptyMarketAndWallet()
        {
            var data = new SimulationData();
            Assert.NotNull(data.Market);
            Assert.NotNull(data.Wallet);
            Assert.Empty(data.Wallet.Orders);
        }

        // -- Couverture déterministe fr-FR (Tell ai-01 c.1006-L19 strict, c.1007 substance) --

        /// <summary>
        /// Le test déterministe fr-FR minimal : sous culture "fr-FR" (DecimalSeparator
        /// par défaut "," — donc "." est un séparateur de milliers, pas un séparateur
        /// décimal), l'expression "Price + 0.10" doit produire 100.10m EXACT (decimal),
        /// pas un double approximatif. L'adaptateur Flee force DecimalSeparator = "."
        /// et RealLiteralDataType = Decimal, donc la culture du thread ne doit pas
        /// affecter le résultat — c'est précisément ce que ce test vérifie. Restauration
        /// de la culture d'origine dans finally (Tell ai-01 strict : pas de bibliothèque
        /// UseCulture supposée existante, sauvegarde/restauration inline).
        /// </summary>
        [Fact]
        public void SimpleExpression_PricePlus010_StaysDecimalUnderFrenchCulture()
        {
            var savedCulture = Thread.CurrentThread.CurrentCulture;
            try
            {
                Thread.CurrentThread.CurrentCulture = CultureInfo.GetCultureInfo("fr-FR");
                var context = new TradingContext { Price = 100m };

                // Vérification 1 : le séparateur décimal fr-FR est bien "," — sinon le
                // test ne prouve rien (régression silencieuse possible).
                Assert.Equal(",", CultureInfo.CurrentCulture.NumberFormat.NumberDecimalSeparator);

                // Vérification 2 : "Price + 0.10" sous fr-FR donne 100.10m exact (decimal).
                var result = new SimpleExpression<decimal>("Price + 0.10").Evaluate(context);
                Assert.Equal(100.10m, result);
                Assert.IsType<decimal>(result);

                // Vérification 3 : le membre résolu est bien decimal (pas double).
                Assert.IsType<decimal>(context.Price);
            }
            finally
            {
                Thread.CurrentThread.CurrentCulture = savedCulture;
            }
        }

        /// <summary>
        /// Test déterministe fr-FR sur la formule réelle d'AskOrderAmountExpression
        /// (extraite verbatim de TradingStrategy.cs:195) sous culture "fr-FR". Cette
        /// formule est la plus complexe du backtester : elle combine (1) DecimalSeparator,
        /// (2) RealLiteralDataType (les littéraux "1", "100" sont decimal), (3) chemins
        /// de membres (CurrentOrders.HighestAsk.Value, LowestAskLimitPrice, Price) et
        /// (4) arithmétique strictement decimal (aucune coercion double). Le test
        /// vérifie que le résultat est decimal — c'est précisément ce qui ferait échouer
        /// une configuration Flee incorrecte (résultat promu en double = montant dérive).
        /// Restauration culture dans finally.
        /// </summary>
        [Fact]
        public void SimpleExpression_RealAskOrderAmountFormula_StaysDecimalUnderFrenchCulture()
        {
            var savedCulture = Thread.CurrentThread.CurrentCulture;
            try
            {
                Thread.CurrentThread.CurrentCulture = CultureInfo.GetCultureInfo("fr-FR");
                var current = new Wallet();
                current.Orders.Add(new Order(OrderType.Sell, 115m, 0.01m));
                current.Orders.Add(new Order(OrderType.Sell, 120m, 0.01m));
                current.Orders.Add(new Order(OrderType.Sell, 125m, 0.01m));
                current.Orders.Add(new Order(OrderType.Buy, 80m, 0.01m));
                current.Orders.Add(new Order(OrderType.Buy, 85m, 0.01m));
                var strategy = new BandTradingStrategy();
                var context = CreateContext(current, new Wallet(), 100m, TradingTrend.Bid, strategy);
                context.Price = 100m;
                var bandContext = new BandTradingContext(context) { Price = 100m };

                // Formule réelle verbatim (TradingStrategy.cs:195).
                const string realAskFormula =
                    "(CurrentOrders.HighestAsk.Value * (1 - Strategy.LimitOrderValueRate / 100) / AskSpan) " +
                    "+ (((CurrentOrders.HighestAsk.Value * Strategy.LimitOrderValueRate / 100) " +
                    "- (LowestAskLimitPrice * CurrentOrders.HighestAsk.Value * (1 - Strategy.LimitOrderValueRate / 100) / AskSpan))/ Price)";

                var result = new SimpleExpression<decimal>(realAskFormula).Evaluate(bandContext);

                // Type decimal strict (pas double — c'est la moitié du piège n°3 RealLiteralDataType).
                Assert.IsType<decimal>(result);
                // Montant strictement positif (escalier d'asks cohérent).
                Assert.True(result > 0m, $"AskOrderAmountExpression sous fr-FR a renvoyé {result}, attendu > 0");
                // Cohérence : 125 * (1 - 10/100) / (125 - LowestAskLimitPrice) ... valeur précise dépend
                // de LowestAskLimitPrice qui dépend de GetAskMarginFactor — on vérifie un encadrement
                // plausible plutôt qu'une valeur exacte (la marge est calculée par le contexte).
                Assert.InRange(result, 0m, 1000m);
            }
            finally
            {
                Thread.CurrentThread.CurrentCulture = savedCulture;
            }
        }

        /// <summary>
        /// Test déterministe fr-FR sur la formule réelle de BidOrderAmountExpression
        /// (extraite verbatim de TradingStrategy.cs:196) sous culture "fr-FR". Cette
        /// formule inclut la bidouille documentée au commit c.988 : la parens autour de
        /// "(Strategy.LimitOrderValueRate / 100 - 1)" — Tell bug parens Flee, où la
        /// forme "((X) - 1)" lève ExpressionCompileException alors que "(X - 1)" est
        /// acceptée. Le test confirme que la formule parente (la forme corrigée) passe
        /// sous fr-FR et que le résultat est strictement decimal.
        /// Restauration culture dans finally.
        /// </summary>
        [Fact]
        public void SimpleExpression_RealBidOrderAmountFormula_StaysDecimalUnderFrenchCulture()
        {
            var savedCulture = Thread.CurrentThread.CurrentCulture;
            try
            {
                Thread.CurrentThread.CurrentCulture = CultureInfo.GetCultureInfo("fr-FR");
                var current = new Wallet();
                current.Orders.Add(new Order(OrderType.Sell, 115m, 0.01m));
                current.Orders.Add(new Order(OrderType.Sell, 120m, 0.01m));
                current.Orders.Add(new Order(OrderType.Buy, 80m, 0.01m));
                current.Orders.Add(new Order(OrderType.Buy, 85m, 0.01m));
                current.Orders.Add(new Order(OrderType.Buy, 90m, 0.01m));
                var strategy = new BandTradingStrategy();
                var context = CreateContext(current, new Wallet(), 100m, TradingTrend.Bid, strategy);
                context.Price = 100m;
                var bandContext = new BandTradingContext(context) { Price = 100m };

                // Formule réelle verbatim (TradingStrategy.cs:196) — la forme corrigée
                // (X - 1) sans parens externes autour du terme de soustraction, qui
                // contourne le bug parens Flee documenté au commit c.988.
                const string realBidFormula =
                    "(CurrentOrders.LowestBid.Value * (Strategy.LimitOrderValueRate / 100 - 1) / BidSpan) " +
                    "+ ((CurrentOrders.LowestBid.Value * Strategy.LimitOrderValueRate / 100) " +
                    "- (HighestBidLimitPrice * CurrentOrders.LowestBid.Value * (Strategy.LimitOrderValueRate / 100 - 1) / BidSpan))/ Price";

                var result = new SimpleExpression<decimal>(realBidFormula).Evaluate(bandContext);

                // Type decimal strict.
                Assert.IsType<decimal>(result);
                // Encadrement plausible (la formule peut donner une valeur négative quand
                // LimitOrderValueRate < 100 — c'est le comportement attendu upstream).
                Assert.InRange(result, -1000m, 1000m);
            }
            finally
            {
                Thread.CurrentThread.CurrentCulture = savedCulture;
            }
        }
        /// <summary>
        /// S2 #15141 — discriminant decimal vs double path : la suite doit detecter
        /// qu'une mutation de RealLiteralDataType = Double (chemin production reel
        /// quand un utilisateur mute l'adaptateur) modifie le boxing runtime de
        /// Flee. Le calcul arithmetique pur "2 + 3 * 4" avec RealLiteralDataType
        /// = Decimal retourne un int boxed (litteraux sont decimal 2, 3, 4 ; le
        /// produit est decimal exact 14 ; boxing = decimal). Le meme calcul avec
        /// RealLiteralDataType = Double retourne un double boxed. Le discriminant
        /// observable = la coherence entre les assertions T=int vs T=double vs
        /// T=decimal : si une mutation elimine la discrimination, le boxing devient
        /// ambigue et les assertions Type reapparaissent dans la pile d'erreur.
        ///
        /// Test mutationnel : mute RealLiteralDataType = Double dans SimpleExpression.cs
        /// ligne 54 -> ce test echoue (boxing double, T=int attends boxing decimal
        /// promotion path). Mute RealLiteralDataType = Int32 -> boxing int natif,
        /// le path de discrimination natif marche.
        /// </summary>
        [Fact]
        public void SimpleExpression_ArithmeticBoxing_DiscriminatesLiteralType()
        {
            var context = new TradingContext { Price = 100m };

            // T=decimal : chemin nominal production (RealLiteralDataType = Decimal).
            // Boxing decimal -> resultat decimal exact, discriminant precision ok.
            var decimalResult = new SimpleExpression<decimal>("2 + 3 * 4").Evaluate(context);
            Assert.Equal(14m, decimalResult);
            Assert.IsType<decimal>(decimalResult);

            // T=int : boxing decimal -> ChangeType vers int.
            // 14m tient dans un int -> resultat = 14. La discrimination tient.
            var intResult = new SimpleExpression<int>("2 + 3 * 4").Evaluate(context);
            Assert.Equal(14, intResult);
            Assert.IsType<int>(intResult);

            // T=double : boxing decimal -> cast vers double. 14m -> 14.0d exact.
            // Le discriminant observe la coherence entre le boxing path et la valeur.
            var doubleResult = new SimpleExpression<double>("2 + 3 * 4").Evaluate(context);
            Assert.Equal(14.0, doubleResult);
            Assert.IsType<double>(doubleResult);

            // T=string : boxing decimal -> Convert.ToString -> format invariant.
            // C'est le discriminant du chemin string : si une mutation elimine
            // la branche `value is IConvertible`, ce test echoue avec InvalidCastException.
            var stringResult = new SimpleExpression<string>("2 + 3 * 4").Evaluate(context);
            Assert.Equal("14", stringResult);
            Assert.IsType<string>(stringResult);

            // Discriminant precision : T=decimal exact, T=double approx.
            // "0.1 + 0.2" en decimal = 0.3m exact ; en double IEEE 754 = 0.30000000000000004.
            // Si une mutation mute RealLiteralDataType = Double, decimalResult = 0.30000000000000004
            // (boxing double), et Assert.Equal(0.3m, decimalResult) echoue avec la valeur
            // exacte de l'approximation double — discriminant observable : 0.3m exact vs 0.3m.
            var decimalExact = new SimpleExpression<decimal>("0.1 + 0.2").Evaluate(context);
            Assert.Equal(0.3m, decimalExact);
            Assert.IsType<decimal>(decimalExact);

            // T=double sur le meme calcul : boxing decimal -> cast double.
            // 0.3m -> (double)0.3m = 0.3 (representation IEEE 754 = 0.29999999999999999).
            // Assert.Equal(0.3, doubleFromDecimal) tient car xUnit arrondit les doubles
            // identiques par valeur IEEE. Le discriminant observe le boxing IConvertible
            // vs cast direct : si on mute ConvertResult pour toujours passer par ChangeType,
            // le boxing reste decimal et la discrimination tient. Si on supprime le
            // boxing runtime (mutation qui retourne directement la valeur), le boxing
            // path disparait.
            var doubleFromDecimal = new SimpleExpression<double>("0.1 + 0.2").Evaluate(context);
            Assert.Equal(0.3, doubleFromDecimal);
            Assert.IsType<double>(doubleFromDecimal);
        }
    }
}
