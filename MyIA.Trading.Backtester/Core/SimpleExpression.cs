using System;
using System.Globalization;
using Flee.PublicTypes;

namespace MyIA.Trading.Backtester
{
    /// <summary>
    /// Expression dynamique evaluee contre un contexte de trading via Flee 2.0.0
    /// (Fast Lightweight Expression Evaluator, NuGet PackageReference deja cablee sur
    /// main). Le constructeur configure le parser pour la culture fr-FR et le type
    /// decimal : <see cref="ExpressionContext.ParserOptions.DecimalSeparator"/> = '.',
    /// <see cref="ExpressionParserOptions.RecreateParser"/> (le parser est en cache,
    /// sans RecreateParser le changement de DecimalSeparator est inoperant) et
    /// <see cref="ExpressionOptions.RealLiteralDataType"/> = Decimal (CompileGeneric&lt;decimal&gt;
    /// doit recevoir des littéraux Decimal, sinon le resultat est promu en Double
    /// et les montants derivent). Les chemins de membres (ex. "Market.Ticker.Last",
    /// "CurrentOrders.HighestAsk.Value", "LowestAsk.price") sont resolus par Flee
    /// sur l'owner via reflection case-insensitive. L'arithmetique suit la
    /// semantique C# : division entiere si deux litteraux entiers, decimale des
    /// qu'un operande est decimal. Operateurs relationnels et logiques en
    /// dialecte Flee : "=" et "&lt;&gt;" (pas "==" / "!="), "and" / "or" (pas "&amp;&amp;"
    /// / "||"). Voir MEMORY "Flee 2.0.0 pièges fr-FR + dialecte" pour les 4 pieges
    /// et la mesure 16/17 banc c.988.
    /// </summary>
    [Serializable]
    public class SimpleExpression<T>
    {
        public string Expression { get; set; }

        public SimpleExpression()
        {
        }

        public SimpleExpression(string expression)
        {
            Expression = expression;
        }

        public T Evaluate(TradingContext tContext)
        {
            if (string.IsNullOrWhiteSpace(Expression))
            {
                throw new InvalidOperationException(
                    "SimpleExpression : expression vide (definissez Expression avant l'evaluation)");
            }
            if (tContext == null)
            {
                throw new ArgumentNullException(nameof(tContext));
            }

            var context = new ExpressionContext(tContext);
            context.ParserOptions.DecimalSeparator = '.';
            context.ParserOptions.RecreateParser();
            context.Options.RealLiteralDataType = RealLiteralDataType.Decimal;

            object result = context.CompileGeneric<object>(Expression).Evaluate();
            return ConvertResult(result);
        }

        private T ConvertResult(object value)
        {
            if (value is T typedValue)
            {
                return typedValue;
            }
            if (value is decimal decimalValue)
            {
                if (typeof(T) == typeof(decimal))
                {
                    return (T)(object)decimalValue;
                }
                return (T)Convert.ChangeType(decimalValue, typeof(T), CultureInfo.InvariantCulture);
            }
            if (value is IConvertible)
            {
                return (T)Convert.ChangeType(value, typeof(T), CultureInfo.InvariantCulture);
            }
            throw new InvalidOperationException(string.Format(
                CultureInfo.InvariantCulture,
                "SimpleExpression : le resultat de type {0} n'est pas convertible en {1} (expression : '{2}')",
                value.GetType().Name, typeof(T).Name, Expression));
        }
    }
}
