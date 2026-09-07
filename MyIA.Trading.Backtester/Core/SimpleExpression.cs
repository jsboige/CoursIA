using System;
using System.Collections.Generic;
using System.Globalization;
using System.Reflection;

namespace MyIA.Trading.Backtester
{
    /// <summary>
    /// Expression dynamique evaluee contre un contexte de trading. Substitut autonome
    /// de Aricie.DNN.Services.Flee.SimpleExpression (Flee etant inaccessible hors des
    /// DLL Aricie abandonnees) : la grammaire portee couvre exactement le vocabulaire
    /// des expressions du backtester — litteraux (decimal, bool, chaine), acces de
    /// membres par chemin (ex. "Market.Ticker.Last", "CurrentOrders.HighestAsk.Value",
    /// resolu par reflexion insensible a la casse, ex. "LowestAsk.price"), arithmetique
    /// decimale + - * / unaires et parenteses, comparaisons (&lt; &gt; &lt;= &gt;= == !=)
    /// et operateurs logiques (&amp;&amp; ||). L'arithmetique reste en decimal : aucune
    /// coercion double, les montants ne derivent pas.
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

            var result = new SimpleExpressionEvaluator(Expression).Evaluate(tContext);
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

    /// <summary>
    /// Evaluateur recursif descendant pour les SimpleExpression. Valeurs intermediaires
    /// en object : decimal pour tout le numerique, bool pour comparaisons et logique,
    /// string pour les litteraux de chaine. Precedence usuelle : || puis &amp;&amp; puis
    /// comparaisons puis + - puis * / puis unaire.
    /// </summary>
    internal sealed class SimpleExpressionEvaluator
    {
        private readonly string _expression;
        private int _position;

        internal SimpleExpressionEvaluator(string expression)
        {
            _expression = expression;
        }

        internal object Evaluate(object context)
        {
            var value = ParseOr(context);
            SkipWhitespace();
            if (_position < _expression.Length)
            {
                throw Fail($"caractere inattendu '{_expression[_position]}'");
            }
            return value;
        }

        private object ParseOr(object context)
        {
            var left = ParseAnd(context);
            while (TryConsumeOperator("||"))
            {
                var right = ParseAnd(context);
                left = ToBoolean(left) || ToBoolean(right);
            }
            return left;
        }

        private object ParseAnd(object context)
        {
            var left = ParseComparison(context);
            while (TryConsumeOperator("&&"))
            {
                var right = ParseComparison(context);
                left = ToBoolean(left) && ToBoolean(right);
            }
            return left;
        }

        private object ParseComparison(object context)
        {
            var left = ParseAdditive(context);
            string op = ReadComparisonOperator();
            if (op == null)
            {
                return left;
            }
            var right = ParseAdditive(context);
            if (left is string || right is string)
            {
                if (op != "==" && op != "!=")
                {
                    throw Fail($"comparaison '{op}' non applicable a une chaine");
                }
                var equals = string.Equals((string)AsKind(left, typeof(string)), (string)AsKind(right, typeof(string)), StringComparison.Ordinal);
                return op == "==" ? equals : !equals;
            }
            var leftDecimal = ToDecimal(left);
            var rightDecimal = ToDecimal(right);
            switch (op)
            {
                case "<": return leftDecimal < rightDecimal;
                case ">": return leftDecimal > rightDecimal;
                case "<=": return leftDecimal <= rightDecimal;
                case ">=": return leftDecimal >= rightDecimal;
                case "==": return leftDecimal == rightDecimal;
                case "!=": return leftDecimal != rightDecimal;
                default: throw Fail($"operateur inconnu '{op}'");
            }
        }

        private object ParseAdditive(object context)
        {
            var left = ParseMultiplicative(context);
            while (true)
            {
                SkipWhitespace();
                if (TryConsumeOperator("+"))
                {
                    left = ToDecimal(left) + ToDecimal(ParseMultiplicative(context));
                }
                else if (PeekOperator("-"))
                {
                    _position++;
                    left = ToDecimal(left) - ToDecimal(ParseMultiplicative(context));
                }
                else
                {
                    return left;
                }
            }
        }

        private object ParseMultiplicative(object context)
        {
            var left = ParseUnary(context);
            while (true)
            {
                SkipWhitespace();
                if (TryConsumeOperator("*"))
                {
                    left = ToDecimal(left) * ToDecimal(ParseUnary(context));
                }
                else if (PeekOperator("/"))
                {
                    _position++;
                    left = ToDecimal(left) / ToDecimal(ParseUnary(context));
                }
                else
                {
                    return left;
                }
            }
        }

        private object ParseUnary(object context)
        {
            SkipWhitespace();
            if (PeekOperator("-"))
            {
                _position++;
                return -ToDecimal(ParseUnary(context));
            }
            if (PeekOperator("+"))
            {
                _position++;
                return ToDecimal(ParseUnary(context));
            }
            return ParsePrimary(context);
        }

        private object ParsePrimary(object context)
        {
            SkipWhitespace();
            if (_position >= _expression.Length)
            {
                throw Fail("fin d'expression inattendue");
            }
            var current = _expression[_position];
            if (current == '(')
            {
                _position++;
                var value = ParseOr(context);
                SkipWhitespace();
                if (!TryConsumeOperator(")"))
                {
                    throw Fail("parenthese fermante attendue");
                }
                return value;
            }
            if (current == '"')
            {
                return ReadStringLiteral();
            }
            if (char.IsDigit(current) || (current == '.' && _position + 1 < _expression.Length && char.IsDigit(_expression[_position + 1])))
            {
                return ReadNumber();
            }
            if (char.IsLetter(current) || current == '_')
            {
                var path = ReadMemberPath();
                var firstSegment = path[0];
                if (path.Count == 1)
                {
                    if (string.Equals(firstSegment, "true", StringComparison.OrdinalIgnoreCase))
                    {
                        return true;
                    }
                    if (string.Equals(firstSegment, "false", StringComparison.OrdinalIgnoreCase))
                    {
                        return false;
                    }
                }
                return ResolvePath(path, context);
            }
            throw Fail($"jeton inattendu '{current}'");
        }

        private string ReadStringLiteral()
        {
            _position++;
            var start = _position;
            while (_position < _expression.Length && _expression[_position] != '"')
            {
                _position++;
            }
            if (_position >= _expression.Length)
            {
                throw Fail("chaine non fermee");
            }
            var value = _expression.Substring(start, _position - start);
            _position++;
            return value;
        }

        private decimal ReadNumber()
        {
            var start = _position;
            while (_position < _expression.Length
                   && (char.IsDigit(_expression[_position]) || _expression[_position] == '.'))
            {
                _position++;
            }
            if (!decimal.TryParse(_expression.Substring(start, _position - start), NumberStyles.Number,
                CultureInfo.InvariantCulture, out var value))
            {
                throw Fail($"nombre invalide '{_expression.Substring(start, _position - start)}'");
            }
            return value;
        }

        private List<string> ReadMemberPath()
        {
            var segments = new List<string>();
            while (true)
            {
                var start = _position;
                while (_position < _expression.Length
                       && (char.IsLetterOrDigit(_expression[_position]) || _expression[_position] == '_'))
                {
                    _position++;
                }
                if (_position == start)
                {
                    throw Fail("identifiant attendu");
                }
                segments.Add(_expression.Substring(start, _position - start));
                if (_position < _expression.Length && _expression[_position] == '.')
                {
                    _position++;
                }
                else
                {
                    return segments;
                }
            }
        }

        private object ResolvePath(List<string> path, object context)
        {
            object current = context;
            foreach (var segment in path)
            {
                if (current == null)
                {
                    throw Fail($"membre '{segment}' resolu sur null (chemin '{string.Join(".", path)}')");
                }
                current = GetMember(current, segment, path);
            }
            return current;
        }

        private object GetMember(object target, string segment, List<string> path)
        {
            var type = target.GetType();
            foreach (var property in type.GetProperties(BindingFlags.Public | BindingFlags.Instance))
            {
                if (property.GetIndexParameters().Length == 0
                    && string.Equals(property.Name, segment, StringComparison.OrdinalIgnoreCase))
                {
                    return property.GetValue(target);
                }
            }
            foreach (var field in type.GetFields(BindingFlags.Public | BindingFlags.Instance))
            {
                if (string.Equals(field.Name, segment, StringComparison.OrdinalIgnoreCase))
                {
                    return field.GetValue(target);
                }
            }
            throw Fail($"membre '{segment}' introuvable sur {type.Name} (chemin '{string.Join(".", path)}')");
        }

        private string ReadComparisonOperator()
        {
            SkipWhitespace();
            foreach (var op in new[] { "<=", ">=", "==", "!=", "<", ">" })
            {
                if (TryConsumeOperator(op))
                {
                    return op;
                }
            }
            return null;
        }

        private bool PeekOperator(string op)
        {
            SkipWhitespace();
            return _position + op.Length <= _expression.Length
                   && _expression.Substring(_position, op.Length) == op;
        }

        private bool TryConsumeOperator(string op)
        {
            if (!PeekOperator(op))
            {
                return false;
            }
            _position += op.Length;
            return true;
        }

        private void SkipWhitespace()
        {
            while (_position < _expression.Length && char.IsWhiteSpace(_expression[_position]))
            {
                _position++;
            }
        }

        private static decimal ToDecimal(object value)
        {
            if (value is decimal decimalValue)
            {
                return decimalValue;
            }
            if (value is int || value is long || value is short || value is byte
                || value is double || value is float || value is uint || value is ulong)
            {
                return Convert.ToDecimal(value, CultureInfo.InvariantCulture);
            }
            throw new InvalidOperationException(string.Format(
                CultureInfo.InvariantCulture,
                "SimpleExpression : operande de type {0} inattendu dans un calcul numerique", value?.GetType().Name ?? "null"));
        }

        private static bool ToBoolean(object value)
        {
            if (value is bool boolValue)
            {
                return boolValue;
            }
            throw new InvalidOperationException(string.Format(
                CultureInfo.InvariantCulture,
                "SimpleExpression : operande de type {0} inattendu dans une operation logique", value?.GetType().Name ?? "null"));
        }

        private static object AsKind(object value, Type type)
        {
            return Convert.ChangeType(value, type, CultureInfo.InvariantCulture);
        }

        private InvalidOperationException Fail(string message)
        {
            return new InvalidOperationException(
                $"SimpleExpression : {message} (expression : '{_expression}', position {_position})");
        }
    }
}
