using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Globalization;
using System.IO;
using System.Linq;
using System.Linq.Dynamic.Core;
using System.Linq.Dynamic.Core.CustomTypeProviders;
using System.Linq.Expressions;
using System.Reflection;
using System.Text.RegularExpressions;
using System.Web;
using Utf8Json.Formatters;

namespace MyIA.Trading.Converter
{
    public static class Extensions
    {

        public static List<Trade> Skip(this List<Trade> input, double ratio)
        {
            if (ratio<=0)
            {
                return input;
            }
            var objRandom = new FastRandom((int)DateTime.Now.Ticks);
            var toReturn = new List<Trade>();
            foreach (var objTrade in input)
            {
                if (objRandom.NextDouble() > ratio)
                {
                    toReturn.Add(objTrade);
                }
            }
            return toReturn;
        }

        

        public static List<Trade> GetRange(this List<Trade> input, DateTime start, DateTime end)
        {
            var startUnix = start.ToUnixTime();
            var endUnix = end.ToUnixTime();
            var toReturn = new List<Trade>((int)Math.DivRem(endUnix - startUnix, input.Last().UnixTime - input.First().UnixTime, out _) * input.Count);
            foreach (var objTrade in input)
            {
                if (objTrade.UnixTime > endUnix)
                {
                    break;
                }
                if (objTrade.UnixTime >= startUnix)
                {
                    toReturn.Add(objTrade);
                }
            }
            return toReturn;
        }



       

        public static long ToUnixTime(this DateTime objDate)
        {
            return ((DateTimeOffset)objDate).ToUnixTimeSeconds();

        }

        public static String GetRawExtensionUpper(this string fileName)
        {
            return Path.GetExtension(fileName)?.TrimStart('.').ToUpperInvariant();

        }

        public static List<Tickbar> ToTickbars(this List<Trade> input, TimeSpan period, bool randomPeriodStart)
        {
            var toReturn = new List<Tickbar>();
            if (input.Count == 0)
            {
                return toReturn;
            }

            var firstTradeTime = input.First().Time;

            var startPeriod = firstTradeTime.GetPeriodStart(period);

            var startIdx = 0;
            if (randomPeriodStart)
            {
                var objRandom = new Random();
                var randomOffset = TimeSpan.FromTicks((long)(objRandom.NextDouble() * period.Ticks));
                startPeriod = startPeriod + randomOffset;
                startIdx = input.FindIndex(x => x.Time >= startPeriod);
            }
            var currentTarget = startPeriod.Add(period);
            var currentTickTrades = new List<Trade>();
            for (var index = startIdx; index < input.Count; index++)
            {
                var objTrade = input[index];
                if (objTrade.Time > currentTarget)
                {
                    var tickBarDate = currentTarget.Subtract(period);
                    var currentTickBar = (currentTickTrades.ToTickbar(tickBarDate));
                    toReturn.Add(currentTickBar);
                    currentTickTrades.Clear();
                    currentTarget = objTrade.Time.GetPeriodStart(period).Add(period);
                }

                currentTickTrades.Add(objTrade);
            }

            return toReturn;
        }

        private static DateTime GetPeriodStart(this DateTime firstTradeTime, TimeSpan period )
        {
            DateTime startPeriod;

            if (period == TimeSpan.FromDays(1))
            {
                startPeriod = new DateTime(firstTradeTime.Year, firstTradeTime.Month, firstTradeTime.Day);
            }
            else if (period == TimeSpan.FromHours(1))
            {
                startPeriod = new DateTime(firstTradeTime.Year, firstTradeTime.Month, firstTradeTime.Day, firstTradeTime.Hour,
                    0, 0);
            }
            else if (period == TimeSpan.FromMinutes(1))
            {
                startPeriod = new DateTime(firstTradeTime.Year, firstTradeTime.Month, firstTradeTime.Day, firstTradeTime.Hour,
                    firstTradeTime.Minute, 0);
            }
            else if (period == TimeSpan.FromSeconds(1))
            {
                startPeriod = new DateTime(firstTradeTime.Year, firstTradeTime.Month, firstTradeTime.Day, firstTradeTime.Hour,
                    firstTradeTime.Minute, firstTradeTime.Second);
            }
            else
            {
                // fallback to previous logic or throw exception
                startPeriod = firstTradeTime;
            }

            return startPeriod;
        }

        public static Tickbar ToTickbar(this List<Trade> input, DateTime dateTime)
        {
            if (input.Count == 0)
            {
                return null;
            }

            var toReturn = new Tickbar
            {
                DateTime = dateTime,
                Open = input.First().Price,
                High = decimal.MinValue,
                Low = decimal.MaxValue,
                Close = input.Last().Price
            };
            foreach (var objTrade in input)
            {
                if (toReturn.High < objTrade.Price)
                {
                    toReturn.High = objTrade.Price;
                }
                if (toReturn.Low > objTrade.Price)
                {
                    toReturn.Low = objTrade.Price;
                }
                toReturn.Volume += objTrade.Amount;
            }
            return toReturn;
        }


        private static readonly Regex s_interpolateRegex = new(@"{(\D.+?)}", RegexOptions.Compiled);

        private static ConcurrentDictionary<string, Delegate> s_cachedInterpolationLinqExpressions = new();

        /// <summary>
        /// Most advanced interpolation that uses DynamicLinq to parse and compile a lambda expression at runtime.
        /// </summary>
        /// <remarks>
        /// Warning: Please be careful when using this feature as it can be a security risk if the input is not sanitized.
        /// Note that this is mitigated because templating capabilities only apply to their own level in a hierarchy of nested templates, they won't affect the inner template nor user inputs.
        /// </remarks>
        public static string Interpolate(this string value, Dictionary<string, object> context)
        {
            return s_interpolateRegex.Replace(value,
                match =>
                {
                    var matchToken = match.Groups[1].Value;
                    var key = $"{value}/{matchToken}";
                    if (!s_cachedInterpolationLinqExpressions.TryGetValue(key, out var tokenDelegate))
                    {
                        var parameters = new List<ParameterExpression>(context.Count);
                        foreach (var contextObject in context)
                        {
                            var p = Expression.Parameter(contextObject.Value.GetType(), contextObject.Key);
                            parameters.Add(p);
                        }

                        ParsingConfig config = new();
                        config.CustomTypeProvider = new CustomDynamicTypeProvider(context, config.CustomTypeProvider);

                        var e = System.Linq.Dynamic.Core.DynamicExpressionParser.ParseLambda(config, parameters.ToArray(), null, matchToken);
                        tokenDelegate = e.Compile();
                        s_cachedInterpolationLinqExpressions[key] = tokenDelegate;
                    }

                    return (tokenDelegate.DynamicInvoke(context.Values.ToArray()) ?? "").ToString();
                });
        }


        private sealed class CustomDynamicTypeProvider : IDynamicLinkCustomTypeProvider
        {
            private readonly Dictionary<string, object> _context;

            public CustomDynamicTypeProvider(Dictionary<string, object> context, IDynamicLinkCustomTypeProvider dynamicLinkCustomTypeProvider)
            {
                this._context = context;
                this.DefaultProvider = dynamicLinkCustomTypeProvider;
            }

            public IDynamicLinkCustomTypeProvider DefaultProvider { get; set; }

            public HashSet<Type> GetCustomTypes()
            {
                HashSet<Type> types = this.DefaultProvider.GetCustomTypes();
                types.Add(typeof(string));
                types.Add(typeof(Regex));
                types.Add(typeof(RegexOptions));
                types.Add(typeof(CultureInfo));
                types.Add(typeof(HttpUtility));
                types.Add(typeof(Enumerable));
                foreach (var contextObject in this._context)
                {
                    types.Add(contextObject.Value.GetType());
                }

                return types;
            }

            public Dictionary<Type, List<MethodInfo>> GetExtensionMethods()
            {
                return this.DefaultProvider.GetExtensionMethods();
            }

            public Type? ResolveType(string typeName)
            {
                return this.DefaultProvider.ResolveType(typeName);
            }

            public Type? ResolveTypeBySimpleName(string simpleTypeName)
            {
                return this.DefaultProvider.ResolveTypeBySimpleName(simpleTypeName);
            }
        }


    }

   


}
