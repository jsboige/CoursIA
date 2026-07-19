using System;
using System.Diagnostics;
using System.Globalization;
using System.IO;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using CsvHelper.Configuration;
using Utf8Json;
using Utf8Json.Formatters;
using Utf8Json.Resolvers;
//using System.Text.Json;

namespace MyIA.Trading.Converter
{
    class Program
    {
        //static async Task Main(string[] args)
        static void Main(string[] args)
        {
            RunningTime.Start();

            static string ResolveFromFilename(string csvPath)
        {
            var name = Path.GetFileNameWithoutExtension(csvPath) ?? string.Empty;
            if (name.Contains("_hourly", StringComparison.OrdinalIgnoreCase) || name.Contains("hour", StringComparison.OrdinalIgnoreCase))
            {
                return "hourly";
            }
            return "daily";
        }

        // Mode demo E1 #7265 : `dotnet run -- ohlcv2lean <input.csv> <output.zip> [daily|hourly]`
            // Resolution arg optional : deduit du nom de fichier si absent.
            if (args.Length >= 1 && args[0] == "ohlcv2lean")
            {
                if (args.Length < 3)
                {
                    Console.Error.WriteLine("Usage : dotnet run -- ohlcv2lean <input.csv> <output.zip> [daily|hourly]");
                    Environment.Exit(1);
                }
                string resolution = args.Length >= 4 ? args[3].ToLowerInvariant() : ResolveFromFilename(args[1]);
                if (resolution != "daily" && resolution != "hourly")
                {
                    Console.Error.WriteLine($"Resolution '{resolution}' invalide. Valeurs : daily | hourly");
                    Environment.Exit(1);
                }
                int written = Demo.ConvertOhlcvCsvToLeanZip(args[1], args[2], resolution, Log);
                Console.WriteLine($"Wrote {written} tickbars to {args[2]} (Lean {resolution} format)");
                return;
            }

            // Mode legacy upstream : charge ConverterConfig.json et lance Process()
            var config = GetConfig();
            Log("Config Loaded");
            config.Process(Log);

            Console.WriteLine($"End > {RunningTime.Elapsed.TotalSeconds:##.#####}s");
            Console.WriteLine("Appuyez sur une touche pour fermer la fenêtre");
            Console.ReadKey();
        }


        static TradeConverter GetConfig()
        {

            var configFileName = Path.Combine(Environment.CurrentDirectory, "ConverterConfig.json");
            CompositeResolver.RegisterAndSetAsDefault(new IJsonFormatter[] { new TimeSpanFormatter() }, new IJsonFormatterResolver[] { StandardResolver.Default });
            if (!File.Exists(configFileName))
            {
                var newConfig = new TradeConverter();
                var strNewConfig = JsonSerializer.PrettyPrint(JsonSerializer.ToJsonString(newConfig));
                File.WriteAllText(configFileName, strNewConfig);
            }

            using var configStream = File.OpenRead(configFileName);
            var config = JsonSerializer.Deserialize<TradeConverter>(configStream);
            return config;
        }


        static System.Diagnostics.Stopwatch RunningTime = new Stopwatch();

        private static TimeSpan _currentElpased = TimeSpan.Zero;

        public static void Log(string message)
        {
            var totalElapsed = RunningTime.Elapsed;
            var stepElapsed = totalElapsed - _currentElpased;
            _currentElpased = totalElapsed;
            Console.WriteLine($"+{stepElapsed.TotalSeconds:##.#####}s> {message}");

        }


    }


}
