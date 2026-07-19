// Demo.cs — démo E1 #7265 : conversion CSV-local OHLCV -> format Lean daily/hourly zip
// via TradeConverter.SaveTradingData<Tickbar> (API publique verbatim upstream).
//
// Usage :
//   dotnet run --project MyIA.AI.Shared/MyIA.Trading.Converter -- ohlcv2lean <input.csv> <output.zip> [daily|hourly]
// Resolution arg optionnel : deduit du nom de fichier si absent (`_hourly` -> hourly, sinon daily).
//
// Format CSV OHLCV attendu (header ligne 1, colonnes 0..5) :
//   Date,Open,High,Low,Close,Volume[,...]
// Les colonnes supplémentaires (spread, bid/ask, ...) sont ignorees.
//
// Format Lean officiel (cible) : CSV non-header, format identique daily/hourly :
//   yyyyMMdd HH:mm,Open,High,Low,Close,Volume
//   (format 6 col OHLCV produit par la demo ; le format complet 10 col avec bid/ask
//    est une extension future — voir README.md).
// References :
//   daily  -> partner-course-quant-trading/lean-workspace/data/cfd/oanda/daily/xauusd.zip
//   hourly -> partner-course-quant-trading/lean-workspace/data/cfd/oanda/hour/xauusd.zip

using System;
using System.Collections.Generic;
using System.Globalization;
using System.IO;
using System.Linq;
using SevenZip;

namespace MyIA.Trading.Converter
{
    public static class Demo
    {
        /// <summary>
        /// Convertit un CSV OHLCV local (Date,Open,High,Low,Close,Volume[,...]) en
        /// Tickbar zip au format Lean daily/hourly via TradeConverter.SaveTradingData<Tickbar>.
        /// Le format `yyyyMMdd HH:mm` est identique pour daily et hourly ; le seul changement
        /// porte sur l'étiquetage du fichier produit (le zip Lean daily contient `<sym>.csv`
        /// non-header, et le dossier de destination diffère côté Lean — non géré ici, le zip
        /// reste nommé via le `outputZipPath` fourni).
        /// </summary>
        /// <param name="resolution">"daily" ou "hourly" — utilisé uniquement pour le log final et
        /// pour adapter la détection d'en-tête si la première ligne diffère (réservé usage futur).</param>
        /// <returns>Nombre de tickbars écrits dans le zip de sortie.</returns>
        public static int ConvertOhlcvCsvToLeanZip(
            string inputCsvPath,
            string outputZipPath,
            string resolution,
            Action<string> logger = null)
        {
            logger ??= Console.WriteLine;

            if (!File.Exists(inputCsvPath))
            {
                throw new FileNotFoundException($"Input CSV introuvable : {inputCsvPath}", inputCsvPath);
            }
            if (resolution != "daily" && resolution != "hourly")
            {
                throw new ArgumentException($"Resolution '{resolution}' invalide. Valeurs : daily | hourly", nameof(resolution));
            }

            // 1. Parse CSV OHLCV -> List<Tickbar>
            var tickbars = LoadOhlcvCsv(inputCsvPath, logger);
            logger($"Loaded {tickbars.Count} tickbars from {inputCsvPath}");

            if (tickbars.Count == 0)
            {
                logger("WARN : 0 tickbar charge, zip vide non produit.");
                return 0;
            }

            // 2. Sérialisation config : Lean format = DateTimeFormat="yyyyMMdd HH:mm"
            //    Identique pour daily et hourly (les zips de référence daily et hourly
            //    de xauusd utilisent le même format ; la différence daily/hourly est dans
            //    le NOM DU DOSSIER côté Lean : data/cfd/oanda/daily/ vs data/cfd/oanda/hour/).
            //    IncludeHeader=false (Lean CSV sans header).
            //    Compression=SharpCompress + ZIP = format Lean (.zip contenant .csv).
            //    SevenZipSharp necessite 7z.dll natif runtime charge correctement ;
            //    SharpCompress est managed pure, plus portable pour demo.
            var config = new SerializationConfig
            {
                Culture = "en-US",
                Csv = CsvSerializationType.FlatFiles,
                IncludeHeader = false,
                DateTimeFormat = "yyyyMMdd HH:mm",
                Compression = new CompressionConfig
                {
                    Library = CompressionLibrary.SharpCompress,
                    Level = CompressionLevel.Normal
                }
            };

            // 3. Sauvegarde Tickbar zip via API publique TradeConverter.
            var outputDir = Path.GetDirectoryName(Path.GetFullPath(outputZipPath));
            if (!string.IsNullOrEmpty(outputDir) && !Directory.Exists(outputDir))
            {
                Directory.CreateDirectory(outputDir);
            }

            TradeConverter.SaveTradingData<Tickbar>(tickbars, outputZipPath, "", logger, config);
            logger($"Wrote {tickbars.Count} tickbars to {outputZipPath} (Lean {resolution} format)");

            return tickbars.Count;
        }

        /// <summary>
        /// Parse CSV OHLCV (Date,Open,High,Low,Close,Volume[,...]).
        /// Colonnes 0..5 obligatoires, colonnes 6+ ignorees (spread, bid/ask, ...).
        /// Format Date : yyyy-MM-dd (ISO 8601, format interne CoursIA).
        /// </summary>
        private static List<Tickbar> LoadOhlcvCsv(string path, Action<string> logger)
        {
            var result = new List<Tickbar>();
            var ci = CultureInfo.InvariantCulture;
            int lineNo = 0;
            int skipped = 0;

            using var reader = new StreamReader(path);
            string line;
            while ((line = reader.ReadLine()) != null)
            {
                lineNo++;
                if (string.IsNullOrWhiteSpace(line)) continue;

                var parts = line.Split(',');
                if (parts.Length < 6)
                {
                    skipped++;
                    continue;
                }

                // Skip header (premiere ligne si elle commence par "Date" ou n'est pas numerique)
                if (lineNo == 1 && !double.TryParse(parts[1], NumberStyles.Any, ci, out _))
                {
                    continue;
                }

                if (!DateTime.TryParse(parts[0], ci, DateTimeStyles.None, out var date))
                {
                    skipped++;
                    continue;
                }
                if (!decimal.TryParse(parts[1], NumberStyles.Any, ci, out var open) ||
                    !decimal.TryParse(parts[2], NumberStyles.Any, ci, out var high) ||
                    !decimal.TryParse(parts[3], NumberStyles.Any, ci, out var low) ||
                    !decimal.TryParse(parts[4], NumberStyles.Any, ci, out var close) ||
                    !decimal.TryParse(parts[5], NumberStyles.Any, ci, out var volume))
                {
                    skipped++;
                    continue;
                }

                result.Add(new Tickbar
                {
                    DateTime = date,
                    Open = open,
                    High = high,
                    Low = low,
                    Close = close,
                    Volume = volume
                });
            }

            if (skipped > 0)
            {
                logger($"WARN : {skipped} lignes skipped (format invalide ou < 6 colonnes)");
            }

            return result;
        }
    }
}
