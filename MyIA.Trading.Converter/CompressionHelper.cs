using System;
using System.Collections.Generic;
using System.Configuration;
using System.IO;
using System.Linq;
using System.Reflection;
using SevenZip;
using SevenZipExtractor;
using SharpCompress.Common;
using SharpCompress.Readers;
using SharpCompress.Writers;

namespace MyIA.Trading.Converter
{

    public enum InputArchiveFormat
    {
        Undefined,
        SevenZip,
        Arj,
        BZip2,
        Cab,
        Chm,
        Compound,
        Cpio,
        Deb,
        GZip,
        Iso,
        Lzh,
        Lzma,
        Nsis,
        Rar,
        Rar5,
        Rpm,
        Split,
        Tar,
        Wim,
        Lzw,
        Zip,
        Udf,
        Xar,
        Mub,
        Hfs,
        Dmg,
        XZ,
        Mslz,
        Flv,
        Swf,
        PE,
        Elf,
        Msi,
        Vhd,
        SquashFS,
        Lzma86,
        Ppmd,
        TE,
        UEFIc,
        UEFIs,
        CramFS,
        APM,
        Swfc,
        Ntfs,
        Fat,
        Mbr,
        MachO,
        Brotli,
        Lz4,
        lizard,
        Lz5,
        Zstd,
        Flzma2,
        SevenZipAES,
        AES256CBC,
        RawSplitter,
        Lzip,
        Ext,
        Ar,
        Gpt,
        IHex,
        MsLZ,
        Coff,
        Te,
        Qcow,
        Hxs
    }

    public enum OutputArchiveFormat
    {
        SevenZip,
        Zip,
        GZip,
        BZip2,
        Tar,
        XZ,
    }

    public enum CompressionAlgorithm
    {
        Default,
        Copy,
        Deflate,
        Deflate64,
        BZip2,
        Lzma,
        Lzma2,
        Ppmd,
        Brotli,
        Lz4,
        Lizard,
        Lz5,
        Zstd,
        Flzma2,
        SevenZipAES,
        AES256CBC,
        //RawSplitter
    }


    public enum CompressionLibrary
    {
        SevenZipExtractor,
        SevenZipSharp,
        SharpCompress
    }

    public class CompressionConfig
    {
        public CompressionLibrary Library { get; set; }

        public CompressionLevel Level { get; set; }

        public OutputArchiveFormat DefaultOutputFormat { get; set; }

        public CompressionAlgorithm DefaultAlgorithm { get; set; }

    }

    public static class CompressionHelper
    {

        public static Stream DecompressSingleFile(this Stream entryStream, out string fileName, CompressionConfig config, InputArchiveFormat? format = null)
        {
            switch (config.Library)
            {
                case CompressionLibrary.SevenZipExtractor:
                    return entryStream.DecompressSingleFileSevenZipExtractor(out fileName, format);
                case CompressionLibrary.SevenZipSharp:
                    return entryStream.DecompressSingleFileSevenZipSharp(out fileName, format);
                case CompressionLibrary.SharpCompress:
                    return entryStream.DecompressSingleFileSharpCompress(out fileName);
                default:
                    throw new ArgumentOutOfRangeException(nameof(config.Library), config.Library, null);
            }

        }




        public static void CompressSingleFile(this Stream entryStream, Stream archiveFileStream, string innerFileName, CompressionConfig config, InputArchiveFormat format)
        {
            switch (config.Library)
            {
                case CompressionLibrary.SevenZipExtractor:
                    throw new ArgumentOutOfRangeException(nameof(config.Library), config.Library, "SevenZipExtractor only supports decompression");
                case CompressionLibrary.SevenZipSharp:
                    entryStream.CompressSingleFileSevenZipSharp(archiveFileStream, innerFileName, format, config);
                    break;
                case CompressionLibrary.SharpCompress:
                    entryStream.CompressSingleFileSharpCompress(archiveFileStream, innerFileName, format);
                    break;
                default:
                    throw new ArgumentOutOfRangeException(nameof(config.Library), config.Library, null);
            }
        }


        private static Stream DecompressSingleFileSharpCompress(this Stream entryStream, out string fileName)
        {
            fileName = string.Empty;
            using var reader = ReaderFactory.Open(entryStream);
            while (reader.MoveToNextEntry())
            {
                if (!reader.Entry.IsDirectory)
                {
                    fileName = reader.Entry.Key;
                    var exitStream = new MemoryStream((int)reader.Entry.Size);
                    reader.WriteEntryTo(exitStream);
                    exitStream.Position = 0;
                    return exitStream;
                }
            }

            return null;
        }

        private static Dictionary<string, SevenZipFormat> _sevenZipExtractorFormatDictionary = System.Enum.GetNames(typeof(SevenZipFormat))
            .ToDictionary(s => s, s => System.Enum.Parse<SevenZipFormat>(s), StringComparer.OrdinalIgnoreCase);

        private static Stream DecompressSingleFileSevenZipExtractor(this Stream entryStream, out string fileName, InputArchiveFormat? format = null)
        {
            fileName = string.Empty;
            SevenZipFormat? szFormat = null;
            if (format.HasValue)
            {
                if (_sevenZipExtractorFormatDictionary.TryGetValue(format.ToString()!, out var szFormatFound))
                {
                    // 7z has different GUID for Pre-RAR5 and RAR5, but they have both same extension (.rar)
                    // If it is [0x52 0x61 0x72 0x21 0x1A 0x07 0x01 0x00] then file is RAR5 otherwise RAR.
                    // https://www.rarlab.com/technote.htm
                    // We are unable to guess right format just by looking at extension and have to check signature
                    if (szFormatFound != SevenZipFormat.Rar)
                    {
                        szFormat = szFormatFound;
                    }
                }
                else
                {
                    szFormat = SevenZipFormat.SevenZip;
                }
            }
            using ArchiveFile archiveFile = new ArchiveFile(entryStream, szFormat);
            foreach (SevenZipExtractor.Entry entry in archiveFile.Entries)
            {
                if (!entry.IsFolder)
                {
                    // extract to stream
                    fileName = entry.FileName;
                    Stream exitStream;
                    if (entry.Size > int.MaxValue)
                    {
                        exitStream = new HugeMemoryStream();
                    }
                    else
                    {
                        exitStream = new MemoryStream((int)entry.Size);
                    }
                    entry.Extract(exitStream);
                    exitStream.Position = 0;
                    return exitStream;
                }
            }

            return null;
        }

        private static Dictionary<string, InArchiveFormat> _sevenZipSharpFormatDictionary = System.Enum.GetNames(typeof(InArchiveFormat))
            .ToDictionary(s => s, s => System.Enum.Parse<InArchiveFormat>(s), StringComparer.OrdinalIgnoreCase);

        private static Stream DecompressSingleFileSevenZipSharp(this Stream entryStream, out string fileName, InputArchiveFormat? format = null)
        {
            DetermineLibraryFilePath();
            InArchiveFormat inFormat = InArchiveFormat.SevenZip;
            if (format.HasValue)
            {
                if (!_sevenZipSharpFormatDictionary.TryGetValue(format.ToString()!, out inFormat))
                {
                    inFormat = InArchiveFormat.SevenZip;
                }
            }
            using var extractor = new SevenZip.SevenZipExtractor(entryStream, true, inFormat);
            var archiveFile = extractor.ArchiveFileData[0];
            fileName = archiveFile.FileName;
            Stream exitStream;
            if (archiveFile.Size > int.MaxValue)
            {
                exitStream = new HugeMemoryStream();
            }
            else
            {
                exitStream = new MemoryStream((int)archiveFile.Size);
            }

            extractor.ExtractFile(0, exitStream);
            exitStream.Position = 0;
            return exitStream;
        }

        private static void DetermineLibraryFilePath()
        {
            if (string.IsNullOrEmpty(ConfigurationManager.AppSettings["7zLocation"]))
                ConfigurationManager.AppSettings["7zLocation"] = Path.Combine(Path.GetDirectoryName(Assembly.GetExecutingAssembly().Location) ?? Environment.CurrentDirectory, Environment.Is64BitProcess ? "7z-x64.dll" : "7z-x86.dll");
        }

        private static void CompressSingleFileSharpCompress(this Stream entryStream, Stream archiveFileStream, string fileName, InputArchiveFormat format)
        {
            var objArchiveType = GetArchiveTypeFromSevenZipFormat(format);
            var objCompressionType = GetCompressionTypeFromSevenZipFormat(format);
            using var writer = WriterFactory.Open(archiveFileStream, objArchiveType, new WriterOptions(objCompressionType));
            writer.Write(fileName, entryStream);
        }

        private static void CompressSingleFileSevenZipSharp(this Stream entryStream, Stream archiveFileStream,
            string fileName, InputArchiveFormat format, CompressionConfig config)
        {
            DetermineLibraryFilePath();
            //bool enableLz4 = false;
            //if (format == ~SevenZipFormat.SevenZip)
            //{
            //    format = SevenZipFormat.SevenZip;
            //    enableLz4 = true;

            //}
            if (!Enum.TryParse<OutArchiveFormat>(format.ToString(), true, out var outArchiveFormat))
            {
                if (!Enum.TryParse<OutArchiveFormat>( config.DefaultOutputFormat.ToString(), true, out outArchiveFormat))
                {
                    outArchiveFormat = OutArchiveFormat.SevenZip;
                }
            }

            CompressionAlgorithm algorithm;
            if (!Enum.TryParse<CompressionAlgorithm>(format.ToString(), true, out algorithm))
            {
                algorithm = config.DefaultAlgorithm;
            }

            CompressionMethod objMethod;
            if (!Enum.TryParse<CompressionMethod>(algorithm.ToString(), true, out objMethod))
            {
                objMethod = CompressionMethod.Default;
            }

            var compressor = new SevenZipCompressor
            {
                DirectoryStructure = false, 
                ArchiveFormat = outArchiveFormat, 
                CompressionMethod = objMethod,
                CompressionLevel = config.Level, 
                DefaultItemName = fileName
            };
            switch (algorithm)
            {
                
                case CompressionAlgorithm.Brotli:
                    compressor.CustomParameters.Add("0", "brotli");
                    break;
                case CompressionAlgorithm.Lz4:
                    compressor.CustomParameters.Add("0", "lz4");
                    break;
                case CompressionAlgorithm.Lizard:
                    compressor.CustomParameters.Add("0", "lizard");
                    break;
                case CompressionAlgorithm.Lz5:
                    compressor.CustomParameters.Add("0", "lz5");
                    break;
                case CompressionAlgorithm.Zstd:
                    compressor.CustomParameters.Add("0", "zstd");
                    break;
                case CompressionAlgorithm.Flzma2:
                    compressor.CustomParameters.Add("0", "flzma2");
                    break;
                case CompressionAlgorithm.SevenZipAES:
                    compressor.CustomParameters.Add("0", "7zAES");
                    break;
                case CompressionAlgorithm.AES256CBC:
                    compressor.CustomParameters.Add("0", "aes256cbc");
                    break;
                //case CompressionAlgorithm.RawSplitter:
                //    compressor.CustomParameters.Add("0", "lz4");
                //    break;
                //compressor.CustomParameters.Add("mt", "on");
                //compressor.CustomParameters.Add("0", "bcj");
            }
            
            compressor.CompressStream(entryStream, archiveFileStream);
        }

        private static ArchiveType GetArchiveTypeFromSevenZipFormat(InputArchiveFormat format)
        {
            if (!ArchiveFormatMapping.TryGetValue(format, out var toReturn))
            {
                toReturn = ArchiveType.SevenZip;
            }

            return toReturn;
        }

        private static CompressionType GetCompressionTypeFromSevenZipFormat(InputArchiveFormat format)
        {
            if (!CompressionTypeMapping.TryGetValue(format, out var toReturn))
            {
                toReturn = CompressionType.None;
            }

            return toReturn;
        }

        public static bool IsCompressedExtension(this string fileExtension, out InputArchiveFormat format)
        {
            if (string.IsNullOrWhiteSpace(fileExtension))
            {
                format = InputArchiveFormat.Undefined;
                return false;
            }

            fileExtension = fileExtension.TrimStart('.').Trim().ToLowerInvariant();

           
            if (!ExtensionFormatMapping.TryGetValue(fileExtension, out format))
            {
                format = InputArchiveFormat.Undefined;
                return false;
            }

            format = ExtensionFormatMapping[fileExtension];
            return true;
        }


        private static readonly Dictionary<InputArchiveFormat, CompressionType> CompressionTypeMapping = new Dictionary<InputArchiveFormat, CompressionType>
        {
            {InputArchiveFormat.SevenZip, CompressionType.LZMA},
            {InputArchiveFormat.GZip, CompressionType.GZip},
            {InputArchiveFormat.Tar, CompressionType.None},
            {InputArchiveFormat.Rar, CompressionType.Rar},
            {InputArchiveFormat.Zip, CompressionType.Deflate},
            {InputArchiveFormat.Lzma, CompressionType.LZMA},
            {InputArchiveFormat.Lzh, CompressionType.LZip},
            {InputArchiveFormat.BZip2, CompressionType.BZip2},
            {InputArchiveFormat.Ppmd, CompressionType.PPMd},
            {InputArchiveFormat.XZ, CompressionType.Xz}
        };


        private static readonly Dictionary<InputArchiveFormat, ArchiveType> ArchiveFormatMapping = new Dictionary<InputArchiveFormat, ArchiveType>
        {
            {InputArchiveFormat.SevenZip, ArchiveType.SevenZip},
            {InputArchiveFormat.GZip, ArchiveType.GZip},
            {InputArchiveFormat.Tar, ArchiveType.Tar},
            {InputArchiveFormat.Rar, ArchiveType.Rar},
            {InputArchiveFormat.Zip, ArchiveType.Zip},
        };


        private static readonly Dictionary<string, InputArchiveFormat> ExtensionFormatMapping = new Dictionary<string, InputArchiveFormat>(StringComparer.OrdinalIgnoreCase)
        {
            {"apm", InputArchiveFormat.APM},
            {"ar", InputArchiveFormat.Ar},
            {"arj", InputArchiveFormat.Arj},
            {"brotli", InputArchiveFormat.Brotli},
            {"bz2", InputArchiveFormat.BZip2},
            {"bzip2", InputArchiveFormat.BZip2},
            {"cab", InputArchiveFormat.Cab},
            {"chm", InputArchiveFormat.Chm},
            {"obj", InputArchiveFormat.Coff},
            {"msi", InputArchiveFormat.Compound},
            {"msp", InputArchiveFormat.Compound},
            {"doc", InputArchiveFormat.Compound},
            {"xls", InputArchiveFormat.Compound},
            {"ppt", InputArchiveFormat.Compound},
            {"cpio", InputArchiveFormat.Cpio},
            {"cramfs", InputArchiveFormat.CramFS},
            {"deb", InputArchiveFormat.Deb},
            {"dmg", InputArchiveFormat.Dmg},
            {"elf", InputArchiveFormat.Elf},
            {"ext", InputArchiveFormat.Ext},
            {"ext1", InputArchiveFormat.Ext},
            {"ext2", InputArchiveFormat.Ext},
            {"ext3", InputArchiveFormat.Ext},
            {"ext4", InputArchiveFormat.Ext},
            {"fat", InputArchiveFormat.Fat},
            {"img", InputArchiveFormat.Fat},
            {"flv", InputArchiveFormat.Flv},
            {"flzma2", InputArchiveFormat.Flzma2},
            {"gpt", InputArchiveFormat.Gpt},
            {"gz", InputArchiveFormat.GZip},
            {"gzip", InputArchiveFormat.GZip},
            {"tgz", InputArchiveFormat.GZip},
            {"tgzip", InputArchiveFormat.GZip},
            {"hfs", InputArchiveFormat.Hfs},
            {"hfsx", InputArchiveFormat.Hfs},
            {"hxs", InputArchiveFormat.Hxs},
            {"ihex", InputArchiveFormat.IHex},
            {"iso", InputArchiveFormat.Iso},
            {"lizard", InputArchiveFormat.lizard},
            {"liz", InputArchiveFormat.lizard},
            {"tliz", InputArchiveFormat.lizard},
            {"lz4", InputArchiveFormat.Lz4},
            {"tlz4", InputArchiveFormat.Lz4},
            {"lz5", InputArchiveFormat.Lz5},
            {"tlz5", InputArchiveFormat.Lz5},
            {"lzh", InputArchiveFormat.Lzh},
            {"lz", InputArchiveFormat.Lzip},
            {"tlz", InputArchiveFormat.Lzip},
            {"lzma", InputArchiveFormat.Lzma},
            {"lzma86", InputArchiveFormat.Lzma86},
            {"z", InputArchiveFormat.Lzw},
            {"macho", InputArchiveFormat.MachO},
            {"mbr", InputArchiveFormat.Mbr},
            {"mslz", InputArchiveFormat.MsLZ},
            {"mub", InputArchiveFormat.Mub},
            {"nsis", InputArchiveFormat.Nsis},
            {"ntfs", InputArchiveFormat.Ntfs},
            {"dll", InputArchiveFormat.PE},
            {"exe", InputArchiveFormat.PE},
            {"sys", InputArchiveFormat.PE},
            {"pmd", InputArchiveFormat.Ppmd},
            {"qcow", InputArchiveFormat.Qcow},
            {"qcow2", InputArchiveFormat.Qcow},
            {"qcow2c", InputArchiveFormat.Qcow},
            {"rar", InputArchiveFormat.Rar},
            {"r00", InputArchiveFormat.Rar},
            {"rar5", InputArchiveFormat.Rar5},
            {"rpm", InputArchiveFormat.Rpm},
            {"001", ~InputArchiveFormat.Split},
            {"7z", InputArchiveFormat.SevenZip},
            {"Squashfs", InputArchiveFormat.SquashFS},
            {"swf", InputArchiveFormat.Swf},
            {"tar", InputArchiveFormat.Tar},
            {"te", InputArchiveFormat.Te},
            {"udf", InputArchiveFormat.Udf},
            {"vhd", InputArchiveFormat.Vhd},
            {"wim", InputArchiveFormat.Wim},
            {"xar", InputArchiveFormat.Xar},
            {"xz", InputArchiveFormat.XZ},
            {"zip", InputArchiveFormat.Zip},
            {"z01", InputArchiveFormat.Zip},
            {"zipx", InputArchiveFormat.Zip},
            {"jar", InputArchiveFormat.Zip},
            {"xpi", InputArchiveFormat.Zip},
            {"odt", InputArchiveFormat.Zip},
            {"ods", InputArchiveFormat.Zip},
            {"docx", InputArchiveFormat.Zip},
            {"xslx", InputArchiveFormat.Zip},
            {"epub", InputArchiveFormat.Zip},
            {"ipa", InputArchiveFormat.Zip},
            {"apk", InputArchiveFormat.Zip},
            {"appx", InputArchiveFormat.Zip},
            {"pptx", InputArchiveFormat.Zip},
            {"zstd", InputArchiveFormat.Zstd},

        };


    }
}
