// Copyright (c) 2026 CoursIA — port verbatim from Argumentum under LGPL-3.0 + AGPL-3.0
// See NOTICE in this directory for full attribution.
//
// CoursIA-side addition: the upstream Argumentum.AssetConverter.Logger class is
// an internal utility (in the same assembly as the rest of Argumentum) — it is
// not a public NuGet package, so a verbatim port cannot keep the unqualified
// `Logger.LogProblem(...)` reference. This local interface is the smallest
// surface that lets us preserve every call site 1:1 (every LogProblem call
// becomes `_logger.LogProblem(...)` against a private field initialised to
// `NullLegacyLogger.Instance` by default).

namespace CoursIA.SymbolicAI.Argument_Analysis.AssetConverter.Ontology
{
    /// <summary>
    /// Minimal logger interface that mirrors the upstream
    /// `Argumentum.AssetConverter.Logger.LogProblem(string)` static method.
    /// </summary>
    public interface ILegacyLogger
    {
        void LogProblem(string message);
    }

    /// <summary>
    /// No-op implementation. Default logger used by the port when no other
    /// logger has been supplied — keeps the upstream behaviour
    /// (Argumentum.AssetConverter.Logger is silent in production paths).
    /// </summary>
    public sealed class NullLegacyLogger : ILegacyLogger
    {
        public static readonly NullLegacyLogger Instance = new NullLegacyLogger();

        public void LogProblem(string message)
        {
            // Intentionally empty — see file header rationale.
        }
    }
}
