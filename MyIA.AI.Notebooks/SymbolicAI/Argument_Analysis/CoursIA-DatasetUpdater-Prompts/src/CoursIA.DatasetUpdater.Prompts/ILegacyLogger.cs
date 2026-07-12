// ILegacyLogger and NullLegacyLogger are NEW files (LGPL v3 §5 modification log:
// added files, no upstream equivalent). They replace the upstream
// `Argumentum.Logger.Log(string)` static helper, which the ported TokenManager
// depended on. Mirrors the same pattern used in `CoursIA.OwlAdapter` (tranche B
// of EPIC #4960, MERGED via PR #5167) for consistency across the Argumentum port.

namespace CoursIA.SymbolicAI.Argument_Analysis.AssetConverter.DatasetUpdater;

/// <summary>
/// Local abstraction for the upstream <c>Argumentum.Logger.Log(string)</c> static helper,
/// preserved verbatim from the original Argumentum.AssetConverter surface so the port remains
/// a drop-in replacement at call sites that emitted progress / diagnostic lines.
/// </summary>
public interface ILegacyLogger
{
	void Log(string message);
}

/// <summary>
/// Default no-op implementation. Mirrors the upstream behaviour of <c>Argumentum.Logger.Log</c>
/// when no logger has been wired (silent). Use this in tests and in headless / batch contexts
/// where progress output is undesirable.
/// </summary>
public sealed class NullLegacyLogger : ILegacyLogger
{
	public void Log(string message) { /* intentional no-op */ }
}