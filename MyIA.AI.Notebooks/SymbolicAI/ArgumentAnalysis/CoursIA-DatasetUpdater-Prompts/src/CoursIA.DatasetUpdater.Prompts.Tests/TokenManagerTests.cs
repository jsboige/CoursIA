using FluentAssertions;
using Xunit;

namespace CoursIA.SymbolicAI.Argument_Analysis.AssetConverter.DatasetUpdater.Tests;

/// <summary>
/// Deterministic ITokenCounter test double — returns a caller-specified token count
/// so the rate-limit sliding window can be exercised without any real tokenizer.
/// </summary>
internal sealed class FixedTokenCounter : ITokenCounter
{
	private readonly int _tokensPerText;
	public FixedTokenCounter(int tokensPerText) { _tokensPerText = tokensPerText; }
	public int CountTokens(string text) => _tokensPerText;
}

public class TokenManagerTests
{
	[Fact]
	public void TokenManager_DefaultMillisecondsDelay_Is5000()
	{
		// Mirrors the upstream Argumentum.AssetConverter.TokenManager default:
		// MillisecondsDelay = 5000
		new TokenManager(maxTokensPerMinute: 1000).MillisecondsDelay.Should().Be(5000);
	}

	[Fact]
	public void TokenManager_DefaultCurrentMinuteTokenCount_IsZero_BeforeAnyTokenize()
	{
		var mgr = new TokenManager(maxTokensPerMinute: 1000);
		mgr.CurrentMinuteTokenCount.Should().Be(0);
		mgr.TotalMaxTokens.Should().Be(0);
	}

	[Fact]
	public void TokenManager_TokenizeAction_AccumulatesTotalTokens_AndCurrentMinute()
	{
		var mgr = new TokenManager(maxTokensPerMinute: 1000, counter: new FixedTokenCounter(tokensPerText: 10));

		mgr.TokenizerAction("hello world");
		mgr.TokenizerAction("another text");

		mgr.TotalMaxTokens.Should().Be(20);
		mgr.CurrentMinuteTokenCount.Should().Be(20);
	}

	[Fact]
	public void TokenManager_DefaultTokenizerAction_IsNotNull()
	{
		new TokenManager(maxTokensPerMinute: 1000).TokenizerAction.Should().NotBeNull();
	}

	[Fact]
	public void TokenManager_NullCounter_FallsBackToNoOpCounter()
	{
		// Mirrors the upstream `GptEncoding.GetEncodingForModel` fallback path:
		// when no model binding is available, encoding defaults to "cl100k_base".
		// In the ported version, a null counter falls back to NullTokenCounter
		// (every text tokenises to 0), so the manager is still safe to construct.
		var mgr = new TokenManager(maxTokensPerMinute: 1000, counter: null);
		mgr.TokenizerAction("any text");
		mgr.TotalMaxTokens.Should().Be(0);
		mgr.CurrentMinuteTokenCount.Should().Be(0);
	}

	[Fact]
	public void TokenManager_AcceptsCustomLegacyLogger_ForRateLimitWait_Logging()
	{
		// Wiring an ILegacyLogger must not throw. The actual wait path requires
		// hitting MaxTokensPerMinute which then polls; here we just verify the
		// logger reference is captured without crashing on construction.
		var logger = new RecordingLogger();
		var mgr = new TokenManager(maxTokensPerMinute: 1000, counter: null, logger: logger);
		mgr.Should().NotBeNull();
	}

	[Fact]
	public void NullLegacyLogger_Log_IsSilentNoOp()
	{
		// Documented contract: NullLegacyLogger.Log swallows its argument.
		var logger = new NullLegacyLogger();
		logger.Invoking(l => l.Log("anything")).Should().NotThrow();
	}
}

internal sealed class RecordingLogger : ILegacyLogger
{
	public System.Collections.Generic.List<string> Messages { get; } = new();
	public void Log(string message) => Messages.Add(message);
}