// Ported from Argumentum/Argumentum, file Generation/Converters/Argumentum.AssetConverter/DatasetUpdater/TokenManager.cs
// Original commit: ac33f607a4889d8a982093c413804ed25bef3dc0 (EPIC #4960 tranche C, 2026-07-03)
// Original author: jsboige
// Upstream license: LGPL-3.0 OR AGPL-3.0 (network use). See NOTICE in this directory.
//
// This file is free software; you can redistribute it and/or modify it under the
// terms of the GNU Lesser General Public License as published by the Free Software
// Foundation; either version 3 of the License, or (at your option) any later
// version. See <https://www.gnu.org/licenses/lgpl-3.0.html>.
//
// Modifications from upstream (LGPL v3 §5 modification log):
//   - Namespace moved from `Argumentum.AssetConverter` to
//     `CoursIA.SymbolicAI.Argument_Analysis.AssetConverter.DatasetUpdater`.
//   - SharpToken dependency stripped: `GptEncoding.GetEncodingForModel(model)`
//     replaced by an abstract `ITokenCounter` interface (in this file).
//     Rate-limit algorithm preserved verbatim (concurrent timestamp queue,
//     sliding 1-minute window, throttle on MaxTokensPerMinute,
//     WaitForTokenAvailability polling).
//   - `Argumentum.Logger.Log(string)` static coupling replaced by an injectable
//     `ILegacyLogger` interface (defined alongside this file). A
//     `NullLegacyLogger` no-op default is provided for headless / batch contexts.
// Justification: see NOTICE §4-§5.

using System;
using System.Collections.Concurrent;
using System.Linq;
using System.Threading.Tasks;

namespace CoursIA.SymbolicAI.Argument_Analysis.AssetConverter.DatasetUpdater;

/// <summary>
/// Rate-limiting helper for LLM token consumption. Verbatim port of the upstream
/// <c>Argumentum.AssetConverter.TokenManager</c> (POCO surface + cleanup logic), with the
/// SharpToken encoding dependency stripped: the upstream <c>GptEncoding.GetEncodingForModel</c>
/// is replaced by an abstract <see cref="ITokenCounter"/> so the lib stays free of any
/// concrete tokenizer binding. Callers wire whichever encoding matches their target model
/// (cl100k_base, o200k_base, etc.) and the rate-limiter continues to govern throughput
/// against the configured <see cref="MaxTokensPerMinute"/>.
/// </summary>
public class TokenManager
{
	private readonly ConcurrentQueue<(int tokenCount, DateTime timestamp)> tokenTimestamps;
	private readonly ITokenCounter _counter;
	private readonly ILegacyLogger _logger;

	public int MillisecondsDelay { get; set; } = 5000;
	public int MaxTokensPerMinute { get; set; }

	public int CurrentMinuteTokenCount
	{
		get
		{
			CleanupTokens();
			return tokenTimestamps.Sum(item => item.tokenCount);
		}
	}

	public int TotalMaxTokens { get; set; } = 0;

	/// <summary>
	/// Constructs a rate-limiter that delegates token counting to the supplied
	/// <paramref name="counter"/>. A null counter is treated as the no-op default
	/// (every text tokenises to 0, which makes the rate-limiter a pure throttle).
	/// </summary>
	public TokenManager(int maxTokensPerMinute, ITokenCounter counter = null, ILegacyLogger logger = null)
	{
		this.MaxTokensPerMinute = maxTokensPerMinute;
		this._counter = counter ?? NullTokenCounter.Instance;
		this._logger = logger ?? new NullLegacyLogger();
		tokenTimestamps = new ConcurrentQueue<(int, DateTime)>();
	}

	public Action<string> TokenizerAction => Tokenize;

	private void Tokenize(string text)
	{
		var tokenCount = _counter.CountTokens(text);
		TotalMaxTokens += tokenCount;
		tokenTimestamps.Enqueue((tokenCount, DateTime.UtcNow));
		CleanupTokens();
	}

	public void WaitForTokenAvailability()
	{
		while (CurrentMinuteTokenCount >= MaxTokensPerMinute)
		{
			CleanupTokens();
			_logger.Log($"Waiting for token availability. Current token count: {CurrentMinuteTokenCount}");
			Task.Delay(MillisecondsDelay).Wait();
		}
		_logger.Log($"Tokens over last minute: {CurrentMinuteTokenCount}");
	}

	private void CleanupTokens()
	{
		while (tokenTimestamps.TryPeek(out var item) && (DateTime.UtcNow - item.timestamp).TotalMinutes >= 1)
		{
			tokenTimestamps.TryDequeue(out _);
		}
	}
}

/// <summary>
/// Abstraction over a tokenizer. Implementations wrap a concrete model encoding
/// (SharpToken cl100k_base, o200k_base, tiktoken, etc.) without forcing the lib
/// to take a hard dependency on a particular package.
/// </summary>
public interface ITokenCounter
{
	int CountTokens(string text);
}

internal sealed class NullTokenCounter : ITokenCounter
{
	public static readonly NullTokenCounter Instance = new NullTokenCounter();
	public int CountTokens(string text) => 0;
}