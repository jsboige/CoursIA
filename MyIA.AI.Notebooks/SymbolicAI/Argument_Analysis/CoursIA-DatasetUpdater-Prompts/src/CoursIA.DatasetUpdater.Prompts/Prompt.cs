// Ported from Argumentum/Argumentum, file Generation/Converters/Argumentum.AssetConverter/DatasetConverter/Prompt.cs
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
//   - OpenAI SDK stripped: the lazy `_openAIClient` / `_chatClient` fields,
//     the `Send(CancellationToken, Action<string>)` async dispatch, and the
//     reflection-based `CallFunction(string, string)` helper are all removed.
//   - `FunctionToolDef` replaced by the data-only `FunctionDescriptor` record
//     (Name / Description / ParametersJson), keeping the same triple of fields
//     without the SDK-specific `ToChatTool()` factory.
//   - All preserved POCO fields (Model, ApiKey, BaseUrl, MaxOutputTokens,
//     SystemPrompt, UserPrompt, DialogPrompts, Functions, FunctionName,
//     Tokenizer) are kept verbatim. Property defaults match upstream
//     (Model = "gpt-4.1-mini", others = empty list / null / "").
// Justification: see NOTICE §3 — I/O orchestration is consumer-side concern.

using System.Collections.Generic;

namespace CoursIA.SymbolicAI.Argument_Analysis.AssetConverter.DatasetUpdater;

/// <summary>
/// Verbatim port of the upstream <c>Argumentum.AssetConverter.Prompt</c> POCO surface:
/// the request template (system + user + dialog examples) and the function-calling
/// descriptors that drive LLM tool-use.
///
/// The upstream <c>Send(CancellationToken, Action&lt;string&gt;)</c> method is NOT
/// ported: it instantiates an <c>OpenAI.OpenAIClient</c> + <c>ChatClient</c> lazy,
/// binds <c>ChatCompletionOptions</c> and dispatches <c>CompleteChatAsync</c> with
/// reflection-based <c>CallFunction</c> resolution. Those are I/O orchestration, not
/// data: the pedagogical value of the upstream class is the request shape (which the
/// POCO preserves verbatim), not the OpenAI SDK call. Consumers wire their own LLM
/// client (OpenAI, Azure OpenAI, Ollama, etc.) and read the POCO fields to build the
/// request payload.
///
/// The upstream <c>FunctionToolDef</c> nested class is also stripped: it materialises
/// a <c>ChatTool.CreateFunctionTool</c> from the OpenAI SDK, which is again I/O glue
/// rather than data. Tool descriptors can be expressed as a (name, description,
/// parametersJson) triple — the same triple <see cref="FunctionDescriptor"/> below
/// preserves — and the consumer builds the SDK-specific tool from that.
/// </summary>
public class Prompt
{
	public string Model { get; set; } = "gpt-4.1-mini";

	public string ApiKey { get; set; } = "";

	public string BaseUrl { get; set; }

	public int? MaxOutputTokens { get; set; }

	public string SystemPrompt { get; set; } = "";

	public List<PromptExample> DialogPrompts { get; set; } = new();

	public string UserPrompt { get; set; } = "";

	/// <summary>
	/// Optional token-counting callback. Wire to <c>TokenManager.TokenizerAction</c>
	/// to rate-limit prompt assembly before dispatch.
	/// </summary>
	public System.Action<string> Tokenizer { get; set; }

	public List<FunctionDescriptor> Functions { get; set; } = new();

	/// <summary>
	/// If set, instructs the LLM to invoke exactly this function (rather than letting
	/// the model choose). Mirrors the upstream <c>ChatToolChoice.CreateFunctionChoice</c>.
	/// </summary>
	public string FunctionName { get; set; }
}

/// <summary>
/// Tool-use descriptor. Mirrors the upstream <c>FunctionToolDef</c> data fields
/// (name + description + parameters JSON-schema) but drops the SDK-specific
/// <c>ToChatTool()</c> factory and the reflection-based <c>TargetObject</c> /
/// <c>MethodName</c> dispatch — both are I/O concerns the consumer handles.
/// </summary>
public class FunctionDescriptor
{
	public string Name { get; set; }
	public string Description { get; set; }
	public string ParametersJson { get; set; }
}