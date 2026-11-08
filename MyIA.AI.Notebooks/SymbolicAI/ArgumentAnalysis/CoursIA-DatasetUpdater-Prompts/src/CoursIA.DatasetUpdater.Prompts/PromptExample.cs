// Ported from Argumentum/Argumentum, file Generation/Converters/Argumentum.AssetConverter/DatasetUpdater/PromptExample.cs
// Original commit: ac33f607a4889d8a982093c413804ed25bef3dc0 (EPIC #4960 tranche C, 2026-07-03)
// Original author: jsboige
// Upstream license: LGPL-3.0 OR AGPL-3.0 (network use). See NOTICE in this directory.
//
// This file is free software; you can redistribute it and/or modify it under the
// terms of the GNU Lesser General Public License as published by the Free Software
// Foundation; either version 3 of the License, or (at your option) any later
// version. See <https://www.gnu.org/licenses/lgpl-3.0.html>.
//
// Modifications from upstream: namespace moved from `Argumentum.AssetConverter`
// to `CoursIA.SymbolicAI.Argument_Analysis.AssetConverter.DatasetUpdater` (LGPL
// v3 §5 modification log). No other changes — the lazy file-read cache is
// preserved verbatim, byte-for-byte.

using System.IO;

namespace CoursIA.SymbolicAI.Argument_Analysis.AssetConverter.DatasetUpdater;

public class PromptExample
{
	private string _userPrompt;
	public string UserPromptPath { get; set; }

	public string AssistantAnswerPath { get; set; }

	public string UserPrompt
	{
		get
		{
			if (_userPrompt == null)
			{
				_userPrompt = File.ReadAllText(UserPromptPath);
			}
			return _userPrompt;
		}
	}

	private string _assistantAnswer;

	public string AssistantAnswer
	{
		get
		{
			if (_assistantAnswer == null)
			{
				_assistantAnswer = File.ReadAllText(AssistantAnswerPath);
			}
			return _assistantAnswer;
		}
	}

}