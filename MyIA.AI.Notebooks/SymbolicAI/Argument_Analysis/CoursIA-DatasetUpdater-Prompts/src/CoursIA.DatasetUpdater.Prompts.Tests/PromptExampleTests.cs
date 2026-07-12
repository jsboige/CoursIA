using FluentAssertions;
using Xunit;

namespace CoursIA.SymbolicAI.Argument_Analysis.AssetConverter.DatasetUpdater.Tests;

public class PromptExampleTests
{
	[Fact]
	public void PromptExample_ReadsUserPrompt_FromFile_OnFirstAccess()
	{
		var temp = System.IO.Path.GetTempFileName();
		try
		{
			System.IO.File.WriteAllText(temp, "What is the capital of France?");
			var example = new PromptExample { UserPromptPath = temp, AssistantAnswerPath = temp };

			example.UserPrompt.Should().Be("What is the capital of France?");
		}
		finally { System.IO.File.Delete(temp); }
	}

	[Fact]
	public void PromptExample_CachesUserPrompt_AcrossMultipleReads()
	{
		// Upstream pattern: a null _userPrompt guard reads the file only on first access,
		// then caches the result. The port preserves that lazy-cache contract.
		var temp = System.IO.Path.GetTempFileName();
		try
		{
			System.IO.File.WriteAllText(temp, "first read");
			var example = new PromptExample { UserPromptPath = temp, AssistantAnswerPath = temp };

			var firstRead = example.UserPrompt;
			System.IO.File.WriteAllText(temp, "second read (should be ignored by cache)");
			var secondRead = example.UserPrompt;

			firstRead.Should().Be("first read");
			secondRead.Should().Be("first read", "the lazy-cache must not re-read after first access");
		}
		finally { System.IO.File.Delete(temp); }
	}

	[Fact]
	public void PromptExample_ReadsAssistantAnswer_FromFile_OnFirstAccess()
	{
		var temp = System.IO.Path.GetTempFileName();
		try
		{
			System.IO.File.WriteAllText(temp, "Paris is the capital of France.");
			var example = new PromptExample { UserPromptPath = temp, AssistantAnswerPath = temp };

			example.AssistantAnswer.Should().Be("Paris is the capital of France.");
		}
		finally { System.IO.File.Delete(temp); }
	}
}