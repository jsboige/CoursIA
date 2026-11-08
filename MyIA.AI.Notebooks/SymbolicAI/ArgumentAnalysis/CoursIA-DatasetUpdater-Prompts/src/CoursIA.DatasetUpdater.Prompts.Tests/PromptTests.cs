using FluentAssertions;
using Xunit;

namespace CoursIA.SymbolicAI.Argument_Analysis.AssetConverter.DatasetUpdater.Tests;

public class PromptTests
{
	[Fact]
	public void Prompt_DefaultModel_Is_Gpt41Mini()
	{
		// Mirrors the upstream Argumentum.AssetConverter.Prompt default:
		// Model = "gpt-4.1-mini"
		new Prompt().Model.Should().Be("gpt-4.1-mini");
	}

	[Fact]
	public void Prompt_DefaultApiKey_Is_EmptyString()
	{
		// ApiKey must NOT have a hardcoded fallback (secrets-hygiene rule:
		// never inline literals in .cs source). The upstream default is "".
		new Prompt().ApiKey.Should().BeEmpty();
	}

	[Fact]
	public void Prompt_DefaultDialogPrompts_Is_EmptyList()
	{
		new Prompt().DialogPrompts.Should().NotBeNull().And.BeEmpty();
	}

	[Fact]
	public void Prompt_DefaultFunctions_Is_EmptyList()
	{
		new Prompt().Functions.Should().NotBeNull().And.BeEmpty();
	}

	[Fact]
	public void Prompt_DefaultSystemPrompt_UserPrompt_Are_Empty()
	{
		var prompt = new Prompt();
		prompt.SystemPrompt.Should().BeEmpty();
		prompt.UserPrompt.Should().BeEmpty();
	}

	[Fact]
	public void Prompt_FunctionDescriptor_CarriesNameDescriptionParametersJson()
	{
		// Mirrors the upstream FunctionToolDef data fields (Name, Description, ParametersJson).
		// SDK-specific factory stripped (see NOTICE §3); consumer builds the SDK tool from the triple.
		var descriptor = new FunctionDescriptor
		{
			Name = "lookup_argument",
			Description = "Look up a known argument by ID in the corpus.",
			ParametersJson = "{\"type\":\"object\",\"properties\":{\"id\":{\"type\":\"string\"}}}"
		};

		descriptor.Name.Should().Be("lookup_argument");
		descriptor.Description.Should().Contain("Look up");
		descriptor.ParametersJson.Should().Contain("object");
	}

	[Fact]
	public void Prompt_Properties_AreMutable()
	{
		// Verbatim port preserves the upstream POCO pattern (auto-properties with
		// public getters/setters, no init-only restrictions). Tests can build
		// arbitrary configurations.
		var prompt = new Prompt
		{
			Model = "llama-3.3-70b",
			ApiKey = "test-key-from-env-var",
			BaseUrl = "https://api.example.com/v1",
			SystemPrompt = "You are a Socratic tutor.",
			UserPrompt = "Explain the Liar paradox.",
			MaxOutputTokens = 512,
			FunctionName = "lookup_argument"
		};

		prompt.Model.Should().Be("llama-3.3-70b");
		prompt.ApiKey.Should().Be("test-key-from-env-var");
		prompt.BaseUrl.Should().Be("https://api.example.com/v1");
		prompt.SystemPrompt.Should().Contain("Socratic");
		prompt.UserPrompt.Should().Contain("Liar");
		prompt.MaxOutputTokens.Should().Be(512);
		prompt.FunctionName.Should().Be("lookup_argument");
	}
}