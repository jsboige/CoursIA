using FluentAssertions;
using Xunit;

namespace CoursIA.SymbolicAI.Argument_Analysis.AssetConverter.DatasetUpdater.Tests;

public class DivisionModeTests
{
	[Fact]
	public void DivisionMode_HasTwoValues_SequentialChunks_And_PKHierarchicalChar()
	{
		// Mirrors the upstream Argumentum.AssetConverter.DivisionMode enum:
		// SequentialChunks (default chunk-by-chunk CSV split)
		// PKHierarchicalChar (split by primary-key prefix hierarchy)
		var values = System.Enum.GetValues<DivisionMode>();

		values.Should().HaveCount(2);
		values.Should().Contain(DivisionMode.SequentialChunks);
		values.Should().Contain(DivisionMode.PKHierarchicalChar);
	}

	[Fact]
	public void DivisionMode_DefaultUnderlyingType_Is_Int32()
	{
		// POCO surface preservation: upstream enum has no explicit underlying type,
		// so it defaults to int. Verbatim port must preserve that.
		System.Enum.GetUnderlyingType(typeof(DivisionMode)).Should().Be(typeof(int));
	}
}