using System.ComponentModel;
using System.Reflection;
using MyIA.AI.ComponentModel.PropertyEditor;
using Xunit;

namespace MyIA.AI.Shared.Tests;

/// <summary>
/// Battery for the A3-T2a payload layer of the PropertyEditor attribute vocabulary
/// (EPIC #7265, pépite #19088): the attributes that carry editor bindings — data source,
/// paths and file filters, value/text fields, user controls, collection editor,
/// multi-selector and orientation — plus the AttributeUsage fidelity against the VB source.
/// The contracts, the behavior-bearing types and the category/marker attributes live in
/// the sibling tranche and are covered by <c>PropertyEditorCoreAttributesTests</c>.
/// </summary>
public class PropertyEditorPayloadAttributesTests
{
    private sealed class Decorated
    {
        [DataSource("src")]
        [EnableExports(true)]
        [FileExtensions("png,jpg")]
        [OnDemand(true)]
        [Path("/var/data")]
        [TextField("Title")]
        [UserControl("~/controls/Editor.ascx")]
        [ValueField("Id", TypeCode = TypeCode.Int32)]
        [MultiSelectorType(MultiSelectionType.CheckBoxes)]
        [Orientation(Orientation.Vertical)]
        [CollectionEditor(true, false, true, true, 25, CollectionDisplayStyle.List, true, 500, "Name", true)]
        public string? Sample { get; set; }

        public string? Bare { get; set; }
    }

    // --- attributs à charge utile ---

    [Fact]
    public void PayloadAttributes_RoundTripTheirValues()
    {
        var property = typeof(Decorated).GetProperty(nameof(Decorated.Sample))!;

        Assert.Equal("src", property.GetCustomAttribute<DataSourceAttribute>()!.DataSource);
        Assert.True(property.GetCustomAttribute<EnableExportsAttribute>()!.Enabled);
        Assert.Equal("png,jpg", property.GetCustomAttribute<FileExtensionsAttribute>()!.Extensions);
        Assert.True(property.GetCustomAttribute<OnDemandAttribute>()!.Enabled);
        Assert.Equal("/var/data", property.GetCustomAttribute<PathAttribute>()!.Path);
        Assert.Equal("Title", property.GetCustomAttribute<TextFieldAttribute>()!.TextField);
        Assert.Equal("~/controls/Editor.ascx", property.GetCustomAttribute<UserControlAttribute>()!.ControlPath);
        Assert.Equal("Id", property.GetCustomAttribute<ValueFieldAttribute>()!.ValueField);
        Assert.Equal(MultiSelectionType.CheckBoxes, property.GetCustomAttribute<MultiSelectorTypeAttribute>()!.SelectionType);
        Assert.Equal(Orientation.Vertical, property.GetCustomAttribute<OrientationAttribute>()!.Orientation);
    }

    [Fact]
    public void EnableExports_ParameterlessCtor_LeavesEnabledFalse()
        => Assert.False(new EnableExportsAttribute().Enabled);

    [Fact]
    public void OnDemand_ParameterlessCtor_LeavesEnabledFalse()
        => Assert.False(new OnDemandAttribute().Enabled);

    [Fact]
    public void ValueField_TypeCode_DefaultsToEmpty()
        => Assert.Equal(TypeCode.Empty, new ValueFieldAttribute("v").TypeCode);

    // --- CollectionEditor ---

    [Fact]
    public void CollectionEditor_Defaults()
    {
        var attribute = new CollectionEditorAttribute();
        Assert.False(attribute.NoDeletion);
        Assert.False(attribute.NoAdd);
        Assert.False(attribute.ShowAddItem);
        Assert.True(attribute.Ordered);
        Assert.True(attribute.Paged);
        Assert.Equal(30, attribute.PageSize);
        Assert.Equal(CollectionDisplayStyle.Accordion, attribute.DisplayStyle);
        Assert.False(attribute.EnableExport);
        Assert.Equal(0, attribute.MaxItemNb);
        Assert.Equal(string.Empty, attribute.PagerDisplayFieldName);
        Assert.False(attribute.ItemsReadOnly);
    }

    [Fact]
    public void CollectionEditor_FiveArgCtor_SetsTheFiveOptionsOnly()
    {
        var attribute = new CollectionEditorAttribute(true, false, true, true, 25);
        Assert.True(attribute.NoAdd);
        Assert.False(attribute.ShowAddItem);
        Assert.True(attribute.Ordered);
        Assert.True(attribute.Paged);
        Assert.Equal(25, attribute.PageSize);
        Assert.Equal(CollectionDisplayStyle.Accordion, attribute.DisplayStyle);
    }

    [Fact]
    public void CollectionEditor_ChainedCtors_AddOneOptionEach()
    {
        var withStyle = new CollectionEditorAttribute(true, true, false, false, 10, CollectionDisplayStyle.List);
        Assert.Equal(CollectionDisplayStyle.List, withStyle.DisplayStyle);
        Assert.False(withStyle.EnableExport);

        var withExport = new CollectionEditorAttribute(true, true, false, false, 10, CollectionDisplayStyle.List, true);
        Assert.True(withExport.EnableExport);
        Assert.Equal(0, withExport.MaxItemNb);

        var withMax = new CollectionEditorAttribute(true, true, false, false, 10, CollectionDisplayStyle.List, true, 500);
        Assert.Equal(500, withMax.MaxItemNb);
        Assert.Equal(string.Empty, withMax.PagerDisplayFieldName);

        var withPager = new CollectionEditorAttribute(true, true, false, false, 10, CollectionDisplayStyle.List, true, 500, "Name");
        Assert.Equal("Name", withPager.PagerDisplayFieldName);
        Assert.False(withPager.ItemsReadOnly);

        var full = new CollectionEditorAttribute(true, true, false, false, 10, CollectionDisplayStyle.List, true, 500, "Name", true);
        Assert.True(full.ItemsReadOnly);
        Assert.Equal(500, full.MaxItemNb);
        Assert.Equal("Name", full.PagerDisplayFieldName);
    }

    [Fact]
    public void CollectionEditor_LegacyTwoArgCtor_KeptForSourceFidelity()
    {
#pragma warning disable CS0618 // deliberate: the obsolete ctor is part of the ported surface
        var attribute = new CollectionEditorAttribute(true, false);
#pragma warning restore CS0618
        Assert.True(attribute.ShowAddItem);
        Assert.False(attribute.Ordered);
        // The legacy ctor never set NoAdd (VB behaved the same).
        Assert.False(attribute.NoAdd);
    }

    [Fact]
    public void MultiSelectorType_CarriesTheSelectionStyle()
        => Assert.Equal(MultiSelectionType.ListBox, new MultiSelectorTypeAttribute(MultiSelectionType.ListBox).SelectionType);

    // --- AttributeUsage : fidélité au source VB ---

    [Theory]
    [InlineData(typeof(EnableExportsAttribute))]
    [InlineData(typeof(FileExtensionsAttribute))]
    [InlineData(typeof(MultiSelectorTypeAttribute))]
    [InlineData(typeof(CollectionEditorAttribute))]
    public void AttributesWithoutUsageInSource_DeclareNoneInMetadata(Type attributeType)
    {
        // The runtime synthesizes an AttributeUsageAttribute(All) for any attribute class
        // that declares none, so the presence of the attribute object proves nothing — the
        // fidelity check reads the metadata rows instead.
        Assert.DoesNotContain(
            attributeType.GetCustomAttributesData(),
            data => data.AttributeType == typeof(AttributeUsageAttribute));
        Assert.Equal(
            AttributeTargets.All,
            attributeType.GetCustomAttribute<AttributeUsageAttribute>()!.ValidOn);
    }

    [Theory]
    [InlineData(typeof(OnDemandAttribute))]
    [InlineData(typeof(DataSourceAttribute))]
    [InlineData(typeof(PathAttribute))]
    [InlineData(typeof(TextFieldAttribute))]
    [InlineData(typeof(UserControlAttribute))]
    [InlineData(typeof(ValueFieldAttribute))]
    public void PropertyScopedAttributes_RestrictToProperty(Type attributeType)
        => Assert.Equal(AttributeTargets.Property, attributeType.GetCustomAttribute<AttributeUsageAttribute>()!.ValidOn);
}
