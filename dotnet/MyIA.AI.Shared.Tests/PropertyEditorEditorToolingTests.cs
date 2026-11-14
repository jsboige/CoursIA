using System.ComponentModel;
using System.Reflection;
using MyIA.AI.ComponentModel.PropertyEditor;
using Xunit;

namespace MyIA.AI.Shared.Tests;

/// <summary>
/// Battery for the A3-T2b PropertyEditor editor tooling (EPIC #7265, pépite #19088):
/// single-editor-mode attributes, inner editor bindings (Inner/Key/Value), and the
/// selector configuration surface (SelectorAttribute, SelectorInfo,
/// ProvidersSelectorAttribute) against the measured VB source.
/// </summary>
public class PropertyEditorEditorToolingTests
{
    private sealed class SampleEditor
    {
    }

    private sealed class SampleAttributeProvider : IAttributesProvider
    {
        public IEnumerable<Attribute> GetAttributes() => new Attribute[] { new ReadOnlyAttribute(true) };
    }

    private sealed class Decorated
    {
        [EditOnly]
        public string? EditOnlyProp { get; set; }

        [ViewOnly]
        public string? ViewOnlyProp { get; set; }

        [SingleEditorMode(PropertyEditorMode.View)]
        public string? ExplicitMode { get; set; }

        [InnerEditor("My.Editors.Sample, Lib")]
        public string? InnerByname { get; set; }

        [InnerEditor(typeof(SampleEditor), typeof(SampleAttributeProvider))]
        public string? InnerByTypeAndProvider { get; set; }

        [KeyEditor("My.Editors.KeyEditor, Lib")]
        public string? KeyByname { get; set; }

        [ValueEditor(typeof(SampleEditor))]
        public string? ValueByType { get; set; }

        [Selector("My.Selectors.Themes, Lib", "Title", "Id", true, true)]
        public string? SelectorByTypeName { get; set; }

        [Selector(typeof(SampleEditor), "Title", "Id", true, false, "(none)", "", true, false)]
        public string? SelectorByType { get; set; }

        [Selector("Title", "Id", false, true, "(none)", "-", true, false)]
        public string? SelectorByFields { get; set; }

        [Selector("Title", "Id", false, true, "(none)", "-", true, false, false)]
        public string? SelectorWithTextFlag { get; set; }

        [ProvidersSelector]
        public string? ProvidersDefault { get; set; }

        [ProvidersSelector("FriendlyName")]
        public string? ProvidersNamed { get; set; }

        public string? Bare { get; set; }
    }

    private static T Get<T>(string propertyName)
        where T : Attribute
    {
        var prop = typeof(Decorated).GetProperty(propertyName, BindingFlags.Public | BindingFlags.Instance);
        Assert.NotNull(prop);
        return Assert.IsType<T>(prop!.GetCustomAttribute(typeof(T)));
    }

    // --- SingleEditorMode family -------------------------------------------------

    [Fact]
    public void SingleEditorMode_DefaultConstructor_LeavesDefaultMode()
    {
        var attr = new SingleEditorModeAttribute();
        Assert.Equal(default(PropertyEditorMode), attr.EditorMode);
    }

    [Fact]
    public void SingleEditorMode_ExplicitConstructor_SetsMode()
    {
        var attr = new SingleEditorModeAttribute(PropertyEditorMode.View);
        Assert.Equal(PropertyEditorMode.View, attr.EditorMode);
    }

    [Fact]
    public void EditOnly_BindsEditMode()
    {
        Assert.Equal(PropertyEditorMode.Edit, Get<EditOnlyAttribute>("EditOnlyProp").EditorMode);
    }

    [Fact]
    public void ViewOnly_BindsViewMode()
    {
        Assert.Equal(PropertyEditorMode.View, Get<ViewOnlyAttribute>("ViewOnlyProp").EditorMode);
    }

    [Theory]
    [InlineData(nameof(Decorated.EditOnlyProp), typeof(EditOnlyAttribute))]
    [InlineData(nameof(Decorated.ViewOnlyProp), typeof(ViewOnlyAttribute))]
    [InlineData(nameof(Decorated.SelectorByTypeName), typeof(SelectorAttribute))]
    [InlineData(nameof(Decorated.ProvidersDefault), typeof(ProvidersSelectorAttribute))]
    [InlineData(nameof(Decorated.KeyByname), typeof(KeyEditorAttribute))]
    [InlineData(nameof(Decorated.ValueByType), typeof(ValueEditorAttribute))]
    public void AttributeUsage_IsProperty_AsInTheSource(string propertyName, Type attributeType)
    {
        var prop = typeof(Decorated).GetProperty(propertyName, BindingFlags.Public | BindingFlags.Instance);
        var usage = attributeType.GetCustomAttribute<AttributeUsageAttribute>();
        Assert.NotNull(usage);
        Assert.Equal(AttributeTargets.Property, usage!.ValidOn);
        Assert.NotNull(prop);
    }

    // --- Inner editor bindings ---------------------------------------------------

    [Fact]
    public void InnerEditor_ByTypeName_CarriesEditorBinding()
    {
        var attr = Get<InnerEditorAttribute>("InnerByname");
        var editor = attr.GetAttributes(typeof(string)).OfType<EditorAttribute>().Single();
        Assert.StartsWith("My.Editors.Sample, Lib", editor.EditorTypeName, StringComparison.Ordinal);
    }

    [Fact]
    public void InnerEditor_ByTypeAndProvider_CarriesQualifiedNameAndProviderAttributes()
    {
        var attr = Get<InnerEditorAttribute>("InnerByTypeAndProvider");
        var aggregate = attr.GetAttributes(typeof(string));
        Assert.Contains(aggregate, a => a is EditorAttribute e && e.EditorTypeName.StartsWith(
            typeof(SampleEditor).AssemblyQualifiedName!, StringComparison.Ordinal));
        Assert.Contains(aggregate, a => a is ReadOnlyAttribute r && r.IsReadOnly);
    }

    [Fact]
    public void KeyEditor_TargetsTheKeyMember()
    {
        var attr = Get<KeyEditorAttribute>("KeyByname");
        Assert.Equal("Key", attr.PropertyName);
        Assert.Contains(attr.GetAttributes(typeof(string)), a => a is EditorAttribute);
    }

    [Fact]
    public void ValueEditor_ByType_TargetsTheValueMemberWithFullName()
    {
        var attr = Get<ValueEditorAttribute>("ValueByType");
        Assert.Equal("Value", attr.PropertyName);
        var editor = attr.GetAttributes(typeof(string)).OfType<EditorAttribute>().Single();
        // The VB source stored editorType.FullName; EditorAttribute normalizes the stored
        // name for nested types, so the assertion pins namespace and type name without
        // over-specifying the serialized separator.
        Assert.StartsWith(typeof(SampleEditor).Namespace!, editor.EditorTypeName, StringComparison.Ordinal);
        Assert.Contains(nameof(SampleEditor), editor.EditorTypeName, StringComparison.Ordinal);
    }

    // --- Selector family ---------------------------------------------------------

    [Fact]
    public void Selector_FiveArguments_SetsTheFiveFields()
    {
        var info = Get<SelectorAttribute>("SelectorByTypeName").SelectorInfo;
        Assert.Equal("My.Selectors.Themes, Lib", info.SelectorTypeName);
        Assert.Equal("Title", info.DataTextField);
        Assert.Equal("Id", info.DataValueField);
        Assert.True(info.IsExclusive);
        Assert.True(info.InsertNullItem);
        Assert.Equal("---", info.NullItemText);
    }

    [Fact]
    public void Selector_ByType_StoresAssemblyQualifiedName()
    {
        var info = Get<SelectorAttribute>("SelectorByType").SelectorInfo;
        Assert.Equal(typeof(SampleEditor).AssemblyQualifiedName, info.SelectorTypeName);
        Assert.Equal("(none)", info.NullItemText);
        Assert.Equal(string.Empty, info.NullItemValue);
        Assert.True(info.LocalizeItems);
        Assert.False(info.LocalizeNull);
    }

    [Fact]
    public void Selector_ByDataFields_KeepsISelectorMode()
    {
        var info = Get<SelectorAttribute>("SelectorByFields").SelectorInfo;
        // The VB source re-asserts the default explicitly for the dataField-based
        // constructors: the options come from the property's own ISelector.
        Assert.True(info.IsIselector);
        Assert.Equal(string.Empty, info.SelectorTypeName);
        Assert.Equal("-", info.NullItemValue);
    }

    [Fact]
    public void Selector_WithTextFlag_HonorsTheFlagParameter()
    {
        // The VB source assigned a hard-coded true here, ignoring its parameter.
        var info = Get<SelectorAttribute>("SelectorWithTextFlag").SelectorInfo;
        Assert.False(info.LocalizeText);
    }

    [Fact]
    public void SelectorInfo_FieldDefaults_MatchTheSource()
    {
        var info = new SelectorInfo();
        Assert.True(info.IsIselector);
        Assert.Equal("---", info.NullItemText);
        Assert.False(info.IsExclusive);
        Assert.False(info.InsertNullItem);
        Assert.False(info.LocalizeItems);
        Assert.False(info.LocalizeText);
        Assert.False(info.LocalizeNull);
    }

    [Fact]
    public void ProvidersSelector_Default_UsesNameForBothFields()
    {
        var info = Get<ProvidersSelectorAttribute>("ProvidersDefault").SelectorInfo;
        Assert.Equal("Name", info.DataTextField);
        Assert.Equal("Name", info.DataValueField);
        Assert.False(info.IsExclusive);
        Assert.False(info.InsertNullItem);
        Assert.True(info.IsIselector);
    }

    [Fact]
    public void ProvidersSelector_Named_UsesTheNameForBothFields()
    {
        var info = Get<ProvidersSelectorAttribute>("ProvidersNamed").SelectorInfo;
        Assert.Equal("FriendlyName", info.DataTextField);
        Assert.Equal("FriendlyName", info.DataValueField);
    }
}
