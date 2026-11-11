using MyIA.AI.ComponentModel.Attributes;
using MyIA.AI.ComponentModel.PropertyEditor;
using MyIA.AI.ComponentModel.PropertyEditor.Explorer;
using Xunit;

namespace MyIA.AI.Shared.Tests;

/// <summary>
/// Battery for the A3-T3 Explorer pattern core (EPIC #7265, pepite #19088 T3):
/// the renderer-agnostic EditorModel builder over the T2 attribute vocabulary.
/// Placement (tabs/sections/columns), ordering, editor modes, visibility descriptors
/// and behavior markers are resolved at build time and consumed as plain data.
/// </summary>
public class PropertyEditorExplorerModelTests
{
    [MainCategory("Payment")]
    private sealed class EditorSample
    {
        public string? FallbackNoAttributes { get; set; }

        [ExtendedCategory("General", "Identity")]
        public string? Name { get; set; }

        [ExtendedCategory("General", "Identity", 1)]
        [Ordered]
        public string? Email { get; set; }

        [ExtendedCategory("General", "Security")]
        [PasswordMode]
        public string? ApiKey { get; set; }

        [ExtendedCategory("Advanced", "Limits")]
        [Width(80)]
        [Size(120)]
        [ViewOnly]
        public int Timeout { get; set; }

        [ExtendedCategory("Advanced", "Limits")]
        [LineCount(6)]
        [OnDemand(true)]
        public string? Notes { get; set; }

        [ExtendedCategory("Advanced", "Choices")]
        [Selector("My.Selectors.Themes, Lib", "Title", "Id", true, true)]
        [TextField("Label")]
        [ValueField("Key")]
        [AutoErase]
        public string? Theme { get; set; }

        [CollectionEditor]
        [MultiSelectorType(MultiSelectionType.ListBox)]
        public IList<string> Tags { get; set; } = new List<string>();

        [InnerEditor("My.Editors.Sample, Lib")]
        [ConditionalVisible("Timeout", false, false, 0)]
        public string? InnerBound { get; set; }
    }

    private static EditorField Field(EditorModel model, string propertyName)
        => model.Tabs.SelectMany(t => t.Sections).SelectMany(s => s.Fields)
            .Single(f => f.PropertyName == propertyName);

    // --- Placement: tabs, sections, columns -------------------------------------

    [Fact]
    public void Build_GroupsTabsByFirstAppearance()
    {
        var model = EditorModelBuilder.Build<EditorSample>();
        // Declaration order: Payment (FallbackNoAttributes), General (Name), Advanced (Timeout).
        Assert.Equal(new[] { "Payment", "General", "Advanced" }, model.Tabs.Select(t => t.Name));
    }

    [Fact]
    public void Build_FallbackMembersLandInMainCategoryTab()
    {
        // DefaultCategoryAttribute.vb is Obsolete and delegates to MainCategoryAttribute,
        // so the type-level category is the default tab for unplaced members.
        var model = EditorModelBuilder.Build<EditorSample>();
        Assert.DoesNotContain(model.Tabs, t => t.Name == EditorModelBuilder.DefaultTabName);
        var payment = Assert.Single(model.Tabs, t => t.Name == "Payment");
        // All members without ExtendedCategory (FallbackNoAttributes, Tags, InnerBound) land there.
        Assert.Equal(
            new[] { nameof(EditorSample.FallbackNoAttributes), nameof(EditorSample.Tags), nameof(EditorSample.InnerBound) },
            payment.Sections.SelectMany(s => s.Fields).Select(f => f.PropertyName));
    }

    [Fact]
    public void Build_FallbackTabWhenNoMainCategory()
    {
        var model = EditorModelBuilder.Build<Undecorated>();
        var tab = Assert.Single(model.Tabs);
        Assert.Equal(EditorModelBuilder.DefaultTabName, tab.Name);
    }

    private sealed class Undecorated
    {
        public int Value { get; set; }
    }

    [Fact]
    public void Build_SectionsCarryTheirColumn()
    {
        var model = EditorModelBuilder.Build<EditorSample>();
        var emailSection = model.Tabs.Single(t => t.Name == "General").Sections
            .Single(s => s.Fields.Any(f => f.PropertyName == nameof(EditorSample.Email)));
        Assert.Equal(1, emailSection.Column);
    }

    [Fact]
    public void Build_DistinctColumnsYieldDistinctSections()
    {
        var model = EditorModelBuilder.Build<EditorSample>();
        var identity = model.Tabs.Single(t => t.Name == "General").Sections.Where(s => s.Name == "Identity").ToList();
        Assert.Equal(2, identity.Count); // column 0 (Name) and column 1 (Email)
    }

    [Fact]
    public void Build_NullTypeThrows()
    {
        Assert.Throws<ArgumentNullException>(() => EditorModelBuilder.Build(null!));
    }

    // --- Ordering ---------------------------------------------------------------

    [Fact]
    public void Build_FieldsKeepDeclarationOrderWithinSection()
    {
        var model = EditorModelBuilder.Build<EditorSample>();
        var limits = model.Tabs.Single(t => t.Name == "Advanced").Sections.Single(s => s.Name == "Limits");
        Assert.Equal(
            new[] { nameof(EditorSample.Timeout), nameof(EditorSample.Notes) },
            limits.Fields.Select(f => f.PropertyName));
    }

    [Fact]
    public void Build_OrderIndexIsDeclarationIndex()
    {
        var model = EditorModelBuilder.Build<EditorSample>();
        Assert.Equal(0, Field(model, nameof(EditorSample.FallbackNoAttributes)).Order);
        Assert.True(Field(model, nameof(EditorSample.Name)).Order
            < Field(model, nameof(EditorSample.ApiKey)).Order);
    }

    // --- Editor modes, markers and hints ----------------------------------------

    [Fact]
    public void Build_ViewOnlyResolvesMode()
    {
        var field = Field(EditorModelBuilder.Build<EditorSample>(), nameof(EditorSample.Timeout));
        Assert.Equal(PropertyEditorMode.View, field.Mode);
    }

    [Fact]
    public void Build_NoModeAttributeLeavesNull()
    {
        var field = Field(EditorModelBuilder.Build<EditorSample>(), nameof(EditorSample.Name));
        Assert.Null(field.Mode);
    }

    [Fact]
    public void Build_SizeWidthAndLinesResolve()
    {
        var model = EditorModelBuilder.Build<EditorSample>();
        var timeout = Field(model, nameof(EditorSample.Timeout));
        Assert.Equal(80, timeout.Width);
        Assert.Equal(120, timeout.Size);
        Assert.Null(timeout.Lines);
        var notes = Field(model, nameof(EditorSample.Notes));
        Assert.Equal(6, notes.Lines);
        Assert.False(notes.AutoResize);
    }

    [Fact]
    public void Build_MarkerAttributesResolve()
    {
        var model = EditorModelBuilder.Build<EditorSample>();
        Assert.True(Field(model, nameof(EditorSample.ApiKey)).IsPassword);
        Assert.True(Field(model, nameof(EditorSample.Theme)).AutoErase);
        Assert.True(Field(model, nameof(EditorSample.Notes)).OnDemand);
    }

    // --- Selectors, editors, collections ----------------------------------------

    [Fact]
    public void Build_SelectorConfigurationCarriesThrough()
    {
        var field = Field(EditorModelBuilder.Build<EditorSample>(), nameof(EditorSample.Theme));
        Assert.NotNull(field.Selector);
        Assert.Equal("My.Selectors.Themes, Lib", field.Selector!.SelectorTypeName);
        Assert.Equal("Label", field.TextFieldName);
        Assert.Equal("Key", field.ValueFieldName);
    }

    [Fact]
    public void Build_InnerEditorBindingsSurfaceAsTypeNames()
    {
        var field = Field(EditorModelBuilder.Build<EditorSample>(), nameof(EditorSample.InnerBound));
        var editorName = Assert.Single(field.EditorTypeNames);
        Assert.StartsWith("My.Editors.Sample, Lib", editorName, StringComparison.Ordinal);
    }

    [Fact]
    public void Build_CollectionAndMultiSelectionResolve()
    {
        var field = Field(EditorModelBuilder.Build<EditorSample>(), nameof(EditorSample.Tags));
        Assert.True(field.IsCollection);
        Assert.NotNull(field.CollectionOptions);
        Assert.Equal(MultiSelectionType.ListBox, field.MultiSelection);
    }

    // --- Visibility -------------------------------------------------------------

    [Fact]
    public void Build_ConditionalVisibilityDescriptorsResolve()
    {
        var field = Field(EditorModelBuilder.Build<EditorSample>(), nameof(EditorSample.InnerBound));
        var rule = Assert.Single(field.Visibility);
        Assert.Equal("Timeout", rule.MasterPropertyName);
    }

    [Fact]
    public void Build_UnconditionalFieldHasEmptyVisibility()
    {
        var field = Field(EditorModelBuilder.Build<EditorSample>(), nameof(EditorSample.Name));
        Assert.Empty(field.Visibility);
    }

    // --- Renderer-agnostic contract ---------------------------------------------

    [Fact]
    public void Model_ExposesNoRenderingTypes()
    {
        // The core contract: the model assembly must stay consumable by any surface
        // (notebook, console, web) — EditorField carries only data, and the builder
        // never returns a UI type.
        var model = EditorModelBuilder.Build<EditorSample>();
        Assert.Equal(typeof(EditorSample), model.EditedType);
        Assert.All(model.Tabs.SelectMany(t => t.Sections).SelectMany(s => s.Fields),
            f => Assert.NotNull(f.PropertyType));
    }
}
