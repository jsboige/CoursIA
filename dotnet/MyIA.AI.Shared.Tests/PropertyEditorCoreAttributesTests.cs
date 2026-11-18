using System.ComponentModel;
using System.Reflection;
using MyIA.AI.ComponentModel.PropertyEditor;
using Xunit;

namespace MyIA.AI.Shared.Tests;

/// <summary>
/// Battery for the A3-T2a core layer of the PropertyEditor attribute vocabulary
/// (EPIC #7265, pépite #19088): the two contracts, the two behavior-bearing types
/// (ConditionalVisibleInfo, AttributeContainerAttribute), the extended-category model and
/// the placement/marker attributes, plus the AttributeUsage fidelity against the VB source.
/// The payload attributes that carry editor bindings (data source, paths, collections,
/// orientation) live in the sibling tranche and are covered by
/// <c>PropertyEditorPayloadAttributesTests</c>.
/// </summary>
public class PropertyEditorCoreAttributesTests
{
    [Flags]
    private enum SampleFlags
    {
        None = 0,
        Alpha = 1,
        Beta = 2,
    }

    private sealed class Decorated
    {
        [LineCount(4, AutoResize = true)]
        [Size(12)]
        [Width(320)]
        [PasswordMode]
        [NoFlag]
        [AutoErase]
        [AutoPostBack]
        [Ordered]
        [FieldStyle("100%", "30%", "70%")]
        [ExtendedCategory("Tab", "Section", 2)]
        public string? Sample { get; set; }

        public string? Bare { get; set; }
    }

    // --- attributs marqueurs et à charge utile ---

    [Fact]
    public void MarkerAttributes_AreReadableOnAProperty()
    {
        var property = typeof(Decorated).GetProperty(nameof(Decorated.Sample))!;
        Assert.NotNull(property.GetCustomAttribute<AutoEraseAttribute>());
        Assert.NotNull(property.GetCustomAttribute<AutoPostBackAttribute>());
        Assert.NotNull(property.GetCustomAttribute<NoFlagAttribute>());
        Assert.NotNull(property.GetCustomAttribute<PasswordModeAttribute>());
        Assert.NotNull(property.GetCustomAttribute<OrderedAttribute>());
    }

    [Fact]
    public void CoreAttributes_RoundTripTheirValues()
    {
        var property = typeof(Decorated).GetProperty(nameof(Decorated.Sample))!;

        var lineCount = property.GetCustomAttribute<LineCountAttribute>()!;
        Assert.Equal(4, lineCount.Lines);
        Assert.True(lineCount.AutoResize);
        Assert.Equal(12, property.GetCustomAttribute<SizeAttribute>()!.Size);
        Assert.Equal(320, property.GetCustomAttribute<WidthAttribute>()!.Width);
    }

    [Fact]
    public void LineCount_AutoResize_DefaultsToFalse()
        => Assert.False(new LineCountAttribute(3).AutoResize);

    [Fact]
    public void FieldStyle_ExposesTheThreeWidths()
    {
        var style = new FieldStyleAttribute("100%", "30%", "70%");
        Assert.Equal("100%", style.Width);
        Assert.Equal("30%", style.LabelWidth);
        Assert.Equal("70%", style.EditControlWidth);
    }

    // --- AttributeUsage : fidélité au source VB ---

    [Theory]
    [InlineData(typeof(LineCountAttribute))]
    [InlineData(typeof(OrderedAttribute))]
    [InlineData(typeof(ExtendedCategoryAttribute))]
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
    [InlineData(typeof(AutoEraseAttribute))]
    [InlineData(typeof(AutoPostBackAttribute))]
    [InlineData(typeof(NoFlagAttribute))]
    [InlineData(typeof(PasswordModeAttribute))]
    [InlineData(typeof(SizeAttribute))]
    [InlineData(typeof(WidthAttribute))]
    [InlineData(typeof(FieldStyleAttribute))]
    [InlineData(typeof(AttributeContainerAttribute))]
    public void PropertyScopedAttributes_RestrictToProperty(Type attributeType)
        => Assert.Equal(AttributeTargets.Property, attributeType.GetCustomAttribute<AttributeUsageAttribute>()!.ValidOn);

    [Fact]
    public void ConditionalVisible_RestrictsToPropertyAndMethod_AndRepeats()
    {
        var usage = typeof(ConditionalVisibleAttribute).GetCustomAttribute<AttributeUsageAttribute>()!;
        Assert.Equal(AttributeTargets.Property | AttributeTargets.Method, usage.ValidOn);
        Assert.True(usage.AllowMultiple);
    }

    // --- ExtendedCategory ---

    [Fact]
    public void ExtendedCategory_CtorArities_FillTheExpectedFields()
    {
        var byTab = new ExtendedCategory("T");
        Assert.Equal("T", byTab.TabName);
        Assert.Equal(string.Empty, byTab.SectionName);
        Assert.Equal(0, byTab.Column);

        var bySection = new ExtendedCategory("S", 3);
        Assert.Equal(string.Empty, bySection.TabName);
        Assert.Equal("S", bySection.SectionName);
        Assert.Equal(3, bySection.Column);

        var full = new ExtendedCategory("T", "S", 2);
        Assert.Equal("T", full.TabName);
        Assert.Equal("S", full.SectionName);
        Assert.Equal(2, full.Column);
        Assert.Null(full.Prefix);
    }

    private sealed class CategorySamples
    {
        [Category("FromStandardCategory")]
        [ExtendedCategory("Tab", "Section")]
        public string? Both { get; set; }

        [ExtendedCategory("OnlyTab")]
        public string? ExtendedOnly { get; set; }

        public string? Neither { get; set; }
    }

    [Fact]
    public void ExtendedCategory_FromMember_StandardCategoryWins()
    {
        var property = typeof(CategorySamples).GetProperty(nameof(CategorySamples.Both))!;
        var category = ExtendedCategory.FromMember(property);
        Assert.Equal("FromStandardCategory", category.SectionName);
    }

    [Fact]
    public void ExtendedCategory_FromMember_FallsBackToTheExtendedAttribute()
    {
        var property = typeof(CategorySamples).GetProperty(nameof(CategorySamples.ExtendedOnly))!;
        var category = ExtendedCategory.FromMember(property);
        Assert.Equal("OnlyTab", category.TabName);
    }

    [Fact]
    public void ExtendedCategory_FromMember_EmptyWhenUndeclared_ButPrefixIsAlwaysSet()
    {
        var property = typeof(CategorySamples).GetProperty(nameof(CategorySamples.Neither))!;
        var category = ExtendedCategory.FromMember(property);
        Assert.Equal(string.Empty, category.TabName);
        Assert.Equal(string.Empty, category.SectionName);
        Assert.Equal(nameof(CategorySamples), category.Prefix);
    }

    // --- ConditionalVisibleInfo ---

    [Fact]
    public void ConditionalVisible_DefaultPredicate_MapsBooleanTruth()
    {
        var info = new ConditionalVisibleInfo("Enabled", false, true);
        Assert.True(info.MatchValue!(true));
        Assert.False(info.MatchValue!(false));
        Assert.False(info.MatchValue!(null!));
        Assert.Equal("Enabled", info.MasterPropertyName);
        Assert.True(info.EnforceAutoPostBack);
    }

    [Fact]
    public void ConditionalVisible_DefaultPredicate_NegatesWhenAsked()
    {
        var info = new ConditionalVisibleInfo("Enabled", true, false);
        Assert.False(info.MatchValue!(true));
        Assert.True(info.MatchValue!(false));
    }

    [Fact]
    public void ConditionalVisible_DefaultPredicate_TreatsEmptyStringAsAbsent()
    {
        var info = new ConditionalVisibleInfo("Text", false, false);
        Assert.False(info.MatchValue!(string.Empty));
    }

    [Fact]
    public void ConditionalVisible_DefaultPredicate_ParsesStringBooleans()
    {
        // VB CType(value, Boolean) converts; the port uses Convert.ToBoolean for the same
        // semantics (a plain cast would throw on a string).
        var info = new ConditionalVisibleInfo("Flag", false, false);
        Assert.True(info.MatchValue!("True"));
        Assert.False(info.MatchValue!("False"));
    }

    [Fact]
    public void ConditionalVisible_MatchingValues_EqualityDecides()
    {
        var info = new ConditionalVisibleInfo("Mode", false, true, "A", "B");
        Assert.True(info.MatchValue!("A"));
        Assert.True(info.MatchValue!("B"));
        Assert.False(info.MatchValue!("C"));
    }

    [Fact]
    public void ConditionalVisible_MatchingValues_NegateInvertsBothOutcomes()
    {
        var info = new ConditionalVisibleInfo("Mode", true, true, "A");
        Assert.False(info.MatchValue!("A"));
        Assert.True(info.MatchValue!("C"));
    }

    [Fact]
    public void ConditionalVisible_MatchingValues_FlagsSubsetMatches()
    {
        var info = new ConditionalVisibleInfo("Flags", false, true, SampleFlags.Alpha);
        Assert.True(info.MatchValue!(SampleFlags.Alpha | SampleFlags.Beta));
        Assert.False(info.MatchValue!(SampleFlags.Beta));
    }

    [Fact]
    public void ConditionalVisible_MatchingValues_NullEntryDoesNotThrow()
    {
        // Deviation: VB objValue.Equals(value) threw on a null entry of the array.
        var info = new ConditionalVisibleInfo("Mode", false, true, new object?[] { null, "A" });
        Assert.True(info.MatchValue!("A"));
        Assert.False(info.MatchValue!("C"));
    }

    [Fact]
    public void ConditionalVisible_ExplicitPredicate_IsUsed()
    {
        var info = new ConditionalVisibleInfo("Score", false, true, o => (int)o! > 10);
        Assert.True(info.MatchValue!(11));
        Assert.False(info.MatchValue!(10));
    }

    [Fact]
    public void ConditionalVisible_SecondaryCtor_StoresTheSecondaryCondition()
    {
        // Deviation restored: the VB seven-argument ctor dropped the three secondary
        // arguments, leaving SecondaryPropertyName null and MatchSecondary inert.
        var info = new ConditionalVisibleInfo(true, "Master", false, "on", "Secondary", false, "yes");
        Assert.Equal("Master", info.MasterPropertyName);
        Assert.Equal("Secondary", info.SecondaryPropertyName);
        Assert.True(info.MatchValue!("on"));

        Assert.True(info.MatchSecondary("yes"));
        Assert.False(info.MatchSecondary("no"));
        Assert.False(info.MatchSecondary(null));
    }

    [Fact]
    public void ConditionalVisible_Secondary_MatchesNullAgainstNull()
    {
        var info = new ConditionalVisibleInfo(false, "M", false, "on", "S", false, null);
        Assert.True(info.MatchSecondary(null));
        Assert.False(info.MatchSecondary("x"));
    }

    [Fact]
    public void ConditionalVisible_Secondary_NegateInverts()
    {
        var info = new ConditionalVisibleInfo(false, "M", false, "on", "S", true, "yes");
        Assert.False(info.MatchSecondary("yes"));
        Assert.True(info.MatchSecondary("no"));
    }

    [Fact]
    public void ConditionalVisible_ParameterlessInfo_HasNullPredicate()
        => Assert.Null(new ConditionalVisibleInfo().MatchValue);

    private sealed class VisibilitySamples
    {
        [ConditionalVisible("Master")]
        [ConditionalVisible("Other", true, false, "A")]
        public string? Both { get; set; }

        public string? Neither { get; set; }
    }

    [Fact]
    public void ConditionalVisible_FromMember_ReadsEveryAttribute()
    {
        var property = typeof(VisibilitySamples).GetProperty(nameof(VisibilitySamples.Both))!;
        var infos = ConditionalVisibleInfo.FromMember(property);
        Assert.Equal(2, infos.Count);

        // Resolved by name: attribute metadata order is not part of the contract.
        var plain = Assert.Single(infos, info => info.MasterPropertyName == "Master");
        Assert.True(plain.MatchValue!(true));

        var negated = Assert.Single(infos, info => info.MasterPropertyName == "Other");
        Assert.False(negated.MatchValue!("A")); // negate=true, "A" is an accepted value
        Assert.True(negated.MatchValue!("B"));
    }

    [Fact]
    public void ConditionalVisible_FromMember_EmptyWhenNone()
        => Assert.Empty(ConditionalVisibleInfo.FromMember(
            typeof(VisibilitySamples).GetProperty(nameof(VisibilitySamples.Neither))!));

    [Fact]
    public void ConditionalVisible_Attribute_ShortCtors_DefaultEnforcePostBackTrue()
    {
        Assert.True(new ConditionalVisibleAttribute("M").Value.EnforceAutoPostBack);
        Assert.True(new ConditionalVisibleAttribute("M", true).Value.EnforceAutoPostBack);
        var explicitFalse = new ConditionalVisibleAttribute("M", false, false);
        Assert.False(explicitFalse.Value.EnforceAutoPostBack);
    }

    [Fact]
    public void ConditionalVisible_Attribute_ValueIsAssignable()
    {
        var attribute = new ConditionalVisibleAttribute("M", false, false);
        attribute.Value = new ConditionalVisibleInfo("Replaced", false, true);
        Assert.Equal("Replaced", attribute.Value.MasterPropertyName);
    }

    [Fact]
    public void ConditionalVisible_Attribute_FullCtor_ReachesTheSecondaryCondition()
    {
        var attribute = new ConditionalVisibleAttribute(false, "M", false, "on", "S", false, "yes");
        Assert.Equal("S", attribute.Value.SecondaryPropertyName);
        Assert.True(attribute.Value.MatchSecondary("yes"));
    }

    // --- AttributeContainerAttribute ---

    private sealed class StaticProvider : IAttributesProvider
    {
        public IEnumerable<Attribute> GetAttributes() => new Attribute[] { new DescriptionAttribute("static") };
    }

    private sealed class DynamicProvider : IDynamicAttributesProvider
    {
        public IEnumerable<Attribute> GetAttributes(Type valueType)
            => new Attribute[] { new DescriptionAttribute(valueType.Name) };
    }

    private sealed class NotAProvider
    {
    }

    private sealed class Container : AttributeContainerAttribute
    {
        public Container(Type providerType)
            : base(providerType)
            => AddAttribute(new CategoryAttribute("added"));
    }

    [Fact]
    public void AttributeContainer_StaticProvider_AttributesAreReturnedAndCached()
    {
        var container = new Container(typeof(StaticProvider));
        var first = container.GetProviderAttributes(typeof(int));
        var second = container.GetProviderAttributes(typeof(string));
        Assert.Same(first, second); // type-independent: cached
        Assert.Equal("static", Assert.IsType<DescriptionAttribute>(first[0]).Description);
    }

    [Fact]
    public void AttributeContainer_DynamicProvider_IsRecomputedPerValueType()
    {
        // Deviation: the VB cached the first result, so every later value type got the
        // attributes computed for the first one.
        var container = new Container(typeof(DynamicProvider));
        var forInt = container.GetProviderAttributes(typeof(int));
        var forString = container.GetProviderAttributes(typeof(string));
        Assert.Equal("Int32", Assert.IsType<DescriptionAttribute>(forInt[0]).Description);
        Assert.Equal("String", Assert.IsType<DescriptionAttribute>(forString[0]).Description);
    }

    [Fact]
    public void AttributeContainer_GetAttributes_MergesSubclassAndProvider()
    {
        var container = new Container(typeof(StaticProvider));
        var merged = container.GetAttributes(typeof(int));
        Assert.Equal(2, merged.Count);
        Assert.Equal("added", Assert.IsType<CategoryAttribute>(merged[0]).Category);
        Assert.Equal("static", Assert.IsType<DescriptionAttribute>(merged[1]).Description);
    }

    [Fact]
    public void AttributeContainer_WithoutProvider_ReturnsOnlyTheSubclassAttributes()
    {
        var container = new Container(null!);
        Assert.Empty(container.GetProviderAttributes(typeof(int)));
        Assert.Single(container.GetAttributes(typeof(int)));
    }

    [Fact]
    public void AttributeContainer_TypeImplementingNeitherInterface_ContributesNothing()
    {
        var container = new Container(typeof(NotAProvider));
        Assert.Empty(container.GetProviderAttributes(typeof(int)));
    }

    [Fact]
    public void AttributeContainer_CanBeAppliedToAProperty()
    {
        var usage = typeof(AttributeContainerAttribute).GetCustomAttribute<AttributeUsageAttribute>()!;
        Assert.Equal(AttributeTargets.Property, usage.ValidOn);
        // The protected parameterless ctor exists for subclassing (VB declared it Protected).
        Assert.NotNull(typeof(AttributeContainerAttribute).GetConstructor(
            BindingFlags.Instance | BindingFlags.NonPublic, null, Type.EmptyTypes, null));
    }

    [Fact]
    public void ProviderInterfaces_HaveTheExpectedShape()
    {
        Assert.Equal(typeof(IEnumerable<Attribute>), typeof(IAttributesProvider).GetMethod("GetAttributes")!.ReturnType);
        var dynamicMethod = typeof(IDynamicAttributesProvider).GetMethod("GetAttributes")!;
        Assert.Equal(typeof(IEnumerable<Attribute>), dynamicMethod.ReturnType);
        Assert.Equal(new[] { typeof(Type) }, dynamicMethod.GetParameters().Select(p => p.ParameterType).ToArray());
    }
}
