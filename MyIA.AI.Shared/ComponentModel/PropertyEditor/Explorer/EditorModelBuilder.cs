using System.ComponentModel;
using System.Reflection;
using MyIA.AI.ComponentModel.Attributes;

namespace MyIA.AI.ComponentModel.PropertyEditor.Explorer;

/// <summary>
/// Builds an <see cref="EditorModel"/> from a type by reflecting over the T2 attribute
/// vocabulary — the renderer-agnostic core of the Explorer pattern (EPIC #7265, A3-T3).
/// </summary>
/// <remarks>
/// Placement semantics (modernized reading of the VB <c>AriciePropertyEditorControl</c>
/// category slotting, which the obsolete <c>DefaultCategoryAttribute</c> delegated to
/// <c>MainCategoryAttribute</c>): a member with <c>[ExtendedCategory]</c> lands in its
/// declared tab/section/column; a member without one lands in the type-level
/// <c>[MainCategory]</c> tab when present, else in "(General)". Tabs, sections and fields
/// keep first-appearance (declaration) order — the VB comparer
/// (<c>AriciePropertySortOrderComparer</c>) lived in the control layer and is deliberately
/// not ported; declaration order is the deterministic renderer-agnostic default.
/// </remarks>
public static class EditorModelBuilder
{
    /// <summary>Fallback tab name for members with no placement metadata at all.</summary>
    public const string DefaultTabName = "(General)";

    /// <summary>Builds the full tab/section/field model for <typeparamref name="T"/>.</summary>
    public static EditorModel Build<T>()
        => Build(typeof(T));

    /// <summary>Builds the full tab/section/field model for a type.</summary>
    public static EditorModel Build(Type editedType)
    {
        if (editedType is null)
        {
            throw new ArgumentNullException(nameof(editedType));
        }

        var mainCategory = editedType.GetCustomAttribute<MainCategoryAttribute>();
        var fallbackTab = mainCategory is null ? DefaultTabName : mainCategory.Name;

        var tabs = new Dictionary<string, List<PropertySection>>(StringComparer.Ordinal);
        var sectionFields = new Dictionary<PropertySection, List<EditorField>>(ReferenceEqualityComparer.Instance);
        var sectionKeys = new Dictionary<(string Tab, string Section, int Column), PropertySection>();

        var order = 0;
        foreach (var property in editedType.GetProperties(BindingFlags.Public | BindingFlags.Instance))
        {
            var field = BuildField(property, order++);
            var category = field.Category;
            var tabName = category is null ? fallbackTab
                : string.IsNullOrEmpty(category.TabName) ? fallbackTab
                : category.TabName;
            var sectionName = category?.SectionName ?? string.Empty;
            var column = category?.Column ?? 0;

            if (!tabs.TryGetValue(tabName, out var sections))
            {
                sections = new List<PropertySection>();
                tabs.Add(tabName, sections);
            }

            var key = (tabName, sectionName, column);
            if (!sectionKeys.TryGetValue(key, out var section))
            {
                section = new PropertySection(sectionName, column, Array.Empty<EditorField>());
                sectionKeys.Add(key, section);
                sections.Add(section);
                sectionFields.Add(section, new List<EditorField>());
            }

            sectionFields[section].Add(field);
        }

        var builtTabs = tabs.Select(pair => new PropertyTab(
            pair.Key,
            pair.Value.Select(s => new PropertySection(s.Name, s.Column, sectionFields[s])).ToList()))
            .ToList();
        return new EditorModel(editedType, builtTabs);
    }

    private static EditorField BuildField(PropertyInfo property, int order)
    {
        ExtendedCategory? category = property.GetCustomAttribute<ExtendedCategoryAttribute>()?.ExtendedCategory;

        PropertyEditorMode? mode = null;
        var single = property.GetCustomAttribute<SingleEditorModeAttribute>();
        if (single is not null)
        {
            mode = single.EditorMode;
        }

        var visibility = ConditionalVisibleInfo.FromMember(property) ?? new List<ConditionalVisibleInfo>();

        int? width = property.GetCustomAttribute<WidthAttribute>() is { } w ? w.Width : null;
        int? size = property.GetCustomAttribute<SizeAttribute>() is { } s ? s.Size : null;
        int? lines = null;
        bool? autoResize = null;
        if (property.GetCustomAttribute<LineCountAttribute>() is { } lc)
        {
            lines = lc.Lines;
            autoResize = lc.AutoResize;
        }

        var selector = property.GetCustomAttribute<SelectorAttribute>()?.SelectorInfo;
        var textFieldName = property.GetCustomAttribute<TextFieldAttribute>() is { } tf ? tf.TextField : null;
        var valueFieldName = property.GetCustomAttribute<ValueFieldAttribute>() is { } vf ? vf.ValueField : null;

        // [InnerEditor] aggregates standard EditorAttribute bindings; surface consumers
        // resolve the qualified editor type names without reflecting again.
        var editorTypeNames = property.GetCustomAttribute<InnerEditorAttribute>() is { } inner
            ? inner.GetAttributes(property.PropertyType)
                .OfType<EditorAttribute>()
                .Select(e => e.EditorTypeName)
                .Where(n => !string.IsNullOrEmpty(n))
                .ToList()
            : (IReadOnlyList<string>)Array.Empty<string>();

        var collectionOptions = property.GetCustomAttribute<CollectionEditorAttribute>();
        MultiSelectionType? multiSelection =
            property.GetCustomAttribute<MultiSelectorTypeAttribute>() is { } ms ? ms.SelectionType : null;

        return new EditorField(
            property.Name,
            property.PropertyType,
            order,
            property.GetCustomAttribute<OrderedAttribute>() is not null,
            category,
            mode,
            visibility,
            width,
            size,
            lines,
            autoResize,
            property.GetCustomAttribute<FieldStyleAttribute>(),
            selector,
            textFieldName,
            valueFieldName,
            editorTypeNames,
            collectionOptions is not null,
            collectionOptions,
            multiSelection,
            property.GetCustomAttribute<PasswordModeAttribute>() is not null,
            property.GetCustomAttribute<OnDemandAttribute>() is { } od ? od.Enabled : null,
            property.GetCustomAttribute<AutoEraseAttribute>() is not null,
            property.GetCustomAttribute<AutoPostBackAttribute>() is not null,
            property.GetCustomAttribute<NoFlagAttribute>() is not null);
    }
}
