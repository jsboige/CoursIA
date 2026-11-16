namespace MyIA.AI.ComponentModel.PropertyEditor.Explorer;

/// <summary>
/// Renderer-agnostic view model of an editable object: the tabs, sections and fields a
/// property-editor surface should render, derived purely from the T2 attribute vocabulary
/// (EPIC #7265, ancre A3-T3, design-gate tranchee : core agnostique + surface notebook).
/// </summary>
/// <remarks>
/// The model carries <b>no rendering types</b>: a console renderer, an HTML fragment for a
/// .NET Interactive notebook or a web grid are all consumers of the same instance. The VB
/// source expressed this contract through WebForms controls (<c>AriciePropertyEditorControl</c>,
/// <c>EditControls/*</c>); the port keeps only the metadata-driven placement and behavior facts
/// those controls read, which T2 already ported as attributes.
/// </remarks>
public class EditorModel
{
    /// <summary>Type the model was built from.</summary>
    public Type EditedType { get; }

    /// <summary>Tabs in first-appearance order (declaration order of the members).</summary>
    public IReadOnlyList<PropertyTab> Tabs { get; }

    public EditorModel(Type editedType, IReadOnlyList<PropertyTab> tabs)
    {
        EditedType = editedType;
        Tabs = tabs;
    }
}

/// <summary>Top-level grouping of the editor: one tab, holding ordered sections.</summary>
public class PropertyTab
{
    /// <summary>Tab name. Comes from <c>ExtendedCategory.TabName</c>, or the type-level
    /// <c>MainCategoryAttribute</c> for members without explicit placement, or "(General)".</summary>
    public string Name { get; }

    /// <summary>Sections in first-appearance order.</summary>
    public IReadOnlyList<PropertySection> Sections { get; }

    public PropertyTab(string name, IReadOnlyList<PropertySection> sections)
    {
        Name = name;
        Sections = sections;
    }
}

/// <summary>Sub-grouping inside a tab. A section owns a column index, letting a surface
/// place sections side by side (the VB grid rendered columns within the category block).</summary>
public class PropertySection
{
    /// <summary>Section name (empty string = the tab's root section).</summary>
    public string Name { get; }

    /// <summary>Column the section occupies inside its tab (0 = first).</summary>
    public int Column { get; }

    /// <summary>Fields in declaration order.</summary>
    public IReadOnlyList<EditorField> Fields { get; }

    public PropertySection(string name, int column, IReadOnlyList<EditorField> fields)
    {
        Name = name;
        Column = column;
        Fields = fields;
    }
}

/// <summary>Every placement and behavior fact the T2 vocabulary states about one editable
/// member, resolved at build time. A surface reads this instead of reflecting.</summary>
public class EditorField
{
    /// <summary>Property name (reflection).</summary>
    public string PropertyName { get; }

    /// <summary>Property type (reflection).</summary>
    public Type PropertyType { get; }

    /// <summary>Declaration index within the type — the deterministic ordering key.
    /// The VB <c>OrderedAttribute</c> is a bare marker; ordering came from declaration
    /// order in the reflected member list, which the port keeps as-is.</summary>
    public int Order { get; }

    /// <summary>True when the member carries <c>[Ordered]</c> (participates in explicit
    /// ordering rather than the category default slotting).</summary>
    public bool IsOrdered { get; }

    /// <summary>Placement resolved from <c>ExtendedCategoryAttribute</c>, when present.</summary>
    public ExtendedCategory? Category { get; }

    /// <summary>Editor mode from <c>[EditOnly]</c>/<c>[ViewOnly]</c>/<c>[SingleEditorMode]</c>;
    /// null = the surface default applies.</summary>
    public PropertyEditorMode? Mode { get; }

    /// <summary>Conditional visibility descriptors resolved from
    /// <c>[ConditionalVisible]</c> (empty when unconditional).</summary>
    public IReadOnlyList<ConditionalVisibleInfo> Visibility { get; }

    /// <summary>Width hint from <c>[Width]</c>, in grid units.</summary>
    public int? Width { get; }

    /// <summary>Size hint from <c>[Size]</c>.</summary>
    public int? Size { get; }

    /// <summary>Text-area line count from <c>[LineCount]</c>.</summary>
    public int? Lines { get; }

    /// <summary>Auto-resize flag carried by <c>[LineCount]</c>.</summary>
    public bool? AutoResize { get; }

    /// <summary>Style hints from <c>[FieldStyle]</c> (CSS-like width strings).</summary>
    public FieldStyleAttribute? FieldStyle { get; }

    /// <summary>Selector configuration from <c>[Selector]</c>/<c>[ProvidersSelector]</c>.</summary>
    public SelectorInfo? Selector { get; }

    /// <summary>Text field name for selector-backed list rendering (<c>[TextField]</c>).</summary>
    public string? TextFieldName { get; }

    /// <summary>Value field name for selector-backed list rendering (<c>[ValueField]</c>).</summary>
    public string? ValueFieldName { get; }

    /// <summary>Editor type names bound through <c>[InnerEditor]</c> (qualified names the
    /// attribute emits as standard <c>EditorAttribute</c> bindings).</summary>
    public IReadOnlyList<string> EditorTypeNames { get; }

    /// <summary>True for <c>[CollectionEditor]</c> members: the field edits a group of
    /// items, whose own grid behavior is described by the collection attribute itself.</summary>
    public bool IsCollection { get; }

    /// <summary>Collection grid options when <see cref="IsCollection"/> is true.</summary>
    public CollectionEditorAttribute? CollectionOptions { get; }

    /// <summary>Multi-selection flavor from <c>[MultiSelectorType]</c>, when present.</summary>
    public MultiSelectionType? MultiSelection { get; }

    /// <summary>True when the value must be masked (<c>[PasswordMode]</c>).</summary>
    public bool IsPassword { get; }

    /// <summary>On-demand (lazy-loaded) flag from <c>[OnDemand]</c>; null when absent.</summary>
    public bool? OnDemand { get; }

    /// <summary>Marker facts (bare attributes): <c>[AutoErase]</c>.</summary>
    public bool AutoErase { get; }

    /// <summary>Marker facts (bare attributes): <c>[AutoPostBack]</c>.</summary>
    public bool AutoPostBack { get; }

    /// <summary>Marker facts (bare attributes): <c>[NoFlag]</c> (the field is excluded from
    /// flag-style rendering).</summary>
    public bool NoFlag { get; }

    public EditorField(
        string propertyName,
        Type propertyType,
        int order,
        bool isOrdered,
        ExtendedCategory? category,
        PropertyEditorMode? mode,
        IReadOnlyList<ConditionalVisibleInfo> visibility,
        int? width,
        int? size,
        int? lines,
        bool? autoResize,
        FieldStyleAttribute? fieldStyle,
        SelectorInfo? selector,
        string? textFieldName,
        string? valueFieldName,
        IReadOnlyList<string> editorTypeNames,
        bool isCollection,
        CollectionEditorAttribute? collectionOptions,
        MultiSelectionType? multiSelection,
        bool isPassword,
        bool? onDemand,
        bool autoErase,
        bool autoPostBack,
        bool noFlag)
    {
        PropertyName = propertyName;
        PropertyType = propertyType;
        Order = order;
        IsOrdered = isOrdered;
        Category = category;
        Mode = mode;
        Visibility = visibility;
        Width = width;
        Size = size;
        Lines = lines;
        AutoResize = autoResize;
        FieldStyle = fieldStyle;
        Selector = selector;
        TextFieldName = textFieldName;
        ValueFieldName = valueFieldName;
        EditorTypeNames = editorTypeNames;
        IsCollection = isCollection;
        CollectionOptions = collectionOptions;
        MultiSelection = multiSelection;
        IsPassword = isPassword;
        OnDemand = onDemand;
        AutoErase = autoErase;
        AutoPostBack = autoPostBack;
        NoFlag = noFlag;
    }
}
