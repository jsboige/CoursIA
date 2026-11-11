namespace MyIA.AI.ComponentModel.PropertyEditor;

/// <summary>Declares the editor behavior of a collection property (addition, ordering,
/// paging, display style, export). Modernized port of Aricie.Shared
/// CollectionEditorAttribute (EPIC #7265, A3 T2a).</summary>
/// <remarks>The VB original exposes a chain of overloads each adding one option to the
/// previous one; the port keeps every arity so existing declarative call sites translate
/// one-to-one. The <see cref="AttributeUsageAttribute"/> is absent in the source, so the
/// port carries none either (C# default: <see cref="AttributeTargets.All"/>).</remarks>
public sealed class CollectionEditorAttribute : Attribute
{
    public CollectionEditorAttribute()
    {
    }

    [Obsolete("Use the other constructor")]
    public CollectionEditorAttribute(bool showAddItem, bool ordered)
    {
        ShowAddItem = showAddItem;
        Ordered = ordered;
    }

    public CollectionEditorAttribute(bool noAddition, bool showAddItem, bool ordered, bool paged, int pageSize)
    {
        NoAdd = noAddition;
        ShowAddItem = showAddItem;
        Ordered = ordered;
        Paged = paged;
        PageSize = pageSize;
    }

    public CollectionEditorAttribute(
        bool noAddition, bool showAddItem, bool ordered, bool paged, int pageSize, CollectionDisplayStyle displayStyle)
        : this(noAddition, showAddItem, ordered, paged, pageSize)
    {
        DisplayStyle = displayStyle;
    }

    public CollectionEditorAttribute(
        bool noAddition,
        bool showAddItem,
        bool ordered,
        bool paged,
        int pageSize,
        CollectionDisplayStyle displayStyle,
        bool enableExport)
        : this(noAddition, showAddItem, ordered, paged, pageSize, displayStyle)
    {
        EnableExport = enableExport;
    }

    public CollectionEditorAttribute(
        bool noAddition,
        bool showAddItem,
        bool ordered,
        bool paged,
        int pageSize,
        CollectionDisplayStyle displayStyle,
        bool enableExport,
        int maxItemNb)
        : this(noAddition, showAddItem, ordered, paged, pageSize, displayStyle, enableExport)
    {
        MaxItemNb = maxItemNb;
    }

    public CollectionEditorAttribute(
        bool noAddition,
        bool showAddItem,
        bool ordered,
        bool paged,
        int pageSize,
        CollectionDisplayStyle displayStyle,
        bool enableExport,
        int maxItemNb,
        string pagerDisplayFieldName)
        : this(noAddition, showAddItem, ordered, paged, pageSize, displayStyle, enableExport, maxItemNb)
    {
        PagerDisplayFieldName = pagerDisplayFieldName;
    }

    public CollectionEditorAttribute(
        bool noAddition,
        bool showAddItem,
        bool ordered,
        bool paged,
        int pageSize,
        CollectionDisplayStyle displayStyle,
        bool enableExport,
        int maxItemNb,
        string pagerDisplayFieldName,
        bool itemsReadOnly)
        : this(noAddition, showAddItem, ordered, paged, pageSize, displayStyle, enableExport, maxItemNb, pagerDisplayFieldName)
    {
        ItemsReadOnly = itemsReadOnly;
    }

    /// <summary>Whether item deletion is disabled.</summary>
    public bool NoDeletion { get; set; }

    /// <summary>Whether item addition is disabled.</summary>
    public bool NoAdd { get; set; }

    /// <summary>Whether the "add item" affordance is shown.</summary>
    public bool ShowAddItem { get; set; }

    /// <summary>Whether items can be reordered.</summary>
    public bool Ordered { get; set; } = true;

    /// <summary>Whether the collection is paged.</summary>
    public bool Paged { get; set; } = true;

    /// <summary>Page size when paged.</summary>
    public int PageSize { get; set; } = 30;

    /// <summary>Display style of the collection.</summary>
    public CollectionDisplayStyle DisplayStyle { get; set; } = CollectionDisplayStyle.Accordion;

    /// <summary>Whether the collection can be exported.</summary>
    public bool EnableExport { get; set; }

    /// <summary>Maximum number of items.</summary>
    public int MaxItemNb { get; set; }

    /// <summary>Field used to display an item in the pager.</summary>
    public string PagerDisplayFieldName { get; set; } = string.Empty;

    /// <summary>Whether individual items are read-only.</summary>
    public bool ItemsReadOnly { get; set; }
}

/// <summary>Display styles for a collection editor (companion enum of
/// <see cref="CollectionEditorAttribute"/>).</summary>
public enum CollectionDisplayStyle
{
    /// <summary>Flat list.</summary>
    List,

    /// <summary>Collapsible accordion.</summary>
    Accordion
}
