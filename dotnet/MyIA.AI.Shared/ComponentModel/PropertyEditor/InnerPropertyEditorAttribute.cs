namespace MyIA.AI.ComponentModel.PropertyEditor;

/// <summary>Base of the editor bindings that target one named inner property of a composite
/// editor (the <c>Key</c> / <c>Value</c> pair of a dictionary editor, for instance).
/// Modernized port of Aricie.Shared InnerPropertyEditorAttribute (EPIC #7265, A3 T2b).</summary>
public abstract class InnerPropertyEditorAttribute : InnerEditorAttribute
{
    /// <summary>Name of the inner property the editor binding targets.</summary>
    public string PropertyName { get; }

    protected InnerPropertyEditorAttribute(string propertyName, Type attributeProviderType)
        : base(attributeProviderType)
    {
        PropertyName = propertyName;
    }

    protected InnerPropertyEditorAttribute(string propertyName, string editorTypeName)
        : base(editorTypeName)
    {
        PropertyName = propertyName;
    }

    protected InnerPropertyEditorAttribute(string propertyName, string editorTypeName, Type attributeProviderType)
        : base(editorTypeName, attributeProviderType)
    {
        PropertyName = propertyName;
    }

    protected InnerPropertyEditorAttribute(string propertyName, Type editorType, Type attributeProviderType)
        : this(propertyName, editorType.FullName!, attributeProviderType)
    {
    }
}
