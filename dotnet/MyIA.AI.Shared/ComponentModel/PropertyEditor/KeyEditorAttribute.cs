namespace MyIA.AI.ComponentModel.PropertyEditor;

/// <summary>Editor binding for the <c>Key</c> member of a composite editor.
/// Modernized port of Aricie.Shared KeyEditorAttribute (EPIC #7265, A3 T2b).</summary>
[AttributeUsage(AttributeTargets.Property)]
public sealed class KeyEditorAttribute : InnerPropertyEditorAttribute
{
    private const string PropName = "Key";

    public KeyEditorAttribute(string editorTypeName)
        : base(PropName, editorTypeName)
    {
    }

    public KeyEditorAttribute(Type editorType)
        : base(PropName, editorType.FullName!)
    {
    }

    public KeyEditorAttribute(string editorTypeName, Type attributeProviderType)
        : base(PropName, editorTypeName, attributeProviderType)
    {
    }

    public KeyEditorAttribute(Type editorType, Type attributeProviderType)
        : base(PropName, editorType.FullName!, attributeProviderType)
    {
    }
}
