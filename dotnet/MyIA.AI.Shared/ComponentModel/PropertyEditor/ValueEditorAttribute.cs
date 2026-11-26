namespace MyIA.AI.ComponentModel.PropertyEditor;

/// <summary>Editor binding for the <c>Value</c> member of a composite editor.
/// Modernized port of Aricie.Shared ValueEditorAttribute (EPIC #7265, A3 T2b).</summary>
[AttributeUsage(AttributeTargets.Property)]
public sealed class ValueEditorAttribute : InnerPropertyEditorAttribute
{
    private const string PropName = "Value";

    public ValueEditorAttribute(string editorTypeName)
        : base(PropName, editorTypeName)
    {
    }

    public ValueEditorAttribute(Type editorType)
        : base(PropName, editorType.FullName!)
    {
    }

    public ValueEditorAttribute(string editorTypeName, Type attributeProviderType)
        : base(PropName, editorTypeName, attributeProviderType)
    {
    }

    public ValueEditorAttribute(Type editorType, Type attributeProviderType)
        : base(PropName, editorType.FullName!, attributeProviderType)
    {
    }
}
