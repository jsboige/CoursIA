using System.ComponentModel;

namespace MyIA.AI.ComponentModel.PropertyEditor;

/// <summary>Binds a property to an editor type, optionally enriching it with the attributes
/// of a provider type. Modernized port of Aricie.Shared InnerEditorAttribute
/// (EPIC #7265, A3 T2b).</summary>
/// <remarks>Deviation from the VB source: the original emitted
/// <c>New EditorAttribute(editorTypeName, GetType(DotNetNuke.UI.WebControls.EditControl))</c>,
/// and the DNN <c>EditControl</c> web-control base does not exist on net9. The port keeps the
/// standard <see cref="EditorAttribute"/> binding — the editor type name is the metadata that
/// survives — with a neutral base type; the real editor contract belongs to the rendering
/// layer that tranche T3 will design-gate.</remarks>
public class InnerEditorAttribute : AttributeContainerAttribute
{
    protected InnerEditorAttribute()
    {
    }

    public InnerEditorAttribute(Type attributeProviderType)
        : base(attributeProviderType)
    {
    }

    public InnerEditorAttribute(string editorTypeName, Type attributeProviderType)
        : this(attributeProviderType)
    {
        AddAttribute(new EditorAttribute(editorTypeName, typeof(object)));
    }

    public InnerEditorAttribute(Type editorType, Type attributeProviderType)
        : this(editorType.AssemblyQualifiedName!, attributeProviderType)
    {
    }

    public InnerEditorAttribute(string editorTypeName)
    {
        AddAttribute(new EditorAttribute(editorTypeName, typeof(object)));
    }
}
