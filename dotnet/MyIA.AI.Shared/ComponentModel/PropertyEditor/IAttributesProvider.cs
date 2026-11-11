namespace MyIA.AI.ComponentModel.PropertyEditor;

/// <summary>Supplies a fixed set of attributes, independent of the decorated value's type.
/// Modernized port of Aricie.Shared IAttributesProvider (EPIC #7265, A3 T2a).</summary>
public interface IAttributesProvider
{
    /// <summary>Returns the attributes this provider contributes.</summary>
    IEnumerable<Attribute> GetAttributes();
}

/// <summary>Supplies attributes computed from the decorated value's type. Modernized port
/// of Aricie.Shared IDynamicAttributesProvider (EPIC #7265, A3 T2a).</summary>
public interface IDynamicAttributesProvider
{
    /// <summary>Returns the attributes this provider contributes for <paramref name="valueType"/>.</summary>
    IEnumerable<Attribute> GetAttributes(Type valueType);
}
