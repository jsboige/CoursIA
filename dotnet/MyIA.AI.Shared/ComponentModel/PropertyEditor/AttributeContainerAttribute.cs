namespace MyIA.AI.ComponentModel.PropertyEditor;

/// <summary>Aggregates the attributes applying to a property: those added by a subclass plus
/// those produced by a provider type (either a fixed <see cref="IAttributesProvider"/> or a
/// type-driven <see cref="IDynamicAttributesProvider"/>). Modernized port of Aricie.Shared
/// AttributeContainerAttribute (EPIC #7265, A3 T2a).</summary>
/// <remarks>
/// <para>Name collision, deliberate: <c>MyIA.AI.ComponentModel.Attributes.AttributeContainerAttribute</c>
/// (A1, twin port of the same source file name) marks a type as a container of child entities
/// for the provider model. Both are kept, in their respective namespaces, because they do
/// different jobs — the A1 one is a discovery marker, this one is an attribute aggregator.</para>
/// <para>Deviations from the VB source: (1) the source exposes the provider attributes as a
/// <em>parameterized property</em> (<c>ProviderAttributes(objValueType)</c>), which C# has no
/// equivalent for — it becomes <see cref="GetProviderAttributes"/>; (2) the source caches the
/// provider result once and forever, which silently returns the first value type's attributes
/// for every later type when the provider is dynamic — the port caches only the type-independent
/// (static) case and recomputes the dynamic one; (3) the interface test uses
/// <see cref="Type.IsAssignableFrom(Type)"/> instead of the string-based
/// <c>Type.GetInterface("IAttributesProvider")</c>.</para>
/// </remarks>
[AttributeUsage(AttributeTargets.Property)]
public class AttributeContainerAttribute : Attribute
{
    private readonly Type? _attributeProviderType;
    private readonly List<Attribute> _attributes = new();
    private List<Attribute>? _providerAttributes;

    protected AttributeContainerAttribute()
    {
    }

    public AttributeContainerAttribute(Type attributeProviderType) => _attributeProviderType = attributeProviderType;

    /// <summary>Attributes contributed by the provider type, plus those added by a subclass.</summary>
    /// <param name="objValueType">Value type passed to a dynamic provider.</param>
    public IList<Attribute> GetAttributes(Type objValueType)
    {
        var toReturn = new List<Attribute>();
        toReturn.AddRange(_attributes);
        toReturn.AddRange(GetProviderAttributes(objValueType));
        return toReturn;
    }

    /// <summary>Attributes produced by the configured provider type (empty when none is set
    /// or when it implements neither provider interface).</summary>
    /// <param name="objValueType">Value type passed to a dynamic provider.</param>
    public List<Attribute> GetProviderAttributes(Type objValueType)
    {
        if (_attributeProviderType is null)
        {
            return new List<Attribute>();
        }

        if (typeof(IAttributesProvider).IsAssignableFrom(_attributeProviderType))
        {
            // Type-independent: computed once and cached.
            if (_providerAttributes is not null)
            {
                return _providerAttributes;
            }

            var staticProvider = (IAttributesProvider)Activator.CreateInstance(_attributeProviderType)!;
            _providerAttributes = new List<Attribute>(staticProvider.GetAttributes());
            return _providerAttributes;
        }

        if (typeof(IDynamicAttributesProvider).IsAssignableFrom(_attributeProviderType))
        {
            // Type-dependent: never cached across value types (VB cached the first one).
            var dynamicProvider = (IDynamicAttributesProvider)Activator.CreateInstance(_attributeProviderType)!;
            return new List<Attribute>(dynamicProvider.GetAttributes(objValueType));
        }

        return new List<Attribute>();
    }

    /// <summary>Registers an attribute for subclasses.</summary>
    protected void AddAttribute(Attribute attr) => _attributes.Add(attr);
}
