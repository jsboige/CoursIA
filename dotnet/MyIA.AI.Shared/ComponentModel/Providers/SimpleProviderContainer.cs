using System.Collections.Generic;

namespace MyIA.AI.ComponentModel.Providers;

/// <summary>
/// Flat, explicitly-registered provider: types are added by hand under a category key,
/// with no reflection and no decoration required. This is the no-magic base of the
/// <c>Aricie.Shared</c> provider hierarchy (EPIC #7265, ancre A1+): where
/// <see cref="ReflectedProviderContainer"/> discovers by decoration and
/// <see cref="AutoProviderContainer"/> by naming convention, this container discovers
/// nothing — the caller states exactly what it holds. Marker-interface buckets
/// (<see cref="IProviderContainer.SimpleEntities"/>, <see cref="IProviderContainer.ChildEntities"/>,
/// <see cref="IProviderContainer.Mergeables"/>) are still derived from the registered types,
/// so the read surface is uniform across the three strategies.
/// </summary>
/// <remarks>
/// Registration is fluent and appendable; the read-model is rebuilt lazily and invalidated
/// on each <see cref="Register"/>. The same type may be registered under several categories
/// (it then appears in each) but only once per (type, category) pair.
/// </remarks>
public sealed class SimpleProviderContainer : IProviderContainer
{
    private readonly Dictionary<string, List<Type>> _byCategory = new(StringComparer.Ordinal);
    private readonly HashSet<Type> _types = new();
    private ProviderModel? _model;

    /// <summary>Registers <typeparamref name="T"/> under <paramref name="category"/>.</summary>
    public SimpleProviderContainer Register<T>(string category) where T : class
        => Register(typeof(T), category);

    /// <summary>Registers <paramref name="type"/> under <paramref name="category"/>.</summary>
    public SimpleProviderContainer Register(Type type, string category)
    {
        ArgumentNullException.ThrowIfNull(type);
        if (string.IsNullOrWhiteSpace(category))
        {
            throw new ArgumentException(
                "Category cannot be null, empty, or whitespace.", nameof(category));
        }

        if (!_byCategory.TryGetValue(category, out var bucket))
        {
            bucket = new List<Type>();
            _byCategory[category] = bucket;
        }

        if (!bucket.Contains(type))
        {
            bucket.Add(type);
        }

        _types.Add(type);
        _model = null; // invalidate the cached read-model
        return this;
    }

    private ProviderModel Model
    {
        get
        {
            if (_model is null)
            {
                // A type's categories = the keys under which it was registered (0..N).
                _model = ProviderModel.Build(
                    _types,
                    type => _byCategory
                        .Where(kv => kv.Value.Contains(type))
                        .Select(kv => kv.Key));
            }

            return _model;
        }
    }

    /// <summary>Categories registered, in first-seen order.</summary>
    public IEnumerable<string> Categories => Model.Categories;

    /// <summary>Types registered under <paramref name="category"/>, or empty if unknown.</summary>
    public IReadOnlyList<Type> this[string category] => Model[category];

    /// <summary>Types marked with <c>AttributeContainerAttribute</c> among the registered set.</summary>
    public IReadOnlyList<Type> Containers => Model.Containers;

    /// <summary>Registered types implementing <c>IChildEntity</c>.</summary>
    public IReadOnlyList<Type> ChildEntities => Model.ChildEntities;

    /// <summary>Registered types implementing <c>ISimpleEntity</c>.</summary>
    public IReadOnlyList<Type> SimpleEntities => Model.SimpleEntities;

    /// <summary>Registered types implementing <c>IMergeable</c>.</summary>
    public IReadOnlyList<Type> Mergeables => Model.Mergeables;
}
