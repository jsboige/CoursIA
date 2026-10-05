namespace MyIA.AI.ComponentModel.Filters;

/// <summary>
/// <see cref="IComparer{T}"/> wrapper around a <see cref="Comparison{T}"/> delegate.
/// Modernized port of Aricie.Shared CustomSorter (EPIC #7265, pépite A3, T1). The VB
/// original exposed its comparison as a public field; the port binds it at construction.
/// </summary>
/// <typeparam name="T">Compared type.</typeparam>
public class CustomSorter<T> : IComparer<T>
{
    private readonly Comparison<T> _comparison;

    public CustomSorter(Comparison<T> comparison) => _comparison = comparison;

    public int Compare(T? x, T? y) => _comparison.Invoke(x!, y!);
}
