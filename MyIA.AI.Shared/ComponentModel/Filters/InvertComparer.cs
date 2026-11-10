namespace MyIA.AI.ComponentModel.Filters;

/// <summary>
/// <see cref="IComparer{T}"/> reversing a source comparer. Modernized port of Aricie.Shared
/// InvertComparer (VB file InvertConverter.vb, namespace Aricie.ComponentModel — unified
/// under Filters here) (EPIC #7265, pépite A3, T1).
/// </summary>
/// <typeparam name="T">Compared type.</typeparam>
public class InvertComparer<T> : IComparer<T>
{
    private readonly IComparer<T> _sourceComparer;

    public InvertComparer(IComparer<T> sourceComparer) => _sourceComparer = sourceComparer;

    public int Compare(T? x, T? y) => -_sourceComparer.Compare(x!, y!);
}
