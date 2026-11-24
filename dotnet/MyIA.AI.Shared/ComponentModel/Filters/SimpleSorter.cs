using System.ComponentModel;

namespace MyIA.AI.ComponentModel.Filters;

/// <summary>
/// Direction-aware <see cref="IComparer{T}"/> over whole <see cref="IComparable"/> values.
/// Modernized port of Aricie.Shared SimpleSorter (EPIC #7265, pépite A3, T1).
/// </summary>
/// <typeparam name="T">Compared type.</typeparam>
/// <remarks>
/// The VB original carries a <see cref="PropertyName"/> it never reads (whole-value
/// comparison); the property is kept for API compatibility with the grid UIs that
/// instantiate sorters by column name. The original's unused private <c>_Value</c> field is
/// not carried over.
/// </remarks>
public class SimpleSorter<T> : IComparer<T> where T : IComparable
{
    public SimpleSorter(IConvertible propName, ListSortDirection direction)
    {
        PropertyName = propName;
        SortDirection = direction;
    }

    /// <summary>Column name (kept for API compatibility — not read by the comparison).</summary>
    public IConvertible PropertyName { get; set; } = "";

    /// <summary>Sort direction applied to the comparison result.</summary>
    public ListSortDirection SortDirection { get; set; }

    public int Compare(T? x, T? y)
    {
        var invertCoef = SortDirection == ListSortDirection.Ascending ? 1 : -1;
        return invertCoef * x!.CompareTo(y);
    }
}
