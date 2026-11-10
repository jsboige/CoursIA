namespace MyIA.AI.ComponentModel.Filters;

/// <summary>
/// Case-insensitive, culture-invariant equality comparer for chars. Modernized port of
/// Aricie.Shared InvariantCharComparer (EPIC #7265, pépite A3, T1).
/// </summary>
public class InvariantCharComparer : IEqualityComparer<char>
{
    public bool Equals(char x, char y) => char.ToUpperInvariant(x) == char.ToUpperInvariant(y);

    public int GetHashCode(char obj) => char.ToUpperInvariant(obj).GetHashCode();
}
