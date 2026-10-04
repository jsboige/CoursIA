using System.Collections;
using System.ComponentModel;
using System.Globalization;
using System.Reflection;

namespace MyIA.AI.ComponentModel.Filters;

/// <summary>
/// Non-generic reflection comparer over a property of the compared objects, with sort
/// direction. When the property is not found, falls back to comparing the whole objects
/// through <see cref="IComparable"/>. Modernized port of Aricie.Shared SimpleComparer, base
/// class (EPIC #7265, pépite A3, T1).
/// </summary>
public class SimpleComparer : IComparer
{
    public SimpleComparer()
    {
    }

    public SimpleComparer(IConvertible propName, ListSortDirection direction, bool isHybrid = false)
    {
        PropertyName = propName;
        SortDirection = direction;
        _isHybrid = isHybrid;
    }

    private bool _isHybrid;

    /// <summary>Name of the property compared (empty = whole-object comparison).</summary>
    public IConvertible PropertyName { get; set; } = "";

    /// <summary>Sort direction applied to the comparison result.</summary>
    public ListSortDirection SortDirection { get; set; }

    /// <summary>Resolved property info (lazily populated by <see cref="SetUp"/>).</summary>
    public PropertyInfo? PropInfo { get; set; }

    protected void SetUp(object x)
    {
        if (_isHybrid || PropInfo is null)
        {
            var objType = x.GetType();
            ReflectionCache.Properties(objType).TryGetValue(
                PropertyName.ToString(CultureInfo.InvariantCulture)!, out var pi);
            PropInfo = pi;
        }
    }

    /// <remarks>Port note: when neither operand is set up, the VB original resolved the
    /// property against a null object (reflection on Nothing) which left
    /// <see cref="PropInfo"/> null; the port keeps the null-property fallback explicitly.</remarks>
    public virtual int Compare(object? x, object? y)
    {
        var invertCoef = SortDirection == ListSortDirection.Ascending ? 1 : -1;
        if (x is not null)
        {
            SetUp(x);
        }
        else if (y is not null)
        {
            SetUp(y);
        }
        else
        {
            return 0;
        }

        int toReturn = PropInfo is null
            ? ((IComparable)x!).CompareTo(y)
            : ((IComparable)PropInfo.GetValue(x!)!).CompareTo(PropInfo.GetValue(y));
        return invertCoef * toReturn;
    }
}

/// <summary>
/// Generic <see cref="SimpleComparer"/> extended with delegate-based comparison and
/// <see cref="IEqualityComparer{T}"/> over the compared property. Modernized port of
/// Aricie.Shared SimpleComparer(Of T) (EPIC #7265, pépite A3, T1).
/// </summary>
/// <typeparam name="T">Compared type.</typeparam>
public class SimpleComparer<T> : SimpleComparer, IComparer<T>, IEqualityComparer<T>
{
    private readonly Func<T, T, int>? _compareDelegate;
    private readonly Func<T, int>? _hashCodeDelegate;

    public SimpleComparer(IConvertible propName, ListSortDirection direction, bool isHybrid = false)
        : base(propName, direction, isHybrid)
    {
    }

    public SimpleComparer(Func<T, T, int> objCompareFunction, Func<T, int> objHashCodeFunction)
    {
        _compareDelegate = objCompareFunction;
        _hashCodeDelegate = objHashCodeFunction;
    }

    public int Compare(T? x, T? y)
    {
        if (_compareDelegate is not null)
        {
            return _compareDelegate.Invoke(x!, y!);
        }

        return base.Compare(x, y);
    }

    /// <remarks>Port note: the VB original routed through a Match-like indirection;
    /// equality is <c>Compare(x, y) == 0</c> here as there.</remarks>
    public bool Equals(T? x, T? y) => Compare(x, y) == 0;

    /// <remarks>Port note: the VB original cast to <see cref="IConvertible"/> before calling
    /// GetHashCode — the cast never changed the hash (interface dispatch to the same
    /// override) and only added a throw for non-IConvertible types; dropped as cosmetic.</remarks>
    public int GetHashCode(T obj)
    {
        if (_hashCodeDelegate is not null)
        {
            return _hashCodeDelegate.Invoke(obj);
        }

        SetUp(obj!);
        return PropInfo is null
            ? obj!.GetHashCode()
            : PropInfo.GetValue(obj)!.GetHashCode();
    }
}
