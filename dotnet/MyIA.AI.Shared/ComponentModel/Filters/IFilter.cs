namespace MyIA.AI.ComponentModel.Filters;

/// <summary>
/// General-purpose generic filtering interface. Modernized port of Aricie.Shared IFilter
/// (EPIC #7265, pépite A3, T1).
/// </summary>
public interface IFilter : IDescriptor
{
    /// <summary>Whether <see cref="Match{T}"/> is evaluable directly by reflection.</summary>
    bool IsSimpleMatch { get; }

    /// <summary>Whether <paramref name="content"/> passes the filter.</summary>
    bool Match<T>(T content);
}
