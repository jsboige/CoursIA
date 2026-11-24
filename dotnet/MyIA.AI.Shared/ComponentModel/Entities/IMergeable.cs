namespace MyIA.AI.ComponentModel.Entities;

/// <summary>
/// An entity that knows how to merge the state of another compatible instance into itself.
/// Backs the merge semantics of the Aricie.Shared socle (e.g. reconciling two decorated
/// subtrees). Modernized port (EPIC #7265, ancre A1).
/// </summary>
public interface IMergeable
{
    /// <summary>
    /// Merges the state of <paramref name="other"/> into this instance.
    /// </summary>
    /// <param name="other">The source entity to merge from.</param>
    /// <returns><c>true</c> if the merge was applied; <c>false</c> if <paramref name="other"/>
    /// was incompatible or a no-op.</returns>
    bool Merge(IMergeable other);
}
