namespace MyIA.AI.ComponentModel.Entities;

/// <summary>
/// A hierarchical entity: it owns a parent reference and a collection of children,
/// enabling the infinite parent/child hierarchy that the Aricie.Shared socle is built on.
/// Modernized port (EPIC #7265, ancre A1).
/// </summary>
public interface IChildEntity
{
    /// <summary>Parent in the hierarchy, or null at the root.</summary>
    IChildEntity? Parent { get; set; }

    /// <summary>Children of this node (empty for a leaf).</summary>
    IReadOnlyList<IChildEntity> Children { get; }
}
