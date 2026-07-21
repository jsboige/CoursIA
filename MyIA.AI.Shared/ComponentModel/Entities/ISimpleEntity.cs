namespace MyIA.AI.ComponentModel.Entities;

/// <summary>
/// A simple (leaf, non-hierarchical) entity: it carries a name but no parent/children.
/// Counterpart of <see cref="IChildEntity"/> for the flat entities of the socle.
/// Modernized port (EPIC #7265, ancre A1).
/// </summary>
public interface ISimpleEntity
{
    /// <summary>Display/identity name of the entity.</summary>
    string Name { get; }
}
