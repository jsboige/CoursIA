namespace MyIA.AI.ComponentModel.Attributes;

/// <summary>
/// Marks a type as a CONTAINER of child entities, i.e. a node that aggregates
/// <see cref="MyIA.AI.ComponentModel.Entities.IChildEntity"/> instances and can serve as
/// the root of an introspection tree (infinite hierarchy). Modernized port of
/// <c>Aricie.Shared</c>'s <c>AttributeContainerAttribute</c> (EPIC #7265, ancre A1).
/// </summary>
/// <remarks>
/// A type decorated with <c>[AttributeContainer]</c> signals to a
/// <see cref="MyIA.AI.ComponentModel.Providers.ReflectedProviderContainer"/> that it is a
/// legitimate parent in the decoration-driven hierarchy, as opposed to a leaf
/// (<see cref="MyIA.AI.ComponentModel.Entities.ISimpleEntity"/>) or a plain child.
/// </remarks>
[AttributeUsage(AttributeTargets.Class | AttributeTargets.Interface,
    AllowMultiple = false, Inherited = true)]
public sealed class AttributeContainerAttribute : Attribute
{
    /// <summary>
    /// Optional constraint on the child entity type the container accepts. When null
    /// (default) the container is polymorphic and accepts any <c>IChildEntity</c>.
    /// </summary>
    public Type? ChildType { get; set; }
}
