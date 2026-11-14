using System.Collections.Generic;

namespace MyIA.AI.ComponentModel.Providers;

/// <summary>
/// Read surface shared by the <c>Aricie.Shared</c> provider hierarchy (EPIC #7265,
/// ancre A1+). A container exposes the types it knows grouped by category and by the A1
/// marker interfaces, regardless of <em>how</em> they were discovered: decoration for
/// <see cref="ReflectedProviderContainer"/>, explicit registration for
/// <see cref="SimpleProviderContainer"/>, naming/namespace convention for
/// <see cref="AutoProviderContainer"/>. The three strategies are interchangeable through
/// this contract so a consumer can ask for types without coupling to the discovery mode.
/// </summary>
public interface IProviderContainer
{
    /// <summary>Category names known to this container, in first-seen order.</summary>
    IEnumerable<string> Categories { get; }

    /// <summary>Types registered under <paramref name="category"/>, or empty if unknown.</summary>
    IReadOnlyList<Type> this[string category] { get; }

    /// <summary>Types marked with <c>AttributeContainerAttribute</c>.</summary>
    IReadOnlyList<Type> Containers { get; }

    /// <summary>Types implementing <c>IChildEntity</c> (hierarchical nodes).</summary>
    IReadOnlyList<Type> ChildEntities { get; }

    /// <summary>Types implementing <c>ISimpleEntity</c> (flat leaves).</summary>
    IReadOnlyList<Type> SimpleEntities { get; }

    /// <summary>Types implementing <c>IMergeable</c>.</summary>
    IReadOnlyList<Type> Mergeables { get; }
}
