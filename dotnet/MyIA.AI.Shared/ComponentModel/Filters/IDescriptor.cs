using System.CodeDom;

namespace MyIA.AI.ComponentModel.Filters;

/// <summary>
/// Describes a filter as a CodeDom expression plus a stable string signature of its
/// arguments. Modernized port of Aricie.Shared IDescriptor (EPIC #7265, pépite A3, T1).
/// </summary>
public interface IDescriptor
{
    /// <summary>CodeDom representation of the descriptor (expression composition).</summary>
    CodeExpression GetCodeExpression();

    /// <summary>Stable string signature of the descriptor's arguments (cache-key shape).</summary>
    string GetArgs();
}
