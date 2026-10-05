using System;

namespace MyIA.AI.ComponentModel.PropertyEditor;

/// <summary>Names the value property of a bound item, with an optional type code.
/// Modernized port of Aricie.Shared ValueFieldAttribute (EPIC #7265, A3 T2a).</summary>
[AttributeUsage(AttributeTargets.Property)]
public sealed class ValueFieldAttribute : Attribute
{
    public ValueFieldAttribute(string valueField) => ValueField = valueField;

    /// <summary>Name of the property providing the value.</summary>
    public string ValueField { get; }

    /// <summary>Optional type code of the value (TypeCode.Empty when unset).</summary>
    public TypeCode TypeCode { get; set; } = TypeCode.Empty;
}
