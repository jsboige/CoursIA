namespace MyIA.AI.ComponentModel.PropertyEditor;

/// <summary>Names the data source feeding a property's editor. Modernized port of
/// Aricie.Shared DataSourceAttribute (EPIC #7265, A3 T2a).</summary>
[AttributeUsage(AttributeTargets.Property)]
public sealed class DataSourceAttribute : Attribute
{
    public DataSourceAttribute(string datasource) => DataSource = datasource;

    /// <summary>Name of the data source.</summary>
    public string DataSource { get; set; }
}
