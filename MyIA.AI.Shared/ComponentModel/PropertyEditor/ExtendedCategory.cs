using System.ComponentModel;
using System.Reflection;

namespace MyIA.AI.ComponentModel.PropertyEditor;

/// <summary>Describes where a member is rendered: tab, section, column, plus the resource
/// prefix used to look up a localized label. Modernized port of Aricie.Shared
/// ExtendedCategory (EPIC #7265, A3 T2a).</summary>
/// <remarks>Deviations from the VB source: (1) <c>[Serializable]</c> is not carried — the
/// attribute only marks BinaryFormatter serialization, a path disabled by default on net9
/// and unused by the A2/A2+ serializers, which round-trip the model through their own
/// contracts; (2) <see cref="FromMember"/> reads the attributes through
/// <see cref="MemberInfo.GetCustomAttributes(bool)"/> instead of the Aricie
/// <c>ReflectionHelper</c> (not ported); (3) <see cref="GetResourcePrefix"/> guards the
/// declaring-types that reflection can legitimately return as null for global members.</remarks>
public class ExtendedCategory
{
    public ExtendedCategory()
    {
    }

    public ExtendedCategory(string tabName)
    {
        TabName = tabName;
        SectionName = string.Empty;
        Column = 0;
    }

    public ExtendedCategory(string sectionName, int column)
    {
        TabName = string.Empty;
        SectionName = sectionName;
        Column = column;
    }

    public ExtendedCategory(string tabName, string sectionName)
    {
        TabName = tabName;
        SectionName = sectionName;
        Column = 0;
    }

    public ExtendedCategory(string tabName, string sectionName, int column)
    {
        TabName = tabName;
        SectionName = sectionName;
        Column = column;
    }

    /// <summary>Tab the member is grouped under.</summary>
    public string TabName { get; set; } = string.Empty;

    /// <summary>Section within the tab.</summary>
    public string SectionName { get; set; } = string.Empty;

    /// <summary>Column within the section.</summary>
    public int Column { get; set; }

    /// <summary>Resource prefix used to resolve the localized label.</summary>
    public string? Prefix { get; set; }

    /// <summary>Builds the category of a member: the standard <see cref="CategoryAttribute"/>
    /// wins when present, otherwise <see cref="ExtendedCategoryAttribute"/>, otherwise an
    /// empty category. The resource prefix is always filled in.</summary>
    public static ExtendedCategory FromMember(MemberInfo member)
    {
        ExtendedCategory toReturn;
        var customAttributes = member.GetCustomAttributes(true);
        var categoryAttributes = customAttributes.OfType<CategoryAttribute>().ToList();
        if (categoryAttributes.Count > 0)
        {
            toReturn = new ExtendedCategory { SectionName = categoryAttributes[0].Category ?? string.Empty };
        }
        else
        {
            var extendedAttributes = customAttributes.OfType<ExtendedCategoryAttribute>().ToList();
            toReturn = extendedAttributes.Count > 0
                ? extendedAttributes[0].ExtendedCategory
                : new ExtendedCategory();
        }

        toReturn.Prefix = GetResourcePrefix(member);
        return toReturn;
    }

    private static string GetResourcePrefix(MemberInfo member)
    {
        string? toReturn = member switch
        {
            PropertyInfo property => property.GetAccessors().FirstOrDefault()?.GetBaseDefinition().DeclaringType?.Name,
            MethodInfo method => method.GetBaseDefinition().DeclaringType?.Name,
            _ => member.DeclaringType?.Name,
        };
        return toReturn ?? string.Empty;
    }
}
