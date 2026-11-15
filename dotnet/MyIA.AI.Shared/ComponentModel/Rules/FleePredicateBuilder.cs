using System.Reflection;
using Flee.PublicTypes;

namespace MyIA.AI.ComponentModel.Rules;

/// <summary>
/// Compiles a business rule written as a string (Flee expression syntax) into a reusable
/// predicate over an entity type. This is the "universal predicate" of the socle
/// (EPIC #7265, nugget B4 "le liant universel"): a non-developper writes a rule as text,
/// the builder compiles it once, and it filters any collection of entities discovered by
/// reflection (cf. <see cref="Providers.ReflectedProviderContainer"/>). The rule changes
/// without recompiling the host — the low-code bridge between data and code.
/// </summary>
/// <remarks>
/// <para><b>Expression syntax.</b> Flee uses a VB-like operator set: <c>and</c> / <c>or</c>
/// / <c>not</c> (words, <b>not</b> <c>&amp;&amp;</c>/<c>||</c>) and <c>=</c> for equality
/// (<b>not</b> <c>==</c>). Comparisons (<c>&gt;</c>, <c>&lt;</c>, <c>&gt;=</c>, <c>&lt;&gt;</c>)
/// and arithmetic are as expected. Example: <c>"Montant &gt; 1000 and Pays = \"FR\""</c>.</para>
/// <para><b>How it binds.</b> Public instance properties of <typeparamref name="T"/> become
/// the rule's variables, by name. The expression is compiled once against the property
/// types (a non-null sentinel of each type is set before compile so Flee can infer them),
/// then evaluated per entity by reflecting its current property values. Compile cost is
/// paid once; evaluation is a variable-mutation + native delegate call.</para>
/// </remarks>
public static class FleePredicateBuilder
{
    /// <summary>
    /// Compiles <paramref name="rule"/> into a predicate over <typeparamref name="T"/>.
    /// </summary>
    /// <typeparam name="T">Entity type whose public properties are the rule variables.</typeparam>
    /// <param name="rule">Flee expression evaluating to a boolean, e.g.
    /// <c>"Montant &gt; 1000 and Pays = \"FR\""</c>.</param>
    /// <returns>A predicate that, given a <typeparamref name="T"/> instance, reflects its
    /// properties into the compiled expression and returns the boolean verdict.</returns>
    /// <exception cref="ArgumentNullException"><paramref name="rule"/> is null/empty.</exception>
    /// <exception cref="Flee.PublicTypes.ExpressionCompileException">The rule is syntactically
    /// invalid or references a property that does not exist on <typeparamref name="T"/>.</exception>
    public static Func<T, bool> Create<T>(string rule)
    {
        if (string.IsNullOrWhiteSpace(rule))
        {
            throw new ArgumentNullException(nameof(rule));
        }

        // Reflect the public instance properties once: they become the rule's variables.
        var props = typeof(T)
            .GetProperties(BindingFlags.Public | BindingFlags.Instance)
            // Indexers are not scalar variables — exclude them (Flee binds names to values).
            .Where(p => p.GetIndexParameters().Length == 0)
            .ToArray();

        var context = new ExpressionContext();
        context.Options.CaseSensitive = true;

        // A non-null sentinel of each property type lets Flee infer variable types at
        // compile time. Flee rejects null values, so string => "" and reference types
        // without a parameterless ctor fall back to "" (they bind by name, not by value).
        foreach (var prop in props)
        {
            context.Variables[prop.Name] = NonNullDefault(prop.PropertyType);
        }

        var compiled = context.CompileGeneric<bool>(rule);

        return entity =>
        {
            foreach (var prop in props)
            {
                var value = prop.GetValue(entity);
                context.Variables[prop.Name] = value ?? NonNullDefault(prop.PropertyType);
            }

            return compiled.Evaluate();
        };
    }

    private static object NonNullDefault(Type type)
    {
        if (type == typeof(string))
        {
            return string.Empty;
        }

        if (type.IsValueType)
        {
            return Activator.CreateInstance(type)!;
        }

        // Reference type: prefer a parameterless ctor, else an empty string sentinel
        // (the variable binds by name; the placeholder is replaced per-entity at eval time).
        return Activator.CreateInstance(type) ?? (object)string.Empty;
    }
}
