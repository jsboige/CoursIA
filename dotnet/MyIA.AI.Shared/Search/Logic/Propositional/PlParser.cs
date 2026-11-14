using System.Text;

namespace MyIA.AI.Shared.Search.Logic.Propositional;

/// <summary>Erreur de syntaxe levee par <see cref="PlParser"/>.</summary>
public sealed class PlParseException : Exception
{
    public PlParseException(string message) : base(message)
    {
    }
}

/// <summary>
/// Parseur de formules propositionnelles sur la syntaxe d'AIMA (chapitre 7).
/// </summary>
/// <remarks>
/// <para>
/// Connecteurs acceptes, du plus faible au plus fort : <c>&lt;=&gt;</c> (ou <c>&lt;-&gt;</c>),
/// <c>=&gt;</c> (ou <c>-&gt;</c>), <c>|</c>, <c>&amp;</c>, <c>~</c> (ou <c>!</c>).
/// Les parentheses groupent ; l'implication est associative a droite.
/// </para>
/// <para>
/// Un symbole est une suite de lettres, chiffres et soulignes, commencant par une
/// lettre ou un souligne. Le parsing est total : une entree mal formee leve une
/// <see cref="PlParseException"/> nommant la position fautive, elle ne rend jamais
/// une formule approximative.
/// </para>
/// </remarks>
public static class PlParser
{
    /// <summary>Analyse une formule et rend son arbre syntaxique.</summary>
    public static PlFormula Parse(string source)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(source);

        List<PlToken> tokens = Tokenize(source);
        int position = 0;
        PlFormula formula = ParseBiconditional(tokens, ref position);

        if (position != tokens.Count)
        {
            throw new PlParseException(
                $"Jeton inattendu '{tokens[position].Text}' a la position {tokens[position].Position} ; " +
                "la formule se termine avant la fin de l'entree.");
        }

        return formula;
    }

    private static PlFormula ParseBiconditional(List<PlToken> tokens, ref int position)
    {
        PlFormula left = ParseImplication(tokens, ref position);

        while (PeekIs(tokens, position, PlTokenKind.Biconditional))
        {
            position++;
            PlFormula right = ParseImplication(tokens, ref position);
            left = new PlBiconditional(left, right);
        }

        return left;
    }

    private static PlFormula ParseImplication(List<PlToken> tokens, ref int position)
    {
        PlFormula left = ParseDisjunction(tokens, ref position);

        // Associativite a droite : A => B => C se lit A => (B => C).
        if (PeekIs(tokens, position, PlTokenKind.Implies))
        {
            position++;
            PlFormula right = ParseImplication(tokens, ref position);
            return new PlImplies(left, right);
        }

        return left;
    }

    private static PlFormula ParseDisjunction(List<PlToken> tokens, ref int position)
    {
        PlFormula left = ParseConjunction(tokens, ref position);

        while (PeekIs(tokens, position, PlTokenKind.Or))
        {
            position++;
            PlFormula right = ParseConjunction(tokens, ref position);
            left = new PlOr(left, right);
        }

        return left;
    }

    private static PlFormula ParseConjunction(List<PlToken> tokens, ref int position)
    {
        PlFormula left = ParseUnary(tokens, ref position);

        while (PeekIs(tokens, position, PlTokenKind.And))
        {
            position++;
            PlFormula right = ParseUnary(tokens, ref position);
            left = new PlAnd(left, right);
        }

        return left;
    }

    private static PlFormula ParseUnary(List<PlToken> tokens, ref int position)
    {
        if (PeekIs(tokens, position, PlTokenKind.Not))
        {
            position++;
            return new PlNot(ParseUnary(tokens, ref position));
        }

        return ParsePrimary(tokens, ref position);
    }

    private static PlFormula ParsePrimary(List<PlToken> tokens, ref int position)
    {
        if (position >= tokens.Count)
        {
            throw new PlParseException("Formule incomplete : un symbole ou une parenthese ouvrante est attendu.");
        }

        PlToken token = tokens[position];

        if (token.Kind == PlTokenKind.Open)
        {
            position++;
            PlFormula inner = ParseBiconditional(tokens, ref position);

            if (!PeekIs(tokens, position, PlTokenKind.Close))
            {
                throw new PlParseException(
                    $"Parenthese fermante attendue a la position {token.Position}, " +
                    $"trouve '{(position < tokens.Count ? tokens[position].Text : "fin d'entree")}'.");
            }

            position++;
            return inner;
        }

        if (token.Kind == PlTokenKind.Symbol)
        {
            position++;
            return new PlAtom(token.Text);
        }

        throw new PlParseException(
            $"Jeton inattendu '{token.Text}' a la position {token.Position} ; " +
            "un symbole ou une parenthese ouvrante est attendu.");
    }

    private static bool PeekIs(List<PlToken> tokens, int position, PlTokenKind kind) =>
        position < tokens.Count && tokens[position].Kind == kind;

    private static List<PlToken> Tokenize(string source)
    {
        List<PlToken> tokens = new();
        int index = 0;

        while (index < source.Length)
        {
            char current = source[index];

            if (char.IsWhiteSpace(current))
            {
                index++;
                continue;
            }

            int start = index;

            // Connecteurs a deux caracteres d'abord (maximal munch).
            if (index + 1 < source.Length)
            {
                string pair = source.Substring(index, 2);
                if (pair is "=>" or "->")
                {
                    tokens.Add(new PlToken(PlTokenKind.Implies, pair, start));
                    index += 2;
                    continue;
                }
            }

            if (index + 2 < source.Length && source.Substring(index, 3) == "<=>")
            {
                tokens.Add(new PlToken(PlTokenKind.Biconditional, "<=>", start));
                index += 3;
                continue;
            }

            if (index + 2 < source.Length && source.Substring(index, 3) == "<->")
            {
                tokens.Add(new PlToken(PlTokenKind.Biconditional, "<->", start));
                index += 3;
                continue;
            }

            switch (current)
            {
                case '~':
                case '!':
                    tokens.Add(new PlToken(PlTokenKind.Not, current.ToString(), start));
                    index++;
                    continue;
                case '&':
                    tokens.Add(new PlToken(PlTokenKind.And, "&", start));
                    index++;
                    continue;
                case '|':
                    tokens.Add(new PlToken(PlTokenKind.Or, "|", start));
                    index++;
                    continue;
                case '(':
                    tokens.Add(new PlToken(PlTokenKind.Open, "(", start));
                    index++;
                    continue;
                case ')':
                    tokens.Add(new PlToken(PlTokenKind.Close, ")", start));
                    index++;
                    continue;
            }

            if (char.IsLetter(current) || current == '_')
            {
                StringBuilder builder = new();
                while (index < source.Length && (char.IsLetterOrDigit(source[index]) || source[index] == '_'))
                {
                    builder.Append(source[index]);
                    index++;
                }

                tokens.Add(new PlToken(PlTokenKind.Symbol, builder.ToString(), start));
                continue;
            }

            throw new PlParseException(
                $"Caractere inattendu '{current}' a la position {start}.");
        }

        if (tokens.Count == 0)
        {
            throw new PlParseException("Entree vide : aucune formule a analyser.");
        }

        return tokens;
    }

    private enum PlTokenKind
    {
        Symbol,
        Not,
        And,
        Or,
        Implies,
        Biconditional,
        Open,
        Close,
    }

    private readonly record struct PlToken(PlTokenKind Kind, string Text, int Position);
}
