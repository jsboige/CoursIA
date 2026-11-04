namespace MyIA.AI.Shared.Search.Logic.FirstOrder;

/// <summary>
/// Parseur de formules du premier ordre, syntaxe AIMA ch. 9.
/// </summary>
/// <remarks>
/// Port de la surface <c>FolKbInfo</c> du patrimoine Aricie (EPIC #7265, volet B2
/// tranche 2, issue #24320) : les phrases stockees dans la base sont des chaines
/// dans la syntaxe du <c>FOLParser</c> d'aima-core. Grammaire acceptee :
/// <c>FORALL x ( ... )</c>, <c>EXISTS y ( ... )</c>, connecteurs
/// <c>AND OR NOT =&gt; &lt;=&gt;</c> et leurs synonymes <c>&amp; | ~ -&gt; &lt;-&gt;</c>,
/// atomes <c>Predicat(t1, t2)</c>. Convention de casse AIMA : minuscule initiale =
/// variable, majuscule = constante, fonction ou predicat. Toute erreur est
/// positionnee : le parseur ne rend jamais une formule approximative.
/// </remarks>
public static class FolParser
{
    /// <summary>Analyse une formule complete ; refuse le texte apres la formule.</summary>
    public static FolFormula Parse(string source)
    {
        ArgumentNullException.ThrowIfNull(source);
        List<Token> tokens = Tokenize(source);
        Parser parser = new(tokens);
        FolFormula formula = parser.ParseFormula();
        if (parser.Current is not null)
        {
            throw new FormatException($"Jeton inattendu '{parser.Current.Text}' a la position {parser.Current.Position} apres la formule.");
        }

        return formula;
    }

    private sealed record Token(string Text, int Position);

    private static List<Token> Tokenize(string source)
    {
        List<Token> tokens = new();
        int i = 0;
        while (i < source.Length)
        {
            char c = source[i];
            if (char.IsWhiteSpace(c))
            {
                i++;
                continue;
            }

            if (c is '(' or ')' or ',')
            {
                tokens.Add(new Token(c.ToString(), i));
                i++;
                continue;
            }

            if (c is '&' or '|')
            {
                tokens.Add(new Token(c.ToString(), i));
                i++;
                continue;
            }

            if (c == '~')
            {
                tokens.Add(new Token("~", i));
                i++;
                continue;
            }

            if (c == '=' && i + 1 < source.Length && source[i + 1] == '>')
            {
                tokens.Add(new Token("=>", i));
                i += 2;
                continue;
            }

            if (c == '<' && i + 2 < source.Length && source[i + 1] == '=' && source[i + 2] == '>')
            {
                tokens.Add(new Token("<=>", i));
                i += 3;
                continue;
            }

            if (c == '-' && i + 1 < source.Length && source[i + 1] == '>')
            {
                tokens.Add(new Token("->", i));
                i += 2;
                continue;
            }

            if (c == '<' && i + 1 < source.Length && source[i + 1] == '-')
            {
                // "<->" ecrit avec un tiret simple.
                if (i + 2 < source.Length && source[i + 2] == '>')
                {
                    tokens.Add(new Token("<->", i));
                    i += 3;
                    continue;
                }

                throw new FormatException($"Sequence '<-' incomplete a la position {i} : attendu '<->'.");
            }

            if (char.IsLetter(c))
            {
                int start = i;
                while (i < source.Length && (char.IsLetterOrDigit(source[i]) || source[i] == '_'))
                {
                    i++;
                }

                tokens.Add(new Token(source[start..i], start));
                continue;
            }

            throw new FormatException($"Caractere inattendu '{c}' a la position {i}.");
        }

        return tokens;
    }

    private sealed class Parser
    {
        private readonly List<Token> tokens;
        private int index;

        public Parser(List<Token> tokens)
        {
            this.tokens = tokens;
        }

        public Token? Current => this.index < this.tokens.Count ? this.tokens[this.index] : null;

        private Token Take()
        {
            if (this.Current is null)
            {
                throw new FormatException("Fin de la source inattendue.");
            }

            Token token = this.tokens[this.index];
            this.index++;
            return token;
        }

        private Token Expect(string text)
        {
            Token token = this.Take();
            if (!string.Equals(token.Text, text, StringComparison.Ordinal))
            {
                throw new FormatException($"Attendu '{text}' mais trouve '{token.Text}' a la position {token.Position}.");
            }

            return token;
        }

        private bool TryTakeKeyword(string keyword)
        {
            if (this.Current is { } token && string.Equals(token.Text, keyword, StringComparison.OrdinalIgnoreCase))
            {
                this.index++;
                return true;
            }

            return false;
        }

        private bool TryTakeSymbol(string symbol)
        {
            if (this.Current is { } token && string.Equals(token.Text, symbol, StringComparison.Ordinal))
            {
                this.index++;
                return true;
            }

            return false;
        }

        // Grammaire : implication est associative a droite, plus faible que la disjonction.
        public FolFormula ParseFormula()
        {
            return this.ParseImplication();
        }

        private FolFormula ParseImplication()
        {
            FolFormula left = this.ParseBiconditional();
            if (this.Current is { Text: "=>" or "->" })
            {
                this.Take();
                FolFormula right = this.ParseImplication();
                return new FolFormula.Implies(left, right);
            }

            return left;
        }

        private FolFormula ParseBiconditional()
        {
            FolFormula left = this.ParseDisjunction();
            while (this.Current is { Text: "<=>" or "<->" })
            {
                this.Take();
                FolFormula right = this.ParseDisjunction();
                left = new FolFormula.Biconditional(left, right);
            }

            return left;
        }

        private FolFormula ParseDisjunction()
        {
            FolFormula left = this.ParseConjunction();
            while (this.TryTakeKeyword("OR") || this.TryTakeSymbol("|"))
            {
                FolFormula right = this.ParseConjunction();
                left = new FolFormula.Or(left, right);
            }

            return left;
        }

        private FolFormula ParseConjunction()
        {
            FolFormula left = this.ParseUnary();
            while (this.TryTakeKeyword("AND") || this.TryTakeSymbol("&"))
            {
                FolFormula right = this.ParseUnary();
                left = new FolFormula.And(left, right);
            }

            return left;
        }

        private FolFormula ParseUnary()
        {
            if (this.TryTakeSymbol("~") || this.TryTakeKeyword("NOT"))
            {
                return new FolFormula.Not(this.ParseUnary());
            }

            if (this.TryTakeKeyword("FORALL"))
            {
                return new FolFormula.ForAll(this.TakeVariable(), this.ParseUnary());
            }

            if (this.TryTakeKeyword("EXISTS"))
            {
                return new FolFormula.Exists(this.TakeVariable(), this.ParseUnary());
            }

            if (this.TryTakeSymbol("("))
            {
                // Sous-formule parenthesee : la priorite reprend a zero,
                // c'est ce qui rend "FORALL x (A => B)" analysable.
                FolFormula inner = this.ParseFormula();
                this.Expect(")");
                return inner;
            }

            return this.ParseAtom();
        }

        private string TakeVariable()
        {
            Token token = this.Take();
            if (!char.IsLower(token.Text[0]))
            {
                throw new FormatException(
                    $"La variable quantifiee '{token.Text}' (position {token.Position}) doit commencer par une minuscule.");
            }

            return token.Text;
        }

        private FolFormula ParseAtom()
        {
            Token name = this.Take();
            if (!char.IsUpper(name.Text[0]))
            {
                throw new FormatException(
                    $"Le symbole '{name.Text}' (position {name.Position}) doit commencer par une majuscule : predicat, constante ou fonction.");
            }

            List<FolTerm> arguments = new();
            if (this.Current is { Text: "(" })
            {
                this.Take();
                if (this.Current is not { Text: ")" })
                {
                    arguments.Add(this.ParseTerm());
                    while (this.Current is { Text: "," })
                    {
                        this.Take();
                        arguments.Add(this.ParseTerm());
                    }
                }

                this.Expect(")");
            }

            return new FolFormula.Predicate(name.Text, arguments);
        }

        private FolTerm ParseTerm()
        {
            Token name = this.Take();
            if (!char.IsLetter(name.Text[0]))
            {
                throw new FormatException($"Terme inattendu '{name.Text}' a la position {name.Position}.");
            }

            List<FolTerm> arguments = new();
            if (this.Current is { Text: "(" })
            {
                this.Take();
                arguments.Add(this.ParseTerm());
                while (this.Current is { Text: "," })
                {
                    this.Take();
                    arguments.Add(this.ParseTerm());
                }

                this.Expect(")");

                if (char.IsLower(name.Text[0]))
                {
                    throw new FormatException(
                        $"La fonction '{name.Text}' (position {name.Position}) doit commencer par une majuscule.");
                }

                return new FolTerm.FunctionApplication(name.Text, arguments);
            }

            return char.IsLower(name.Text[0])
                ? new FolTerm.Variable(name.Text)
                : new FolTerm.Constant(name.Text);
        }
    }
}
