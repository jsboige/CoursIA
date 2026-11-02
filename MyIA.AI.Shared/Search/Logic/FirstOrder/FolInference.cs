namespace MyIA.AI.Shared.Search.Logic.FirstOrder;

using System.Linq.Expressions;
using Z3.Linq;

/// <summary>Procedures d'inference FOL exposees par le wrapper Aricie (noms verbatim).</summary>
public enum FolInferenceProcedure
{
    /// <summary>Proveur de theoremes de la famille OTTER : decision par ancrage Z3.Linq.</summary>
    OTTERLikeTheoremProver,

    /// <summary>Chainage arriere (AIMA ch. 9, recherche ET-OU).</summary>
    BCAsk,

    /// <summary>Chainage avant (AIMA ch. 9, Modus Ponens generalise).</summary>
    FCAsk,

    /// <summary>Elimination de modeles : decision par ancrage Z3.Linq.</summary>
    ModelElimination,

    /// <summary>Resolution TFM (two-fledgling method) : decision par ancrage Z3.Linq.</summary>
    TFMResolution,
}

/// <summary>Resultat d'une question posee a une base FOL.</summary>
/// <param name="Entailed">Vrai si la question est demontree.</param>
/// <param name="Cost">Cout mesure de la procedure, dans l'unite de <paramref name="CostUnit"/>.</param>
/// <param name="CostUnit">Unite du cout mesure : ce qui rend les procedures comparables entre elles.</param>
public sealed record FolAskResult(bool Entailed, long Cost, string CostUnit);

/// <summary>
/// Procedures de deduction du premier ordre : chainage avant, chainage arriere,
/// et la famille de resolution branchee sur l'organe <c>Z3.Linq</c> du sous-module
/// <c>SymbolicAI/SMT/Z3.Linq</c>.
/// </summary>
/// <remarks>
/// Port de la surface <c>FolKbInferInfo</c> du patrimoine Aricie (EPIC #7265,
/// volet B2 tranche 2, issue #24320). Les procedures de la famille resolution
/// (OTTER-like, ModelElimination, TFMResolution) ne reimplémentent pas un proveur :
/// elles anchorient les phrases sur le domaine fini (FORALL en conjonction,
/// EXISTS en disjonction) et deleguent la decision de satisfiabilite au
/// veritable solveur du sous-module, en retour duquel la question devient :
/// KB ET NON(question) insatisfiable ?
/// </remarks>
public static class FolInference
{
    /// <summary>Chainage avant : Modus Ponens generalise jusqu'a point fixe (AIMA ch. 9).</summary>
    /// <remarks>Cout mesure : faits ajoutes avant stabilite de l'agenda.</remarks>
    public static FolAskResult FcEntails(FolKnowledgeBase kb, FolFormula.Predicate query)
    {
        ArgumentNullException.ThrowIfNull(kb);
        ArgumentNullException.ThrowIfNull(query);

        List<FolDefiniteClause> rules = kb.DefiniteClauses().Where(c => c.Premises.Count > 0).ToList();
        List<FolFormula.Predicate> facts = kb.DefiniteClauses().Where(c => c.Premises.Count == 0)
            .Select(c => c.Head).ToList();

        int added = 0;
        bool progressed = true;
        while (progressed)
        {
            progressed = false;
            foreach (FolDefiniteClause rule in rules)
            {
                if (MatchPremises(rule.Premises, facts, new Substitution()) is { } theta
                    && Unify.Apply(rule.Head, theta) is FolFormula.Predicate derived
                    && facts.All(f => Unify.TryUnifyTerms(f, derived) is null))
                {
                    facts.Add(derived);
                    added++;
                    progressed = true;
                }
            }
        }

        bool entailed = facts.Any(f => Unify.TryUnifyTerms(f, query) is not null);
        return new FolAskResult(entailed, added, "faits ajoutes par Modus Ponens generalise");
    }

    /// <summary>Chainage arriere : recherche ET-OU sur les buts (AIMA ch. 9).</summary>
    /// <remarks>
    /// Cout mesure : sous-buts explores. Chaque clause est standardisee a part a
    /// chaque application (compteur unique par question) et la substitution
    /// composee d'une premisse satisfaite reflue vers les suivantes. Un but sol
    /// deja present sur la branche courante echoue (garde anti-cycles) ; une
    /// borne de profondeur termine les cycles par variables, qui ne sont pas
    /// detectables par la garde. La borne (16) est un NON-DEMO au-dela, pas une
    /// lenteur : une preuve plus profonde rend faux alors que l'ancrage Z3
    /// demontre -- le desaccord est epingle par le temoin
    /// <c>ChaineProfonde_LeCapDeProfondeurDuBCProvoqueLeDesaccordDocumente</c>
    /// (revue Hermes #24324, point 2).
    /// </remarks>
    public static FolAskResult BcEntails(FolKnowledgeBase kb, FolFormula.Predicate query)
    {
        ArgumentNullException.ThrowIfNull(kb);
        ArgumentNullException.ThrowIfNull(query);

        int[] explored = { 0 };
        int[] renames = { 0 };
        bool entailed = SatisfyGoal(kb, query, new Substitution(), explored, renames, depth: 0,
            ancestors: new HashSet<string>(StringComparer.Ordinal)) is not null;
        return new FolAskResult(entailed, explored[0], "sous-buts explores");
    }

    private const int MaxDepth = 16;

    /// <summary>Rend la substitution composee si le but est prouve, null sinon.</summary>
    private static Substitution? SatisfyGoal(
        FolKnowledgeBase kb,
        FolFormula.Predicate goal,
        Substitution theta,
        int[] explored,
        int[] renames,
        int depth,
        HashSet<string> ancestors)
    {
        if (depth > MaxDepth)
        {
            return null;
        }

        FolFormula.Predicate instance = (FolFormula.Predicate)Unify.Apply(goal, theta);
        bool ground = instance.Arguments.All(argument => argument is FolTerm.Constant);
        string? key = ground ? instance.ToString() : null;
        if (key is not null && !ancestors.Add(key))
        {
            // But sol deja en cours de preuve sur cette branche : cycle.
            return null;
        }

        try
        {
            explored[0]++;
            foreach (FolDefiniteClause clause in kb.DefiniteClauses())
            {
                FolDefiniteClause fresh = StandardizeApart(clause, renames);
                Substitution extended = theta.Clone();
                if (!Unify.TryUnifyTerms(fresh.Head, instance, extended))
                {
                    continue;
                }

                if (SatisfyPremises(kb, fresh.Premises, 0, extended, explored, renames, depth + 1, ancestors)
                    is { } composed)
                {
                    return composed;
                }
            }

            return null;
        }
        finally
        {
            if (key is not null)
            {
                ancestors.Remove(key);
            }
        }
    }

    private static Substitution? SatisfyPremises(
        FolKnowledgeBase kb,
        IReadOnlyList<FolFormula.Predicate> premises,
        int index,
        Substitution theta,
        int[] explored,
        int[] renames,
        int depth,
        HashSet<string> ancestors)
    {
        if (index == premises.Count)
        {
            return theta;
        }

        if (depth > MaxDepth)
        {
            return null;
        }

        return SatisfyGoal(kb, premises[index], theta, explored, renames, depth, ancestors) is { } withBindings
            ? SatisfyPremises(kb, premises, index + 1, withBindings, explored, renames, depth, ancestors)
            : null;
    }

    /// <summary>
    /// Question FOL par ancrage sur le domaine fini et decision Z3.Linq.
    /// </summary>
    /// <remarks>
    /// Chaque quantificateur devient une iteration sur les constantes du domaine,
    /// chaque atome un booleen symbolique du theorem ; Z3 decide si
    /// KB ET NON(question) est insatisfiable. Les variables libres de la question
    /// sont quantifiees existentiellement : la question demontree est
    /// « existe-t-il une instance de la question que la KB implique ».
    /// Cout mesure : atomes ancres + contraintes posees.
    /// Limite honnete : phrases relationnelles (termes = variables ou constantes).
    /// </remarks>
    public static FolAskResult Z3Entails(FolKnowledgeBase kb, FolFormula query)
    {
        ArgumentNullException.ThrowIfNull(kb);
        ArgumentNullException.ThrowIfNull(query);

        if (kb.Domain.Constants.Count == 0)
        {
            throw new InvalidOperationException(
                "L'ancrage Z3 exige un domaine fini non vide : declarer les constantes du domaine.");
        }

        Grounding grounding = new(kb.Domain);
        grounding.ValidateDeclaredConstants(kb.Sentences, query);
        List<Expression<Func<FolGrounding, bool>>> constraints = new();
        foreach (FolFormula sentence in kb.Sentences)
        {
            constraints.Add(BuildConstraint(sentence, grounding));
        }

        constraints.Add(BuildConstraint(NegateWithFreeExistentials(query), grounding));

        using Z3Context context = new();
        Theorem<FolGrounding> theorem =
            context.NewTheorem(new FolGrounding { Atoms = new bool[grounding.AtomCount] });
        foreach (Expression<Func<FolGrounding, bool>> constraint in constraints)
        {
            theorem = theorem.Where(constraint);
        }

        bool counterModelExists = theorem.TrySolve(out FolGrounding? _);
        return new FolAskResult(
            !counterModelExists,
            grounding.AtomCount + constraints.Count,
            "atomes ancres + contraintes posees");
    }

    /// <summary>
    /// Enumeration naive sur toutes les affectations des atomes ancres : la
    /// verification independante du pont Z3, et la baseline de la mesure de
    /// discrimination. Cout mesure : affectations essayees.
    /// </summary>
    public static FolAskResult NaiveEntails(FolKnowledgeBase kb, FolFormula query)
    {
        ArgumentNullException.ThrowIfNull(kb);
        ArgumentNullException.ThrowIfNull(query);

        Grounding grounding = new(kb.Domain);
        grounding.ValidateDeclaredConstants(kb.Sentences, query);
        FolFormula target = CloseExistentially(query);
        int atomCount = grounding.ProbeAtomCount(kb.Sentences, target);
        // Seuil recalibre a 24 atomes (revue Hermes #24324, point 3) : au-dela de
        // 2^24 affectations (~40 s au plafond, mesure 2^20 = 2,4 s), la baseline
        // coute plus cher que la decision Z3 qu'elle est censee verifier.
        if (atomCount > 24)
        {
            throw new InvalidOperationException(
                $"L'enumeration naive exige au plus 24 atomes ancres (trouves : {atomCount}) : "
                + "au-dela, la decision Z3 reste le seul chemin praticable.");
        }

        long tried = 0;
        for (long mask = 0; mask < 1L << atomCount; mask++)
        {
            bool[] assignment = new bool[atomCount];
            for (int bit = 0; bit < atomCount; bit++)
            {
                assignment[bit] = (mask & (1L << bit)) != 0;
            }

            tried++;
            bool kbHolds = kb.Sentences.Count == 0 || kb.Sentences.All(sentence =>
                EvaluateGround(sentence, grounding, new Dictionary<string, string>(), assignment));
            if (kbHolds
                && !EvaluateGround(target, grounding, new Dictionary<string, string>(), assignment))
            {
                // Modele de KB ET NON(query) : la question n'est pas demontree.
                return new FolAskResult(false, tried, "affectations essayees");
            }
        }

        return new FolAskResult(true, tried, "affectations essayees");
    }

    /// <summary>Uniformise les appels : chaque procedure de l'enum a son entree ici.</summary>
    public static FolAskResult Ask(FolKnowledgeBase kb, FolFormula query) =>
        kb.Procedure switch
        {
            FolInferenceProcedure.FCAsk => FcEntails(kb, AsPredicate(query, "FCAsk")),
            FolInferenceProcedure.BCAsk => BcEntails(kb, AsPredicate(query, "BCAsk")),
            FolInferenceProcedure.OTTERLikeTheoremProver
                or FolInferenceProcedure.ModelElimination
                or FolInferenceProcedure.TFMResolution => Z3Entails(kb, query),
            _ => throw new ArgumentOutOfRangeException(nameof(kb), $"Procedure inconnue : {kb.Procedure}"),
        };

    private static FolFormula.Predicate AsPredicate(FolFormula query, string procedure)
    {
        if (query is not FolFormula.Predicate predicate)
        {
            throw new ArgumentException(
                $"{procedure} exige un atome en question ; pour une formule composee, utiliser l'ancrage Z3.");
        }

        return predicate;
    }

    private static FolFormula CloseExistentially(FolFormula formula)
    {
        FolFormula closed = formula;
        foreach (string variable in formula.FreeVariables())
        {
            closed = new FolFormula.Exists(variable, closed);
        }

        return closed;
    }

    private static FolFormula NegateWithFreeExistentials(FolFormula query) =>
        new FolFormula.Not(CloseExistentially(query));

    /// <summary>Apparie recursivement les premisses d'une clause contre les faits connus.</summary>
    private static Substitution? MatchPremises(
        IReadOnlyList<FolFormula.Predicate> premises,
        List<FolFormula.Predicate> facts,
        Substitution theta)
    {
        if (premises.Count == 0)
        {
            return theta;
        }

        FolFormula.Predicate premise = (FolFormula.Predicate)Unify.Apply(premises[0], theta);
        foreach (FolFormula.Predicate fact in facts)
        {
            Substitution extended = theta.Clone();
            if (Unify.TryUnifyTerms(fact, premise, extended)
                && MatchPremises(premises.Skip(1).ToArray(), facts, extended) is { } composed)
            {
                return composed;
            }
        }

        return null;
    }

    private static FolDefiniteClause StandardizeApart(FolDefiniteClause clause, int[] renames)
    {
        string suffix = "/" + renames[0]++;
        FolTerm Rename(FolTerm term) => term switch
        {
            FolTerm.Variable v => new FolTerm.Variable(v.Name + suffix),
            FolTerm.FunctionApplication f => new FolTerm.FunctionApplication(
                f.Name, f.Arguments.Select(Rename).ToArray()),
            _ => term,
        };

        FolFormula.Predicate RenameAtom(FolFormula.Predicate atom) =>
            new(atom.Name, atom.Arguments.Select(Rename).ToArray());

        return new FolDefiniteClause(clause.Premises.Select(RenameAtom).ToArray(), RenameAtom(clause.Head));
    }

    // ------------------------------------------------------------------
    // Ancrage domaine fini -> contraintes booleennes (pont Z3 et enumeration naive).
    // ------------------------------------------------------------------

    /// <summary>Environnement du theorem Z3 : un booleen par atome ancre.</summary>
    public sealed class FolGrounding
    {
        /// <summary>Atomes ancres ; la taille fixe le tableau symbolique Z3.</summary>
        public bool[] Atoms { get; set; } = Array.Empty<bool>();
    }

    /// <summary>Table des atomes ancres : (predicat, arguments canoniques) -> indice.</summary>
    private sealed class Grounding
    {
        private readonly Dictionary<string, int> atomIndices = new(StringComparer.Ordinal);
        private readonly FolDomain domain;

        public Grounding(FolDomain domain) => this.domain = domain;

        public int AtomCount => this.atomIndices.Count;

        public IEnumerable<string> DomainConstants() => this.domain.Constants;

        /// <summary>
        /// Garde de l'ancrage (revue Hermes #24324, point 1) : les quantificateurs
        /// iterent les constantes declarees, donc une constante non declaree y est
        /// invisible -- refuser ici plutot que d'ancrer une phrase amputee.
        /// </summary>
        public void ValidateDeclaredConstants(IReadOnlyList<FolFormula> sentences, FolFormula query)
        {
            HashSet<string> declared = new(this.domain.Constants, StringComparer.Ordinal);
            foreach (FolFormula sentence in sentences.Append(query))
            {
                foreach (string constant in sentence.AllConstants())
                {
                    if (!declared.Contains(constant))
                    {
                        throw new InvalidOperationException(
                            $"La constante '{constant}' de la phrase {sentence} n'est pas declaree au domaine : "
                            + $"l'ancrage itererait les quantificateurs sans jamais la couvrir. Ajouter AddConstant(\"{constant}\").");
                    }
                }
            }
        }

        public int IndexOf(string predicateName, IReadOnlyList<FolTerm> arguments)
        {
            string canonical = predicateName + "(" + string.Join(",", arguments.Select(TermKey)) + ")";
            if (!this.atomIndices.TryGetValue(canonical, out int index))
            {
                index = this.atomIndices.Count;
                this.atomIndices[canonical] = index;
            }

            return index;
        }

        /// <summary>Numérote tous les atomes des phrases et de la question sans poser de contrainte.</summary>
        public int ProbeAtomCount(IReadOnlyList<FolFormula> sentences, FolFormula closedQuery)
        {
            foreach (FolFormula sentence in sentences)
            {
                Probe(sentence, new Dictionary<string, string>());
            }

            Probe(closedQuery, new Dictionary<string, string>());
            return this.atomIndices.Count;
        }

        private void Probe(FolFormula formula, IReadOnlyDictionary<string, string> binding)
        {
            switch (formula)
            {
                case FolFormula.ForAll f:
                    foreach (string constant in this.domain.Constants)
                    {
                        Probe(f.Body, Extended(binding, f.Variable, constant));
                    }

                    break;
                case FolFormula.Exists e:
                    foreach (string constant in this.domain.Constants)
                    {
                        Probe(e.Body, Extended(binding, e.Variable, constant));
                    }

                    break;
                case FolFormula.Not n:
                    Probe(n.Operand, binding);
                    break;
                case FolFormula.And a:
                    Probe(a.Left, binding);
                    Probe(a.Right, binding);
                    break;
                case FolFormula.Or o:
                    Probe(o.Left, binding);
                    Probe(o.Right, binding);
                    break;
                case FolFormula.Implies i:
                    Probe(i.Left, binding);
                    Probe(i.Right, binding);
                    break;
                case FolFormula.Biconditional b:
                    Probe(b.Left, binding);
                    Probe(b.Right, binding);
                    break;
                case FolFormula.Predicate p:
                    IndexOfAtom(p, binding);
                    break;
            }
        }

        private int IndexOfAtom(FolFormula.Predicate predicate, IReadOnlyDictionary<string, string> binding)
        {
            List<FolTerm> arguments = new();
            foreach (FolTerm argument in predicate.Arguments)
            {
                if (argument is FolTerm.Variable v)
                {
                    if (!binding.TryGetValue(v.Name, out string? constant))
                    {
                        throw new InvalidOperationException(
                            $"Variable libre '{v.Name}' dans l'atome {predicate.Name} : la phrase doit etre fermee.");
                    }

                    arguments.Add(new FolTerm.Constant(constant));
                }
                else
                {
                    arguments.Add(argument);
                }
            }

            return this.IndexOf(predicate.Name, arguments);
        }

        private static IReadOnlyDictionary<string, string> Extended(
            IReadOnlyDictionary<string, string> binding, string variable, string constant)
        {
            Dictionary<string, string> extended = new(binding) { [variable] = constant };
            return extended;
        }

        private static string TermKey(FolTerm term) => term switch
        {
            FolTerm.Variable v => v.Name,
            FolTerm.Constant c => c.Name,
            FolTerm.FunctionApplication => throw new InvalidOperationException(
                "L'ancrage sur domaine fini porte des phrases relationnelles : les fonctions ne sont pas ancrees "
                + "(utiliser FCAsk/BCAsk)."),
            _ => throw new InvalidOperationException($"Terme inconnu : {term.GetType().Name}"),
        };
    }

    private static Expression<Func<FolGrounding, bool>> BuildConstraint(FolFormula formula, Grounding grounding)
    {
        ParameterExpression theorem = Expression.Parameter(typeof(FolGrounding), "t");
        Expression body = Ground(formula, grounding, new Dictionary<string, string>(), theorem);
        return Expression.Lambda<Func<FolGrounding, bool>>(body, theorem);
    }

    private static Expression Ground(
        FolFormula formula,
        Grounding grounding,
        IReadOnlyDictionary<string, string> binding,
        ParameterExpression theorem)
    {
        return formula switch
        {
            FolFormula.ForAll f => GroundQuantified(f.Body, f.Variable, grounding, binding, theorem, universal: true),
            FolFormula.Exists e => GroundQuantified(e.Body, e.Variable, grounding, binding, theorem, universal: false),
            FolFormula.Not n => Expression.Not(Ground(n.Operand, grounding, binding, theorem)),
            FolFormula.And a => Expression.AndAlso(
                Ground(a.Left, grounding, binding, theorem), Ground(a.Right, grounding, binding, theorem)),
            FolFormula.Or o => Expression.OrElse(
                Ground(o.Left, grounding, binding, theorem), Ground(o.Right, grounding, binding, theorem)),
            FolFormula.Implies i => Expression.Or(
                Expression.Not(Ground(i.Left, grounding, binding, theorem)),
                Ground(i.Right, grounding, binding, theorem)),
            FolFormula.Biconditional b => Expression.Equal(
                Ground(b.Left, grounding, binding, theorem), Ground(b.Right, grounding, binding, theorem)),
            FolFormula.Predicate p => AtomExpression(p, grounding, binding, theorem),
            _ => throw new InvalidOperationException($"Formule inconnue : {formula.GetType().Name}"),
        };
    }

    private static Expression GroundQuantified(
        FolFormula body,
        string variable,
        Grounding grounding,
        IReadOnlyDictionary<string, string> binding,
        ParameterExpression theorem,
        bool universal)
    {
        Expression? accumulator = null;
        foreach (string constant in grounding.DomainConstants())
        {
            Dictionary<string, string> extended = new(binding) { [variable] = constant };
            Expression instance = Ground(body, grounding, extended, theorem);
            accumulator = accumulator is null
                ? instance
                : universal
                    ? Expression.AndAlso(accumulator, instance)
                    : Expression.OrElse(accumulator, instance);
        }

        return accumulator ?? Expression.Constant(universal);
    }

    private static Expression AtomExpression(
        FolFormula.Predicate predicate,
        Grounding grounding,
        IReadOnlyDictionary<string, string> binding,
        ParameterExpression theorem)
    {
        int index = IndexOfGroundAtom(predicate, grounding, binding);
        Expression atoms = Expression.Property(theorem, nameof(FolGrounding.Atoms));
        return Expression.ArrayIndex(atoms, Expression.Constant(index));
    }

    private static bool EvaluateGround(
        FolFormula formula,
        Grounding grounding,
        IReadOnlyDictionary<string, string> binding,
        bool[] assignment)
    {
        return formula switch
        {
            FolFormula.ForAll f => grounding.DomainConstants().All(constant =>
                EvaluateGround(f.Body, grounding, ExtendedBinding(binding, f.Variable, constant), assignment)),
            FolFormula.Exists e => grounding.DomainConstants().Any(constant =>
                EvaluateGround(e.Body, grounding, ExtendedBinding(binding, e.Variable, constant), assignment)),
            FolFormula.Not n => !EvaluateGround(n.Operand, grounding, binding, assignment),
            FolFormula.And a => EvaluateGround(a.Left, grounding, binding, assignment)
                && EvaluateGround(a.Right, grounding, binding, assignment),
            FolFormula.Or o => EvaluateGround(o.Left, grounding, binding, assignment)
                || EvaluateGround(o.Right, grounding, binding, assignment),
            FolFormula.Implies i => !EvaluateGround(i.Left, grounding, binding, assignment)
                || EvaluateGround(i.Right, grounding, binding, assignment),
            FolFormula.Biconditional b => EvaluateGround(b.Left, grounding, binding, assignment)
                == EvaluateGround(b.Right, grounding, binding, assignment),
            FolFormula.Predicate p => assignment[IndexOfGroundAtom(p, grounding, binding)],
            _ => throw new InvalidOperationException($"Formule inconnue : {formula.GetType().Name}"),
        };
    }

    private static IReadOnlyDictionary<string, string> ExtendedBinding(
        IReadOnlyDictionary<string, string> binding, string variable, string constant)
    {
        Dictionary<string, string> extended = new(binding) { [variable] = constant };
        return extended;
    }

    private static int IndexOfGroundAtom(
        FolFormula.Predicate predicate,
        Grounding grounding,
        IReadOnlyDictionary<string, string> binding)
    {
        List<FolTerm> arguments = new();
        foreach (FolTerm argument in predicate.Arguments)
        {
            if (argument is FolTerm.Variable v)
            {
                if (!binding.TryGetValue(v.Name, out string? constant))
                {
                    throw new InvalidOperationException(
                        $"Variable libre '{v.Name}' dans l'atome {predicate.Name} : la phrase doit etre fermee.");
                }

                arguments.Add(new FolTerm.Constant(constant));
            }
            else
            {
                arguments.Add(argument);
            }
        }

        return grounding.IndexOf(predicate.Name, arguments);
    }
}

/// <summary>Substitution variables -> termes, et unification AIMA (avec occurs check).</summary>
public static class Unify
{
    /// <summary>Unifie deux atomes dans une substitution neuve ; rend null si aucun unificateur.</summary>
    public static Substitution? TryUnifyTerms(FolFormula.Predicate left, FolFormula.Predicate right)
    {
        Substitution theta = new();
        return TryUnifyTerms(left, right, theta) ? theta : null;
    }

    /// <summary>Unifie deux atomes en etendant la substitution donnee ; rend faux en cas d'echec.</summary>
    public static bool TryUnifyTerms(FolFormula.Predicate left, FolFormula.Predicate right, Substitution theta)
    {
        if (!string.Equals(left.Name, right.Name, StringComparison.Ordinal)
            || left.Arguments.Count != right.Arguments.Count)
        {
            return false;
        }

        for (int i = 0; i < left.Arguments.Count; i++)
        {
            if (!UnifyTerms(Apply(left.Arguments[i], theta), Apply(right.Arguments[i], theta), theta))
            {
                return false;
            }
        }

        return true;
    }

    /// <summary>Unifie deux termes en etendant la substitution ; rend faux en cas d'echec.</summary>
    public static bool UnifyTerms(FolTerm left, FolTerm right, Substitution theta)
    {
        if (theta.Lookup(left) is { } boundLeft)
        {
            return UnifyTerms(boundLeft, right, theta);
        }

        if (theta.Lookup(right) is { } boundRight)
        {
            return UnifyTerms(left, boundRight, theta);
        }

        switch (left, right)
        {
            case (FolTerm.Variable lv, FolTerm.Variable rv) when lv.Name == rv.Name:
                return true;
            case (FolTerm.Variable lv, _):
                return !Occurs(lv.Name, right) && theta.Bind(lv.Name, right);
            case (_, FolTerm.Variable rv):
                return !Occurs(rv.Name, left) && theta.Bind(rv.Name, left);
            case (FolTerm.Constant lc, FolTerm.Constant rc):
                return string.Equals(lc.Name, rc.Name, StringComparison.Ordinal);
            case (FolTerm.FunctionApplication lf, FolTerm.FunctionApplication rf)
                when string.Equals(lf.Name, rf.Name, StringComparison.Ordinal)
                    && lf.Arguments.Count == rf.Arguments.Count:
            {
                for (int i = 0; i < lf.Arguments.Count; i++)
                {
                    if (!UnifyTerms(Apply(lf.Arguments[i], theta), Apply(rf.Arguments[i], theta), theta))
                    {
                        return false;
                    }
                }

                return true;
            }

            default:
                return false;
        }
    }

    private static bool Occurs(string variable, FolTerm term) =>
        term.Variables().Contains(variable);

    /// <summary>Applique la substitution a un terme.</summary>
    public static FolTerm Apply(FolTerm term, Substitution theta)
    {
        while (term is FolTerm.Variable v && theta.Lookup(v) is { } bound)
        {
            term = bound;
        }

        return term is FolTerm.FunctionApplication f
            ? new FolTerm.FunctionApplication(f.Name, f.Arguments.Select(argument => Apply(argument, theta)).ToArray())
            : term;
    }

    /// <summary>Applique la substitution a une formule (termes des atomes).</summary>
    public static FolFormula Apply(FolFormula formula, Substitution theta) => formula switch
    {
        FolFormula.Predicate p => new FolFormula.Predicate(p.Name, p.Arguments.Select(t => Apply(t, theta)).ToArray()),
        FolFormula.Not n => new FolFormula.Not(Apply(n.Operand, theta)),
        FolFormula.And a => new FolFormula.And(Apply(a.Left, theta), Apply(a.Right, theta)),
        FolFormula.Or o => new FolFormula.Or(Apply(o.Left, theta), Apply(o.Right, theta)),
        FolFormula.Implies i => new FolFormula.Implies(Apply(i.Left, theta), Apply(i.Right, theta)),
        FolFormula.Biconditional b => new FolFormula.Biconditional(Apply(b.Left, theta), Apply(b.Right, theta)),
        FolFormula.ForAll f => new FolFormula.ForAll(f.Variable, Apply(f.Body, theta)),
        FolFormula.Exists e => new FolFormula.Exists(e.Variable, Apply(e.Body, theta)),
        _ => throw new InvalidOperationException($"Formule inconnue : {formula.GetType().Name}"),
    };
}

/// <summary>Substitution : dictionnaire variable -> terme, avec resolution des chaines.</summary>
public sealed class Substitution
{
    private readonly Dictionary<string, FolTerm> bindings = new(StringComparer.Ordinal);

    /// <summary>Etend la substitution : la variable ne doit pas deja etre liee dans la chaine courante.</summary>
    public bool Bind(string variable, FolTerm term)
    {
        this.bindings[variable] = term;
        return true;
    }

    /// <summary>Cherche le terme lie a une variable, en suivant les chaines.</summary>
    public FolTerm? Lookup(FolTerm term) =>
        term is FolTerm.Variable v && this.bindings.TryGetValue(v.Name, out FolTerm? bound) ? bound : null;

    /// <summary>Copie la substitution : la composition du chainage arriere part de l'externe deja liee.</summary>
    public Substitution Clone()
    {
        Substitution clone = new();
        foreach (KeyValuePair<string, FolTerm> pair in this.bindings)
        {
            clone.bindings[pair.Key] = pair.Value;
        }

        return clone;
    }

    /// <summary>Representation de la substitution pour les temoins de test.</summary>
    public override string ToString() =>
        "{" + string.Join(", ", this.bindings.OrderBy(pair => pair.Key, StringComparer.Ordinal)
            .Select(pair => $"{pair.Key} -> {pair.Value}")) + "}";
}
