using MyIA.AI.Shared.Search.Logic.Propositional;
using Xunit;
using Xunit.Abstractions;

namespace MyIA.AI.Shared.Tests.Search.Logic;

/// <summary>
/// Temoins des six procedures d'inference propositionnelle
/// (EPIC #7265, volet B2 tranche 1, issue #23584).
/// </summary>
/// <remarks>
/// Les instances de reference sont celles du chapitre 7 d'AIMA. Les procedures ne
/// sont pas seulement verifiees correctes : elles sont verifiees <i>falsifiables
/// entre elles</i>, sur la meme instance, avec des couts mesures et des unites
/// distinctes.
/// </remarks>
public sealed class PlInferenceTests
{
    private readonly ITestOutputHelper _output;

    public PlInferenceTests(ITestOutputHelper output) => _output = output;

    /// <summary>Base du chapitre 7 d'AIMA : <c>{~A | B, A}</c>.</summary>
    private static PlKnowledgeBase AimaChapter7() =>
        new PlKnowledgeBase()
            .Tell("~A | B")
            .Tell("A");

    /// <summary>Chaine d'implications sans cycle : <c>{(A|B), (~A|C), (~B|C), (~C|D)}</c>.</summary>
    private static PlKnowledgeBase Chained() =>
        new PlKnowledgeBase()
            .Tell("A | B")
            .Tell("~A | C")
            .Tell("~B | C")
            .Tell("~C | D");

    [Fact]
    public void AimaChapitre7_LaBaseImpliqueLePredicat()
    {
        PlKnowledgeBase knowledgeBase = AimaChapter7();
        PlFormula query = PlParser.Parse("B");

        Assert.Equal(PlVerdict.Yes, PlInference.TtEntails(knowledgeBase, query).Verdict);
        Assert.Equal(PlVerdict.Yes, PlInference.Resolve(knowledgeBase, query).Verdict);
        Assert.Equal(PlVerdict.Yes, PlInference.DpllEntails(knowledgeBase, query).Verdict);
    }

    [Fact]
    public void AimaChapitre7_LaBaseNImpliquePasUnSymboleAbsent()
    {
        PlKnowledgeBase knowledgeBase = AimaChapter7();
        PlFormula query = PlParser.Parse("C");

        Assert.Equal(PlVerdict.No, PlInference.TtEntails(knowledgeBase, query).Verdict);
        Assert.Equal(PlVerdict.No, PlInference.Resolve(knowledgeBase, query).Verdict);
        Assert.Equal(PlVerdict.No, PlInference.DpllEntails(knowledgeBase, query).Verdict);
    }

    [Fact]
    public void DisjonctionSeule_NAppliquePasSesTermes()
    {
        // A | B est vraie sans que A le soit : la base n'implique pas A.
        PlKnowledgeBase knowledgeBase = new PlKnowledgeBase().Tell("A | B");

        Assert.Equal(PlVerdict.No, PlInference.DpllEntails(knowledgeBase, PlParser.Parse("A")).Verdict);
    }

    [Fact]
    public void DpllSatisfiable_RendUnModeleQuiSatisfaitVraimentLaBase()
    {
        PlKnowledgeBase knowledgeBase = Chained();

        PlInferenceResult result = PlInference.DpllSatisfiable(knowledgeBase);

        Assert.Equal(PlVerdict.Yes, result.Verdict);
        Assert.NotNull(result.Model);
        Assert.True(
            knowledgeBase.IsSatisfiedBy(result.Model!),
            "le modele rendu doit satisfaire la base, pas seulement etre annonce satisfaisant");
    }

    [Fact]
    public void DpllSatisfiable_DetecteLInsatisfiabiliteTroisClauses()
    {
        // Temoin a trois clauses d'AIMA : {A, ~A | B, ~B}. La propagation unitaire suffit.
        PlKnowledgeBase knowledgeBase = new PlKnowledgeBase()
            .Tell("A")
            .Tell("~A | B")
            .Tell("~B");

        PlInferenceResult result = PlInference.DpllSatisfiable(knowledgeBase);

        Assert.Equal(PlVerdict.No, result.Verdict);
        Assert.Null(result.Model);
    }

    [Fact]
    public void DpllSatisfiable_DetecteLInsatisfiabiliteSansClauseUnitaire()
    {
        // Les quatre clauses complementaires : insatisfiable, sans aucune clause unitaire,
        // donc DPLL doit prendre de vraies decisions.
        PlKnowledgeBase knowledgeBase = new PlKnowledgeBase()
            .Tell("A | B")
            .Tell("~A | B")
            .Tell("A | ~B")
            .Tell("~A | ~B");

        PlInferenceResult result = PlInference.DpllSatisfiable(knowledgeBase);

        Assert.Equal(PlVerdict.No, result.Verdict);
        Assert.True(result.Steps >= 1, "l'instance exige au moins une decision DPLL");
    }

    [Fact]
    public void LaChaineImpliqueD()
    {
        PlKnowledgeBase knowledgeBase = Chained();
        PlFormula query = PlParser.Parse("D");

        Assert.Equal(PlVerdict.Yes, PlInference.TtEntails(knowledgeBase, query).Verdict);
        Assert.Equal(PlVerdict.Yes, PlInference.Resolve(knowledgeBase, query).Verdict);
        Assert.Equal(PlVerdict.Yes, PlInference.DpllEntails(knowledgeBase, query).Verdict);
    }

    [Fact]
    public void WalkSat_RendUnknownSurUneInstanceInsatisfiable()
    {
        // Une recherche locale qui echoue ne prouve pas l'insatisfiabilite : le verdict
        // doit rester Unknown. Rendre No serait une affirmation non mesuree.
        PlKnowledgeBase knowledgeBase = new PlKnowledgeBase()
            .Tell("A")
            .Tell("~A");

        PlInferenceResult result = PlInference.WalkSatKb(knowledgeBase, maxFlips: 200, seed: 7);

        Assert.Equal(PlVerdict.Unknown, result.Verdict);
        Assert.False(result.IsConclusive);
        Assert.Null(result.Model);
    }

    [Fact]
    public void WalkSatPredicate_RendUnModeleQuiSatisfaitBaseEtRequete()
    {
        PlKnowledgeBase knowledgeBase = Chained();
        PlFormula query = PlParser.Parse("D");

        PlInferenceResult result = PlInference.WalkSatPredicate(knowledgeBase, query, maxFlips: 2000, seed: 3);

        Assert.Equal(PlVerdict.Yes, result.Verdict);
        Assert.NotNull(result.Model);
        Assert.True(knowledgeBase.IsSatisfiedBy(result.Model!));
        Assert.True(query.Evaluate(result.Model!));
    }

    [Fact]
    public void WalkSat_EstReproductibleALaMemeGraine()
    {
        PlKnowledgeBase knowledgeBase = Chained();

        PlInferenceResult first = PlInference.WalkSatKb(knowledgeBase, maxFlips: 500, seed: 42);
        PlInferenceResult second = PlInference.WalkSatKb(knowledgeBase, maxFlips: 500, seed: 42);

        Assert.Equal(first.Verdict, second.Verdict);
        Assert.Equal(first.Steps, second.Steps);
    }

    [Fact]
    public void LesTroisProceduresCompletesConcordentSurChaqueInstance()
    {
        // Falsifiabilite croisee : aucune procedure complete ne doit contredire les autres.
        (string Base, string Query, PlVerdict Expected)[] instances =
        {
            ("~A | B", "A => B", PlVerdict.Yes),
            ("A & B", "A", PlVerdict.Yes),
            ("A | B", "A", PlVerdict.No),
            ("A => B", "~B => ~A", PlVerdict.Yes),
            ("A <=> B", "A => B", PlVerdict.Yes),
            ("(A | B) & (~A | C) & (~B | C) & (~C | D)", "D", PlVerdict.Yes),
        };

        foreach ((string baseSource, string querySource, PlVerdict expected) in instances)
        {
            PlKnowledgeBase knowledgeBase = new PlKnowledgeBase().Tell(baseSource);
            PlFormula query = PlParser.Parse(querySource);

            PlInferenceResult truthTable = PlInference.TtEntails(knowledgeBase, query);
            PlInferenceResult resolution = PlInference.Resolve(knowledgeBase, query);
            PlInferenceResult dpll = PlInference.DpllEntails(knowledgeBase, query);

            _output.WriteLine($"base={baseSource} | requete={querySource} -> {truthTable.Verdict}/{resolution.Verdict}/{dpll.Verdict}");

            Assert.Equal(expected, truthTable.Verdict);
            Assert.Equal(expected, resolution.Verdict);
            Assert.Equal(expected, dpll.Verdict);
        }
    }

    [Fact]
    public void DiscriminationMesuree_LesProceduresDifferentParLeurCoutPasParLeurVerdict()
    {
        // Une instance ou les quatre procedures concluent, avec des couts dans des unites
        // differentes : c'est ce qui rend la tranche falsifiable entre procedures, et pas
        // seulement correcte.
        PlKnowledgeBase knowledgeBase = Chained();
        PlFormula query = PlParser.Parse("D");

        PlInferenceResult truthTable = PlInference.TtEntails(knowledgeBase, query);
        PlInferenceResult resolution = PlInference.Resolve(knowledgeBase, query);
        PlInferenceResult dpll = PlInference.DpllEntails(knowledgeBase, query);
        PlInferenceResult walkSat = PlInference.WalkSatPredicate(knowledgeBase, query, maxFlips: 2000, seed: 11);

        _output.WriteLine("procedure | verdict | pas | unite");
        _output.WriteLine($"{truthTable.Procedure} | {truthTable.Verdict} | {truthTable.Steps} | {truthTable.StepUnit}");
        _output.WriteLine($"{resolution.Procedure} | {resolution.Verdict} | {resolution.Steps} | {resolution.StepUnit}");
        _output.WriteLine($"{dpll.Procedure} | {dpll.Verdict} | {dpll.Steps} | {dpll.StepUnit}");
        _output.WriteLine($"{walkSat.Procedure} | {walkSat.Verdict} | {walkSat.Steps} | {walkSat.StepUnit}");

        // 1. Meme verdict.
        Assert.Equal(PlVerdict.Yes, truthTable.Verdict);
        Assert.Equal(PlVerdict.Yes, resolution.Verdict);
        Assert.Equal(PlVerdict.Yes, dpll.Verdict);
        Assert.Equal(PlVerdict.Yes, walkSat.Verdict);

        // 2. Unites distinctes : sans elles, les couts ne seraient pas comparables.
        Assert.Equal("lignes de table de verite", truthTable.StepUnit);
        Assert.Equal("resolvantes derivees", resolution.StepUnit);
        Assert.Equal("tentatives de branchement DPLL", dpll.StepUnit);
        Assert.Equal("flips", walkSat.StepUnit);

        // 3. La table de verite paie l'exponentielle : 4 symboles, donc 16 lignes.
        Assert.Equal(16, truthTable.Steps);

        // 4. Les procedures dirigees paient strictement moins que l'enumeration.
        Assert.True(
            dpll.Steps < truthTable.Steps,
            $"DPLL ({dpll.Steps} decisions) doit couter moins que l'enumeration ({truthTable.Steps} lignes)");
        Assert.True(
            resolution.Steps <= truthTable.Steps,
            $"la resolution ({resolution.Steps} resolvantes) ne doit pas depasser l'enumeration");
        Assert.True(
            walkSat.Steps < truthTable.Steps,
            $"WalkSAT ({walkSat.Steps} flips) doit couter moins que l'enumeration sur une instance saine");

        // 5. Cout nul de DPLL, et sa raison : la negation de la requete est une clause
        //    unitaire (~D), qui propage D=false puis C=false, A=false et B=true jusqu'a
        //    la clause contradictoire. Aucune decision n'est necessaire.
        Assert.Equal(0, dpll.Steps);

        // 6. Pincage exact des deux couts restants de la table de mesures (15 resolvantes,
        //    1 flip) : procedures deterministes, WalkSAT seedee -- compteurs reproductibles.
        Assert.Equal(15, resolution.Steps);
        Assert.Equal(1, walkSat.Steps);
    }

    /// <summary>
    /// Instance a decisions reelles : trois pigeons, deux trous (PHP(3,2)), insatisfiable
    /// et sans propagation unitaire. C'est le temoin qui fait bouger le compteur de DPLL,
    /// la ou <see cref="Chained"/> le laissait a zero.
    /// </summary>
    private static PlKnowledgeBase Pigeonhole32()
    {
        PlKnowledgeBase knowledgeBase = new PlKnowledgeBase();

        // Chaque pigeon occupe au moins un trou.
        for (int pigeon = 0; pigeon < 3; pigeon++)
        {
            knowledgeBase.Tell($"P{pigeon}_0 | P{pigeon}_1");
        }

        // Deux pigeons ne partagent pas un trou.
        for (int hole = 0; hole < 2; hole++)
        {
            for (int first = 0; first < 3; first++)
            {
                for (int second = first + 1; second < 3; second++)
                {
                    knowledgeBase.Tell($"~P{first}_{hole} | ~P{second}_{hole}");
                }
            }
        }

        return knowledgeBase;
    }

    [Fact]
    public void DiscriminationMesuree_SurUneInstanceAvecDecisionsReelles()
    {
        // PHP(3,2) : 6 symboles, 9 clauses, insatisfiable. La table de verite coute 2^6,
        // DPLL doit decider, la resolution derive la clause vide.
        PlKnowledgeBase knowledgeBase = Pigeonhole32();
        PlFormula query = PlParser.Parse("P0_0");

        PlInferenceResult truthTable = PlInference.TtEntails(knowledgeBase, query);
        PlInferenceResult resolution = PlInference.Resolve(knowledgeBase, query);
        PlInferenceResult dpll = PlInference.DpllEntails(knowledgeBase, query);
        PlInferenceResult satisfiable = PlInference.DpllSatisfiable(knowledgeBase);

        _output.WriteLine("instance PHP(3,2) -- insatisfiable");
        _output.WriteLine($"{truthTable.Procedure} | {truthTable.Verdict} | {truthTable.Steps} | {truthTable.StepUnit}");
        _output.WriteLine($"{resolution.Procedure} | {resolution.Verdict} | {resolution.Steps} | {resolution.StepUnit}");
        _output.WriteLine($"{dpll.Procedure} | {dpll.Verdict} | {dpll.Steps} | {dpll.StepUnit}");
        _output.WriteLine($"{satisfiable.Procedure} | {satisfiable.Verdict} | {satisfiable.Steps} | {satisfiable.StepUnit}");

        // Une base insatisfiable implique n'importe quelle requete : les trois procedures
        // completes doivent le dire, et la satisfiabilite doit repondre non.
        Assert.Equal(PlVerdict.Yes, truthTable.Verdict);
        Assert.Equal(PlVerdict.Yes, resolution.Verdict);
        Assert.Equal(PlVerdict.Yes, dpll.Verdict);
        Assert.Equal(PlVerdict.No, satisfiable.Verdict);

        // La table de verite enumere les 2^6 affectations.
        Assert.Equal(64, truthTable.Steps);

        // DPLL conduit par la requete : la negation de la requete est une clause unitaire,
        // qui propage ~P0_0 a travers les 9 clauses jusqu'a la contradiction. Zero decision.
        Assert.Equal(0, dpll.Steps);

        // En revanche, la satisfiabilite de la base seule n'a aucune clause unitaire :
        // DPLL doit y decider, et c'est ce qui distingue les deux procedures DPLL.
        Assert.True(
            satisfiable.Steps >= 1,
            "PHP(3,2) sans clause unitaire doit faire decider DPLL au moins une fois");
        Assert.True(satisfiable.Steps < truthTable.Steps);

        // La resolution doit atteindre la clause vide, donc deriver au moins une resolvante.
        Assert.True(resolution.Steps >= 1, "la refutation doit deriver au moins la clause vide");

        // Pincage exact des deux couts restants de la table de mesures (63 resolvantes,
        // 2 decisions) : procedures deterministes -- compteurs reproductibles.
        Assert.Equal(63, resolution.Steps);
        Assert.Equal(2, satisfiable.Steps);
    }

    [Fact]
    public void TtEntails_RefuseUneInstanceTropGrandeAuLieuDeLaTronquer()
    {
        // 21 symboles = 2 097 152 lignes : la procedure le dit au lieu d'echouer en silence.
        PlKnowledgeBase knowledgeBase = new PlKnowledgeBase();
        List<string> symbols = new();

        for (int index = 0; index < 21; index++)
        {
            symbols.Add($"S{index}");
        }

        knowledgeBase.Tell(string.Join(" & ", symbols));

        Assert.Throws<InvalidOperationException>(() => PlInference.TtEntails(knowledgeBase, PlParser.Parse("S0")));
    }

    [Fact]
    public void IsSatisfiable_RendUnModeleTotalConsommableParLaBase()
    {
        // Repro de la reserve 1 de la review : DPLL n'assigne que A dans "B | A",
        // le modele rendu doit quand meme couvrir B, sinon IsSatisfiedBy leve.
        PlKnowledgeBase knowledgeBase = new PlKnowledgeBase().Tell("B | A");

        bool satisfiable = PlInference.IsSatisfiable(knowledgeBase.ToClauses(), out IReadOnlyDictionary<string, bool>? model);

        Assert.True(satisfiable);
        Assert.NotNull(model);
        Assert.True(
            knowledgeBase.IsSatisfiedBy(model!),
            "le modele rendu doit etre total et consumable par la base, pas seulement annoncer satisfiabilite");
        Assert.Contains("B", model!);
    }

    [Fact]
    public void TtEntails_RefuseUneBorneDepasseeAuLieuDeTronquerLaTable()
    {
        // Repro de la reserve 2 : maxSymbols: 32 sur 32 symboles tronquait la table
        // (le decalage d'un int est masque sur 5 bits, donc 1 << 32 == 1) et rendait
        // un verdict sur une seule ligne. La borne publique desormais refuse.
        PlKnowledgeBase knowledgeBase = new PlKnowledgeBase();
        List<string> symbols = new();

        for (int index = 0; index < 32; index++)
        {
            symbols.Add($"S{index}");
        }

        knowledgeBase.Tell(string.Join(" & ", symbols));

        Assert.Throws<ArgumentOutOfRangeException>(
            () => PlInference.TtEntails(knowledgeBase, PlParser.Parse("S0"), maxSymbols: 32));
    }

    [Fact]
    public void Resolve_RefuseUnBudgetNulDeResolvantes()
    {
        // maxResolvents: 0 levait apres la premiere resolvante avec un message
        // qui decrivait un depassement de regime ; la borne refuse en entree.
        PlKnowledgeBase knowledgeBase = AimaChapter7();

        Assert.Throws<ArgumentOutOfRangeException>(
            () => PlInference.Resolve(knowledgeBase, PlParser.Parse("B"), maxResolvents: 0));
    }

    [Fact]
    public void WalkSat_RefuseUnBudgetNulDeFlips()
    {
        // maxFlips: 0 rendait Unknown silencieux, indiscernable d'un vrai echec.
        PlKnowledgeBase knowledgeBase = AimaChapter7();

        Assert.Throws<ArgumentOutOfRangeException>(
            () => PlInference.WalkSatKb(knowledgeBase, maxFlips: 0));
    }

    [Fact]
    public void PlCnf_RefuseUneDistributionExponentielleSansBudget()
    {
        // Repro de la reserve 3 : (a1 & b1) | ... | (a15 & b15) produit 2^15 = 32768
        // clauses avant que le moindre budget de procedure ne s'applique. La
        // conversion CNF desormais bornee le dit au lieu de deriver.
        List<string> conjunctions = new();

        for (int index = 1; index <= 15; index++)
        {
            conjunctions.Add($"(a{index} & b{index})");
        }

        PlFormula formula = PlParser.Parse(string.Join(" | ", conjunctions));

        InvalidOperationException exception = Assert.Throws<InvalidOperationException>(
            () => PlCnf.ToClauses(formula));
        Assert.Contains("clauses", exception.Message);
    }

    [Fact]
    public void PlKbInferProcedureInfo_DistribueLesSixProcedures()
    {
        PlKnowledgeBase knowledgeBase = AimaChapter7();
        PlFormula query = PlParser.Parse("B");

        foreach (PlInferProcedure procedure in Enum.GetValues<PlInferProcedure>())
        {
            PlKbInferProcedureInfo info = new(procedure, maxFlips: 500, seed: 5);
            PlInferenceResult result = info.Ask(knowledgeBase, query);

            _output.WriteLine($"{procedure}: {result.Question} -> {result.Verdict} ({result.Steps} {result.StepUnit})");

            Assert.Equal(procedure, result.Procedure);
            Assert.NotEmpty(result.Question);
            Assert.NotEmpty(result.StepUnit);
        }
    }
}
