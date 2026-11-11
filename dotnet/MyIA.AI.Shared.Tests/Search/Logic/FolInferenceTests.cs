using System.Diagnostics;
using MyIA.AI.Shared.Search.Logic.FirstOrder;
using Xunit;
using Xunit.Abstractions;

namespace MyIA.AI.Shared.Tests.Search.Logic;

/// <summary>
/// Temoins des procedures d'inference du premier ordre (EPIC #7265, volet B2
/// tranche 2, issue #24320).
/// </summary>
/// <remarks>
/// Les instances de reference sont celles du chapitre 9 d'AIMA. Les procedures
/// ne sont pas seulement verifiees correctes : elles sont verifiees <i>falsifiables
/// entre elles</i>, la meme instance passee au chainage, au pont Z3.Linq et a
/// l'enumeration naive, avec des couts mesures et des unites distinctes.
/// </remarks>
public sealed class FolInferenceTests
{
    private readonly ITestOutputHelper _output;

    public FolInferenceTests(ITestOutputHelper output) => _output = output;

    /// <summary>
    /// L'instance criminelle du chapitre 9 d'AIMA : West est-il criminel ?
    /// Quatre constantes (America, M1, Nono, West) — reservee au chainage,
    /// l'atome Sells/3 y produit 64 atomes ancres, au-dela de l'enumeration naive.
    /// </summary>
    private static FolKnowledgeBase CrimeWest()
    {
        FolKnowledgeBase kb = new();
        kb.Domain.AddConstant("America").AddConstant("M1").AddConstant("Nono").AddConstant("West");
        kb.Domain.AddPredicate("American/1").AddPredicate("Criminal/1").AddPredicate("Weapon/1")
            .AddPredicate("Missile/1").AddPredicate("Owns/2").AddPredicate("Sells/3")
            .AddPredicate("Hostile/1").AddPredicate("Enemy/2");
        kb.Tell("American(West)");
        kb.Tell("Missile(M1)");
        kb.Tell("Owns(Nono, M1)");
        kb.Tell("Sells(West, M1, Nono)");
        kb.Tell("Enemy(Nono, America)");
        kb.Tell("FORALL x (Missile(x) => Weapon(x))");
        kb.Tell("FORALL x (Enemy(x, America) => Hostile(x))");
        kb.Tell("FORALL x (FORALL y (FORALL z (American(x) AND Weapon(y) AND Sells(x, y, z) AND Hostile(z) => Criminal(x))))");
        return kb;
    }

    /// <summary>
    /// Instance compacte pour l'accord a quatre procedures : deux constantes,
    /// une regle d'ancestralite. Le chainage la prouve par Modus Ponens,
    /// le pont Z3 par insatisfiabilite, la naive par balayage.
    /// </summary>
    private static FolKnowledgeBase Genealogie()
    {
        FolKnowledgeBase kb = new();
        kb.Domain.AddConstant("Armand").AddConstant("Cedric");
        kb.Domain.AddPredicate("Pere/2").AddPredicate("Ancetre/2");
        kb.Tell("FORALL x (Pere(x, Cedric) => Ancetre(x, Cedric))");
        kb.Tell("Pere(Armand, Cedric)");
        return kb;
    }

    [Fact]
    public void Crime_AimaChapitre9_LeChainageAvantDemontreCriminalWest()
    {
        FolAskResult result = FolInference.FcEntails(CrimeWest(),
            Assert.IsType<FolFormula.Predicate>(FolParser.Parse("Criminal(West)")));

        Assert.True(result.Entailed);
        Assert.Equal(3, result.Cost);
        _output.WriteLine($"FC (crime) : {result.Cost} {result.CostUnit}");
    }

    [Fact]
    public void Crime_AimaChapitre9_LeChainageArriereDemontreCriminalWest()
    {
        FolAskResult result = FolInference.BcEntails(CrimeWest(),
            Assert.IsType<FolFormula.Predicate>(FolParser.Parse("Criminal(West)")));

        Assert.True(result.Entailed);
        _output.WriteLine($"BC (crime) : {result.Cost} {result.CostUnit}");
    }

    [Fact]
    public void Crime_NonoNEstPasCriminel()
    {
        FolKnowledgeBase kb = CrimeWest();
        FolFormula.Predicate query = Assert.IsType<FolFormula.Predicate>(FolParser.Parse("Criminal(Nono)"));

        Assert.False(FolInference.FcEntails(kb, query).Entailed);
        Assert.False(FolInference.BcEntails(kb, query).Entailed);
    }

    [Fact]
    public void Genealogie_QuatreProceduresDaccordSurLEntaillement()
    {
        FolKnowledgeBase kb = Genealogie();
        FolFormula.Predicate query = Assert.IsType<FolFormula.Predicate>(FolParser.Parse("Ancetre(Armand, Cedric)"));

        FolAskResult fc = FolInference.FcEntails(kb, query);
        FolAskResult bc = FolInference.BcEntails(kb, query);
        FolAskResult z3 = FolInference.Z3Entails(kb, query);
        FolAskResult naive = FolInference.NaiveEntails(kb, query);

        Assert.True(fc.Entailed);
        Assert.True(bc.Entailed);
        Assert.True(z3.Entailed);
        Assert.True(naive.Entailed);
        _output.WriteLine($"FC : {fc.Cost} {fc.CostUnit} | BC : {bc.Cost} {bc.CostUnit}");
        _output.WriteLine($"Z3 : {z3.Cost} {z3.CostUnit} | naive : {naive.Cost} {naive.CostUnit}");
    }

    /// <summary>
    /// Berthe n'est declaree pere de personne : les quatre procedures doivent
    /// refuser Ancetre(Berthe, Cedric) sur la meme base augmentee de la constante.
    /// </summary>
    [Fact]
    public void Genealogie_QuatreProceduresDaccordSurLeNonEntaillement()
    {
        FolKnowledgeBase kb = new();
        kb.Domain.AddConstant("Armand").AddConstant("Berthe").AddConstant("Cedric");
        kb.Domain.AddPredicate("Pere/2").AddPredicate("Ancetre/2");
        kb.Tell("FORALL x (Pere(x, Cedric) => Ancetre(x, Cedric))");
        kb.Tell("Pere(Armand, Cedric)");

        FolFormula.Predicate query = Assert.IsType<FolFormula.Predicate>(FolParser.Parse("Ancetre(Berthe, Cedric)"));

        Assert.False(FolInference.FcEntails(kb, query).Entailed);
        Assert.False(FolInference.BcEntails(kb, query).Entailed);
        Assert.False(FolInference.Z3Entails(kb, query).Entailed);
        // La naive trouve un contre-modele : elle ne balaie pas tout.
        Assert.False(FolInference.NaiveEntails(kb, query).Entailed);
    }

    [Fact]
    public void BaseInsatisfiable_EntailleToutParExplosion()
    {
        FolKnowledgeBase kb = new();
        kb.Domain.AddConstant("A");
        kb.Domain.AddPredicate("P/1").AddPredicate("Q/1");
        kb.Tell("P(A)");
        kb.Tell("~P(A)");

        FolFormula.Predicate query = Assert.IsType<FolFormula.Predicate>(FolParser.Parse("Q(A)"));

        // KB ET NON(Q) est insatisfiable parce que la KB l'est deja : les deux
        // chemins doivent le voir de la meme facon.
        Assert.True(FolInference.Z3Entails(kb, query).Entailed);
        Assert.True(FolInference.NaiveEntails(kb, query).Entailed);
    }

    /// <summary>Les variables libres de la question sont existentielles : « quelqu'un est une personne ».</summary>
    [Fact]
    public void QuestionAVariableLibre_ExistenceDUneInstance()
    {
        FolKnowledgeBase kb = new();
        kb.Domain.AddConstant("Louis");
        kb.Domain.AddPredicate("Roi/1").AddPredicate("Personne/1");
        kb.Tell("FORALL x (Roi(x) => Personne(x))");
        kb.Tell("Roi(Louis)");

        FolFormula.Predicate query = Assert.IsType<FolFormula.Predicate>(FolParser.Parse("Personne(x)"));

        Assert.True(FolInference.Z3Entails(kb, query).Entailed);
        Assert.True(FolInference.FcEntails(kb, query).Entailed);
        Assert.True(FolInference.BcEntails(kb, query).Entailed);
    }

    /// <summary>
    /// KB cyclique a buts sols : P(A) :- Q(A), Q(A) :- P(A). La garde anti-cycles
    /// doit la terminer par un echec, pas par une recursion infinie.
    /// </summary>
    [Fact]
    public void KB_CycliqueSol_LeChainageArriereTermineParEchec()
    {
        FolKnowledgeBase kb = new();
        kb.Domain.AddConstant("A");
        kb.Domain.AddPredicate("P/1").AddPredicate("Q/1");
        kb.Tell("FORALL x (Q(x) => P(x))");
        kb.Tell("FORALL x (P(x) => Q(x))");

        FolFormula.Predicate query = Assert.IsType<FolFormula.Predicate>(FolParser.Parse("P(A)"));

        Assert.False(FolInference.BcEntails(kb, query).Entailed);
    }

    /// <summary>
    /// Une constante utilisee sans etre declaree au domaine serait invisible aux
    /// quantificateurs de l'ancrage (ils iterent les constantes declarees) : la
    /// garde la refuse en nommant la constante et la phrase, des l'ancrage Z3
    /// comme a l'enumeration naive (revue Hermes #24324, point 1 -- le piege
    /// etait silencieux avant).
    /// </summary>
    [Fact]
    public void ConstanteNonDeclaree_LAncrageRefusePlutotQuAncrerAmpute()
    {
        FolKnowledgeBase kb = new();
        kb.Domain.AddConstant("Armand");
        kb.Domain.AddPredicate("Aime/2");
        kb.Tell("Aime(Armand, Cedric)"); // Cedric n'est pas declare au domaine.

        FolFormula.Predicate query =
            Assert.IsType<FolFormula.Predicate>(FolParser.Parse("Aime(Armand, Cedric)"));

        InvalidOperationException z3Error = Assert.Throws<InvalidOperationException>(
            () => FolInference.Z3Entails(kb, query));
        Assert.Contains("Cedric", z3Error.Message, StringComparison.Ordinal);
        Assert.Throws<InvalidOperationException>(() => FolInference.NaiveEntails(kb, query));
    }

    /// <summary>
    /// Le plafond de profondeur du chainage arriere (16) est un NON-DEMO, pas une
    /// lenteur : sur une chaine de vingt implications (profondeur de preuve 20),
    /// BC rend faux alors que l'ancrage Z3 demontre l'entaillement. Ce temoin
    /// epingle le desaccord documente dans les remarques de <c>BcEntails</c>
    /// (revue Hermes #24324, point 2) : au-dela de la borne, croiser avec Z3
    /// avant de conclure.
    /// </summary>
    [Fact]
    public void ChaineProfonde_LeCapDeProfondeurDuBCProvoqueLeDesaccordDocumente()
    {
        FolKnowledgeBase kb = new();
        kb.Domain.AddConstant("Armand");
        for (int level = 1; level <= 20; level++)
        {
            kb.Domain.AddPredicate($"Palier{level}/1");
        }

        for (int level = 1; level < 20; level++)
        {
            kb.Tell($"FORALL x (Palier{level}(x) => Palier{level + 1}(x))");
        }

        kb.Tell("Palier1(Armand)");

        FolFormula.Predicate query =
            Assert.IsType<FolFormula.Predicate>(FolParser.Parse("Palier20(Armand)"));

        Assert.True(FolInference.Z3Entails(kb, query).Entailed);
        // Profondeur de preuve 20 > borne 16 : non-demo, pas refus.
        Assert.False(FolInference.BcEntails(kb, query).Entailed);
    }

    /// <summary>
    /// Témoin de discrimination : chaine de cinq predicats binaires sur deux
    /// constantes (20 atomes ancrés). Le meme entaillement est decide par Z3 en
    /// un appel du solveur et par la naive par balayage integral des 2^20
    /// affectations. Les durees mesurees vont au rapport de cycle.
    /// </summary>
    [Fact]
    public void ChaineDePredicats_Z3Decide_ouLaNaiveBalaie()
    {
        FolKnowledgeBase kb = new();
        kb.Domain.AddConstant("Armand").AddConstant("Cedric");
        for (int level = 1; level <= 5; level++)
        {
            kb.Domain.AddPredicate($"Palier{level}/2");
        }

        for (int level = 1; level < 5; level++)
        {
            kb.Tell($"FORALL x (FORALL y (Palier{level}(x, y) => Palier{level + 1}(x, y)))");
        }

        kb.Tell("Palier1(Armand, Cedric)");

        FolFormula.Predicate query =
            Assert.IsType<FolFormula.Predicate>(FolParser.Parse("Palier5(Armand, Cedric)"));

        Stopwatch z3Watch = Stopwatch.StartNew();
        FolAskResult z3 = FolInference.Z3Entails(kb, query);
        z3Watch.Stop();

        Stopwatch naiveWatch = Stopwatch.StartNew();
        FolAskResult naive = FolInference.NaiveEntails(kb, query);
        naiveWatch.Stop();

        Assert.True(z3.Entailed);
        Assert.True(naive.Entailed);
        // L'entaillement etant vrai, la naive ne peut pas s'arreter tot :
        // elle a essaye les 2^20 affectations, Z3 a pose 20 atomes + 6 contraintes.
        Assert.Equal(1_048_576, naive.Cost);
        Assert.Equal(26, z3.Cost);
        _output.WriteLine($"Z3 : {z3.Cost} {z3.CostUnit} en {z3Watch.ElapsedMilliseconds} ms");
        _output.WriteLine($"naive : {naive.Cost} {naive.CostUnit} en {naiveWatch.ElapsedMilliseconds} ms");
    }

    /// <summary>
    /// Au-dela de 24 atomes ancrés (seuil recalibre par la revue Hermes #24324,
    /// point 3 : 2^24 affectations ≈ 40 s au plafond, mesure 2^20 = 2,4 s),
    /// l'enumeration naive refuse, honnetement.
    /// </summary>
    [Fact]
    public void EnumerationNaive_RefuseAuDelaDeVingtQuatreAtomes()
    {
        FolKnowledgeBase kb = new();
        kb.Domain.AddConstant("Armand").AddConstant("Cedric");
        for (int level = 1; level <= 8; level++)
        {
            kb.Domain.AddPredicate($"Palier{level}/2");
        }

        for (int level = 1; level < 8; level++)
        {
            kb.Tell($"FORALL x (FORALL y (Palier{level}(x, y) => Palier{level + 1}(x, y)))");
        }

        kb.Tell("Palier1(Armand, Cedric)");

        FolFormula.Predicate query =
            Assert.IsType<FolFormula.Predicate>(FolParser.Parse("Palier8(Armand, Cedric)"));

        Assert.Throws<InvalidOperationException>(() => FolInference.NaiveEntails(kb, query));
    }

    /// <summary>Le routeur <c>Ask</c> joint chaque nom de l'enum Aricie a sa procedure.</summary>
    [Fact]
    public void Ask_RouteChaqueProcedureDeLEnumAricie()
    {
        FolFormula.Predicate query =
            Assert.IsType<FolFormula.Predicate>(FolParser.Parse("Ancetre(Armand, Cedric)"));

        foreach (FolInferenceProcedure procedure in Enum.GetValues<FolInferenceProcedure>())
        {
            FolKnowledgeBase kb = Genealogie();
            kb.Procedure = procedure;
            Assert.True(FolInference.Ask(kb, query).Entailed, $"procedure {procedure}");
        }
    }

    /// <summary>Une question composee (conjonction) passe par Z3, pas par le chainage.</summary>
    [Fact]
    public void Ask_ChainageRefuseLesQuestionsComposees()
    {
        FolKnowledgeBase kb = Genealogie();
        kb.Procedure = FolInferenceProcedure.FCAsk;
        FolFormula composed = FolParser.Parse("Ancetre(Armand, Cedric) AND Pere(Armand, Cedric)");

        Assert.Throws<ArgumentException>(() => FolInference.Ask(kb, composed));
    }
}
