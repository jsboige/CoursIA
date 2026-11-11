using System.Collections.Generic;

namespace MyIA.AI.Shared.Search.Graph;

/// <summary>
/// Probleme de recherche dans un espace d'etats, tel que le definit AIMA
/// (Russell et Norvig, chapitre 3) : etat initial, actions applicables, transition,
/// test de but et cout de pas.
/// </summary>
/// <remarks>
/// <para>
/// Port du patrimoine Aricie (EPIC #7265, pepite B2). La version d'origine
/// (<c>aima.core.search.framework.Problem</c>, utilisee par
/// <c>Libraries/AI/Search.cs</c>) n'etait atteignable qu'a travers un wrapper DNN
/// et une traduction IKVM de la bibliotheque Java AIMA : ceci est du C# nu, sans
/// dependance DNN ni Java.
/// </para>
/// <para>
/// Le type d'etat doit offrir une egalite utilisable en recherche graphe (valeur
/// pour un type valeur, <c>Equals</c>/<c>GetHashCode</c> coherents pour une classe).
/// </para>
/// </remarks>
/// <typeparam name="TState">Type de l'etat.</typeparam>
/// <typeparam name="TAction">Type de l'action.</typeparam>
public interface ISearchProblem<TState, TAction>
{
    /// <summary>Etat de depart.</summary>
    TState InitialState { get; }

    /// <summary>
    /// Actions applicables dans un etat. L'ordre rendu est celui que la recherche
    /// explore : il doit etre deterministe pour que les compteurs soient reproductibles.
    /// </summary>
    IReadOnlyList<TAction> Actions(TState state);

    /// <summary>Etat atteint en appliquant une action a un etat.</summary>
    TState Result(TState state, TAction action);

    /// <summary>Vrai si l'etat satisfait le but.</summary>
    bool IsGoal(TState state);

    /// <summary>
    /// Cout du pas de <paramref name="state"/> vers <paramref name="nextState"/>
    /// par <paramref name="action"/>. Strictement positif pour que le cout uniforme
    /// et A* restent optimaux.
    /// </summary>
    double StepCost(TState state, TAction action, TState nextState);
}
