namespace MyIA.AI.Shared.Search.Adversarial;

/// <summary>
/// Jeu a deux joueurs, somme nulle, tour par tour -- le modele AIMA du chapitre
/// « Adversarial Search » (jeux competitifs).
/// </summary>
/// <remarks>
/// <para>
/// Port du patrimoine Aricie (EPIC #7265, pepite B3). La source d'origine
/// (<c>Libraries/AI/Games.cs</c>) manipulait l'interface Java <c>aima.core.search.adversarial.Game</c>
/// via IKVM : elle n'est pas recompilable ici. Ceci en est la transcription C#
/// eulerienne : les cinq operations du contrat (<c>getPlayer</c>, <c>getActions</c>,
/// <c>getResult</c>, <c>isTerminal</c>, <c>getUtility</c>) y gardent leur nom et leur sens.
/// </para>
/// <para>
/// <b>Somme nulle</b> : l'utilite d'un etat terminal est attendue antisymetrique,
/// <c>Utility(s, p) = -Utility(s, q)</c> pour les deux joueurs <c>p</c> et <c>q</c>.
/// C'est cette hypothese qui donne a Minimax son nom -- chaque noeud MAX a un
/// noeud MIN miroir -- et a l'elagage alpha-beta sa validite. Elle n'est pas
/// verifiee a l'execution : un jeu qui la viole produit des decisions sous-optimales,
/// pas d'erreur.
/// </para>
/// </remarks>
/// <typeparam name="TState">Type de l'etat du jeu.</typeparam>
/// <typeparam name="TAction">Type d'un coup.</typeparam>
/// <typeparam name="TPlayer">Type du joueur (ou couleur).</typeparam>
public interface IGame<TState, TAction, TPlayer> where TState : notnull
{
    /// <summary>Etat initial de la partie.</summary>
    TState InitialState { get; }

    /// <summary>Joueur a qui c'est le tour dans cet etat.</summary>
    TPlayer Player(TState state);

    /// <summary>Coups legaux dans cet etat. L'ordre du resultat est l'ordre d'exploration : il est significatif pour l'elagage.</summary>
    IReadOnlyList<TAction> Actions(TState state);

    /// <summary>Etat obtenu en jouant <paramref name="action"/> dans <paramref name="state"/>.</summary>
    TState Result(TState state, TAction action);

    /// <summary>Vrai si la partie est finie dans cet etat.</summary>
    bool IsTerminal(TState state);

    /// <summary>
    /// Utilite d'un etat terminal pour <paramref name="player"/>. La valeur pour un
    /// etat non terminal n'est pas lue par les moteurs complets ; la recherche
    /// iterative la remplace par l'heuristique a la borne de profondeur.
    /// </summary>
    double Utility(TState state, TPlayer player);
}
