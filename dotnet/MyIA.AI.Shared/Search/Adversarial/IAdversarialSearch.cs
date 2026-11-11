namespace MyIA.AI.Shared.Search.Adversarial;

/// <summary>
/// Moteur de decision pour un jeu a deux joueurs : rend le meilleur coup pour le
/// joueur au trait dans l'etat donne.
/// </summary>
/// <remarks>
/// Correspond au <c>AdversarialSearch.makeDecision(state)</c> du patrimoine. Le
/// contrat est volontairement mince : un seul point d'entree, une decision, des
/// compteurs. Tout ce qui faisait boucler le patrimoine (enchainement de coups
/// jusqu'a la fin de partie, impression des actions) est de l'orchestration
/// d'appelant, pas du moteur.
/// </remarks>
/// <typeparam name="TState">Type de l'etat du jeu.</typeparam>
/// <typeparam name="TAction">Type d'un coup.</typeparam>
/// <typeparam name="TPlayer">Type du joueur.</typeparam>
public interface IAdversarialSearch<TState, TAction, TPlayer>
    where TState : notnull
{
    /// <summary>
    /// Rend le meilleur coup legal dans <paramref name="state"/>, ou <c>null</c> si
    /// l'etat est terminal ou sans coup legal. Les compteurs de la decision sont
    /// relatifs a cet appel uniquement.
    /// </summary>
    AdversarialDecision<TAction>? MakeDecision(TState state);
}
