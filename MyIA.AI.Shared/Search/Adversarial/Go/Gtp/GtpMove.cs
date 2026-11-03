namespace MyIA.AI.Shared.Search.Adversarial.Go.Gtp;

/// <summary>
/// Resultat type d'une commande <c>genmove</c> : un sommet, le passe, ou
/// l'abandon. EPIC #7265, pepite B3, tranche 10.
/// </summary>
/// <remarks>
/// <para>
/// GTP rend ces trois issues dans le meme champ texte : une intersection
/// (« D4 »), « pass », ou « resign ». Leur donner un type commun evite le
/// piege inverse : traiter « resign » comme une intersection, ou le jeter
/// parce qu'il n'en est pas une.
/// </para>
/// <para>
/// <see cref="GtpCoordinate.Parse"/> reste un parseur d'intersection et
/// continue de refuser « resign » : la decision d'abandonner appartient au
/// moteur qui repond, puis au joueur qui la lit — jamais au decodeur de
/// coordonnees.
/// </para>
/// </remarks>
/// <param name="Vertex">Sommet joue, ou <see cref="GoPoint.Pass"/> ; <see langword="null"/> sur abandon.</param>
/// <param name="IsResign">Vrai si le moteur a rendu « resign ».</param>
public sealed record GtpMove(GoPoint? Vertex, bool IsResign)
{
    /// <summary>Un coup de passe.</summary>
    public static GtpMove Pass => new(GoPoint.Pass, IsResign: false);

    /// <summary>Un abandon : pas de sommet, la partie est rendue.</summary>
    public static GtpMove Resign => new(Vertex: null, IsResign: true);

    /// <summary>Un coup sur une intersection.</summary>
    /// <param name="vertex">Sommet joue, hors sentinelles.</param>
    public static GtpMove FromVertex(GoPoint vertex) => new(vertex, IsResign: false);

    /// <summary>Ce resultat est-il un passe ?</summary>
    public bool IsPass => !IsResign && Vertex == GoPoint.Pass;

    /// <summary>
    /// Sommet joue. Lever sur un abandon : « resign » n'est pas une
    /// intersection, cet acces nomme l'erreur au lieu de rendre un point fictif.
    /// </summary>
    public GoPoint Point =>
        Vertex ?? throw new InvalidOperationException(
            "le moteur a abandonne : il n'y a pas de sommet a lire");
}
