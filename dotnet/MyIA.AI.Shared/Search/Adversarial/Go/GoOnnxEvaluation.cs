using Microsoft.ML.OnnxRuntime;
using Microsoft.ML.OnnxRuntime.Tensors;

namespace MyIA.AI.Shared.Search.Adversarial.Go;

/// <summary>
/// Evaluation Go apprise, consommee depuis un modele ONNX. EPIC #7265, pepite B3,
/// tranche 8. La techno du patrimoine (CNTK) est archivee en lecture seule : le
/// verdict de substitution passe par l'axe 6 de la checklist SOTA, et c'est ONNX
/// Runtime qui tient le role (voie que CNTK 2.7 lui-meme designe, avec precedent
/// dans le depot via <c>ML/ML.Net/ML-6-ONNX.ipynb</c>).
/// </summary>
/// <remarks>
/// <para>
/// Le modele est un petit reseau de valeur entraine sur du auto-jeu aleatoire
/// pyspiel 9x9 (komi 0) par <c>oracles/train_go_eval_onnx.py</c> : il predit le
/// score d'aire FINAL du plateau courant, dans le referentiel de
/// <see cref="GoGame.AreaScore()"/> sans la komi. La komi n'est pas apprise :
/// elle est ajoutee apres l'inference, en arithmetique exacte.
/// </para>
/// <para>
/// La baseline honnete reste <see cref="GoGameAdapter.TerritoryHeuristic"/> : le
/// MAE comparatif net/baseline est mesure a la generation et consigne dans la
/// fixture <c>go_eval_onnx_expected.json</c>. Cette classe ne cache pas ce
/// releve -- qui veut trier les deux evaluations le relit.
/// </para>
/// <para>
/// <b>Orientation du tenseur</b> : ligne 0 = bas du goban (ligne GTP 1), colonne
/// 0 = A -- le referentiel <see cref="GoPoint"/>. Les donnees d'entrainement
/// utilisent le meme, via le parse <c>to_string()</c> de pyspiel range par
/// numero de ligne GTP decroissant (convention tranche 2b).
/// </para>
/// </remarks>
public sealed class GoOnnxEvaluation : IDisposable
{
    /// <summary>Taille de plateau du modele fige -- il en existe une seule.</summary>
    public const int SupportedSize = 9;

    private readonly InferenceSession _session;
    private readonly double _komiOverride;

    /// <summary>
    /// Charge le modele <paramref name="modelPath"/> (ONNX, entree <c>input</c>
    /// 1x3x9x9, sortie <c>score</c> scalaire -- les noms sont poses par
    /// l'exporteur et verifies par les temoins).
    /// </summary>
    /// <param name="modelPath">Chemin du fichier .onnx.</param>
    /// <param name="komiOverride">
    /// Komi a ajouter au score appris. Par defaut : celle de l'etat evalue.
    /// Le parametre existe pour les plateaux construits sans komi (tests,
    /// fixtures) qu'on veut quand meme scorer avec la komi reelle d'une partie.
    /// </param>
    public GoOnnxEvaluation(string modelPath, double? komiOverride = null)
    {
        _session = new InferenceSession(modelPath);
        _komiOverride = komiOverride ?? double.NaN;
    }

    /// <summary>Le score d'aire FINAL predit pour le noir, komi comprise.</summary>
    /// <remarks>
    /// Prediction du reseau + komi exacte. Antisymetrique par construction du
    /// jeu (le score blanc est l'oppose) -- <see cref="Evaluate"/> l'applique.
    /// </remarks>
    public double PredictBlackArea(GoGame state)
    {
        ArgumentNullException.ThrowIfNull(state);
        if (state.Size != SupportedSize)
        {
            throw new InvalidOperationException(
                $"Le modele fige vaut pour un goban {SupportedSize}x{SupportedSize}, "
                + $"pas {state.Size}x{state.Size} : reentrainer et figer un autre "
                + "modele (oracles/train_go_eval_onnx.py).");
        }

        using IDisposableReadOnlyCollection<DisposableNamedOnnxValue> results =
            _session.Run(new[]
            {
                NamedOnnxValue.CreateFromTensor("input", BuildInput(state)),
            });
        Tensor<float> output = results.First().AsTensor<float>();
        double learned = output[0];
        double komi = double.IsNaN(_komiOverride) ? state.Komi : _komiOverride;
        return learned + komi;
    }

    /// <summary>
    /// L'evaluation du point de vue d'un joueur : le score d'aire final predit,
    /// positif pour <paramref name="player"/>, negatif pour l'adversaire --
    /// le meme contrat que <see cref="GoGameAdapter.Utility"/> et
    /// <see cref="GoGameAdapter.TerritoryHeuristic"/>. Le vide n'est pas un joueur.
    /// </summary>
    public double Evaluate(GoGame state, GoColor player)
    {
        ArgumentNullException.ThrowIfNull(state);
        return player switch
        {
            GoColor.Black => PredictBlackArea(state),
            GoColor.White => -PredictBlackArea(state),
            _ => throw new ArgumentOutOfRangeException(
                nameof(player), player, "Le vide n'est pas un joueur."),
        };
    }

    /// <summary>
    /// Tenseur d'entree du reseau : 1x3x9x9 float32. Plan 0 pierres noires,
    /// plan 1 pierres blanches, plan 2 = 1 si noir au trait ; ligne 0 = bas du
    /// goban (referentiel <see cref="GoPoint"/>), colonne 0 = A. Visibilite
    /// interne : les temoins la traversent pour verifier l'orientation.
    /// </summary>
    internal static DenseTensor<float> BuildInput(GoGame state)
    {
        DenseTensor<float> tensor = new(new[] { 1, 3, SupportedSize, SupportedSize });
        for (int y = 0; y < SupportedSize; y++)
        {
            for (int x = 0; x < SupportedSize; x++)
            {
                GoColor color = state.ColorAt(new GoPoint(x, y));
                if (color == GoColor.Black)
                {
                    tensor[0, 0, y, x] = 1f;
                }
                else if (color == GoColor.White)
                {
                    tensor[0, 1, y, x] = 1f;
                }
            }
        }

        if (state.ToPlay == GoColor.Black)
        {
            for (int y = 0; y < SupportedSize; y++)
            {
                for (int x = 0; x < SupportedSize; x++)
                {
                    tensor[0, 2, y, x] = 1f;
                }
            }
        }

        return tensor;
    }

    /// <inheritdoc />
    public void Dispose() => _session.Dispose();
}
