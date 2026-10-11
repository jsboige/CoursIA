namespace MyIA.AI.Shared.Search.Adversarial.Go.Gtp;

/// <summary>
/// Reponse d'une commande GTP : le statut (<c>=</c> reussite, <c>?</c> erreur),
/// l'identifiant optionnel de la commande, et le contenu multi-lignes.
/// </summary>
/// <param name="IsSuccess">La reponse portait-elle le prefixe <c>=</c> ?</param>
/// <param name="Id">Identifiant echoe, ou <see langword="null"/> si la commande n'en portait pas.</param>
/// <param name="Content">Le resultat sans le prefixe, chaque ligne nettoyee de son CR.</param>
public sealed record GtpResponse(bool IsSuccess, int? Id, string Content)
{
    /// <summary>Une reponse en erreur ne se lit pas comme un resultat vide : elle se nomme.</summary>
    public void EnsureSuccess(string command)
    {
        if (!IsSuccess)
        {
            throw new GtpException($"la commande GTP « {command} » a ete refusee : {Content}");
        }
    }
}

/// <summary>Erreur de protocole ou moteur GTP : cadre invalide, silence, timeout.</summary>
public sealed class GtpException(string message) : Exception(message);
