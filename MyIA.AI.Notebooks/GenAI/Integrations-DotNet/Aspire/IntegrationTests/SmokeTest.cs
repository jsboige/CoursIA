using TUnit.Core;

namespace IntegrationTests;

/// <summary>
/// Fumigenne : prouve que le harnais TUnit + Microsoft Testing Platform est
/// cable (sans base) — premier reflexe quand on echafaude un projet de tests.
/// </summary>
public class SmokeTest
{
    [Test]
    public async Task SmokeTest_Harness_IsWired()
    {
        // Valeur non constante (le linter TUnit refuse les assertions
        // constantes) : si cette ligne passe, le runner a bien execute du
        // code utilisateur.
        await Assert.That(DateTime.UtcNow.Year).IsGreaterThanOrEqualTo(2026);
    }
}
