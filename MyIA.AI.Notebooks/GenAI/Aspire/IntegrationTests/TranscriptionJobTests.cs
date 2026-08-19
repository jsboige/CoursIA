using IntegrationTests.Data;
using Microsoft.EntityFrameworkCore;
using TUnit.Core;

namespace IntegrationTests;

/// <summary>
/// Tests d'integration EF Core + Postgres reel (conteneur Testcontainers),
/// isoles par rollback transactionnel. Convention de nommage trois parties :
/// Entite_Etat_Testee_Comportement_Attendu.
/// </summary>
[ClassDataSource<PgDatabaseFixture>(Shared = SharedType.PerTestSession)]
public class TranscriptionJobTests(PgDatabaseFixture pg) : PgTransactionalTestBase(pg)
{
    [Test]
    public async Task TranscriptionJob_WriteThenRead_RoundTrips()
    {
        Context.Jobs.Add(new TranscriptionJob
        {
            FileName = "echantillon-test-fr.wav",
            Model = "faster-whisper-large-v3-turbo",
            DurationSeconds = 12.5,
            Status = "Done",
        });

        await Context.SaveChangesAsync();

        Context.ChangeTracker.Clear(); // relecture forcee depuis la base

        var job = await Context.Jobs.FirstOrDefaultAsync();

        await Assert.That(job).IsNotNull();
        await Assert.That(job!.FileName).IsEqualTo("echantillon-test-fr.wav");
        await Assert.That(job.Id).IsNotEqualTo(Guid.Empty); // genere par le serveur
    }

    [Test]
    public async Task TranscriptionJob_AfterEachRollback_TableIsStillEmpty()
    {
        // Preuve d'isolation : meme si WriteThenRead (ou n'importe quel test
        // execute avant/apres en parallele) a COMMITTE dans SA transaction,
        // la table est vide ici — les lignes non commitees sont invisibles,
        // et chaque transaction est rollbackee a la fin de son test.
        var count = await Context.Jobs.CountAsync();

        await Assert.That(count).IsEqualTo(0);
    }

    [Test]
    public async Task TranscriptionJob_DuplicateFileName_RejectedByUniqueIndex()
    {
        Context.Jobs.Add(new TranscriptionJob { FileName = "doublon.wav", Model = "m", Status = "Pending" });
        await Context.SaveChangesAsync();

        Context.ChangeTracker.Clear();
        Context.Jobs.Add(new TranscriptionJob { FileName = "doublon.wav", Model = "m", Status = "Pending" });

        // L'index UNIQUE pose dans TranscriptionJobConfiguration doit parler :
        // le SAVEINSERT leve DbUpdateException, la transaction est rollbackee.
        await Assert.ThrowsAsync<DbUpdateException>(async () =>
            await Context.SaveChangesAsync());
    }

    [Test]
    public async Task TranscriptionJob_StatusUpdate_PersistsWithinTransaction()
    {
        var job = new TranscriptionJob { FileName = "maj.wav", Model = "m", Status = "Pending" };
        Context.Jobs.Add(job);
        await Context.SaveChangesAsync();

        Context.ChangeTracker.Clear();
        var stored = await Context.Jobs.SingleAsync(j => j.FileName == "maj.wav");
        stored.Status = "Done";
        await Context.SaveChangesAsync();

        Context.ChangeTracker.Clear();
        var reloaded = await Context.Jobs.SingleAsync(j => j.FileName == "maj.wav");

        await Assert.That(reloaded.Status).IsEqualTo("Done");
    }
}
