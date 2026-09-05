using IntegrationTests.Data;
using Microsoft.EntityFrameworkCore.Storage;
using TUnit.Core;

namespace IntegrationTests;

/// <summary>
/// Base transactionnelle : chaque test s'execute dans SA transaction, ouverte
/// en [Before(Test)] et ROLLBACKEE en [After(Test)]. Aucun test ne laisse de
/// ligne derriere lui — l'etat de depart (base vide) est un invariant, et les
/// tests peuvent tourner en parallele sur le meme conteneur.
/// </summary>
public abstract class PgTransactionalTestBase(PgDatabaseFixture pg)
{
    private IDbContextTransaction? _transaction;

    // TUnit instancie la classe pour CHAQUE test : le champ est frais a chaque fois
    protected TranscriptionDbContext Context = pg.CreateContext();

    [Before(Test)]
    public async Task BeginTransaction()
    {
        _transaction = await Context.Database.BeginTransactionAsync();
    }

    [After(Test)]
    public async Task RollbackTransaction()
    {
        if (_transaction is not null)
        {
            await _transaction.RollbackAsync();
            await _transaction.DisposeAsync();
        }

        await Context.DisposeAsync();
    }
}
