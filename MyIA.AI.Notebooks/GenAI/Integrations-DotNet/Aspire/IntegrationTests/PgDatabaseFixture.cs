using DotNet.Testcontainers.Builders;
using IntegrationTests.Data;
using Microsoft.EntityFrameworkCore;
using Testcontainers.PostgreSql;
using TUnit.Core.Interfaces;

namespace IntegrationTests;

/// <summary>
/// Fixture TUnit : demarre UN conteneur Postgres 18 par session de tests,
/// sur un port hote aleatoire (jamais 5432 en dur), puis cree le schema.
/// Un seul conteneur pour toute la session : les tests s'executent en
/// parallele dessus, isoles par rollback transactionnel (cf.
/// <see cref="PgTransactionalTestBase"/>).
/// </summary>
public class PgDatabaseFixture : IAsyncInitializer, IAsyncDisposable
{
    private PostgreSqlContainer? _container;
    private DbContextOptions<TranscriptionDbContext>? _options;

    private DbContextOptions<TranscriptionDbContext> EnsureOptions()
    {
        if (_container is null)
        {
            throw new InvalidOperationException("Le conteneur Postgres n'est pas initialise.");
        }

        return _options ??= new DbContextOptionsBuilder<TranscriptionDbContext>()
            .UseNpgsql(_container.GetConnectionString())
            .EnableDetailedErrors(true)
            .UseSnakeCaseNamingConvention()
            .Options;
    }

    /// <summary>Contexte neuf, branche sur le conteneur de la session.</summary>
    public TranscriptionDbContext CreateContext() => new(EnsureOptions());

    /// <summary>Chaine de connexion effective (port aleatoire alloue par Docker).</summary>
    public string ConnectionString =>
        _container?.GetConnectionString()
        ?? throw new InvalidOperationException("Le conteneur Postgres n'est pas initialise.");

    public async Task InitializeAsync()
    {
        _container = new PostgreSqlBuilder("postgres:18")
            // true = port hote ALEATOIRE : plusieurs sessions coexistent sans collision
            .WithPortBinding(5432, true)
            .WithUsername("tests")
            .WithPassword("password")
            .WithDatabase("genai_tests")
            .WithWaitStrategy(
                Wait.ForUnixContainer()
                    .UntilMessageIsLogged("database system is ready to accept connections")
                    .UntilInternalTcpPortIsAvailable(5432))
            .WithAutoRemove(true)
            .Build();

        await _container.StartAsync();

        // Schema : EnsureCreated suffit ici (pas de migrations evolutives a
        // rejouer dans un conteneur jetable).
        await using var context = new TranscriptionDbContext(EnsureOptions());
        await context.Database.EnsureCreatedAsync();
    }

    public async ValueTask DisposeAsync()
    {
        if (_container is not null)
        {
            await _container.DisposeAsync();
        }

        GC.SuppressFinalize(this);
    }
}
