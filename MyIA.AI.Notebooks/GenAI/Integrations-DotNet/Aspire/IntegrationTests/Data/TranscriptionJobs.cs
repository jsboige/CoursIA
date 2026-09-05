using System.ComponentModel.DataAnnotations;
using Microsoft.EntityFrameworkCore;
using Microsoft.EntityFrameworkCore.Metadata.Builders;

namespace IntegrationTests.Data;

/// <summary>
/// Modele de domaine pur : une demande de transcription soumise au service
/// whisper-api de la pile GenAI (cf. notebooks 01/02 de la serie Aspire).
/// </summary>
public class TranscriptionJob
{
    public Guid Id { get; set; }

    [MaxLength(255)]
    public string FileName { get; set; } = string.Empty;

    [MaxLength(64)]
    public string Model { get; set; } = string.Empty;

    public double DurationSeconds { get; set; }

    [MaxLength(16)]
    public string Status { get; set; } = "Pending";

    public DateTime CreatedAtUtc { get; set; } = DateTime.UtcNow;
}

/// <summary>
/// Mapping de stockage EF Core, separe du modele de domaine pur.
/// </summary>
public class TranscriptionJobConfiguration : IEntityTypeConfiguration<TranscriptionJob>
{
    public void Configure(EntityTypeBuilder<TranscriptionJob> builder)
    {
        builder.HasKey(j => j.Id);
        builder.Property(j => j.FileName).IsRequired();
        builder.Property(j => j.Model).IsRequired();
        builder.Property(j => j.Status).IsRequired();
        builder.Property(j => j.CreatedAtUtc).IsRequired();
        // Un meme fichier ne peut etre soumis qu'une fois : contrainte UNIQUE
        // en base, testee par TranscriptionJobTests.
        builder.HasIndex(j => j.FileName).IsUnique();
    }
}

/// <summary>
/// DbContext EF Core sur Postgres (convention snake_case, comme la source
/// Part 4 de la digestion #11516).
/// </summary>
public class TranscriptionDbContext(DbContextOptions<TranscriptionDbContext> options)
    : DbContext(options)
{
    public DbSet<TranscriptionJob> Jobs => Set<TranscriptionJob>();

    protected override void OnModelCreating(ModelBuilder modelBuilder)
    {
        modelBuilder.ApplyConfigurationsFromAssembly(typeof(TranscriptionDbContext).Assembly);
    }
}
