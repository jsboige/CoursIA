param(
    [string]$NotebookPath
)

# Vérifier si le chemin du notebook est fourni
if (-not $NotebookPath) {
    Write-Error "Veuillez fournir le chemin du notebook à exécuter."
    exit 1
}

# Vérifier si le fichier notebook existe
if (-not (Test-Path $NotebookPath)) {
    Write-Error "Le fichier notebook '$NotebookPath' n'a pas été trouvé."
    exit 1
}

# Exécuter le notebook en utilisant nbconvert
try {
    Write-Host "Exécution du notebook: $NotebookPath"
    jupyter nbconvert --to notebook --execute $NotebookPath --output $NotebookPath
    Write-Host "Exécution terminée avec succès."
} catch {
    Write-Error "Une erreur s'est produite lors de l'exécution du notebook:"
    Write-Error $_
    exit 1
}