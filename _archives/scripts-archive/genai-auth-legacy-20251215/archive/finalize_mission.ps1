# Script de finalisation de la mission ComfyUI-Login
# Ce script ajoute les fichiers modifiés, commite et crée le tag de version stable

Write-Host "=== DÉBUT DE LA FINALISATION DE LA MISSION COMFYUI-LOGIN ===" -ForegroundColor Cyan

# 1. Vérification de l'état Git
Write-Host "`n1. Vérification de l'état Git..." -ForegroundColor Yellow
git status

# 2. Ajout des fichiers modifiés
Write-Host "`n2. Ajout des fichiers modifiés..." -ForegroundColor Yellow
# Ajout spécifique des fichiers de documentation et scripts modifiés
git add docs/suivis/genai-image/phase-32-restauration-post-reorganisation/RAPPORT-FINAL-CLOTURE-MISSION-COMFYUI-LOGIN.md
git add scripts/genai-auth/
git add docker-configurations/services/comfyui-qwen/entrypoint.sh
git add docker-configurations/services/comfyui-qwen/docker-compose.yml

# 3. Commit des changements
Write-Host "`n3. Commit des changements..." -ForegroundColor Yellow
git commit -m "Finalisation Mission ComfyUI-Login : Restauration complète et validation"

# 4. Création du tag stable
Write-Host "`n4. Création du tag comfyui-auth-v1.0-stable..." -ForegroundColor Yellow
# Vérifier si le tag existe déjà et le supprimer si nécessaire (pour éviter les erreurs en local)
if (git tag -l "comfyui-auth-v1.0-stable") {
    Write-Host "Le tag existe déjà, suppression..." -ForegroundColor Gray
    git tag -d comfyui-auth-v1.0-stable
}
git tag -a comfyui-auth-v1.0-stable -m "Version stable 1.0 de l'authentification ComfyUI - Production Ready"

# 5. Vérification finale
Write-Host "`n5. Vérification finale..." -ForegroundColor Yellow
git show comfyui-auth-v1.0-stable --summary

Write-Host "`n=== MISSION FINALISÉE AVEC SUCCÈS ===" -ForegroundColor Green
Write-Host "Le tag 'comfyui-auth-v1.0-stable' a été créé."