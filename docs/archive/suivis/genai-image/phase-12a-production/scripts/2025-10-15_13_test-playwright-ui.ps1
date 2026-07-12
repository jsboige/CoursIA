# Script de test Playwright pour ComfyUI + Forge UI
# Date: 2025-10-15
# Teste visuellement les deux interfaces après configuration IIS + SSL

Write-Host "=== Test Playwright - ComfyUI + Forge UI ===" -ForegroundColor Cyan

# Vérifier si Node.js est installé
try {
    $nodeVersion = node --version
    Write-Host "✓ Node.js installé: $nodeVersion" -ForegroundColor Green
} catch {
    Write-Host "✗ Node.js non trouvé. Installation requise." -ForegroundColor Red
    exit 1
}

# Créer le répertoire de test
$testDir = "D:\Production\playwright-tests"
if (-not (Test-Path $testDir)) {
    New-Item -ItemType Directory -Path $testDir | Out-Null
    Write-Host "✓ Répertoire de test créé: $testDir" -ForegroundColor Green
}

# Créer le fichier package.json
$packageJson = @"
{
  "name": "comfyui-forge-ui-tests",
  "version": "1.0.0",
  "description": "Tests visuels Playwright pour ComfyUI et Forge",
  "scripts": {
    "test": "node test-ui.js"
  },
  "dependencies": {
    "playwright": "^1.40.0"
  }
}
"@

Set-Content -Path "$testDir\package.json" -Value $packageJson
Write-Host "✓ package.json créé" -ForegroundColor Green

# Créer le script de test Playwright
$testScript = @"
const { chromium } = require('playwright');
const fs = require('fs');
const path = require('path');

(async () => {
  console.log('🚀 Démarrage des tests Playwright...\n');
  
  const browser = await chromium.launch({ 
    headless: false,
    args: ['--ignore-certificate-errors']
  });
  
  const context = await browser.newContext({ 
    ignoreHTTPSErrors: true,
    viewport: { width: 1920, height: 1080 }
  });
  
  const resultsDir = 'D:\\\\Production\\\\playwright-tests\\\\results';
  if (!fs.existsSync(resultsDir)) {
    fs.mkdirSync(resultsDir, { recursive: true });
  }
  
  // Test 1: ComfyUI (nouveau site)
  console.log('📸 Test 1: ComfyUI à https://qwen-image-edit.myia.io');
  try {
    const page1 = await context.newPage();
    await page1.goto('https://qwen-image-edit.myia.io', { 
      waitUntil: 'networkidle',
      timeout: 30000 
    });
    
    await page1.waitForTimeout(5000);
    
    const screenshotPath1 = path.join(resultsDir, 'comfyui-ui.png');
    await page1.screenshot({ 
      path: screenshotPath1, 
      fullPage: true 
    });
    
    console.log('  ✅ ComfyUI UI capturée:', screenshotPath1);
    
    // Vérifier la présence d'éléments ComfyUI
    const hasCanvas = await page1.locator('canvas').count() > 0;
    const hasQueue = await page1.getByText('Queue', { exact: false }).count() > 0;
    
    console.log('  - Canvas détecté:', hasCanvas ? '✓' : '✗');
    console.log('  - Bouton Queue détecté:', hasQueue ? '✓' : '✗');
    
    await page1.close();
    
  } catch (error) {
    console.error('  ❌ Erreur ComfyUI:', error.message);
  }
  
  // Test 2: Forge (site existant - vérification non-régression)
  console.log('\n📸 Test 2: Forge à https://turbo.stable-diffusion-webui-forge.myia.io');
  try {
    const page2 = await context.newPage();
    await page2.goto('https://turbo.stable-diffusion-webui-forge.myia.io', { 
      waitUntil: 'networkidle',
      timeout: 30000 
    });
    
    await page2.waitForTimeout(5000);
    
    const screenshotPath2 = path.join(resultsDir, 'forge-ui.png');
    await page2.screenshot({ 
      path: screenshotPath2, 
      fullPage: true 
    });
    
    console.log('  ✅ Forge UI capturée:', screenshotPath2);
    
    // Vérifier la présence d'éléments Forge
    const hasGenerateBtn = await page2.getByText('Generate', { exact: false }).count() > 0;
    const hasPromptBox = await page2.locator('textarea').count() > 0;
    
    console.log('  - Bouton Generate détecté:', hasGenerateBtn ? '✓' : '✗');
    console.log('  - Zone de prompt détectée:', hasPromptBox ? '✓' : '✗');
    
    await page2.close();
    
  } catch (error) {
    console.error('  ❌ Erreur Forge:', error.message);
  }
  
  await browser.close();
  
  console.log('\n✅ Tests terminés. Screenshots dans:', resultsDir);
  
})();
"@

Set-Content -Path "$testDir\test-ui.js" -Value $testScript
Write-Host "✓ Script de test créé: test-ui.js" -ForegroundColor Green

# Installer les dépendances
Write-Host "`nInstallation des dépendances npm..." -ForegroundColor Yellow
Push-Location $testDir
try {
    npm install 2>&1 | Out-Null
    Write-Host "✓ Dépendances installées" -ForegroundColor Green
    
    # Installer les navigateurs Playwright
    Write-Host "Installation des navigateurs Playwright..." -ForegroundColor Yellow
    npx playwright install chromium 2>&1 | Out-Null
    Write-Host "✓ Navigateurs installés" -ForegroundColor Green
    
} catch {
    Write-Host "✗ Erreur lors de l'installation: $_" -ForegroundColor Red
} finally {
    Pop-Location
}

Write-Host "`n=== Pour exécuter les tests ===" -ForegroundColor Cyan
Write-Host "cd $testDir" -ForegroundColor White
Write-Host "npm test" -ForegroundColor White
Write-Host "`nLes screenshots seront dans: $testDir\results\" -ForegroundColor Yellow