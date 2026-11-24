# Rebuild du JAR preferences pour IKVM 8 ; JDK 11+ et PowerShell 7 requis.
[CmdletBinding()]
param()
$ErrorActionPreference = 'Stop'
Set-StrictMode -Version Latest
function Run([string]$command, [string[]]$arguments) {
    & $command @arguments
    if ($LASTEXITCODE -ne 0) { throw "$command a échoué (code $LASTEXITCODE)" }
}
function Download([string]$url, [string]$path) {
    if (Test-Path -LiteralPath $path) { return }
    $tmp = "$path.download"
    try {
        Invoke-WebRequest -Uri $url -OutFile $tmp
        Move-Item -LiteralPath $tmp -Destination $path
    } finally { if (Test-Path -LiteralPath $tmp) { Remove-Item -LiteralPath $tmp -Force } }
}
function Extract([string]$archive, [string]$directory) {
    if (Test-Path -LiteralPath $directory) { Remove-Item -LiteralPath $directory -Recurse -Force }
    New-Item -ItemType Directory -Path $directory | Out-Null
    try {
        [System.IO.Compression.ZipFile]::ExtractToDirectory($archive, $directory)
    } catch {
        throw "Extraction impossible pour $archive : $($_.Exception.Message)"
    }
}
function Patch([string]$path, [string]$old, [string]$new) {
    $path = (Resolve-Path -LiteralPath $path).Path
    $s = [IO.File]::ReadAllText($path)
    if (-not $s.Contains($old)) { throw "Texte attendu absent dans $path : $old" }
    [IO.File]::WriteAllText($path, $s.Replace($old, $new), [Text.UTF8Encoding]::new($false))
}
foreach ($name in @('javac', 'jar', 'tar')) {
    if (-not (Get-Command $name -ErrorAction SilentlyContinue)) { throw "Outil introuvable : $name" }
}
Add-Type -AssemblyName System.IO.Compression.FileSystem
Push-Location $PSScriptRoot
try {
    foreach ($dir in @('jars','sources-jar','sources-extracted','classes')) { New-Item -ItemType Directory -Force $dir | Out-Null }
    $maven = 'https://repo1.maven.org/maven2'
    $deps = [ordered]@{
        'jama-1.0.3.jar' = 'gov/nist/math/jama/1.0.3/jama-1.0.3.jar'
        'slf4j-api-1.7.36.jar' = 'org/slf4j/slf4j-api/1.7.36/slf4j-api-1.7.36.jar'
        'commons-math-2.2.jar' = 'org/apache/commons/commons-math/2.2/commons-math-2.2.jar'
        'commons-math3-3.6.1.jar' = 'org/apache/commons/commons-math3/3.6.1/commons-math3-3.6.1.jar'
        'ojalgo-45.1.1.jar' = 'org/ojalgo/ojalgo/45.1.1/ojalgo-45.1.1.jar'
        'org.sat4j.core-2.3.1.jar' = 'org/sat4j/org.sat4j.core/2.3.1/org.sat4j.core-2.3.1.jar'
        'commons-1.21.jar' = 'org/tweetyproject/commons/1.21/commons-1.21.jar'
    }
    foreach ($name in $deps.Keys) { Download "$maven/$($deps[$name])" "jars/$name" }
    Download 'https://tweetyproject.org/mvn/jspf/core/1.0.2/core-1.0.2.jar' 'jars/jspf-core-1.0.2.jar'
    foreach ($entry in @(@('math','1.21'),@('plugin','1.30'),@('preferences','1.30'))) {
        $name,$version = $entry
        Download "$maven/org/tweetyproject/$name/$version/$name-$version-sources.jar" "sources-jar/$name-$version-sources.jar"
    }
    $commons = Join-Path $PSScriptRoot 'sources-jar/commons-1.21-sources.jar'
    if (-not (Test-Path -LiteralPath $commons)) {
        $tmp = Join-Path ([IO.Path]::GetTempPath()) ([guid]::NewGuid().ToString())
        New-Item -ItemType Directory $tmp | Out-Null
        try {
            $archive = Join-Path $tmp 'commons.tar.gz'
            Download 'https://github.com/TweetyProjectTeam/TweetyProject/archive/refs/tags/v1.21.tar.gz' $archive
            Run 'tar' @('-xzf',$archive,'-C',$tmp,'TweetyProject-1.21/org-tweetyproject-commons/src/main/java/')
            Run 'jar' @('cf',$commons,'-C',(Join-Path $tmp 'TweetyProject-1.21/org-tweetyproject-commons/src/main/java'),'.')
        } finally { Remove-Item -LiteralPath $tmp -Recurse -Force }
    }
    $modules = @('math-1.21','commons-1.21','plugin-1.30','preferences-1.30')
    foreach ($module in $modules) { Extract (Join-Path $PSScriptRoot "sources-jar/$module-sources.jar") (Join-Path $PSScriptRoot "sources-extracted/$module") }
    $parser = 'sources-extracted/commons-1.21/org/tweetyproject/commons/Parser.java'
    Patch $parser 'import java.nio.file.Files;' "import java.nio.charset.StandardCharsets;`nimport java.nio.file.Files;"
    Patch $parser 'import java.nio.file.Path;' "import java.nio.file.Path;`nimport java.nio.file.Paths;"
    Patch $parser 'Files.readString(Path.of(filename))' 'new String(Files.readAllBytes(Paths.get(filename)), StandardCharsets.UTF_8)'
    Patch $parser 'kb_string.isBlank()' 'kb_string.trim().isEmpty()'
    $html = 'sources-extracted/commons-1.21/org/tweetyproject/commons/util/ExamplesHTMLGenerator.java'
    foreach ($pair in @(@('tweety_libraries_dir.isBlank()','tweety_libraries_dir.trim().isEmpty()'),@('doc.substring(doc.indexOf("Copyright"), doc.indexOf("public class")).strip()','doc.substring(doc.indexOf("Copyright"), doc.indexOf("public class")).trim()'),@('doc.substring(doc.indexOf("/**") + 1).strip()','doc.substring(doc.indexOf("/**") + 1).trim()'),@('description.isBlank()','description.trim().isEmpty()'))) { Patch $html $pair[0] $pair[1] }
    $cp = @($deps.Keys | ForEach-Object { Join-Path $PSScriptRoot "jars/$_" }) + @((Join-Path $PSScriptRoot 'jars/jspf-core-1.0.2.jar'))
    foreach ($module in $modules) {
        $dest = Join-Path $PSScriptRoot "classes/$module"
        if (Test-Path -LiteralPath $dest) { Remove-Item -LiteralPath $dest -Recurse -Force }
        New-Item -ItemType Directory $dest | Out-Null
        $files = @(Get-ChildItem -LiteralPath "sources-extracted/$module" -Filter '*.java' -File -Recurse | Where-Object {
            -not ($module -match '^(math|commons)-' -and ($_.FullName -match '[/\\]examples[/\\]' -or ($module -like 'math-*' -and $_.Name -in @('AntColonyOptimization.java','GurobiOptimizer.java','OjAlgoMathUtils.java'))))
        } | ForEach-Object { $_.FullName })
        if ($files.Count -eq 0) { throw "Aucune source Java pour $module" }
        $argfile = Join-Path $PSScriptRoot 'classes/javac-sources.args'
        [IO.File]::WriteAllLines($argfile,[string[]]($files | ForEach-Object { '"' + $_.Replace('\','/') + '"' }),[Text.UTF8Encoding]::new($false))
        Run 'javac' @('--release','8','-encoding','UTF-8','-cp',($cp -join [IO.Path]::PathSeparator),'-d',$dest,"@$argfile")
        $cp += $dest
    }
    $duplicate = 'classes/commons-1.21/org/tweetyproject/logics/commons'
    if (Test-Path -LiteralPath $duplicate) { Remove-Item -LiteralPath $duplicate -Recurse -Force }
    $jspf = Join-Path $PSScriptRoot 'classes/jspf-1.0.2'
    Extract (Join-Path $PSScriptRoot 'jars/jspf-core-1.0.2.jar') $jspf
    $meta = Join-Path $jspf 'META-INF'
    if (Test-Path -LiteralPath $meta) { Remove-Item -LiteralPath $meta -Recurse -Force }
    $output = Join-Path $PSScriptRoot 'jars/org.tweetyproject.tweety-preferences-java8-shade.jar'
    $jarArgs = @('cf',$output)
    foreach ($module in ($modules + 'jspf-1.0.2')) { $jarArgs += @('-C',(Join-Path $PSScriptRoot "classes/$module"),'.') }
    Run 'jar' $jarArgs
    $zip = [IO.Compression.ZipFile]::OpenRead($output)
    try {
        $count = 0
        foreach ($entry in $zip.Entries) {
            if (-not $entry.FullName.EndsWith('.class')) { continue }
            $stream = $entry.Open()
            try {
                $header = [byte[]]::new(8)
                if ($stream.Read($header,0,8) -ne 8 -or $header[0] -ne 0xCA -or $header[1] -ne 0xFE -or $header[2] -ne 0xBA -or $header[3] -ne 0xBE) { throw "Classe invalide : $($entry.FullName)" }
                $major = ([int]$header[6] -shl 8) -bor $header[7]
                if ($major -gt 52) { throw "Bytecode $major supérieur à 52 : $($entry.FullName)" }
                $count++
            } finally { $stream.Dispose() }
        }
        if ($count -eq 0) { throw 'JAR sans classes' }
        Write-Host "Audit bytecode : $count classes, version majeure <= 52"
    } finally { $zip.Dispose() }
    New-Item -ItemType Directory -Force '../libs' | Out-Null
    Copy-Item -LiteralPath $output -Destination '../libs' -Force
    Write-Host 'JAR copié dans Tweety/libs ; construire ensuite build-TweetyPreferencesShade.csproj avec dotnet.'
} finally { Pop-Location }
