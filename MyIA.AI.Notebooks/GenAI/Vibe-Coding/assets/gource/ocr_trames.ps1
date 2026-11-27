param(
    [Parameter(Mandatory = $true)][string]$Root,
    [Parameter(Mandatory = $true)][string]$Out
)

# OCR des trames Gource par le moteur livre avec Windows (Windows.Media.Ocr).
# Parcourt <Root>\<variante>\trame_*.png et ecrit un TSV :
#   variante  indice  x  y  largeur  hauteur  texte
# Reprend la forme qui a deja servi (gource-run/ocr_lines.ps1) : @($line.Words)
# et $line.Text, pas de calcul par mot — un foreach sur $line.Words rend des
# elements imbriques sous PowerShell 5.1 et casse l'arithmetique.
# Chemins resolus en absolu : StorageFile.GetFileFromPathAsync refuse un relatif.
$ErrorActionPreference = 'Stop'
[Console]::OutputEncoding = [System.Text.Encoding]::UTF8

Add-Type -AssemblyName System.Runtime.WindowsRuntime
$null = [Windows.Storage.StorageFile, Windows.Storage, ContentType = WindowsRuntime]
$null = [Windows.Graphics.Imaging.BitmapDecoder, Windows.Graphics.Imaging, ContentType = WindowsRuntime]
$null = [Windows.Media.Ocr.OcrEngine, Windows.Foundation, ContentType = WindowsRuntime]
$null = [Windows.Globalization.Language, Windows.Globalization, ContentType = WindowsRuntime]

$asTaskGeneric = ([System.WindowsRuntimeSystemExtensions].GetMethods() | Where-Object {
        $_.Name -eq 'AsTask' -and $_.GetParameters().Count -eq 1 -and
        $_.GetParameters()[0].ParameterType.Name -eq 'IAsyncOperation`1'
    })[0]

function Await($WinRtTask, $ResultType, $Step) {
    try {
        $asTask = $asTaskGeneric.MakeGenericMethod($ResultType)
        $netTask = $asTask.Invoke($null, @($WinRtTask))
        $netTask.Wait(-1) | Out-Null
        $netTask.Result
    }
    catch {
        $inner = $_.Exception
        while ($null -ne $inner.InnerException) { $inner = $inner.InnerException }
        throw "etape $Step : $($inner.GetType().FullName) :: $($inner.Message)"
    }
}

$Root = [System.IO.Path]::GetFullPath($Root)
$Out = [System.IO.Path]::GetFullPath($Out)
if (-not (Test-Path -LiteralPath $Root -PathType Container)) { throw "repertoire absent : $Root" }

$engine = [Windows.Media.Ocr.OcrEngine]::TryCreateFromLanguage([Windows.Globalization.Language]::new('en-US'))
if ($null -eq $engine) { throw "aucun moteur OCR en-US" }

$files = Get-ChildItem -Path $Root -Recurse -Filter 'trame_*.png' -File | Sort-Object FullName
if ($files.Count -eq 0) { throw "aucune trame trame_*.png sous $Root" }

$rows = New-Object System.Collections.Generic.List[string]
$rows.Add("# moteur`t$($engine.RecognizerLanguage.LanguageTag)`tdimension max $($engine.MaxImageDimension) px`ttrames $($files.Count)")
$failed = 0
$clock = [System.Diagnostics.Stopwatch]::StartNew()

foreach ($item in $files) {
    $variant = $item.Directory.Name
    $index = [int]($item.BaseName -replace '^trame_', '')
    $stream = $null
    try {
        $file = Await ([Windows.Storage.StorageFile]::GetFileFromPathAsync($item.FullName)) ([Windows.Storage.StorageFile]) 'GetFile'
        $stream = Await ($file.OpenAsync([Windows.Storage.FileAccessMode]::Read)) ([Windows.Storage.Streams.IRandomAccessStream]) 'Open'
        $decoder = Await ([Windows.Graphics.Imaging.BitmapDecoder]::CreateAsync($stream)) ([Windows.Graphics.Imaging.BitmapDecoder]) 'Decode'
        $bitmap = Await ($decoder.GetSoftwareBitmapAsync()) ([Windows.Graphics.Imaging.SoftwareBitmap]) 'Bitmap'
        $result = Await ($engine.RecognizeAsync($bitmap)) ([Windows.Media.Ocr.OcrResult]) 'Recognize'
        foreach ($line in $result.Lines) {
            $words = @($line.Words)
            if ($words.Count -eq 0) { continue }
            $r = $words[0].BoundingRect
            [double]$x = $r.X
            [double]$y = $r.Y
            [double]$h = $r.Height
            [double]$right = $x
            foreach ($w in $words) {
                $wr = $w.BoundingRect
                [double]$edge = [double]$wr.X + [double]$wr.Width
                if ($edge -gt $right) { $right = $edge }
            }
            [double]$width = $right - $x
            $text = ($line.Text -replace '\s+', ' ').Trim()
            $rows.Add(("{0}`t{1}`t{2:0}`t{3:0}`t{4:0}`t{5:0}`t{6}" -f $variant, $index, $x, $y, $width, $h, $text))
        }
    }
    catch {
        $failed++
        [Console]::Error.WriteLine("ECHEC $($item.FullName) : $($_.Exception.Message)")
    }
    finally {
        if ($null -ne $stream) { $stream.Dispose() }
    }
}

[System.IO.File]::WriteAllLines($Out, $rows, (New-Object System.Text.UTF8Encoding($false)))
Write-Output ("trames={0} echecs={1} lignes={2} duree={3:0}s sortie={4}" -f $files.Count, $failed, ($rows.Count - 1), $clock.Elapsed.TotalSeconds, $Out)
if ($failed -gt 0) { exit 1 }
