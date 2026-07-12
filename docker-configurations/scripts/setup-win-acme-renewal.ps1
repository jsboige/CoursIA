# Run this script as Administrator to create the win-acme renewal task
# Right-click > Run as Administrator, or: Start-Process powershell -Verb RunAs -ArgumentList "-File `"$PSCommandPath`""

$wacsExe = "C:\tools\win-acme\wacs.exe"
$taskName = "win-acme-cert-renewal"

# Check if already exists
$existing = Get-ScheduledTask -TaskName $taskName -ErrorAction SilentlyContinue
if ($existing) {
    Write-Output "Task '$taskName' already exists (state: $($existing.State)). Removing and recreating..."
    Unregister-ScheduledTask -TaskName $taskName -Confirm:$false
}

$action = New-ScheduledTaskAction -Execute $wacsExe -Argument "--renew --baseurl ""https://acme-v02.api.letsencrypt.org/directory""" -WorkingDirectory "C:\tools\win-acme"
$trigger = New-ScheduledTaskTrigger -Daily -At "03:00"
$principal = New-ScheduledTaskPrincipal -UserId "SYSTEM" -LogonType ServiceAccount -RunLevel Highest
$settings = New-ScheduledTaskSettingsSet -StartWhenAvailable -DontStopOnIdleEnd -AllowStartIfOnBatteries -DontStopIfGoingOnBatteries

Register-ScheduledTask -TaskName $taskName -Action $action -Trigger $trigger -Principal $principal -Settings $settings -Description "Auto-renew Let's Encrypt SSL certificates via win-acme" -Force

Write-Output "`nTask created successfully. Verifying..."
Get-ScheduledTask -TaskName $taskName | Format-List TaskName, State, Description

Write-Output "`nNext: Run 'C:\tools\win-acme\wacs.exe' as admin to import existing certs or create new orders."