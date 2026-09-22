#!/usr/bin/env bash
# Lanceur de la tache planifiee CoursIA-LinuxRunners-po2026.
# Delegue au superviseur du pool dans WSL Ubuntu, DANS un scope systemd borne.
# Sources maintenues hors depot, dans DEUX repertoires distincts : pool.sh sous
# D:\Dev\CoursIA-runners-p0\, et ce lanceur sous C:\dev\CoursIA-runners-p0\ (le
# chemin fige dans l'action de la tache planifiee).
#
# ATTENTION -- piege mesure le 2026-09-22, la raison d'etre de la forme ci-dessous :
# la commande passee a `wsl.exe` ne doit contenir AUCUN `$`. Git Bash (MSYS) mange
# les references `$VAR` avant que WSL ne les voie. La forme precedente,
#   bash -lc 'UNIT=...; systemd-run --scope --unit="$UNIT" ... "$HOME/.../pool.sh"'
# arrivait donc en `--unit=` VIDE et en chemin VIDE, et systemd-run echouait sur
#   "Failed to mangle scope name: Invalid argument"
# sans jamais atteindre pool.sh. Consequence : le pool n'etait pas seulement non
# borne, il n'etait meme pas relancable par la tache planifiee. Les chemins sont
# donc ecrits en clair et la commande ne porte plus aucune variable.
#
# Dimensionnement mesure sur po-2026 (pas recopie d'ai-01) :
#   vCPU 20 (i7-12700H) | VM WSL ~23 Go | swap 32 Go
#   CPUQuota 1400%  -> 14 des 20 vCPU pour la CI, 6 reserves a l'interactif
#   MemoryMax 20 Go -> backstop contre la famine de la lane interactive ;
#                      le plafond dur reste la memoire de la VM
#   NB : le cap annonce etait 16 Go, il est porte a 20 Go. Motif mesure au README
#   du chantier (correction 5) : un cap juge « ~10x le pic mesure » a deja fait OOM
#   un rendu Quarto, et le pic de la phase de test est NON MESURE sur cette machine.
set -e
exec wsl.exe -d Ubuntu -- bash -lc 'systemctl --user reset-failed coursia-pool-po2026.scope 2>/dev/null; exec systemd-run --user --scope --unit=coursia-pool-po2026 -p CPUQuota=1400% -p MemoryMax=20G /home/jesse/CoursIA-runners-p0/pool.sh'
