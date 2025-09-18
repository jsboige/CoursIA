#!/usr/bin/env python3
"""Test des variables d'environnement .NET dans l'environnement mcp-jupyter"""

import os

print("=== TEST VARIABLES D'ENVIRONNEMENT .NET ===")
print(f"DOTNET_ROOT: {os.getenv('DOTNET_ROOT', 'NON DÉFINI')}")
print(f"NUGET_PACKAGES: {os.getenv('NUGET_PACKAGES', 'NON DÉFINI')}")
print(f"PACKAGEMANAGEMENT_HOME: {os.getenv('PACKAGEMANAGEMENT_HOME', 'NON DÉFINI')}")

# Test variables système supplémentaires
print(f"\nAUTRES VARIABLES .NET:")
print(f"PATH (excerpt): {';'.join([p for p in os.getenv('PATH', '').split(';') if 'dotnet' in p.lower()])}")
print(f"DOTNET_CLI_HOME: {os.getenv('DOTNET_CLI_HOME', 'NON DÉFINI')}")
print(f"MSBuildSDKsPath: {os.getenv('MSBuildSDKsPath', 'NON DÉFINI')}")