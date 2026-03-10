$ErrorActionPreference = "Continue"
python scripts/notebook_tools/notebook_tools.py validate MyIA.AI.Notebooks/GenAI --verbose 2>&1 | Out-File -FilePath validation_output.txt -Encoding UTF8
Get-Content validation_output.txt | Select-String -Pattern "receipe_maker|01-5-Qwen|HunyuanVideo" -Context 3,3
