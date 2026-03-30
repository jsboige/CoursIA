import papermill as pm
import os
import sys

# Configuration
input_path = "MyIA.AI.Notebooks/GenAI/01-Images-Foundation/01-4-Forge-SD-XL-Turbo.ipynb"
output_path = "MyIA.AI.Notebooks/GenAI/01-Images-Foundation/01-4-Forge-SD-XL-Turbo_output.ipynb"

# Set environment variable for local testing
os.environ["FORGE_API_URL"] = "http://localhost:17861"
os.environ["FORGE_USER"] = "admin"
os.environ["FORGE_PASSWORD"] = "changeme"

print(f"Starting execution of {input_path}...")

try:
    pm.execute_notebook(
        input_path,
        output_path,
        kernel_name='python3',
        progress_bar=True,
        stdout_file=sys.stdout,
        stderr_file=sys.stderr
    )
    print("Execution completed successfully!")
except Exception as e:
    print(f"Execution failed: {str(e)}")
    sys.exit(1)