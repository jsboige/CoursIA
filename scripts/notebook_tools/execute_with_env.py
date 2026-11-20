#!/usr/bin/env python3
"""
Execute notebook with environment variables loaded from GenAI/.env
Usage: python execute_with_env.py <notebook_path>
"""
import sys
import os
import subprocess
from pathlib import Path

# Load GenAI/.env first
env_file = Path('MyIA.AI.Notebooks/GenAI/.env')
if env_file.exists():
    with open(env_file) as f:
        for line in f:
            line = line.strip()
            if line and not line.startswith('#') and '=' in line:
                # Handle both KEY=VALUE and KEY="VALUE" formats
                if '=' in line:
                    key, value = line.split('=', 1)
                    key = key.strip()
                    value = value.strip().strip('"').strip("'")
                    os.environ[key] = value
                    # Also set OPENAI_API_KEY if OPENROUTER_API_KEY is set (for LangChain)
                    if key == 'OPENROUTER_API_KEY':
                        os.environ['OPENAI_API_KEY'] = value
                    if key == 'OPENROUTER_BASE_URL':
                        os.environ['OPENAI_BASE_URL'] = value

if __name__ == '__main__':
    if len(sys.argv) < 2:
        print("Usage: python execute_with_env.py <notebook_path>")
        sys.exit(1)

    notebook_path = sys.argv[1]

    # Execute notebook_tools.py with the environment variables
    result = subprocess.run(
        [sys.executable, 'scripts/notebook_tools/notebook_tools.py', 'execute', notebook_path],
        env=os.environ,
        timeout=600
    )
    sys.exit(result.returncode)
