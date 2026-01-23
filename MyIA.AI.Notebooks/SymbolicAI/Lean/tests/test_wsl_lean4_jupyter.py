"""
Test lean4_jupyter in WSL via jupyter_client
"""
import subprocess
import sys

# Test script to run in WSL
test_code = '''
import json
from jupyter_client import KernelManager

# Start lean4 kernel
km = KernelManager(kernel_name='lean4')
km.start_kernel()
kc = km.client()
kc.start_channels()

print("Waiting for kernel...")
kc.wait_for_ready(timeout=60)
print("Kernel ready!")

# Test code
lean_code = "#eval 2 + 2"
print(f"Running: {lean_code}")

msg_id = kc.execute(lean_code)

# Get result
while True:
    try:
        msg = kc.get_iopub_msg(timeout=30)
        msg_type = msg['msg_type']
        content = msg.get('content', {})

        if msg_type == 'stream':
            print(f"Output: {content.get('text', '')}")
        elif msg_type == 'execute_result':
            print(f"Result: {content.get('data', {}).get('text/plain', '')}")
        elif msg_type == 'error':
            print(f"Error: {content.get('evalue', '')}")
        elif msg_type == 'status' and content.get('execution_state') == 'idle':
            break
    except Exception as e:
        print(f"Exception: {e}")
        break

# Cleanup
kc.stop_channels()
km.shutdown_kernel(now=True)
print("Done!")
'''

# Write test script
with open('/tmp/test_lean4.py', 'w') as f:
    f.write(test_code)

# Note: This script should be run inside WSL
print("Test script written to /tmp/test_lean4.py")
print("Run with: wsl -d Ubuntu -- bash -c 'source ~/.lean4-venv/bin/activate && source ~/.elan/env && python /tmp/test_lean4.py'")
