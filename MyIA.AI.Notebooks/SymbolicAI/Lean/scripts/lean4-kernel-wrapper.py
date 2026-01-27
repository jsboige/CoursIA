#!/usr/bin/env python3
r"""
Lean 4 Jupyter Kernel Wrapper for WSL

This script converts Windows paths to WSL paths and launches the lean4_jupyter kernel.
It handles various path formats that VSCode/Jupyter might pass:
- Standard Windows paths: C:\Users\...
- Tilde shorthand: ~\AppData\... or ~/AppData/...
- Mangled paths (backslashes eaten): c:UsersjsboiAppData...
"""
import sys
import subprocess
import os
import re


def convert_windows_path(path):
    """Convert Windows path to WSL path, handling various formats."""
    if not path:
        return path

    # Already a Unix path
    if path.startswith('/'):
        return path

    # Handle ~ shorthand (Windows-style: ~\AppData or ~/AppData)
    if path.startswith('~\\') or path.startswith('~/'):
        # Find the Windows user's home directory
        users_dir = '/mnt/c/Users'
        if os.path.exists(users_dir):
            for user in os.listdir(users_dir):
                user_lower = user.lower()
                if user_lower not in ['public', 'default', 'default user', 'all users']:
                    # Check if this looks like a real user directory
                    user_path = os.path.join(users_dir, user)
                    if os.path.isdir(user_path) and os.path.exists(os.path.join(user_path, 'AppData')):
                        win_home = f'/mnt/c/Users/{user}'
                        rest = path[1:].lstrip('\\').lstrip('/')
                        rest = rest.replace('\\', '/')
                        return f'{win_home}/{rest}'
        # Fallback: hardcoded user
        rest = path[1:].lstrip('\\').lstrip('/').replace('\\', '/')
        return f'/mnt/c/Users/jsboi/{rest}'

    # Check for mangled path FIRST (backslashes eaten): c:UsersjsboiAppData...
    # This happens when VSCode passes paths through certain shells
    if len(path) >= 2 and path[1] == ':':
        # Detect mangled path: has Users immediately after drive letter without separator
        if path[2:].startswith('Users') and '\\' not in path and '/' not in path[2:]:
            match = re.match(r'([a-zA-Z]):Users([a-z0-9_]+)AppDataRoaming(.+)', path, re.IGNORECASE)
            if match:
                drive = match.group(1).lower()
                user = match.group(2)
                rest = match.group(3)
                # Re-insert slashes at known boundaries
                rest = rest.replace('jupyter', '/jupyter').replace('runtime', '/runtime')
                rest = rest.replace('kernel-', '/kernel-')
                rest = rest.lstrip('/')
                return f'/mnt/{drive}/Users/{user}/AppData/Roaming/{rest}'

        # Standard Windows path with proper separators (C:\... or C:/...)
        # Use wslpath for proper conversion
        try:
            result = subprocess.run(['wslpath', '-a', path], capture_output=True, text=True, timeout=5)
            if result.returncode == 0:
                return result.stdout.strip()
        except:
            pass
        # Fallback manual conversion for paths with separators
        drive = path[0].lower()
        rest = path[2:].replace('\\', '/').lstrip('/')
        return f'/mnt/{drive}/{rest}'

    return path


def main():
    log_file = os.path.expanduser('~/.lean4-wrapper.log')

    def log(msg):
        try:
            with open(log_file, 'a') as f:
                f.write(f"{msg}\n")
        except:
            pass

    log(f"=== Wrapper started ===")
    log(f"sys.argv: {sys.argv}")

    # Process arguments
    args = sys.argv[1:]
    for i, arg in enumerate(args):
        if arg == '-f' and i + 1 < len(args):
            original = args[i + 1]
            converted = convert_windows_path(args[i + 1])
            args[i + 1] = converted
            log(f"Original: {original}")
            log(f"Converted: {converted}")

            # Check if file exists
            if os.path.exists(converted):
                log(f"Connection file EXISTS")
            else:
                log(f"Connection file MISSING - waiting...")
                # Wait up to 2 seconds for file to appear
                import time
                for _ in range(20):
                    time.sleep(0.1)
                    if os.path.exists(converted):
                        log(f"Connection file appeared")
                        break
                else:
                    log(f"Connection file still missing after wait")
            break

    # Set up environment with CLEAN PATH (not inheriting polluted Windows PATH)
    # The Windows PATH causes issues because it contains spaces and special chars
    os.environ['PATH'] = '/home/jesse/.elan/bin:/home/jesse/.lean4-venv/bin:/usr/local/bin:/usr/bin:/bin'
    os.chdir(os.path.expanduser('~'))
    log(f"PATH set (clean): {os.environ['PATH']}")
    log(f"cwd: {os.getcwd()}")
    log(f"About to launch kernel with args: {args}")

    # Launch the kernel directly using IPKernelApp.launch_instance
    # NOTE: python -m lean4_jupyter.kernel exits immediately for unknown reasons
    # But calling IPKernelApp.launch_instance directly works correctly
    log(f"Launching kernel directly via IPKernelApp.launch_instance")

    try:
        # Set sys.argv for the kernel to parse
        sys.argv = ['lean4_jupyter'] + args
        log(f"sys.argv set to: {sys.argv}")

        # Import and launch the kernel
        from ipykernel.kernelapp import IPKernelApp
        from lean4_jupyter.kernel import Lean4Kernel

        log(f"Starting kernel...")
        IPKernelApp.launch_instance(kernel_class=Lean4Kernel)
        log(f"Kernel exited normally")
    except SystemExit as e:
        log(f"SystemExit: {e}")
        sys.exit(e.code if e.code is not None else 0)
    except Exception as e:
        log(f"Exception launching kernel: {e}")
        import traceback
        log(traceback.format_exc())
        sys.exit(1)


if __name__ == '__main__':
    main()
