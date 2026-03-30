"""
LeanDojo Repository Tests - Full tracing and theorem extraction.

Tests LeanDojo on different Lean repositories:
- lean4-example: Official LeanDojo example (Lean 4, small)
- formal-conjectures: Google DeepMind (Lean 4, Mathlib-based)
- lean-social-choice: Social Choice Theory (Lean 3 - expected failure)

IMPORTANT: On Windows, run with if __name__ == '__main__' guard
due to multiprocessing requirements.

Usage:
    python test_leandojo_repos.py [repo_name]

Examples:
    python test_leandojo_repos.py                  # Test lean4-example (default)
    python test_leandojo_repos.py example          # Test lean4-example
    python test_leandojo_repos.py deepmind         # Test formal-conjectures
    python test_leandojo_repos.py social-choice    # Test lean-social-choice (Lean 3)
    python test_leandojo_repos.py all              # Test all repos
"""
import os
import sys
import time
from pathlib import Path
from multiprocessing import freeze_support


# Repository configurations
REPOS = {
    "example": {
        "name": "lean4-example",
        "url": "https://github.com/yangky11/lean4-example",
        "commit": "7761283d0aed994cd1c7e893786212d2a01d159e",
        "lean_version": "4.x",
        "description": "Official LeanDojo example repo (small, quick test)",
        "expected_success": True,
    },
    "deepmind": {
        "name": "formal-conjectures",
        "url": "https://github.com/google-deepmind/formal-conjectures",
        "commit": "ce0a081ab74d625948c44da6022992e1f9db070a",
        "lean_version": "4.22.0",
        "description": "Google DeepMind formalized conjectures (large, Mathlib-based)",
        "expected_success": True,
        "note": "First trace downloads Mathlib4 dependencies (~1GB)",
    },
    "social-choice": {
        "name": "lean-social-choice",
        "url": "https://github.com/asouther4/lean-social-choice",
        "commit": "9906ade382ace77af4fef1edb70364b84f7afd9c",
        "lean_version": "3.x",
        "description": "Social Choice Theory library (Lean 3)",
        "expected_success": False,
        "note": "LeanDojo 4.x requires Lean 4 repos with lean-toolchain file",
    },
}


def load_github_token():
    """Load GitHub token from local .env file or gh CLI."""
    if "GITHUB_ACCESS_TOKEN" in os.environ:
        return True

    # Try .env files
    for env_path in [
        Path(__file__).parent / ".env",
        Path(__file__).parent.parent / ".env",
    ]:
        if env_path.exists():
            with open(env_path) as f:
                for line in f:
                    line = line.strip()
                    if line.startswith("GITHUB_ACCESS_TOKEN="):
                        os.environ["GITHUB_ACCESS_TOKEN"] = line.split("=", 1)[1].strip()
                        return True
                    elif line.startswith("GITHUB_TOKEN=") and "GITHUB_ACCESS_TOKEN" not in os.environ:
                        os.environ["GITHUB_ACCESS_TOKEN"] = line.split("=", 1)[1].strip()
                        return True

    # Try gh CLI
    try:
        import subprocess
        result = subprocess.run(["gh", "auth", "token"], capture_output=True, text=True)
        if result.returncode == 0:
            os.environ["GITHUB_ACCESS_TOKEN"] = result.stdout.strip()
            return True
    except:
        pass

    return "GITHUB_ACCESS_TOKEN" in os.environ


def test_repo(repo_key: str) -> dict:
    """
    Test LeanDojo on a specific repository.

    Returns dict with:
    - success: bool
    - repo_created: bool
    - traced: bool
    - theorems_count: int
    - dojo_tested: bool
    - trace_time: float
    - error: str or None
    """
    from lean_dojo import LeanGitRepo, trace, is_available_in_cache, Dojo

    config = REPOS[repo_key]
    result = {
        "success": False,
        "repo_created": False,
        "traced": False,
        "theorems_count": 0,
        "dojo_tested": False,
        "trace_time": 0,
        "error": None,
    }

    print(f"\n{'=' * 60}")
    print(f"Testing: {config['name']}")
    print(f"{'=' * 60}")
    print(f"URL: {config['url']}")
    print(f"Lean version: {config['lean_version']}")
    print(f"Description: {config['description']}")
    if "note" in config:
        print(f"Note: {config['note']}")

    # Step 1: Create LeanGitRepo
    print(f"\n[1/4] Creating LeanGitRepo...")
    try:
        repo = LeanGitRepo(config["url"], config["commit"])
        print(f"  Commit: {repo.commit[:12]}")
        print(f"  Exists: {repo.exists()}")
        print(f"  In cache: {is_available_in_cache(repo)}")
        result["repo_created"] = True
    except Exception as e:
        print(f"  ERROR: {e}")
        result["error"] = str(e)
        return result

    # Step 2: Trace the repo
    print(f"\n[2/4] Tracing repo...")
    if config["lean_version"].startswith("3"):
        print("  WARNING: Lean 3 repo - LeanDojo 4.x requires Lean 4")

    start_time = time.time()
    try:
        traced_repo = trace(repo)
        result["trace_time"] = time.time() - start_time
        print(f"  Trace complete in {result['trace_time']:.1f}s")
        result["traced"] = True
    except Exception as e:
        result["trace_time"] = time.time() - start_time
        print(f"  ERROR during trace: {e}")
        result["error"] = str(e)
        if not config["expected_success"]:
            print(f"  (Expected failure for Lean {config['lean_version']} repo)")
        return result

    # Step 3: Extract theorems
    print(f"\n[3/4] Extracting theorems...")
    try:
        theorems = list(traced_repo.get_theorems())
        result["theorems_count"] = len(theorems)
        print(f"  Found {len(theorems)} theorems")

        # Show sample theorems
        print(f"\n  Sample theorems:")
        for i, thm in enumerate(theorems[:5]):
            print(f"    [{i+1}] {thm.full_name}")
            if hasattr(thm, 'file_path'):
                print(f"        File: {thm.file_path}")
    except Exception as e:
        print(f"  ERROR: {e}")
        result["error"] = str(e)
        theorems = []

    # Step 4: Test Dojo interaction
    if theorems:
        print(f"\n[4/4] Testing Dojo interaction...")
        thm = theorems[0]
        print(f"  Theorem: {thm.full_name}")

        try:
            with Dojo(thm) as (dojo, init_state):
                print(f"  Initial state goals: {len(init_state.goals)}")
                if init_state.goals:
                    goal_str = str(init_state.goals[0])
                    if len(goal_str) > 80:
                        goal_str = goal_str[:80] + "..."
                    print(f"  Goal 0: {goal_str}")

                # Try tactics
                for tactic in ["intro", "rfl", "simp"]:
                    tac_result = dojo.run_tac(init_state, tactic)
                    if tac_result is not None:
                        print(f"  After '{tactic}': {len(tac_result.goals)} goals")
                        break
                    else:
                        print(f"  '{tactic}' failed (expected)")

                result["dojo_tested"] = True
        except Exception as e:
            print(f"  ERROR in Dojo: {e}")
    else:
        print(f"\n[4/4] Skipping Dojo test (no theorems found)")

    result["success"] = result["traced"] and result["theorems_count"] > 0
    return result


def print_summary(results: dict):
    """Print summary of all test results."""
    print(f"\n{'=' * 60}")
    print("SUMMARY")
    print(f"{'=' * 60}")

    for repo_key, result in results.items():
        config = REPOS[repo_key]
        status = "PASS" if result["success"] else "FAIL"
        expected = "expected" if result["success"] == config["expected_success"] else "UNEXPECTED"

        print(f"\n{config['name']} ({config['lean_version']}):")
        print(f"  Status: {status} ({expected})")
        print(f"  Repo created: {result['repo_created']}")
        print(f"  Traced: {result['traced']}")
        print(f"  Theorems: {result['theorems_count']}")
        print(f"  Dojo tested: {result['dojo_tested']}")
        if result["trace_time"] > 0:
            print(f"  Trace time: {result['trace_time']:.1f}s")
        if result["error"]:
            print(f"  Error: {result['error'][:100]}")


def main():
    """Main test function."""
    if not load_github_token():
        print("ERROR: No GitHub token found")
        print("Set GITHUB_ACCESS_TOKEN in .env or use 'gh auth login'")
        sys.exit(1)

    print(f"GitHub token: OK ({os.environ['GITHUB_ACCESS_TOKEN'][:10]}...)")
    print(f"Python: {sys.version.split()[0]}")

    # Parse command line arguments
    if len(sys.argv) > 1:
        arg = sys.argv[1].lower()
        if arg == "all":
            repos_to_test = list(REPOS.keys())
        elif arg in REPOS:
            repos_to_test = [arg]
        elif arg in ["lean4-example", "example", "yangky11"]:
            repos_to_test = ["example"]
        elif arg in ["formal-conjectures", "deepmind", "google"]:
            repos_to_test = ["deepmind"]
        elif arg in ["lean-social-choice", "social-choice", "social"]:
            repos_to_test = ["social-choice"]
        else:
            print(f"Unknown repo: {arg}")
            print(f"Available: {', '.join(REPOS.keys())}, all")
            sys.exit(1)
    else:
        repos_to_test = ["example"]  # Default to small example

    # Import LeanDojo (after freeze_support)
    print("\nLoading LeanDojo...")
    try:
        from lean_dojo import LeanGitRepo, trace
        print("LeanDojo imports: OK")
    except ImportError as e:
        print(f"ERROR: Cannot import LeanDojo: {e}")
        sys.exit(1)

    # Run tests
    results = {}
    for repo_key in repos_to_test:
        results[repo_key] = test_repo(repo_key)

    # Print summary
    print_summary(results)

    # Exit code
    all_expected = all(
        results[k]["success"] == REPOS[k]["expected_success"]
        for k in results
    )
    if all_expected:
        print(f"\nAll tests completed as expected.")
    else:
        print(f"\nSome tests had unexpected results!")
        sys.exit(1)


if __name__ == '__main__':
    freeze_support()
    main()
