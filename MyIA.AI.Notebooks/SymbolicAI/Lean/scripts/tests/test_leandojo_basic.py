"""
LeanDojo Basic Tests - Quick validation without tracing.

Tests:
- Module imports
- GitHub token loading
- LeanGitRepo creation
- Cache status check
- API availability

IMPORTANT: On Windows, run with if __name__ == '__main__' guard
due to multiprocessing requirements.

Usage:
    python test_leandojo_basic.py
"""
import os
import sys
from pathlib import Path
from multiprocessing import freeze_support


def load_github_token():
    """Load GitHub token from local .env file or gh CLI."""
    # 1. Check environment
    if "GITHUB_ACCESS_TOKEN" in os.environ:
        return True

    # 2. Try local .env file
    env_path = Path(__file__).parent / ".env"
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

    # 3. Try parent .env file
    env_path = Path(__file__).parent.parent / ".env"
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

    # 4. Try gh CLI
    try:
        import subprocess
        result = subprocess.run(["gh", "auth", "token"], capture_output=True, text=True)
        if result.returncode == 0:
            os.environ["GITHUB_ACCESS_TOKEN"] = result.stdout.strip()
            return True
    except:
        pass

    return "GITHUB_ACCESS_TOKEN" in os.environ


def test_imports():
    """Test LeanDojo module imports."""
    print("\n[1/4] Testing imports...")

    try:
        import lean_dojo
        print(f"  lean_dojo version: {lean_dojo.__version__}")
    except ImportError as e:
        print(f"  ERROR: Cannot import lean_dojo: {e}")
        return False

    try:
        from lean_dojo import LeanGitRepo, trace, Dojo, Theorem, TacticState
        print("  Core classes: OK")
    except ImportError as e:
        print(f"  ERROR: Cannot import core classes: {e}")
        return False

    try:
        from lean_dojo import is_available_in_cache, get_traced_repo_path
        print("  Cache utilities: OK")
    except ImportError as e:
        print(f"  ERROR: Cannot import cache utilities: {e}")
        return False

    return True


def test_repo_creation():
    """Test LeanGitRepo creation without tracing."""
    print("\n[2/4] Testing LeanGitRepo creation...")

    from lean_dojo import LeanGitRepo

    # Test with official example repo
    REPO_URL = "https://github.com/yangky11/lean4-example"
    REPO_COMMIT = "7761283d0aed994cd1c7e893786212d2a01d159e"

    try:
        repo = LeanGitRepo(REPO_URL, REPO_COMMIT)
        print(f"  URL: {repo.url}")
        print(f"  Commit: {repo.commit[:12]}")
        print(f"  Exists: {repo.exists()}")
        return repo
    except Exception as e:
        print(f"  ERROR: {e}")
        return None


def test_cache_status(repo):
    """Test cache status check."""
    print("\n[3/4] Testing cache status...")

    from lean_dojo import is_available_in_cache

    try:
        cached = is_available_in_cache(repo)
        print(f"  In cache: {cached}")

        if cached:
            from lean_dojo import get_traced_repo_path
            path = get_traced_repo_path(repo)
            print(f"  Cache path: {path}")

        return True
    except Exception as e:
        print(f"  ERROR: {e}")
        return False


def test_github_api():
    """Test GitHub API access (used internally by LeanDojo)."""
    print("\n[4/4] Testing GitHub API access...")

    try:
        from lean_dojo.data_extraction.lean import GITHUB
        print(f"  GitHub rate limit: {GITHUB.rate_limiting}")

        # Test simple API call
        gh_repo = GITHUB.get_repo("yangky11/lean4-example")
        print(f"  Test repo: {gh_repo.full_name}")
        print(f"  Stars: {gh_repo.stargazers_count}")
        return True
    except Exception as e:
        print(f"  ERROR: {e}")
        return False


def main():
    """Run all basic tests."""
    print("=" * 60)
    print("LeanDojo Basic Tests")
    print("=" * 60)

    # Load GitHub token
    if load_github_token():
        token = os.environ.get("GITHUB_ACCESS_TOKEN", "")
        print(f"GitHub token: OK ({token[:10]}...)")
    else:
        print("WARNING: No GitHub token found")
        print("Set GITHUB_ACCESS_TOKEN in .env or use 'gh auth login'")

    print(f"Python: {sys.version.split()[0]}")

    # Run tests
    results = {}

    results["imports"] = test_imports()
    if not results["imports"]:
        print("\nERROR: Import test failed, cannot continue")
        sys.exit(1)

    repo = test_repo_creation()
    results["repo_creation"] = repo is not None

    if repo:
        results["cache_status"] = test_cache_status(repo)
    else:
        results["cache_status"] = False

    results["github_api"] = test_github_api()

    # Summary
    print("\n" + "=" * 60)
    print("Summary")
    print("=" * 60)

    passed = sum(1 for v in results.values() if v)
    total = len(results)

    for name, passed_test in results.items():
        status = "PASS" if passed_test else "FAIL"
        print(f"  {name}: {status}")

    print(f"\nResult: {passed}/{total} tests passed")

    if passed == total:
        print("\nLeanDojo basic tests: ALL PASSED")
        print("\nNote: For full tracing tests, run test_leandojo_repos.py")
    else:
        print("\nLeanDojo basic tests: SOME FAILED")
        sys.exit(1)


if __name__ == '__main__':
    freeze_support()
    main()
