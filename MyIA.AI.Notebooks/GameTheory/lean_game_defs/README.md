# Lean Game Definitions

Shared type definitions used by multiple GameTheory Lean projects. Not a standalone Lake project.

## Status

- **Type**: Code snippets (no lakefile, no toolchain)
- **Purpose**: Shared definitions imported by adjacent Lake projects

## Files

| File | Description |
|------|-------------|
| `Basic.lean` | Base type definitions for game theory |
| `Combinatorial.lean` | Combinatorial game definitions |
| `Nash.lean` | Nash equilibrium type definitions |
| `SocialChoice.lean` | Social choice type definitions |

## Notes

- This is NOT a buildable Lake project -- it provides shared definitions
- Other Lake projects in `GameTheory/` reference these files as needed
- Files are meant to be copied or imported into Lake project contexts
