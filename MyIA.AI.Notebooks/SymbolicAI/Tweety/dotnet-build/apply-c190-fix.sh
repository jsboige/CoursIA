#!/bin/bash
# Apply C190 exclusion pattern (isula + commons-lang3 + gurobi) to all shade POMs.
# Pre-requisite: existing shade POMs from C182/C183/C185/C186/C187/C188.
#
# Usage: apply-c190-fix.sh
# Output: All 10 shade POMs updated with the isula/lang3/gurobi exclusions.

set -e

cd "/c/dev/CoursIA-2-ikvm814/MyIA.AI.Notebooks/SymbolicAI/Tweety/dotnet-build"

# Add the C190 exclusion block right before the </exclusions> closing tag
# in each shade POM that has the unit-bom marker (the 6 broken ones).
POMS=(
    build-tweety-advanced-logics-shade.pom.xml
    build-tweety-conditional-logics-shade.pom.xml
    build-tweety-qbf-shade.pom.xml
    build-tweety-ml-shade.pom.xml
    build-tweety-mln-shade.pom.xml
    build-tweety-rpcl-shade.pom.xml
)

for pom in "${POMS[@]}"; do
    if grep -q "isula</artifactId>" "$pom"; then
        echo "[skip] $pom already has isula exclusion"
        continue
    fi

    # Insert the isula/lang3/gurobi exclusion block before </exclusions>
    python3 - "$pom" <<'PYEOF'
import sys, re

pom_path = sys.argv[1]
with open(pom_path) as f:
    content = f.read()

exclusion_block = """        <exclusion>
          <groupId>isula</groupId>
          <artifactId>isula</artifactId>
        </exclusion>
        <exclusion>
          <groupId>org.apache.commons</groupId>
          <artifactId>commons-lang3</artifactId>
        </exclusion>
        <exclusion>
          <groupId>gurobi</groupId>
          <artifactId>gurobi</artifactId>
        </exclusion>
      </exclusions>"""

content = content.replace(
    "      </exclusions>",
    exclusion_block,
    1,
)
content = content.replace(
    exclusion_block.replace("      </exclusions>", "</exclusions>"),
    exclusion_block,
)

with open(pom_path, "w") as f:
    f.write(content)

print(f"  [updated] {pom_path}")
PYEOF
done

echo "Done. Verify with: grep -c isula build-tweety-*-shade.pom.xml"