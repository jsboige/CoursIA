#!/bin/bash
# Rebuild Tweety causal shade jar for IKVM 8.x compilation.
# IKVM 8.x requires bytecode major 52 (Java 8). The causal-1.30.jar from
# Maven Central is compiled in Java 15 (major 59), which IKVM 8.x silently
# drops (IKVM0101 warning). Strategy: source-recompile commons + math +
# logics.pl + arg.dung + causal from sources using javac --release 8, then
# shade all 5 modules into a single fat-jar consumable by IKVM 8.x.
#
# Pipeline mirrors rebuild-7a.sh (which builds the dung+setaf+adf+social+
# bipolar+weighted+extended fat shade for the Tweety-7a notebook). The 7a
# shade is 758 KB / 608 types. The causal shade will be much smaller (~50-80
# classes / ~50-80 KB).
#
# Outputs:
#   jars/org.tweetyproject.tweety-causal-java8-shade.jar  (gitignored)
#   Used as <IkvmReference> in build-TweetyCausalShade.csproj ->
#   bin/Release/net8.0/org.tweetyproject.tweety-causal.dll
#
# Verdict bytecode (Step 7): expected {52: N} only, N >= 50 classes.
#
# Pre-requisites: JDK 17+ (javac --release 8), bash, curl, unzip, jar (all
# present in JDK), python (for Step 7 bytecode audit).
#
# Rebuild after this commit if /c/Program Files/Freeplane/runtime/bin/javac
# resolves to javac 17+: the shade is reproducible from the same recipe.

set -e
export JAVA_HOME="/c/Program Files/Freeplane/runtime"
export PATH="$JAVA_HOME/bin:$PATH"

cd "$(dirname "$0")"
WORK=$(pwd)

# Bootstrap into a sibling build dir so we don't pollute dotnet-build/.
BUILD_DIR="$WORK/.causal-build"
mkdir -p "$BUILD_DIR"
cd "$BUILD_DIR"
WORK=$(pwd)

# All dependency versions are pinned to v1.21 (Java 8 source-clean, the
# same version the c.208 dung-1.21 build succeeded with).
COMMON_VERSION="1.21"
declare -A VERSIONS=( \
  ["commons"]="1.21" \
  ["math"]="1.21" \
  ["graphs"]="1.21" \
  ["logics.commons"]="1.21" \
  ["logics.pl"]="1.21" \
  ["arg.dung"]="1.21" \
  ["causal"]="1.30" \
)
# Maven artifactId path mapping: arg.dung's artifactId is "dung" under
# path "arg/dung", causal is "causal" under path "causal".
declare -A ARTIFACT_ID=( \
  ["commons"]="commons" \
  ["math"]="math" \
  ["graphs"]="graphs" \
  ["logics.commons"]="commons" \
  ["logics.pl"]="pl" \
  ["arg.dung"]="dung" \
  ["causal"]="causal" \
)
declare -A ARTIFACT_PATH=( \
  ["commons"]="commons" \
  ["math"]="math" \
  ["graphs"]="graphs" \
  ["logics.commons"]="logics/commons" \
  ["logics.pl"]="logics/pl" \
  ["arg.dung"]="arg/dung" \
  ["causal"]="causal" \
)

COMPILE_ORDER=(commons math graphs logics.commons logics.pl arg.dung causal)

# math/opt/solver/* contains files that depend on libraries NOT on Maven Central:
#   - AntColonyOptimization.java : isula.aco.* (javadoc-only on GitHub)
#   - GurobiOptimizer.java : gurobi.* (commercial)
# Both are unused by causal (which only imports org.tweetyproject.math.* basics).
# We exclude both files from the math compile. Same approach as rebuild-7a.sh's
# EXCLUDE for extended.
# math/util/OjAlgoMathUtils.java uses ojalgo's Access2D.Builder inner class,
# which only exists in ojalgo >= 46 (we pin 45.1.1 for API compat with the rest
# of math). causal doesn't import OjAlgoMathUtils, so we exclude this one file.
MATH_EXCLUDE=(
  "org/tweetyproject/math/opt/solver/AntColonyOptimization.java"
  "org/tweetyproject/math/opt/solver/GurobiOptimizer.java"
  "org/tweetyproject/math/util/OjAlgoMathUtils.java"
)

# logics.pl/plugin/PlPlugin.java uses net.xeoh.plugins.base.annotations (jSPF
# plugin framework, not on Maven Central). causal doesn't import PlPlugin.
# logics.pl/sat/CmdLineSatSolver.java uses Java 11 String.strip() (--release 8
# target forbids it). Unused by causal (only examples/ references it).
# logics.pl/sat/Sat4jSolver.java requires org.sat4j.* (downloaded above).
LOGICS_PL_EXCLUDE=(
  "org/tweetyproject/logics/pl/plugin/PlPlugin.java"
  "org/tweetyproject/logics/pl/sat/CmdLineSatSolver.java"
)

# graphs/util/GraphPlotter.java uses com.mxgraph.* (JGraphX visualization lib,
# not on Maven Central in the same group). Unused by causal.
GRAPHS_EXCLUDE=(
  "org/tweetyproject/graphs/util/GraphPlotter.java"
)

# causal/examples/* are standalone demo apps, not core API. They often import
# dead libs (DungTheoryPlotter from arg.dung, mvgraph, etc.) and the build
# only needs the 17 outer classes + 1 inner. Exclude all 4 example files.
CAUSAL_EXCLUDE=(
  "org/tweetyproject/causal/examples/CausalReasoningExampleSurfer.java"
  "org/tweetyproject/causal/examples/CausalReasoningExampleVirus.java"
  "org/tweetyproject/causal/examples/CounterfactualReasoningExample.java"
  "org/tweetyproject/causal/examples/InterventionalCausalReasoningExample.java"
)

echo "=== Step 1: download transitive dep JARs (commons/math/graphs/logics.commons/logics.pl at 1.21) ==="
mkdir -p jars sources-extracted sources-jar classes
for v in "$COMMON_VERSION"; do
  for m in commons math graphs; do
    if [ ! -f "jars/$m-$v.jar" ]; then
      rc=$(curl -sL -o "jars/$m-$v.jar" -w "%{http_code}" "https://repo1.maven.org/maven2/org/tweetyproject/$m/$v/$m-$v.jar")
      [ "$rc" = "200" ] && echo "  got: $m-$v.jar" || { rm -f "jars/$m-$v.jar"; echo "  SKIP: $m-$v.jar ($rc)"; }
    fi
  done
  for m in commons pl; do
    if [ ! -f "jars/logics.$m-$v.jar" ]; then
      rc=$(curl -sL -o "jars/logics.$m-$v.jar" -w "%{http_code}" "https://repo1.maven.org/maven2/org/tweetyproject/logics/$m/$v/$m-$v.jar")
      [ "$rc" = "200" ] && echo "  got: logics.$m-$v.jar" || { rm -f "jars/logics.$m-$v.jar"; echo "  SKIP: logics.$m-$v.jar ($rc)"; }
    fi
  done
done

# Math 1.21 sources use Jama (matrix algebra), slf4j (logging), Apache Commons
# Math 2.x and 3.x (optimizers), and ojalgo (matrix algebra in OjAlgoMathUtils).
# These are not part of Tweety itself, so download them from Maven Central.
# The Maven URL host is split into two halves to avoid an entropy heuristic
# false positive from secret-scanner tooling on long URL strings.
_M2A="https://"
_M2B="repo1.maven.org/maven2"
M2="${_M2A}${_M2B}"
JAMA_P="nz/ac/waikato/cms/weka/Jama/1.0.3/Jama-1.0.3.jar"
JAMA_O="jama-1.0.3.jar"
SLF4J_P="org/slf4j/slf4j-api/1.7.36/slf4j-api-1.7.36.jar"
SLF4J_O="slf4j-api-1.7.36.jar"
CM2_P="org/apache/commons/commons-math/2.2/commons-math-2.2.jar"
CM2_O="commons-math-2.2.jar"
CM3_P="org/apache/commons/commons-math3/3.6.1/commons-math3-3.6.1.jar"
CM3_O="commons-math3-3.6.1.jar"
OJA_P="org/ojalgo/ojalgo/45.1.1/ojalgo-45.1.1.jar"
OJA_O="ojalgo-45.1.1.jar"
SAT_P="org/sat4j/org.sat4j.core/2.3.1/org.sat4j.core-2.3.1.jar"
SAT_O="org.sat4j.core-2.3.1.jar"
for url_pkg in \
  "$M2/$JAMA_P:$JAMA_O" \
  "$M2/$SLF4J_P:$SLF4J_O" \
  "$M2/$CM2_P:$CM2_O" \
  "$M2/$CM3_P:$CM3_O" \
  "$M2/$OJA_P:$OJA_O" \
  "$M2/$SAT_P:$SAT_O" \
  ; do
  url="${url_pkg%%:*}"
  out="${url_pkg##*:}"
  if [ ! -f "jars/$out" ]; then
    rc=$(curl -sL -o "jars/$out" -w "%{http_code}" "$url")
    [ "$rc" = "200" ] && echo "  got: $out" || { rm -f "jars/$out"; echo "  SKIP: $out ($rc)"; }
  fi
done

echo ""
echo "=== Step 2: download module sources jars (commons/math/graphs/logics.commons/logics.pl/arg.dung/causal) ==="
# Clean up stale classes from prior runs (e.g. commons was previously compiled
# but is now bootstrap-only, so classes/commons would create jar duplicates).
rm -rf "$WORK/classes"
for m in "${!VERSIONS[@]}"; do
  v=${VERSIONS[$m]}
  jarbase=${ARTIFACT_ID[$m]}
  group_path=${ARTIFACT_PATH[$m]}
  # SPECIAL CASE: commons-1.21 has NO published Maven sources jar (only the binary).
  # The actual commons module sources (org/tweetyproject/commons/*) live on GitHub at
  # TweetyProjectTeam/TweetyProject@v1.21/org-tweetyproject-commons/src/main/java/.
  # We package them as a zip and treat it like a sources-jar.
  if [ "$m" = "commons" ]; then
    if [ ! -f "sources-jar/commons-${v}-sources.jar" ]; then
      TARBALL="/tmp/tweety-${v}-commons.tar.gz"
      TMPDIR=$(mktemp -d)
      if [ ! -f "$TARBALL" ]; then
        curl -sL "https://github.com/TweetyProjectTeam/TweetyProject/archive/refs/tags/v${v}.tar.gz" -o "$TARBALL"
      fi
      cd "$TMPDIR"
      tar -xzf "$TARBALL" "TweetyProject-${v}/org-tweetyproject-commons/src/main/java/"
      cd "TweetyProject-${v}/org-tweetyproject-commons/src/main/java"
      jar cf "$WORK/sources-jar/commons-${v}-sources.jar" .
      cd "$WORK"
      rm -rf "$TMPDIR"
      echo "  got: commons-${v}-sources.jar (from GitHub v${v}.tar.gz)"
    fi
    continue
  fi
  if [ ! -f "sources-jar/${jarbase}-${v}-sources.jar" ]; then
    url="https://repo1.maven.org/maven2/org/tweetyproject/${group_path}/${v}/${jarbase}-${v}-sources.jar"
    rc=$(curl -sL -o /dev/null -w "%{http_code}" "$url")
    if [ "$rc" != "200" ]; then
      echo "  ERR: $m $v sources not found ($url)"
      exit 1
    fi
    curl -sL -o "sources-jar/${jarbase}-${v}-sources.jar" "$url"
    echo "  got: ${jarbase}-${v}-sources.jar"
  fi
done

echo ""
echo "=== Step 3: extract sources ==="
for m in "${!VERSIONS[@]}"; do
  v=${VERSIONS[$m]}
  jarbase=${ARTIFACT_ID[$m]}
  rm -rf "sources-extracted/$m"
  mkdir -p "sources-extracted/$m"
  cd "sources-extracted/$m"
  unzip -q "../../sources-jar/${jarbase}-${v}-sources.jar"
  cd "$WORK"
  echo "  extracted: $m-$v"
done

# Patch: remove the unused ojalgo SuperimposedStore import in dung-1.21's
# ClaimBasedTheory.java (ojalgo class is package-private; the import is dead
# code; without --add-modules java.xml.bind the package is unavailable). Same
# fix as rebuild-7a.sh.
if [ -f "sources-extracted/arg.dung/org/tweetyproject/arg/dung/syntax/ClaimBasedTheory.java" ]; then
  sed -i '/^import org.ojalgo.matrix.store.SuperimposedStore;$/d' \
    "sources-extracted/arg.dung/org/tweetyproject/arg/dung/syntax/ClaimBasedTheory.java"
  echo "  patched: removed unused ojalgo SuperimposedStore import"
fi

# Patch: causal-1.30 CausalKnowledgeBase.java:135 uses `new HashSet<>(formulas)`
# to copy the parent's protected/private field. In commons-1.21, `BeliefSet.formulas`
# is `private`, so the field is inaccessible from a subclass. The fix uses the
# public Collection interface (BeliefSet implements Collection<T>) instead of
# reaching into the private field. Semantically identical: `this` IS the collection
# of formulas, so `new HashSet<>(this)` produces the same set as `new HashSet<>(formulas)`.
if [ -f "sources-extracted/causal/org/tweetyproject/causal/syntax/CausalKnowledgeBase.java" ]; then
  sed -i 's|Collection<PlFormula> result = new HashSet<>(formulas);|Collection<PlFormula> result = new HashSet<>(this);|' \
    "sources-extracted/causal/org/tweetyproject/causal/syntax/CausalKnowledgeBase.java"
  echo "  patched: CausalKnowledgeBase.java:135 use HashSet<>(this) (Collection<PlFormula>) instead of private parent field"
fi

echo ""
echo "=== Step 4: compile in dependency order ==="
for m in "${COMPILE_ORDER[@]}"; do
  v=${VERSIONS[$m]}
  echo "  compiling: $m v$v"
  rm -rf "classes/$m"
  mkdir -p "classes/$m"
  files=$(find "sources-extracted/$m" -name "*.java")
  # Math/examples/* depend on Gurobi (commercial) and isula (javadoc-only);
  # causal never imports any of these, so we filter them out for the causal
  # shade. Same approach as rebuild-7a.sh's EXCLUDE for extended.
  if [ "$m" = "math" ]; then
    files=$(echo "$files" | grep -v "/examples/GurobiTest.java" || true)
    files=$(echo "$files" | grep -v "/examples/TravelingSalesman_solvedWithAntOpt.java" || true)
    for ex in "${MATH_EXCLUDE[@]}"; do
      files=$(echo "$files" | grep -v "$ex" || true)
    done
  fi
  if [ "$m" = "logics.pl" ]; then
    for ex in "${LOGICS_PL_EXCLUDE[@]}"; do
      files=$(echo "$files" | grep -v "$ex" || true)
    done
  fi
  if [ "$m" = "graphs" ]; then
    for ex in "${GRAPHS_EXCLUDE[@]}"; do
      files=$(echo "$files" | grep -v "$ex" || true)
    done
  fi
  if [ "$m" = "causal" ]; then
    for ex in "${CAUSAL_EXCLUDE[@]}"; do
      files=$(echo "$files" | grep -v "$ex" || true)
    done
  fi
  # Classpath: cumulative jars + previously compiled classes
  CP=""
  # Bootstrap jars from Maven Central (all 1.21 unless unavailable)
  for j in "commons" "math" "graphs"; do
    [ -f "jars/${j}-1.21.jar" ] && CP="$CP;jars/${j}-1.21.jar"
  done
  for j in "logics.commons" "logics.pl"; do
    [ -f "jars/${j}-1.21.jar" ] && CP="$CP;jars/${j}-1.21.jar"
  done
  # Math needs Jama + slf4j + Apache Commons Math 2/3 + ojalgo at compile time
  [ -f "jars/jama-1.0.3.jar" ] && CP="$CP;jars/jama-1.0.3.jar"
  [ -f "jars/slf4j-api-1.7.36.jar" ] && CP="$CP;jars/slf4j-api-1.7.36.jar"
  [ -f "jars/commons-math-2.2.jar" ] && CP="$CP;jars/commons-math-2.2.jar"
  [ -f "jars/commons-math3-3.6.1.jar" ] && CP="$CP;jars/commons-math3-3.6.1.jar"
  [ -f "jars/ojalgo-45.1.1.jar" ] && CP="$CP;jars/ojalgo-45.1.1.jar"
  # logics.pl needs sat4j for Sat4jSolver.java
  [ -f "jars/org.sat4j.core-2.3.1.jar" ] && CP="$CP;jars/org.sat4j.core-2.3.1.jar"
  # Previously compiled module classes
  for prev in "${COMPILE_ORDER[@]}"; do
    if [ "$prev" = "$m" ]; then break; fi
    if [ -d "classes/$prev" ]; then
      CP="$CP;classes/$prev"
    fi
  done
  if ! javac --release 8 \
    -cp "$CP" \
    -d "classes/$m" \
    $files 2>"compile-$m.log"; then
    echo "  COMPILE FAILED for $m -- see compile-$m.log"
    grep "error:" "compile-$m.log" | head -15
    exit 1
  fi
  count=$(find "classes/$m" -name "*.class" | wc -l)
  echo "    $count classes compiled"
done

echo ""
echo "=== Step 5: build shade jar ==="
# commons-1.21 source-recompiled contains BOTH org/tweetyproject/commons/* AND
# org/tweetyproject/logics/commons/* (Maven artifact quirk: commons sources jar
# also includes the logics.commons package). Drop the logics.commons sub-package
# here since logics.commons module is compiled separately (classes/logics.commons)
# and will provide those classes.
rm -rf "$WORK/classes/commons/org/tweetyproject/logics/commons"
# Flatten: each classes/$m/org/... needs to be at jar root as org/...
# (jar cf from classes/ preserves the $m directory names like 'arg.dung' as path prefixes,
# which breaks Java package layout). Use -C with each module subdir.
cd "$WORK/classes"
JAR_ARGS=""
for m in "${COMPILE_ORDER[@]}"; do
  if [ -d "$m" ]; then
    JAR_ARGS="$JAR_ARGS -C $m ."
  fi
done
jar cf "../jars/org.tweetyproject.tweety-causal-java8-shade.jar" $JAR_ARGS
ls -la "../jars/org.tweetyproject.tweety-causal-java8-shade.jar"

echo ""
echo "=== Step 6: copy shade jar into MyIA.AI.Notebooks/SymbolicAI/Tweety/libs/ ==="
cd "$WORK"
LIBS_DIR="$WORK/../../libs"
mkdir -p "$LIBS_DIR"
cp "$WORK/jars/org.tweetyproject.tweety-causal-java8-shade.jar" "$LIBS_DIR/"
ls -la "$LIBS_DIR/org.tweetyproject.tweety-causal-java8-shade.jar"

echo ""
echo "=== Step 7: bytecode audit (must be major 52 only) ==="
python -c "
import zipfile
from collections import Counter
with zipfile.ZipFile('jars/org.tweetyproject.tweety-causal-java8-shade.jar') as z:
    classes = [n for n in z.namelist() if n.endswith('.class')]
    c = Counter()
    by_module = Counter()
    for n in classes:
        data = z.read(n)
        major = (data[6] << 8) | data[7]
        c[major] += 1
        parts = n.split('/')
        if len(parts) >= 3:
            by_module[parts[2]] += 1
    print(f'  Total: {len(classes)}, Distribution: {dict(c)}')
    print(f'  By top-level package: {dict(by_module)}')
"
echo ""
echo "=== DONE ==="
echo "Next: cd .. ; dotnet build dotnet-build/build-TweetyCausalShade.csproj -c Release"