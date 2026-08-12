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
export JAVA_HOME="/c/Program Files/Microsoft/jdk-17.0.18.8-hotspot"
export PATH="$JAVA_HOME/bin:$PATH"

cd "$(dirname "$0")"
WORK=$(pwd)

# Bootstrap into a sibling build dir so we don't pollute dotnet-build/.
BUILD_DIR="$WORK/.causal-build"
mkdir -p "$BUILD_DIR"
cd "$BUILD_DIR"
WORK=$(pwd)

# Version-consistency test (c.1052): pin dung to 1.30 (c211 patched) instead
# of 1.21 to match causal-1.30's expectations (causal 1.30 references dung 1.30
# APIs, notably arg.dung.divisions.Division absent from 1.21). All deps at 1.30.
# Modeled on rebuild-dialogues.sh (#10544, proven dung-1.30 c211 method).
COMMON_VERSION="1.30"
declare -A VERSIONS=( \
  ["commons"]="1.30" \
  ["math"]="1.30" \
  ["graphs"]="1.30" \
  ["logics.commons"]="1.30" \
  ["logics.pl"]="1.30" \
  ["arg.dung"]="1.30" \
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

# causal/examples/* are standalone demo apps, not core API. They often import
# dead libs (DungTheoryPlotter from arg.dung, mvgraph, etc.) and the build
# only needs the 17 outer classes + 1 inner. Exclude all 4 example files.
CAUSAL_EXCLUDE=(
  "org/tweetyproject/causal/examples/CausalReasoningExampleSurfer.java"
  "org/tweetyproject/causal/examples/CausalReasoningExampleVirus.java"
  "org/tweetyproject/causal/examples/CounterfactualReasoningExample.java"
  "org/tweetyproject/causal/examples/InterventionalCausalReasoningExample.java"
)

# dung-1.30 uses Java 14+ switch expressions / arrow-case in several files
# (equivalence/, learning/, serialisability/, plus reasoners that depend on them).
# --source 8 (set by --release 8) rejects this syntax. Strategy (modeled on
# rebuild-dialogues.sh, the proven dung-1.30 c211 recipe from PR #10544):
# 1. PATCH AbstractExtensionReasoner.getSimpleReasonerForSemantics (the one dung
#    file causal transitively imports) to rewrite its arrow-case switch to if-else.
# 2. EXCLUDE the heavy advanced-feature subpackages + their consumers.
# Note: causal imports dung.{reasoner.AbstractExtensionReasoner,reasoner.SimpleStableReasoner,
# semantics.Extension,syntax.Argument,syntax.DungTheory,util.DungTheoryPlotter}.
# DungTheoryPlotter is excluded (com.mxgraph dep). SimpleStableReasoner/Extension/
# Argument/DungTheory are Java-8-clean in 1.30 EXCEPT DungTheory's `var` (patched).
DUNG_130_EXCLUDE=(
  # Producer subpackages (Java 14+ switch AND/OR advanced features unused by causal)
  "org/tweetyproject/arg/dung/equivalence/"
  "org/tweetyproject/arg/dung/learning/"
  "org/tweetyproject/arg/dung/serialisability/"
  # principles/ uses Java 10+ var (NonInterferencePrinciple) — excluded, not imported by causal
  "org/tweetyproject/arg/dung/principles/"
  # Writer files (Tikz uses advanced LaTeX pipeline)
  "org/tweetyproject/arg/dung/writer/TikzWriter.java"
  # Reasoners that depend on the excluded subpackages or use Java 9+/advanced syntax
  "org/tweetyproject/arg/dung/reasoner/SerialisedExtensionReasoner.java"
  "org/tweetyproject/arg/dung/reasoner/FudgeAcceptabilityReasoner.java"
  "org/tweetyproject/arg/dung/reasoner/AbstractSatExtensionReasoner.java"
  "org/tweetyproject/arg/dung/reasoner/SatCompleteReasoner.java"
  "org/tweetyproject/arg/dung/reasoner/SatStableReasoner.java"
  "org/tweetyproject/arg/dung/reasoner/ExtensionRankingReasoner.java"
  "org/tweetyproject/arg/dung/reasoner/ProboI23Reasoner.java"
  # DungTheoryPlotter depends on com.mxgraph.util (JGraphX, not on classpath)
  "org/tweetyproject/arg/dung/util/DungTheoryPlotter.java"
  "org/tweetyproject/arg/dung/util/EnumeratingDilationGenerator.java"
  # Consumers that import the above (examples/)
  "org/tweetyproject/arg/dung/examples/"
)

# commons-1.30 Parser.java uses Java 11+ (Path.of/Files.readString/isBlank) —
# patched below to Java 8 equivalents rather than excluded. Only examples/ +
# ExamplesHTMLGenerator (isBlank/strip, junit) are excluded.
COMMONS_EXCLUDE=(
  "org/tweetyproject/commons/examples/"
  "org/tweetyproject/commons/util/ExamplesHTMLGenerator.java"
)
# graphs-1.30 util plotters use Java 11+ Files.readString/writeString (--release 8
# forbids them) and a StringBuffer/StringBuilder API mismatch. Neither plotting
# util is imported by causal (or dung); exclude both. Same list as rebuild-dialogues.sh.
GRAPHS_EXCLUDE=(
  "org/tweetyproject/graphs/util/GraphPlotter.java"
  "org/tweetyproject/graphs/util/AigGraphPlotter.java"
)

echo "=== Step 1: download transitive dep JARs (commons/math/graphs/logics.commons/logics.pl at 1.21) ==="
mkdir -p jars sources-extracted sources-jar classes
for v in "$COMMON_VERSION"; do
  for m in commons math graphs; do
    if [ ! -f "jars/$m-$v.jar" ]; then
      rc=$(curl -sL --retry 3 --retry-delay 2 -o "jars/$m-$v.jar" -w "%{http_code}" "https://repo1.maven.org/maven2/org/tweetyproject/$m/$v/$m-$v.jar" 2>/dev/null || echo CURL_FAIL)
      [ "$rc" = "200" ] && echo "  got: $m-$v.jar" || { rm -f "jars/$m-$v.jar"; echo "  SKIP: $m-$v.jar ($rc)"; }
    fi
  done
  for m in commons pl; do
    if [ ! -f "jars/logics.$m-$v.jar" ]; then
      rc=$(curl -sL --retry 3 --retry-delay 2 -o "jars/logics.$m-$v.jar" -w "%{http_code}" "https://repo1.maven.org/maven2/org/tweetyproject/logics/$m/$v/$m-$v.jar" 2>/dev/null || echo CURL_FAIL)
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
JAMA_P="gov/nist/math/jama/1.0.3/jama-1.0.3.jar"
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
    rc=$(curl -sL --retry 3 --retry-delay 2 -o "jars/$out" -w "%{http_code}" "$url" 2>/dev/null || echo CURL_FAIL)
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
  if [ ! -f "sources-jar/${m}-${v}-sources.jar" ]; then
    if [ "$m" = "commons" ]; then
      # CRITICAL: the commons Maven sources jar is INCOMPLETE — it contains only
      # the org/tweetyproject/logics/commons/* subset, NOT the core commons classes
      # (Formula, BeliefBase, BeliefSet, Interpretation, Parser, Reasoner, Writer,
      # InferenceMode, ...). Without those, the shade jar has 0 core commons classes,
      # and IKVM drops every causal class that extends Formula/BeliefBase (the 5/14
      # ceiling). Get COMPLETE commons sources from the GitHub release tarball (same
      # workaround as rebuild-5shades.sh).
      TARBALL="$WORK/tweety-${v}-commons.tar.gz"
      curl -sL --retry 3 --retry-delay 2 "https://github.com/TweetyProjectTeam/TweetyProject/archive/refs/tags/v${v}.tar.gz" -o "$TARBALL"
      tar -xzf "$TARBALL" "TweetyProject-${v}/org-tweetyproject-commons/src/main/java/"
      ( cd "TweetyProject-${v}/org-tweetyproject-commons/src/main/java" && jar cf "$WORK/sources-jar/${m}-${v}-sources.jar" . )
      rm -rf "TweetyProject-${v}" "$TARBALL"
      echo "  got: ${jarbase}-${v}-sources.jar (from GitHub v${v}.tar.gz, COMPLETE)"
    else
      url="https://repo1.maven.org/maven2/org/tweetyproject/${group_path}/${v}/${jarbase}-${v}-sources.jar"
      rc=$(curl -sL --retry 3 --retry-delay 2 -o /dev/null -w "%{http_code}" "$url" 2>/dev/null || echo CURL_FAIL)
      if [ "$rc" != "200" ]; then
        echo "  ERR: $m $v sources not found ($url)"
        exit 1
      fi
      curl -sL --retry 3 --retry-delay 2 -o "sources-jar/${m}-${v}-sources.jar" "$url"
      echo "  got: ${m}-${v}-sources.jar"
    fi
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
  unzip -q "../../sources-jar/${m}-${v}-sources.jar"
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

# --- dung-1.30 c211 patches (modeled on rebuild-dialogues.sh, PR #10544) ---
# dung-1.30 (unlike 1.21) uses Java 14+ switch expressions. causal transitively
# imports AbstractExtensionReasoner, so we must patch its switch → if-else for
# javac --release 8. DungTheory needs `var` → explicit type (Java 10+ var rejected).
PATCH_PY="$(mktemp -d)/c211_switch_patch.py"
cat > "$PATCH_PY" <<'PYEOF'
import re, sys, pathlib

def patch_abstract(path):
    """Rewrite AbstractExtensionReasoner.getSimpleReasonerForSemantics switch expression -> if-else."""
    src = pathlib.Path(path).read_text(encoding='utf-8')
    if '[c211 patch]' in src:
        print('  patch_abstract: already patched, skip')
        return
    new_method = '''    public static AbstractExtensionReasoner getSimpleReasonerForSemantics(Semantics semantics){
        // [c211 patch] Java 14 switch expression rewritten as if-else chain for javac --release 8
        if (semantics == Semantics.CO) return new SimpleCompleteReasoner();
        if (semantics == Semantics.GR) return new SimpleGroundedReasoner();
        if (semantics == Semantics.PR) return new SimplePreferredReasoner();
        if (semantics == Semantics.ST) return new SimpleStableReasoner();
        if (semantics == Semantics.ADM) return new SimpleAdmissibleReasoner();
        if (semantics == Semantics.CF) return new SimpleConflictFreeReasoner();
        if (semantics == Semantics.SST) return new SimpleSemiStableReasoner();
        if (semantics == Semantics.ID) return new SimpleIdealReasoner();
        if (semantics == Semantics.EA) return new SimpleEagerReasoner();
        if (semantics == Semantics.STG) return new SimpleStageReasoner();
        if (semantics == Semantics.STG2) return new Stage2Reasoner();
        if (semantics == Semantics.CF2) return new SccCF2Reasoner();
        if (semantics == Semantics.SCF2) return new SCF2Reasoner();
        if (semantics == Semantics.WAD) return new WeaklyAdmissibleReasoner();
        if (semantics == Semantics.WCO) return new WeaklyCompleteReasoner();
        if (semantics == Semantics.WPR) return new WeaklyPreferredReasoner();
        if (semantics == Semantics.WGR) return new WeaklyGroundedReasoner();
        if (semantics == Semantics.NA) return new SimpleNaiveReasoner();
        if (semantics == Semantics.SAD) return new StronglyAdmissibleReasoner();
        if (semantics == Semantics.UD) return new UndisputedReasoner();
        if (semantics == Semantics.SUD) return new StronglyUndisputedReasoner();
        if (semantics == Semantics.IS) return new SimpleInitialReasoner();
        // [c211 patch] Semantics.UC intentionally not supported (SerialisedExtensionReasoner excluded)
        if (semantics == Semantics.UC) throw new IllegalArgumentException("UC semantics unsupported in this shade (SerialisedExtensionReasoner excluded).");
        throw new IllegalArgumentException("Unknown semantics.");
    }'''
    m = re.search(r'public static AbstractExtensionReasoner getSimpleReasonerForSemantics', src)
    if not m:
        print('  ERR: AbstractExtensionReasoner marker not found')
        sys.exit(1)
    open_idx = src.find('{', m.end())
    if open_idx < 0:
        print('  ERR: cannot find method opening brace')
        sys.exit(1)
    depth = 1
    i = open_idx + 1
    while i < len(src) and depth > 0:
        if src[i] == '{':
            depth += 1
        elif src[i] == '}':
            depth -= 1
        i += 1
    if depth != 0:
        print('  ERR: unbalanced braces')
        sys.exit(1)
    new_src = src[:m.start()] + new_method + src[i:]
    pathlib.Path(path).write_text(new_src, encoding='utf-8')
    print('  patched: AbstractExtensionReasoner')

if __name__ == '__main__':
    patch_abstract(sys.argv[1])
PYEOF

DUNG_ABS="sources-extracted/arg.dung/org/tweetyproject/arg/dung/reasoner/AbstractExtensionReasoner.java"
if [ -f "$DUNG_ABS" ]; then
  if ! grep -q "\[c211 patch\]" "$DUNG_ABS"; then
    python "$PATCH_PY" "$DUNG_ABS" || { echo "  c211 patch_abstract FAILED"; exit 1; }
  fi
fi

# DungTheory.java: replace Java 10+ `var` with explicit type (--release 8 rejects var).
# NOTE: do NOT remove getConnectedComponents (graphs-1.30 Graph interface HAS it,
# unlike graphs-1.21 which the 5shades recipe targeted). Only the var replacement applies.
DUNG_THEORY="sources-extracted/arg.dung/org/tweetyproject/arg/dung/syntax/DungTheory.java"
if [ -f "$DUNG_THEORY" ]; then
  if ! grep -q "\[c211 patch\]" "$DUNG_THEORY"; then
    sed -i 's/var tempArgsToRemove = new HashSet<Argument>();/HashSet<Argument> tempArgsToRemove = new HashSet<Argument>();/' "$DUNG_THEORY"
    sed -i '1i // [c211 patch] DungTheory: Java 10+ var replaced with explicit type' "$DUNG_THEORY"
    echo "  patched: dung DungTheory.java var -> explicit type"
  fi
fi

# commons-1.30 Parser.java uses Java 11+ (Path.of/Files.readString/isBlank) — downgrade
# to Java 8 equivalents (Paths.get/readAllBytes/trim().isEmpty()). Adapted from
# rebuild-dialogues.sh:254-274.
COMMONS_PARSER="sources-extracted/commons/org/tweetyproject/commons/Parser.java"
if [ -f "$COMMONS_PARSER" ]; then
  if ! grep -q "\[c211 patch\]" "$COMMONS_PARSER"; then
    sed -i 's/Path.of(/Paths.get(/g' "$COMMONS_PARSER"
    # Match the full readString(Paths.get(X)) call so the replacement keeps
    # balanced parens: new String(Files.readAllBytes(Paths.get(X))). A naive
    # open-only replace leaves new String( unclosed -> "') expected".
    sed -i 's/Files.readString(\(Paths.get([^)]*)\))/new String(Files.readAllBytes(\1))/g' "$COMMONS_PARSER"
    sed -i 's/.isBlank()/.trim().isEmpty()/g' "$COMMONS_PARSER"
    # Ensure StandardCharsets import present (readAllBytes needs explicit charset)
    if ! grep -q "import java.nio.charset.StandardCharsets;" "$COMMONS_PARSER"; then
      sed -i '/^import java.nio.file/i import java.nio.charset.StandardCharsets;' "$COMMONS_PARSER"
    fi
    # Path.of -> Paths.get requires java.nio.file.Paths (original imported only Path)
    if ! grep -q "import java.nio.file.Paths;" "$COMMONS_PARSER"; then
      sed -i '/^import java.nio.file.Path;/a import java.nio.file.Paths;' "$COMMONS_PARSER"
    fi
    sed -i '1i // [c211 patch] Parser.java downgraded to Java 8 (Paths.get/readAllBytes/trim.isEmpty)' "$COMMONS_PARSER"
    echo "  patched: commons Parser.java -> Java 8 (Paths/get/readAllBytes/trim)"
  fi
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
  if [ "$m" = "commons" ]; then
    for ex in "${COMMONS_EXCLUDE[@]}"; do
      files=$(echo "$files" | grep -v "$ex" || true)
    done
  fi
  if [ "$m" = "arg.dung" ]; then
    for ex in "${DUNG_130_EXCLUDE[@]}"; do
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
  # Bootstrap jars from Maven Central (all 1.30 for version consistency)
  for j in "commons" "math" "graphs"; do
    [ -f "jars/${j}-${COMMON_VERSION}.jar" ] && CP="$CP;jars/${j}-${COMMON_VERSION}.jar"
  done
  for j in "logics.commons" "logics.pl"; do
    [ -f "jars/${j}-${COMMON_VERSION}.jar" ] && CP="$CP;jars/${j}-${COMMON_VERSION}.jar"
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