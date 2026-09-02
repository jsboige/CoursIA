#!/bin/bash
# Rebuild five Tweety shade jars for IKVM 8.x compilation (issue #10411):
# bipolar-1.21, social-1.21, setaf-1.21, weighted-1.30, extended-1.30.
#
# Like rebuild-causal.sh (c.210), all 5 Maven jars from Maven Central are
# bytecode major 59 (Java 15), which IKVM 8.x silently drops (IKVM0101
# warning). Strategy: source-recompile the dep chain from sources using
# javac --release 8, then shade into a fat-jar consumable by IKVM 8.x.
#
# Pipeline mirrors rebuild-causal.sh (c.210). A SINGLE compilation chain is
# used for all 5 modules — dung-1.21 itself imports org.tweetyproject.logics.pl
# and org.tweetyproject.logics.commons, so we cannot skip them. commons sources
# (GitHub tarball) include a logics.commons subset which we drop before shade
# to avoid duplicates (see Step 5).
#
# Per-module COMPILE_ORDER is the dep chain + the module. The chain is the
# same for all 5 modules; only the final module and dung version change.
#
#   bipolar:   commons-1.21 math-1.21 graphs-1.21 logics.commons-1.21 logics.pl-1.21 dung-1.21 bipolar-1.21
#   social:    commons-1.21 math-1.21 graphs-1.21 logics.commons-1.21 logics.pl-1.21 dung-1.21 social-1.21
#   setaf:     commons-1.21 math-1.21 graphs-1.21 logics.commons-1.21 logics.pl-1.21 dung-1.21 setaf-1.21
#   extended:  commons-1.21 math-1.21 graphs-1.21 logics.commons-1.21 logics.pl-1.21 dung-1.30 extended-1.30
#   weighted:  commons-1.21 math-1.21 graphs-1.21 logics.commons-1.21 logics.pl-1.21 dung-1.30 weighted-1.30
#
# Outputs (5 shade jars, gitignored):
#   jars/org.tweetyproject.tweety-<module>-java8-shade.jar
# Copied into:
#   ../libs/org.tweetyproject.tweety-<module>-java8-shade.jar
# Used as <IkvmReference> in build-Tweety<Module>Shade.csproj ->
#   bin/Release/net8.0/org.tweetyproject.tweety-<module>.dll
#
# Verdict bytecode (Step 7): expected {52: N} only per shade.

set -e
export JAVA_HOME="/c/Program Files/Freeplane/runtime"
export PATH="$JAVA_HOME/bin:$PATH"

cd "$(dirname "$0")"
WORK=$(pwd)

BUILD_DIR="$WORK/.5shades-build"
mkdir -p "$BUILD_DIR"
cd "$BUILD_DIR"
WORK=$(pwd)

# All dep versions are pinned (commons/graphs/math/logics.commons/logics.pl = 1.21
# source-clean; dung 1.21 or 1.30 per module).
declare -A VERSIONS=(
  [commons]="1.21"
  [math]="1.21"
  [graphs]="1.21"
  [logics.commons]="1.21"
  [logics.pl]="1.21"
  [bipolar]="1.21"
  [social]="1.21"
  [setaf]="1.21"
)
# Maven artifactId (often == key but not for logics.commons whose artifactId is
# "commons" — saved as logics.commons-<ver>.jar to namespace apart from the
# top-level commons artifact).
declare -A ARTIFACT_ID=(
  [commons]="commons"
  [math]="math"
  [graphs]="graphs"
  [logics.commons]="commons"
  [logics.pl]="pl"
)
declare -A ARTIFACT_PATH=(
  [commons]="commons"
  [math]="math"
  [graphs]="graphs"
  [logics.commons]="logics/commons"
  [logics.pl]="logics/pl"
)

# Dung and the 5 modules have their own group_path (under arg/, with their
# own artifactId == key).
declare -A MODULE_VERSIONS=(
  [bipolar]="1.21"
  [social]="1.21"
  [setaf]="1.21"
  [extended]="1.30"
  [weighted]="1.30"
)
declare -A MODULE_DUNG_VERSION=(
  [bipolar]="1.21"
  [social]="1.21"
  [setaf]="1.21"
  [extended]="1.30"
  [weighted]="1.30"
)

echo "=== Step 1: download transitive dep JARs (commons/math/graphs/logics.commons/logics.pl/dung) ==="
mkdir -p jars sources-extracted sources-jar classes
for v in 1.21 1.30; do
  for m in commons math graphs; do
    jarbase="${m}-${v}.jar"
    if [ "$v" = "1.21" ] || [ "$m" = "dung" ]; then
      # Only 1.21 is source-clean; dung is published at both 1.21 and 1.30.
      if [ ! -f "jars/$jarbase" ] && [ "$m" != "dung" ]; then
        rc=$(curl -sL -o "jars/$jarbase" -w "%{http_code}" "https://repo1.maven.org/maven2/org/tweetyproject/$m/$v/$m-$v.jar")
        [ "$rc" = "200" ] && echo "  got: $jarbase" || { rm -f "jars/$jarbase"; echo "  SKIP: $jarbase ($rc)"; }
      fi
    fi
  done
  for m in logics.commons logics.pl; do
    if [ "$v" != "1.21" ]; then continue; fi
    short="${m#logics.}"  # commons or pl
    jarbase="${m}-${v}.jar"
    if [ ! -f "jars/$jarbase" ]; then
      rc=$(curl -sL -o "jars/$jarbase" -w "%{http_code}" "https://repo1.maven.org/maven2/org/tweetyproject/logics/$short/$v/$short-$v.jar")
      [ "$rc" = "200" ] && echo "  got: $jarbase" || { rm -f "jars/$jarbase"; echo "  SKIP: $jarbase ($rc)"; }
    fi
  done
  for m in dung; do
    jarbase="${m}-${v}.jar"
    if [ ! -f "jars/$jarbase" ]; then
      rc=$(curl -sL -o "jars/$jarbase" -w "%{http_code}" "https://repo1.maven.org/maven2/org/tweetyproject/arg/$m/$v/$m-$v.jar")
      [ "$rc" = "200" ] && echo "  got: $jarbase" || { rm -f "jars/$jarbase"; echo "  SKIP: $jarbase ($rc)"; }
    fi
  done
done

# Math transitive deps (same as rebuild-causal.sh).
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
echo "=== Step 2: download sources jars ==="
# Commons sources are NOT on Maven Central (binary only); pull from GitHub tag.
for m in "${!VERSIONS[@]}"; do
  v=${VERSIONS[$m]}
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
  artifact="${ARTIFACT_ID[$m]}"
  group_path="${ARTIFACT_PATH[$m]}"
  if [ ! -f "sources-jar/${m}-${v}-sources.jar" ]; then
    url="https://repo1.maven.org/maven2/org/tweetyproject/${group_path}/${v}/${artifact}-${v}-sources.jar"
    rc=$(curl -sL -o /dev/null -w "%{http_code}" "$url")
    if [ "$rc" != "200" ]; then
      echo "  ERR: $m $v sources not found ($url)"
      exit 1
    fi
    curl -sL -o "sources-jar/${m}-${v}-sources.jar" "$url"
    echo "  got: ${m}-${v}-sources.jar"
  fi
done

# Dung sources (both versions) + 5 module sources
for v in 1.21 1.30; do
  if [ ! -f "sources-jar/dung-${v}-sources.jar" ]; then
    url="https://repo1.maven.org/maven2/org/tweetyproject/arg/dung/${v}/dung-${v}-sources.jar"
    rc=$(curl -sL -o /dev/null -w "%{http_code}" "$url")
    if [ "$rc" = "200" ]; then
      curl -sL -o "sources-jar/dung-${v}-sources.jar" "$url"
      echo "  got: dung-${v}-sources.jar"
    else
      echo "  WARN: dung-${v}-sources.jar not on Maven Central (rc=$rc) — module will use binary jar only"
    fi
  fi
done

# Math-1.30 sources — needed for weighted-1.30 (algebra package: Semiring, BooleanSemiring,
# FuzzySemiring, ProbabilisticSemiring, WeightedSemiring, BottleneckSemiring, NonNumericSemiring).
# Math-1.21 does NOT contain algebra. We compile only the algebra package (Java 8 compatible).
if [ ! -f "sources-jar/math-1.30-sources.jar" ]; then
  url="https://repo1.maven.org/maven2/org/tweetyproject/math/1.30/math-1.30-sources.jar"
  rc=$(curl -sL -o /dev/null -w "%{http_code}" "$url")
  if [ "$rc" != "200" ]; then
    echo "  ERR: math-1.30 sources not found ($url)"
    exit 1
  fi
  curl -sL -o "sources-jar/math-1.30-sources.jar" "$url"
  echo "  got: math-1.30-sources.jar"
fi
for m in bipolar social setaf extended weighted; do
  v=${MODULE_VERSIONS[$m]}
  if [ ! -f "sources-jar/${m}-${v}-sources.jar" ]; then
    url="https://repo1.maven.org/maven2/org/tweetyproject/arg/${m}/${v}/${m}-${v}-sources.jar"
    rc=$(curl -sL -o /dev/null -w "%{http_code}" "$url")
    if [ "$rc" != "200" ]; then
      echo "  ERR: $m $v sources not found ($url)"
      exit 1
    fi
    curl -sL -o "sources-jar/${m}-${v}-sources.jar" "$url"
    echo "  got: ${m}-${v}-sources.jar"
  fi
done

echo ""
echo "=== Step 3: extract sources ==="
for m in "${!VERSIONS[@]}"; do
  v=${VERSIONS[$m]}
  rm -rf "sources-extracted/$m"
  mkdir -p "sources-extracted/$m"
  cd "sources-extracted/$m"
  unzip -q "$WORK/sources-jar/${m}-${v}-sources.jar"
  cd "$WORK"
  echo "  extracted: $m-$v"
done
for v in 1.21 1.30; do
  if [ -f "sources-jar/dung-${v}-sources.jar" ]; then
    rm -rf "sources-extracted/dung-${v}"
    mkdir -p "sources-extracted/dung-${v}"
    cd "sources-extracted/dung-${v}"
    unzip -q "$WORK/sources-jar/dung-${v}-sources.jar"
    cd "$WORK"
    echo "  extracted: dung-${v}"
  fi
done
# Extract math-1.30 algebra package (only — rest of math comes from math-1.21)
if [ -f "sources-jar/math-1.30-sources.jar" ]; then
  rm -rf "sources-extracted/math-1.30-algebra"
  mkdir -p "sources-extracted/math-1.30-algebra"
  cd "sources-extracted/math-1.30-algebra"
  unzip -q "$WORK/sources-jar/math-1.30-sources.jar" "org/tweetyproject/math/algebra/*"
  cd "$WORK"
  echo "  extracted: math-1.30-algebra (algebra package only)"
fi
for m in bipolar social setaf extended weighted; do
  v=${MODULE_VERSIONS[$m]}
  rm -rf "sources-extracted/${m}-${v}"
  mkdir -p "sources-extracted/${m}-${v}"
  cd "sources-extracted/${m}-${v}"
  unzip -q "$WORK/sources-jar/${m}-${v}-sources.jar"
  cd "$WORK"
  echo "  extracted: ${m}-${v}"
done

# Patch: remove unused ojalgo SuperimposedStore import in dung's
# ClaimBasedTheory.java (ojalgo class is package-private; the import is dead code).
for ver in 1.21 1.30; do
  if [ -f "sources-extracted/dung-${ver}/org/tweetyproject/arg/dung/syntax/ClaimBasedTheory.java" ]; then
    sed -i '/^import org.ojalgo.matrix.store.SuperimposedStore;$/d' \
      "sources-extracted/dung-${ver}/org/tweetyproject/arg/dung/syntax/ClaimBasedTheory.java"
    echo "  patched: removed unused ojalgo SuperimposedStore import (dung-${ver})"
  fi
done

# Patch: rewrite Java 14+ switch expressions in dung-1.30 reasoner files into
# classic if-else chains so javac --release 8 accepts them. These 3 files are
# transitively required by extended/weighted (AbstractExtensionReasoner is
# imported by LdoInterpretation in dung/ldo/semantics, which is imported by
# extended). The patch is idempotent — runs once per fresh extraction; the
# [c211 patch] marker is the gate.
#
# Implementation: the rewrites are inline Python heredocs. They regenerate the
# patched file from scratch using a regex-based transform that converts
# arrow-case `switch` patterns to classic if-else chains. Sensitive to source
# formatting — keep README.md §dung-1.30 reasoner patch in sync if Tweety
# upstream changes the switch statement shape.
PATCH_PY="$(mktemp -d)/c211_switch_patch.py"
cat > "$PATCH_PY" <<'PYEOF'
import re, sys, pathlib, os

def patch_abstract(path):
    """Rewrite AbstractExtensionReasoner.getSimpleReasonerForSemantics."""
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
        // [c211 patch] Semantics.UC intentionally not supported — SerialisedExtensionReasoner excluded
        // (depends on serialisability.* which is excluded too — see DUNG_130_EXCLUDE).
        if (semantics == Semantics.UC) throw new IllegalArgumentException("UC semantics unsupported in this shade (SerialisedExtensionReasoner excluded).");
        throw new IllegalArgumentException("Unknown semantics.");
    }'''
    # Anchor-based search: find method header, then matching closing brace.
    m = re.search(r'public static AbstractExtensionReasoner getSimpleReasonerForSemantics', src)
    if not m:
        print('  ERR: AbstractExtensionReasoner marker not found')
        sys.exit(1)
    # Find the method opening brace
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
    # Replace from m.start() to i (exclusive), preserving any leading indent + method
    new_src = src[:m.start()] + new_method + src[i:]
    pathlib.Path(path).write_text(new_src, encoding='utf-8')
    print('  patched: AbstractExtensionReasoner')

def patch_dung_theory(path):
    """Patch DungTheory.java — adjust for graphs-1.21 Graph interface (which lacks
    getConnectedComponents but keeps getStronglyConnectedComponents + lacks getNumberOfEdges)
    and replace Java 10+ `var` with explicit type.

    Idempotent: skip if [c211 patch] already present in header.
    """
    src = pathlib.Path(path).read_text(encoding='utf-8')
    if '[c211 patch]' in src:
        print('  patch_dung_theory: already patched, skip')
        return
    # 1. Remove getConnectedComponents method (not in graphs-1.21 Graph interface; not called
    # from DungTheory itself). KEEP getStronglyConnectedComponents (IS in interface).
    get_connected_old = (
        '\t@Override\n'
        '\tpublic Collection<Collection<Argument>> getConnectedComponents() {\n'
        '\t\treturn DefaultGraph.getConnectedComponents(this);\n'
        '\t}\n'
        '\t\n'
    )
    if get_connected_old in src:
        src = src.replace(get_connected_old, '', 1)
        print('  patch_dung_theory: getConnectedComponents removed')
    else:
        print('  patch_dung_theory: WARN getConnectedComponents block not found (already patched or upstream shifted)')
    # 2. Drop @Override from getNumberOfEdges (Graph interface in graphs-1.21 lacks it; called from
    # MaxSatKAdmissibleAstReasoner / MaxSatKStableAstReasoner)
    get_num_edges_old = '\t@Override\n\tpublic int getNumberOfEdges() {\n'
    if get_num_edges_old in src:
        src = src.replace(
            get_num_edges_old,
            '\t// [c211 patch] @Override removed — not in graphs-1.21 Graph interface (added in newer graphs)\n'
            '\tpublic int getNumberOfEdges() {\n',
            1,
        )
        print('  patch_dung_theory: @Override dropped from getNumberOfEdges')
    # 3. Replace 'var' with explicit type (Java 10+ feature, --source 8 rejects)
    if 'var tempArgsToRemove' in src:
        src = src.replace('var tempArgsToRemove', 'HashSet<Argument> tempArgsToRemove')
        print('  patch_dung_theory: var replaced with explicit type')
    # Mark as patched by adding a single comment at top of file
    src = '// [c211 patch] DungTheory: getConnectedComponents dropped, getNumberOfEdges @Override dropped, Java 10+ var replaced\n' + src
    pathlib.Path(path).write_text(src, encoding='utf-8')
    print('  patched: DungTheory')

def patch_enumerating_dilation(path):
    """Patch EnumeratingDilationGenerator.java — replace Java 10+ `var` with Argument type."""
    src = pathlib.Path(path).read_text(encoding='utf-8')
    if '[c211 patch]' in src:
        print('  patch_enumerating_dilation: already patched, skip')
        return
    src = src.replace('for(var arg : frameworkOriginal) {', 'for(Argument arg : frameworkOriginal) {')
    src = src.replace('for(var a : this.arguments) {', 'for(Argument a : this.arguments) {')
    src = src.replace('for(var b : this.arguments) {', 'for(Argument b : this.arguments) {')
    src = '// [c211 patch] Java 10+ var replaced with explicit Argument type\n' + src
    pathlib.Path(path).write_text(src, encoding='utf-8')
    print('  patched: EnumeratingDilationGenerator')


def patch_extended_reasoner(path, simple_prefix, recursive_prefix):
    """Patch AbstractExtendedExtensionReasoner.java and AbstractRecursiveExtendedExtensionReasoner.java
    -- rewrite `return switch (semantics) { ... };` as if-else chain returning directly."""
    src = pathlib.Path(path).read_text(encoding='utf-8')
    if '[c211 patch]' in src:
        print(f'  patch_extended_reasoner({os.path.basename(path)}): already patched, skip')
        return
    is_recursive = 'RecursiveExtended' in path
    prefix = recursive_prefix if is_recursive else simple_prefix
    old_block = f'''        return switch (semantics) {{
            case CF -> new {prefix}ConflictFreeReasoner();
            case ADM -> new {prefix}AdmissibleReasoner();
            case CO -> new {prefix}CompleteReasoner();
            default -> throw new IllegalArgumentException("Unknown semantics.");
        }};'''
    new_block = f'''        // [c211 patch] Java 14 switch expression rewritten as if-else chain for javac --release 8
        if (semantics == Semantics.CF) return new {prefix}ConflictFreeReasoner();
        if (semantics == Semantics.ADM) return new {prefix}AdmissibleReasoner();
        if (semantics == Semantics.CO) return new {prefix}CompleteReasoner();
        throw new IllegalArgumentException("Unknown semantics.");'''
    if old_block in src:
        src = src.replace(old_block, new_block, 1)
        pathlib.Path(path).write_text(src, encoding='utf-8')
        print(f'  patched: {os.path.basename(path)} (switch expression → if-else chain)')
    else:
        print(f'  patch_extended_reasoner({os.path.basename(path)}): WARN old_block not found (upstream shifted?)')


def patch_extended_theory_formulas(path):
    """Patch ExtendedTheory.contains / RecursiveExtendedTheory.contains:
    `this.formulas` is private in commons-1.21 BeliefSet — must use `super.contains(...)` instead."""
    src = pathlib.Path(path).read_text(encoding='utf-8')
    if '[c211 patch]' in src:
        print(f'  patch_extended_theory_formulas({os.path.basename(path)}): already patched, skip')
        return
    old_block = 'return this.formulas.contains((Argument) o);'
    new_block = '// [c211 patch] `formulas` is private in commons-1.21 BeliefSet -- use super.contains\n        return super.contains(o);'
    if old_block in src:
        src = src.replace(old_block, new_block, 1)
        pathlib.Path(path).write_text(src, encoding='utf-8')
        print(f'  patched: {os.path.basename(path)} (formulas → super.contains)')
    else:
        print(f'  patch_extended_theory_formulas({os.path.basename(path)}): WARN old_block not found (upstream shifted?)')


def patch_weighted_set_of(path):
    """Replace Java 9+ `Set.of(x)` with `Collections.singleton(x)` -- --release 8 rejects Set.of."""
    src = pathlib.Path(path).read_text(encoding='utf-8')
    if '[c211 patch]' in src:
        print(f'  patch_weighted_set_of({os.path.basename(path)}): already patched, skip')
        return
    # Imports may need Collections added
    if 'import java.util.Collections;' not in src and 'Set.of(' in src:
        # Add Collections import after the last existing java.util import
        src = re.sub(
            r'(import java\.util\.\*;\n)',
            r'\1import java.util.Collections;\n',
            src, count=1,
        )
    new = src
    new = re.sub(r'Set\.of\((\w+)\)', r'Collections.singleton(\1)', new)
    if new != src:
        pathlib.Path(path).write_text(new, encoding='utf-8')
        print(f'  patched: {os.path.basename(path)} (Set.of → Collections.singleton)')
    else:
        print(f'  patch_weighted_set_of({os.path.basename(path)}): no Set.of found')

def patch_extension_ranking(path):
    """Rewrite ExtensionRankingReasoner.getCompareMethods switch."""
    src = pathlib.Path(path).read_text(encoding='utf-8')
    if '[c211 patch]' in src:
        print('  patch_extension_ranking: already patched, skip')
        return
    new_block = '''        // [c211 patch] Java 14 switch expression rewritten as if-else chain for javac --release 8
        if (semantics == ExtensionRankingSemantics.R_CF) {
            methods.add(ExtensionRankingReasoner.class.getMethod("getConflicts", Extension.class, DungTheory.class));
        } else if (semantics == ExtensionRankingSemantics.R_AD || semantics == ExtensionRankingSemantics.R_PR) {
            methods.add(ExtensionRankingReasoner.class.getMethod("getConflicts", Extension.class, DungTheory.class));
            methods.add(ExtensionRankingReasoner.class.getMethod("getUndefended", Extension.class, DungTheory.class));
        } else if (semantics == ExtensionRankingSemantics.R_CO || semantics == ExtensionRankingSemantics.R_GR) {
            methods.add(ExtensionRankingReasoner.class.getMethod("getConflicts", Extension.class, DungTheory.class));
            methods.add(ExtensionRankingReasoner.class.getMethod("getUndefended", Extension.class, DungTheory.class));
            methods.add(ExtensionRankingReasoner.class.getMethod("getDefendedNotIn", Extension.class, DungTheory.class));
        } else if (semantics == ExtensionRankingSemantics.R_SST) {
            methods.add(ExtensionRankingReasoner.class.getMethod("getConflicts", Extension.class, DungTheory.class));
            methods.add(ExtensionRankingReasoner.class.getMethod("getUndefended", Extension.class, DungTheory.class));
            methods.add(ExtensionRankingReasoner.class.getMethod("getDefendedNotIn", Extension.class, DungTheory.class));
            methods.add(ExtensionRankingReasoner.class.getMethod("getUnattacked", Extension.class, DungTheory.class));
        } else {
            throw new IllegalArgumentException("Unknown semantics.");
        }'''
    # Find the switch in getCompareMethods - use anchor-based search
    m = re.search(r'switch \(semantics\) \{', src)
    if not m:
        print('  ERR: ExtensionRankingReasoner switch start not found')
        sys.exit(1)
    # Find matching closing brace
    i = m.end()
    depth = 1
    while i < len(src) and depth > 0:
        if src[i] == '{':
            depth += 1
        elif src[i] == '}':
            depth -= 1
        i += 1
    if depth != 0:
        print('  ERR: ExtensionRankingReasoner switch unbalanced')
        sys.exit(1)
    new_src = src[:m.start()] + new_block + src[i:]
    pathlib.Path(path).write_text(new_src, encoding='utf-8')
    print('  patched: ExtensionRankingReasoner')

if __name__ == '__main__':
    target = sys.argv[1]
    if 'AbstractExtensionReasoner' in target and 'Extended' not in target:
        patch_abstract(target)
    elif 'AbstractExtendedExtensionReasoner' in target or 'AbstractRecursiveExtendedExtensionReasoner' in target:
        patch_extended_reasoner(target, 'SimpleExtended', 'SimpleRecursiveExtended')
    elif 'ExtensionRankingReasoner' in target:
        patch_extension_ranking(target)
    elif 'DungTheory.java' in target:
        patch_dung_theory(target)
    elif 'EnumeratingDilationGenerator' in target:
        patch_enumerating_dilation(target)
    elif 'ExtendedTheory.java' in target or 'RecursiveExtendedTheory.java' in target:
        patch_extended_theory_formulas(target)
    elif 'WeightedArgumentationFramework' in target:
        patch_weighted_set_of(target)
PYEOF

for tgt in \
  "sources-extracted/dung-1.30/org/tweetyproject/arg/dung/reasoner/AbstractExtensionReasoner.java" \
  "sources-extracted/dung-1.30/org/tweetyproject/arg/dung/reasoner/ExtensionRankingReasoner.java" \
  "sources-extracted/dung-1.30/org/tweetyproject/arg/dung/syntax/DungTheory.java" \
  "sources-extracted/dung-1.30/org/tweetyproject/arg/dung/util/EnumeratingDilationGenerator.java" \
  "sources-extracted/extended-1.30/org/tweetyproject/arg/extended/reasoner/AbstractExtendedExtensionReasoner.java" \
  "sources-extracted/extended-1.30/org/tweetyproject/arg/extended/reasoner/AbstractRecursiveExtendedExtensionReasoner.java" \
  "sources-extracted/extended-1.30/org/tweetyproject/arg/extended/syntax/ExtendedTheory.java" \
  "sources-extracted/extended-1.30/org/tweetyproject/arg/extended/syntax/RecursiveExtendedTheory.java" \
  "sources-extracted/weighted-1.30/org/tweetyproject/arg/weighted/syntax/WeightedArgumentationFramework.java" \
  ; do
  if [ -f "$tgt" ]; then
    if ! grep -q "\[c211 patch\]" "$tgt"; then
      python "$PATCH_PY" "$tgt" || exit 1
    fi
  fi
done

# Files to exclude during compilation (commercial libs / Java 9+ features)
# These are unused by the 5 target modules but still compile in the dep tree.
MATH_EXCLUDE=(
  "org/tweetyproject/math/opt/solver/AntColonyOptimization.java"
  "org/tweetyproject/math/opt/solver/GurobiOptimizer.java"
  "org/tweetyproject/math/util/OjAlgoMathUtils.java"
  # math/examples/* uses commercial / niche libs (gurobi, jSPF, isula).
  # The 5 target modules never reference math.examples.* — exclude the whole subpackage.
  "org/tweetyproject/math/examples/"
)
LOGICS_PL_EXCLUDE=(
  "org/tweetyproject/logics/pl/plugin/PlPlugin.java"
  "org/tweetyproject/logics/pl/sat/CmdLineSatSolver.java"
  # logics.pl/examples/* are standalone demo apps depending on niche libs
  # (stream/datastructure, postulates evaluators). The 5 target modules never
  # reference logics.pl.examples.* — exclude the whole subpackage.
  "org/tweetyproject/logics/pl/examples/"
)
GRAPHS_EXCLUDE=(
  "org/tweetyproject/graphs/util/GraphPlotter.java"
)
# dung-1.30 uses Java 14+ switch expressions / arrow-case / multiple labels in
# ~15 files under equivalence/, learning/, reasoner/, serialisability/, writer/,
# plus their consumers (examples/, divisions/, principles/, several reasoners).
# --source 8 (set by --release 8) rejects this syntax.
#
# Strategy:
# 1. PATCH AbstractExtensionReasoner + ExtensionRankingReasoner to rewrite their
#    arrow-case `switch` to classic if-else chains. These two are transitively
#    required by extended/weighted (AbstractExtensionReasoner is imported by
#    LdoInterpretation in dung/ldo/semantics which is imported by extended).
# 2. EXCLUDE the heavy advanced-feature subpackages (equivalence, learning,
#    serialisability) PLUS all consumers — files in examples/, divisions/,
#    principles/ that reference those subpackages, AND reasoners that use them:
#    SerialisedExtensionReasoner (uses serialisability.* for SelectionFunction,
#    TerminationFunction, SerialisationSequence), FudgeAcceptabilityReasoner
#    (uses logics.pl.sat.DimacsSatSolver absent from logics.pl-1.21 sources),
#    AbstractSatExtensionReasoner (depends on SerialisedExtensionReasoner), and
#    other domain-specific consumers (equivalence/learning use arrow-case +
#    reference AbstractExtensionReasoner via SerialisedExtensionReasoner).
DUNG_130_EXCLUDE=(
  # Producer subpackages (Java 14+ switch AND/OR advanced features)
  "org/tweetyproject/arg/dung/equivalence/"
  "org/tweetyproject/arg/dung/learning/"
  "org/tweetyproject/arg/dung/serialisability/"
  # Writer files (Tikz uses advanced LaTeX pipeline)
  "org/tweetyproject/arg/dung/writer/TikzWriter.java"
  # Reasoners that depend on the excluded subpackages
  "org/tweetyproject/arg/dung/reasoner/SerialisedExtensionReasoner.java"
  "org/tweetyproject/arg/dung/reasoner/FudgeAcceptabilityReasoner.java"
  "org/tweetyproject/arg/dung/reasoner/AbstractSatExtensionReasoner.java"
  "org/tweetyproject/arg/dung/reasoner/SatCompleteReasoner.java"
  "org/tweetyproject/arg/dung/reasoner/SatStableReasoner.java"
  # DungTheoryPlotter depends on com.mxgraph.util (JGraphX — not in the 5 modules' tree)
  "org/tweetyproject/arg/dung/util/DungTheoryPlotter.java"
  # ProboI23Reasoner uses Java 11+ String.strip() (not in --source 8)
  "org/tweetyproject/arg/dung/reasoner/ProboI23Reasoner.java"
  # Consumers that import the above
  "org/tweetyproject/arg/dung/examples/"
  "org/tweetyproject/arg/dung/divisions/"
  "org/tweetyproject/arg/dung/principles/"
)

# Build each module shade.
# Pre-step: compile math-1.30 algebra package (Java 8 compatible, --release 8).
# Math-1.21 does NOT contain algebra. weighted-1.30 imports org.tweetyproject.math.algebra.*
# (BooleanSemiring, Semiring, FuzzySemiring, ProbabilisticSemiring, ...).
# We compile only the algebra package from math-1.30 sources (145 src files total,
# but only ~7 algebra .java files compile cleanly under --release 8).
if [ -d "sources-extracted/math-1.30-algebra" ]; then
  rm -rf "classes/math-1.30-algebra"
  mkdir -p "classes/math-1.30-algebra"
  if ! javac --release 8 \
    -d "classes/math-1.30-algebra" \
    $(find "sources-extracted/math-1.30-algebra" -name "*.java") 2>"compile-math-1.30-algebra.log"; then
    echo "  COMPILE FAILED for math-1.30-algebra -- see compile-math-1.30-algebra.log"
    grep "error:" "compile-math-1.30-algebra.log" | head -10
    exit 1
  fi
  count=$(find "classes/math-1.30-algebra" -name "*.class" | wc -l)
  echo "  pre-compile: math-1.30-algebra ($count classes)"
fi

for module in bipolar social setaf extended weighted; do
  module_ver="${MODULE_VERSIONS[$module]}"
  dung_ver="${MODULE_DUNG_VERSION[$module]}"

  echo ""
  echo "=== Step 4: compile $module-$module_ver (dung $dung_ver) ==="

  # Single chain: math FIRST (commons sources include a logics.commons subset that
  # imports org.tweetyproject.math.*), then commons → graphs → logics.commons → logics.pl → dung → module.
  COMPILE_ORDER=("math:1.21" "commons:1.21" "graphs:1.21" "logics.commons:1.21" "logics.pl:1.21" "dung:$dung_ver" "$module:$module_ver")

  for entry in "${COMPILE_ORDER[@]}"; do
    IFS=':' read -r m v <<< "$entry"
    echo "  compiling: $m v$v"
    rm -rf "classes/$m-$v"
    mkdir -p "classes/$m-$v"
    files=$(find "sources-extracted/$m-$v" -name "*.java")
    if [ "$m" = "math" ]; then
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
    if [ "$m" = "dung" ] && [ "$v" = "1.30" ]; then
      for ex in "${DUNG_130_EXCLUDE[@]}"; do
        files=$(echo "$files" | grep -v "$ex" || true)
      done
    fi

    # Classpath: bootstrap jars + math transitive deps + previously compiled classes.
    CP=""
    for j in commons-1.21 graphs-1.21; do
      [ -f "jars/$j.jar" ] && CP="$CP;jars/$j.jar"
    done
    # math-1.30 algebra package — provides Semiring/BooleanSemiring/etc. for weighted-1.30.
    # math-1.21 does NOT contain algebra.
    if [ -d "classes/math-1.30-algebra" ]; then
      CP="$CP;classes/math-1.30-algebra"
    fi
    # Math transitive deps (jama, slf4j, commons-math, ojalgo, sat4j) needed by
    # math sources + downstream (commons needs math for compilation, the 5 target
    # modules import some of these — e.g. bipolar uses org.apache.commons.math.random).
    if [ "$m" = "math" ] || [ "$m" = "commons" ] || [ "$m" = "graphs" ] || [ "$m" = "logics.commons" ] || [ "$m" = "logics.pl" ] || [ "$m" = "dung" ] || [ "$m" = "bipolar" ] || [ "$m" = "social" ] || [ "$m" = "setaf" ] || [ "$m" = "extended" ] || [ "$m" = "weighted" ]; then
      [ -f "jars/jama-1.0.3.jar" ] && CP="$CP;jars/jama-1.0.3.jar"
      [ -f "jars/slf4j-api-1.7.36.jar" ] && CP="$CP;jars/slf4j-api-1.7.36.jar"
      [ -f "jars/commons-math-2.2.jar" ] && CP="$CP;jars/commons-math-2.2.jar"
      [ -f "jars/commons-math3-3.6.1.jar" ] && CP="$CP;jars/commons-math3-3.6.1.jar"
      [ -f "jars/ojalgo-45.1.1.jar" ] && CP="$CP;jars/ojalgo-45.1.1.jar"
      [ -f "jars/org.sat4j.core-2.3.1.jar" ] && CP="$CP;jars/org.sat4j.core-2.3.1.jar"
    fi
    # Add previously compiled module classes (in COMPILE_ORDER)
    for prev in "${COMPILE_ORDER[@]}"; do
      if [ "$prev" = "$entry" ]; then break; fi
      prev_name="${prev%%:*}"
      prev_ver="${prev##*:}"
      if [ -d "classes/${prev_name}-${prev_ver}" ]; then
        CP="$CP;classes/${prev_name}-${prev_ver}"
      fi
    done

    if ! javac --release 8 \
      -cp "$CP" \
      -d "classes/$m-$v" \
      $files 2>"compile-$m-$v.log"; then
      echo "  COMPILE FAILED for $m-$v -- see compile-$m-$v.log"
      grep "error:" "compile-$m-$v.log" | head -15
      exit 1
    fi
    count=$(find "classes/$m-$v" -name "*.class" | wc -l)
    echo "    $count classes compiled"
  done

  echo ""
  echo "=== Step 5: build shade jar for $module ==="
  # commons sources include a logics.commons subset (Maven artifact quirk);
  # logics.commons is compiled separately, so drop the duplicate from commons.
  if [ -d "classes/commons-1.21/org/tweetyproject/logics/commons" ]; then
    rm -rf "classes/commons-1.21/org/tweetyproject/logics/commons"
  fi
  cd "$WORK/classes"
  JAR_ARGS=""
  for entry in "${COMPILE_ORDER[@]}"; do
    IFS=':' read -r m v <<< "$entry"
    if [ -d "$m-$v" ]; then
      JAR_ARGS="$JAR_ARGS -C $m-$v ."
    fi
  done
  OUT_JAR="$WORK/jars/org.tweetyproject.tweety-${module}-java8-shade.jar"
  jar cf "$OUT_JAR" $JAR_ARGS
  ls -la "$OUT_JAR"

  echo ""
  echo "=== Step 6: copy shade jar into MyIA.AI.Notebooks/SymbolicAI/Tweety/libs/ ==="
  cd "$WORK"
  LIBS_DIR="$WORK/../../libs"
  mkdir -p "$LIBS_DIR"
  cp "$OUT_JAR" "$LIBS_DIR/"
  ls -la "$LIBS_DIR/org.tweetyproject.tweety-${module}-java8-shade.jar"

  echo ""
  echo "=== Step 7: bytecode audit (must be major 52 only) for $module ==="
  WIN_OUT_JAR="$(cygpath -w "$OUT_JAR")"
  python -c "
import zipfile
from collections import Counter
with zipfile.ZipFile(r'$WIN_OUT_JAR') as z:
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
done

echo ""
echo "=== DONE ==="
echo "Next: cd .. ; for m in bipolar social weighted setaf extended; do dotnet build dotnet-build/build-Tweety\${m^}Shade.csproj -c Release; done"
echo "Then: cp dotnet-build/bin/Release/net8.0/org.tweetyproject.tweety-<module>.dll MyIA.AI.Notebooks/SymbolicAI/Tweety/<module>.dll (per module)"
