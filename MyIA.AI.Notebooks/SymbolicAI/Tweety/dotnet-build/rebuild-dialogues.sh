#!/bin/bash
# Rebuild the Tweety dialogues shade jar for IKVM 8.x (issue #10381, Tweety-8).
#
# The Maven Central jars for agents/prob/dialogues-1.30 are bytecode major 59
# (Java 15), which IKVM 8.x silently drops (IKVM0101 warning, classes missing).
# Strategy (identical to rebuild-5shades.sh, #10411): source-recompile the full
# dep chain from sources using javac --release 8, then shade into a fat-jar
# consumable by IKVM 8.x.
#
# Scan confirmed agents/prob/dialogues-1.30 sources contain NO Java 9+ features
# (no records, no text blocks, no switch expressions, no var, no Set.of, no
# instanceof pattern, no stream.toList) -- they compile cleanly under --release 8.
# Only the dung-1.30 layer needs its known c211 patches (switch expressions in
# AbstractExtensionReasoner etc.), reused verbatim from rebuild-5shades.sh.
#
# COMPILE_ORDER (single chain, all modules needed transitively):
#   math:1.30 commons:1.30 graphs:1.30 logics.commons:1.30 logics.pl:1.30
#   dung:1.30 agents:1.30 prob:1.30 dialogues:1.30
#
# Deps notes:
#   - agents-1.30  : groupId org.tweetyproject, artifactId agents
#                    (path org/tweetyproject/agents/1.30). 22 classes. Java 8 pure.
#                    Imports only org.tweetyproject.commons.util.
#   - prob-1.30    : arg/prob. 30 classes. Java 8 pure. Depends on dung.
#   - dialogues    : agents/dialogues. 63 classes (incl. oppmodels). Java 8 pure.
#                    Depends on agents + dung.
#
# Output (gitignored): jars/org.tweetyproject.tweety-dialogues-java8-shade.jar
# Copied into: ../libs/org.tweetyproject.tweety-dialogues-java8-shade.jar
# Used as <IkvmReference> in build-TweetyDialoguesShade.csproj ->
#   bin/Release/net8.0/org.tweetyproject.tweety-dialogues.dll
#
# Verdict bytecode (Step 7): expected {52: N} only.

# set -e  # disabled: transient curl failures killed the script (exit 6)
export JAVA_HOME="/c/Program Files/Freeplane/runtime"
export PATH="$JAVA_HOME/bin:$PATH"

cd "$(dirname "$0")"
WORK=$(pwd)

BUILD_DIR="$WORK/.dialogues-build"
mkdir -p "$BUILD_DIR"
cd "$BUILD_DIR"
WORK=$(pwd)

# Amchain versions (1.30 = source-clean on Maven Central / GitHub for commons).
declare -A VERSIONS=(
  [commons]="1.30"
  [math]="1.30"
  [graphs]="1.30"
  [logics.commons]="1.30"
  [logics.pl]="1.30"
)
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
# 1.30 modules (dung + the 3 dialogues-chain modules).
declare -A MOD130_GROUPPATH=(
  [dung]="arg/dung"
  [agents]="agents"
  [prob]="arg/prob"
  [dialogues]="agents/dialogues"
)

echo "=== Step 1: download transitive dep JARs (commons/math/graphs/logics.commons/logics.pl 1.30 + dung/agents/prob/dialogues 1.30) ==="
mkdir -p jars sources-extracted sources-jar classes
for m in commons math graphs; do
  jarbase="${m}-1.30.jar"
  if [ ! -f "jars/$jarbase" ]; then
    rc=$(curl -sL --retry 3 --retry-delay 2 --retry-all-errors -o "jars/$jarbase" -w "%{http_code}" "https://repo1.maven.org/maven2/org/tweetyproject/$m/1.30/$m-1.30.jar")
    [ "$rc" = "200" ] && echo "  got: $jarbase" || { rm -f "jars/$jarbase"; echo "  SKIP: $jarbase ($rc)"; }
  fi
done
for m in logics.commons logics.pl; do
  short="${m#logics.}"
  jarbase="${m}-1.30.jar"
  if [ ! -f "jars/$jarbase" ]; then
    rc=$(curl -sL --retry 3 --retry-delay 2 --retry-all-errors -o "jars/$jarbase" -w "%{http_code}" "https://repo1.maven.org/maven2/org/tweetyproject/logics/$short/1.30/$short-1.30.jar")
    [ "$rc" = "200" ] && echo "  got: $jarbase" || { rm -f "jars/$jarbase"; echo "  SKIP: $jarbase ($rc)"; }
  fi
done
# 1.30 modules (groupId org.tweetyproject, various sub-paths).
for m in dung agents prob dialogues; do
  gp="${MOD130_GROUPPATH[$m]}"
  jarbase="${m}-1.30.jar"
  if [ ! -f "jars/$jarbase" ]; then
    rc=$(curl -sL --retry 3 --retry-delay 2 --retry-all-errors -o "jars/$jarbase" -w "%{http_code}" "https://repo1.maven.org/maven2/org/tweetyproject/${gp}/1.30/${m}-1.30.jar")
    [ "$rc" = "200" ] && echo "  got: $jarbase" || { rm -f "jars/$jarbase"; echo "  ERR: $jarbase ($rc)"; exit 1; }
  fi
done

# Math transitive deps (same as rebuild-5shades.sh / rebuild-causal.sh).
_M2A="https://"
_M2B="repo1.maven.org/maven2"
M2="${_M2A}${_M2B}"
for url_pkg in \
  "$M2/gov/nist/math/jama/1.0.3/jama-1.0.3.jar:jama-1.0.3.jar" \
  "$M2/org/slf4j/slf4j-api/1.7.36/slf4j-api-1.7.36.jar:slf4j-api-1.7.36.jar" \
  "$M2/org/apache/commons/commons-math/2.2/commons-math-2.2.jar:commons-math-2.2.jar" \
  "$M2/org/apache/commons/commons-math3/3.6.1/commons-math3-3.6.1.jar:commons-math3-3.6.1.jar" \
  "$M2/org/ojalgo/ojalgo/45.1.1/ojalgo-45.1.1.jar:ojalgo-45.1.1.jar" \
  "$M2/org/sat4j/org.sat4j.core/2.3.1/org.sat4j.core-2.3.1.jar:org.sat4j.core-2.3.1.jar" \
  ; do
  url="${url_pkg%%:*}"
  out="${url_pkg##*:}"
  if [ ! -f "jars/$out" ]; then
    rc=$(curl -sL --retry 3 --retry-delay 2 --retry-all-errors -o "jars/$out" -w "%{http_code}" "$url")
    [ "$rc" = "200" ] && echo "  got: $out" || { rm -f "jars/$out"; echo "  SKIP: $out ($rc)"; }
  fi
done

echo ""
echo "=== Step 2: download sources jars ==="
# commons-1.30 sources ARE now on Maven Central (unlike 1.19/1.21 which were binary-only) ->
# pull all 5 chain modules uniformly from Maven sources jars (no GitHub tarball fallback needed).
for m in commons math graphs logics.commons logics.pl; do
  v="1.30"
  if [ ! -f "sources-jar/${m}-${v}-sources.jar" ]; then
    artifact="${ARTIFACT_ID[$m]}"
    group_path="${ARTIFACT_PATH[$m]}"
    url="https://repo1.maven.org/maven2/org/tweetyproject/${group_path}/${v}/${artifact}-${v}-sources.jar"
    rc=$(curl -sL --retry 3 --retry-delay 2 --retry-all-errors -o /dev/null -w "%{http_code}" "$url")
    if [ "$rc" != "200" ]; then echo "  ERR: $m $v sources not found ($url)"; exit 1; fi
    curl -sL --retry 3 --retry-delay 2 --retry-all-errors -o "sources-jar/${m}-${v}-sources.jar" "$url"
    echo "  got: ${m}-${v}-sources.jar"
  fi
done
for m in dung agents prob dialogues; do
  gp="${MOD130_GROUPPATH[$m]}"
  if [ ! -f "sources-jar/${m}-1.30-sources.jar" ]; then
    url="https://repo1.maven.org/maven2/org/tweetyproject/${gp}/1.30/${m}-1.30-sources.jar"
    rc=$(curl -sL --retry 3 --retry-delay 2 --retry-all-errors -o /dev/null -w "%{http_code}" "$url")
    if [ "$rc" != "200" ]; then echo "  ERR: $m 1.30 sources not found ($url)"; exit 1; fi
    curl -sL --retry 3 --retry-delay 2 --retry-all-errors -o "sources-jar/${m}-1.30-sources.jar" "$url"
    echo "  got: ${m}-1.30-sources.jar"
  fi
done

echo ""
echo "=== Step 3: extract sources ==="
for m in "${!VERSIONS[@]}"; do
  v=${VERSIONS[$m]}
  rm -rf "sources-extracted/$m-$v"
  mkdir -p "sources-extracted/$m-$v"
  cd "sources-extracted/$m-$v"
  unzip -q "$WORK/sources-jar/${m}-${v}-sources.jar"
  cd "$WORK"
  echo "  extracted: $m-$v"
done
for m in dung agents prob dialogues; do
  rm -rf "sources-extracted/${m}-1.30"
  mkdir -p "sources-extracted/${m}-1.30"
  cd "sources-extracted/${m}-1.30"
  unzip -q "$WORK/sources-jar/${m}-1.30-sources.jar"
  cd "$WORK"
  echo "  extracted: ${m}-1.30"
done

# Patch: remove unused ojalgo SuperimposedStore import in dung's
# ClaimBasedTheory.java (ojalgo class package-private; dead import).
if [ -f "sources-extracted/dung-1.30/org/tweetyproject/arg/dung/syntax/ClaimBasedTheory.java" ]; then
  sed -i '/^import org.ojalgo.matrix.store.SuperimposedStore;$/d' \
    "sources-extracted/dung-1.30/org/tweetyproject/arg/dung/syntax/ClaimBasedTheory.java"
  echo "  patched: removed unused ojalgo import (dung-1.30)"
fi

# Patch: rewrite Java 14+ switch expressions in dung-1.30 reasoner files into
# classic if-else chains so javac --release 8 accepts them. Verbatim from
# rebuild-5shades.sh (c211 patches). Only AbstractExtensionReasoner is needed
# transitively for the dialogues chain, but we apply the full patch set to keep
# dung-1.30 compilation consistent.
PATCH_PY="$(mktemp -d)/c211_switch_patch.py"
cat > "$PATCH_PY" <<'PYEOF'
import re, sys, pathlib, os

def patch_abstract(path):
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
        if (semantics == Semantics.UC) throw new IllegalArgumentException("UC semantics unsupported in this shade (SerialisedExtensionReasoner excluded).");
        throw new IllegalArgumentException("Unknown semantics.");
    }'''
    m = re.search(r'public static AbstractExtensionReasoner getSimpleReasonerForSemantics', src)
    if not m:
        print('  patch_abstract: marker not found (OK if dung subset)')
        return
    open_idx = src.find('{', m.end())
    if open_idx < 0:
        print('  ERR: cannot find method opening brace'); sys.exit(1)
    depth = 1; i = open_idx + 1
    while i < len(src) and depth > 0:
        if src[i] == '{': depth += 1
        elif src[i] == '}': depth -= 1
        i += 1
    if depth != 0:
        print('  ERR: unbalanced braces'); sys.exit(1)
    new_src = src[:m.start()] + new_method + src[i:]
    pathlib.Path(path).write_text(new_src, encoding='utf-8')
    print('  patched: AbstractExtensionReasoner')

if __name__ == '__main__':
    target = sys.argv[1]
    if 'AbstractExtensionReasoner' in target and 'Extended' not in target:
        patch_abstract(target)
PYEOF

for tgt in \
  "sources-extracted/dung-1.30/org/tweetyproject/arg/dung/reasoner/AbstractExtensionReasoner.java" \
  ; do
  if [ -f "$tgt" ]; then
    if ! grep -q "\[c211 patch\]" "$tgt"; then
      python "$PATCH_PY" "$tgt" || exit 1
    fi
  fi
done

# Patch: downgrade commons-1.30 Parser.java Java 11+ API to Java 8 equivalents
# (Files.readString/Path.of/isBlank are absent under javac --release 8). Parser is
# the abstract base class extended by tweety parsers, so it must compile (cannot be
# excluded). Same approach as the commons-1.19 patch in rebuild-7a.sh.
COMMONS_PARSER="sources-extracted/commons-1.30/org/tweetyproject/commons/Parser.java"
if [ -f "$COMMONS_PARSER" ]; then
  python - "$COMMONS_PARSER" <<'CPYEOF'
import sys, pathlib
p = pathlib.Path(sys.argv[1])
src = p.read_text(encoding='utf-8')
if 'import java.nio.file.Paths;' not in src:
    src = src.replace('import java.nio.file.Path;',
                      'import java.nio.file.Path;\nimport java.nio.file.Paths;\nimport java.nio.charset.StandardCharsets;')
src = src.replace('Path.of(', 'Paths.get(')
# Files.readString(x) -> new String(Files.readAllBytes(x), StandardCharsets.UTF_8)
src = src.replace('Files.readString(', 'new String(Files.readAllBytes(')
src = src.replace('new String(Files.readAllBytes(Paths.get(filename));',
                  'new String(Files.readAllBytes(Paths.get(filename)), StandardCharsets.UTF_8);')
src = src.replace('.isBlank()', '.trim().isEmpty()')
p.write_text(src, encoding='utf-8')
print('  patched: commons Parser.java -> Java 8 (Paths/get/readAllBytes/trim)')
CPYEOF
fi

# Patch: downgrade the single Java 10+ `var` local in dung-1.30 DungTheory.java
# (cleanUpMap helper, line ~1171). DungTheory is the central type, cannot be excluded.
DUNG_THEORY="sources-extracted/dung-1.30/org/tweetyproject/arg/dung/syntax/DungTheory.java"
if [ -f "$DUNG_THEORY" ]; then
  sed -i 's/var tempArgsToRemove = new HashSet<Argument>();/HashSet<Argument> tempArgsToRemove = new HashSet<Argument>();/' "$DUNG_THEORY"
  echo "  patched: dung DungTheory.java var -> explicit type"
fi

# Files to exclude during compilation (commercial libs / Java 9+ features unused by chain).
MATH_EXCLUDE=(
  "org/tweetyproject/math/opt/solver/AntColonyOptimization.java"
  "org/tweetyproject/math/opt/solver/GurobiOptimizer.java"
  "org/tweetyproject/math/util/OjAlgoMathUtils.java"
  "org/tweetyproject/math/examples/"
)
LOGICS_PL_EXCLUDE=(
  "org/tweetyproject/logics/pl/plugin/PlPlugin.java"
  "org/tweetyproject/logics/pl/sat/CmdLineSatSolver.java"
  "org/tweetyproject/logics/pl/examples/"
)
GRAPHS_EXCLUDE=(
  "org/tweetyproject/graphs/util/GraphPlotter.java"
  "org/tweetyproject/graphs/util/AigGraphPlotter.java"
)
# commons-1.30 Parser.java uses Java 11+ (Path.of/Files.readString/isBlank) -- it is
# the abstract base class needed by the chain, so it is PATCHED to Java 8 (see below)
# rather than excluded. Only examples/ (junit) + ExamplesHTMLGenerator (isBlank/strip,
# not used at runtime) are excluded.
COMMONS_EXCLUDE=(
  "org/tweetyproject/commons/examples/"
  "org/tweetyproject/commons/util/ExamplesHTMLGenerator.java"
)
PROB_EXCLUDE=(
  "org/tweetyproject/arg/prob/examples/"
)
# dialogues-1.30 structured/ (SAS = Structured Argumentation Systems) depends on the
# standalone arg.saf module (out of chain), and examples/ are demos. oppmodels/ (the
# Tranche-2 target: ArguingAgent/GroundedGameSystem/T1BeliefState) is independent of both.
DIALOGUES_EXCLUDE=(
  "org/tweetyproject/agents/dialogues/structured/"
  "org/tweetyproject/agents/dialogues/examples/"
)
# dung-1.30 Java 14+ switch / advanced-feature subpackages (adapted from rebuild-5shades.sh,
# but divisions/ is INCLUDED here because prob-1.30 lotteries depend on it -- the 5shades
# excluded it as the chain there did not need prob, the dialogues chain does).
DUNG_130_EXCLUDE=(
  "org/tweetyproject/arg/dung/equivalence/"
  "org/tweetyproject/arg/dung/learning/"
  "org/tweetyproject/arg/dung/serialisability/"
  "org/tweetyproject/arg/dung/writer/TikzWriter.java"
  "org/tweetyproject/arg/dung/reasoner/SerialisedExtensionReasoner.java"
  "org/tweetyproject/arg/dung/reasoner/ExtensionRankingReasoner.java"
  "org/tweetyproject/arg/dung/reasoner/FudgeAcceptabilityReasoner.java"
  "org/tweetyproject/arg/dung/reasoner/AbstractSatExtensionReasoner.java"
  "org/tweetyproject/arg/dung/reasoner/SatCompleteReasoner.java"
  "org/tweetyproject/arg/dung/reasoner/SatStableReasoner.java"
  "org/tweetyproject/arg/dung/util/DungTheoryPlotter.java"
  "org/tweetyproject/arg/dung/util/EnumeratingDilationGenerator.java"
  "org/tweetyproject/arg/dung/reasoner/ProboI23Reasoner.java"
  "org/tweetyproject/arg/dung/examples/"
  "org/tweetyproject/arg/dung/principles/"
)

echo ""
echo "=== Step 4: compile chain (math->commons->graphs->logics.commons->logics.pl->dung->agents->prob->dialogues) ==="
COMPILE_ORDER=("math:1.30" "commons:1.30" "graphs:1.30" "logics.commons:1.30" "logics.pl:1.30" "dung:1.30" "agents:1.30" "prob:1.30" "dialogues:1.30")

for entry in "${COMPILE_ORDER[@]}"; do
  IFS=':' read -r m v <<< "$entry"
  echo "  compiling: $m v$v"
  rm -rf "classes/$m-$v"
  mkdir -p "classes/$m-$v"
  files=$(find "sources-extracted/$m-$v" -name "*.java")
  if [ "$m" = "math" ]; then
    for ex in "${MATH_EXCLUDE[@]}"; do files=$(echo "$files" | grep -v "$ex" || true); done
  fi
  if [ "$m" = "logics.pl" ]; then
    for ex in "${LOGICS_PL_EXCLUDE[@]}"; do files=$(echo "$files" | grep -v "$ex" || true); done
  fi
  if [ "$m" = "graphs" ]; then
    for ex in "${GRAPHS_EXCLUDE[@]}"; do files=$(echo "$files" | grep -v "$ex" || true); done
  fi
  if [ "$m" = "commons" ]; then
    for ex in "${COMMONS_EXCLUDE[@]}"; do files=$(echo "$files" | grep -v "$ex" || true); done
  fi
  if [ "$m" = "prob" ]; then
    for ex in "${PROB_EXCLUDE[@]}"; do files=$(echo "$files" | grep -v "$ex" || true); done
  fi
  if [ "$m" = "dialogues" ]; then
    for ex in "${DIALOGUES_EXCLUDE[@]}"; do files=$(echo "$files" | grep -v "$ex" || true); done
  fi
  if [ "$m" = "dung" ] && [ "$v" = "1.30" ]; then
    for ex in "${DUNG_130_EXCLUDE[@]}"; do files=$(echo "$files" | grep -v "$ex" || true); done
  fi

  CP=""
  for j in commons-1.30 graphs-1.30; do
    [ -f "jars/$j.jar" ] && CP="$CP;jars/$j.jar"
  done
  # Math transitive deps on classpath for all modules in chain.
  for j in jama-1.0.3.jar slf4j-api-1.7.36.jar commons-math-2.2.jar commons-math3-3.6.1.jar ojalgo-45.1.1.jar org.sat4j.core-2.3.1.jar; do
    [ -f "jars/$j" ] && CP="$CP;jars/$j"
  done
  # Add previously compiled module classes (in COMPILE_ORDER).
  for prev in "${COMPILE_ORDER[@]}"; do
    if [ "$prev" = "$entry" ]; then break; fi
    prev_name="${prev%%:*}"; prev_ver="${prev##*:}"
    if [ -d "classes/${prev_name}-${prev_ver}" ]; then
      CP="$CP;classes/${prev_name}-${prev_ver}"
    fi
  done

  if ! javac --release 8 -cp "$CP" -d "classes/$m-$v" $files 2>"compile-$m-$v.log"; then
    echo "  COMPILE FAILED for $m-$v -- see compile-$m-$v.log"
    grep "error:" "compile-$m-$v.log" | head -15
    exit 1
  fi
  count=$(find "classes/$m-$v" -name "*.class" | wc -l)
  echo "    $count classes compiled"
done

echo ""
echo "=== Step 5: build shade jar for dialogues ==="
# commons sources include a logics.commons subset (Maven artifact quirk);
# logics.commons is compiled separately, so drop the duplicate from commons.
if [ -d "classes/commons-1.30/org/tweetyproject/logics/commons" ]; then
  rm -rf "classes/commons-1.30/org/tweetyproject/logics/commons"
fi
cd "$WORK/classes"
JAR_ARGS=""
for entry in "${COMPILE_ORDER[@]}"; do
  IFS=':' read -r m v <<< "$entry"
  if [ -d "$m-$v" ]; then
    JAR_ARGS="$JAR_ARGS -C $m-$v ."
  fi
done
OUT_JAR="$WORK/jars/org.tweetyproject.tweety-dialogues-java8-shade.jar"
jar cf "$OUT_JAR" $JAR_ARGS
ls -la "$OUT_JAR"

echo ""
echo "=== Step 6: copy shade jar into MyIA.AI.Notebooks/SymbolicAI/Tweety/libs/ ==="
cd "$WORK"
LIBS_DIR="$WORK/../../libs"
mkdir -p "$LIBS_DIR"
cp "$OUT_JAR" "$LIBS_DIR/"
ls -la "$LIBS_DIR/org.tweetyproject.tweety-dialogues-java8-shade.jar"

echo ""
echo "=== Step 7: bytecode audit (must be major 52 only) ==="
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

echo ""
echo "=== DONE ==="
echo "Next: dotnet build dotnet-build/build-TweetyDialoguesShade.csproj -c Release"
echo "Then: cp dotnet-build/bin/Release/net8.0/org.tweetyproject.tweety-dialogues.dll ../libs/"
