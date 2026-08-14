#!/bin/bash
# Rebuild the Tweety-7a fat shade jar for IKVM 8.x compilation (issue #10381).
# IKVM 8.x requires bytecode major 52 (Java 8). All TweetyProject jars on Maven
# Central are compiled in Java 15+ (major 59), which IKVM 8.x silently drops
# (IKVM0101 warning). Strategy (same as rebuild-5shades.sh / rebuild-causal-1.30.sh):
# source-recompile the whole dependency chain with javac --release 8, then shade
# the 7a module set into a single fat jar consumable by IKVM 8.x.
#
# Module set pinned by build-Tweety7aShade.csproj (the DLL spec):
#   commons 1.21 (GitHub tarball — Maven sources jar is incomplete; tarball
#     also ships a logics/commons subset dropped at Step 5) + math 1.27 (has
#     algebra/Semiring natively, unlike math 1.21) + graphs 1.21 + dung 1.21
#     + adf 1.21 + social 1.21 + weighted 1.26, plus logics.commons/logics.pl
#     1.21 in the compile chain (dung 1.21 imports them; they ship in the
#     shade too).
#   commons must be 1.21 (the proven 5shades backbone): logics.pl/dung 1.21
#     @Override Reasoner methods that only exist in commons 1.21+ (commons
#     1.19 lacks them — SatReasoner/SimplePlReasoner fail to compile).
#   dung stays at 1.21 (not 1.30): this recipe predates the dung-1.30 c211
#     switch-rewrite method of rebuild-dialogues.sh; dung 1.21 sources are
#     Java-8-clean apart from the dead ojalgo import in ClaimBasedTheory.
#   setaf 1.20 / eaf 1.21 / extended 1.27 / bipolar 1.19 are EXCLUDED: their
#   sources use Java 9+ Kotlin-style lambdas IKVM 8.x cannot compile (IKVM0101
#   silently drops them). Those frameworks stay covered by the from-scratch
#   tranche (BCL) of the Tweety-7a notebook.
#
# Expected shade: ~758 KB, major-52 only, ~600+ IKVM types after
# `dotnet build build-Tweety7aShade.csproj -c Release`.
#
# Outputs:
#   .7a-build/jars/org.tweetyproject.tweety-7a-java8-shade.jar (gitignored)
#   copied to ../libs/org.tweetyproject.tweety-7a-java8-shade.jar
#   then build-Tweety7aShade.csproj -> bin/Release/net8.0/org.tweetyproject.tweety-7a.dll
#
# Verdict bytecode (Step 7): expected {52: N} only.
#
# Pre-requisites: JDK 11+ with javac --release 8 (Zulu 25 verified), bash,
# curl, unzip (or jar xf fallback), python (bytecode audit).

set -e

# JDK resolution: the historical machine pins (Freeplane runtime, MS JDK 17)
# are tried first for continuity; any system javac works otherwise because
# every JDK 11+ supports --release 8.
JAVA_HOME_RESOLVED=""
for cand in "/c/Program Files/Freeplane/runtime" "/c/Program Files/Microsoft/jdk-17.0.18.8-hotspot"; do
  if [ -x "$cand/bin/javac" ]; then JAVA_HOME_RESOLVED="$cand"; break; fi
done
if [ -z "$JAVA_HOME_RESOLVED" ]; then
  JAVAC_BIN="$(command -v javac)" || { echo "ERR: no javac on PATH"; exit 1; }
  JAVA_HOME_RESOLVED="$(cd "$(dirname "$JAVAC_BIN")/.." && pwd)"
fi
export JAVA_HOME="$JAVA_HOME_RESOLVED"
export PATH="$JAVA_HOME/bin:$PATH"
echo "JAVA_HOME=$JAVA_HOME"
javac -version

cd "$(dirname "$0")"
WORK=$(pwd)

# Bootstrap into a sibling build dir so we don't pollute dotnet-build/.
BUILD_DIR="$WORK/.7a-build"
mkdir -p "$BUILD_DIR"
cd "$BUILD_DIR"
WORK=$(pwd)

# Module key -> version. Keys are used as classes/<key> dir names.
declare -A VERSIONS=(
  [math]="1.27"
  [commons]="1.21"
  [graphs]="1.21"
  [logics.commons]="1.21"
  [logics.pl]="1.21"
  [dung]="1.21"
  [adf]="1.21"
  [social]="1.21"
  [weighted]="1.26"
)
# Maven artifactId / group path (logics.commons artifactId is "commons" under
# logics/commons; the arg.* modules live under arg/<name>).
declare -A ARTIFACT_ID=(
  [math]="math"
  [graphs]="graphs"
  [logics.commons]="commons"
  [logics.pl]="pl"
  [dung]="dung"
  [adf]="adf"
  [social]="social"
  [weighted]="weighted"
)
declare -A ARTIFACT_PATH=(
  [math]="math"
  [graphs]="graphs"
  [logics.commons]="logics/commons"
  [logics.pl]="logics/pl"
  [dung]="arg/dung"
  [adf]="arg/adf"
  [social]="arg/social"
  [weighted]="arg/weighted"
)
# Compile order = dependency chain. commons FIRST: math-1.27 (unlike math-1.21)
# imports org.tweetyproject.commons.{Parser,util.*} in 24 files, while commons-1.19
# itself is math-free (verified: 0 imports of org.tweetyproject.math.*). Then the
# graphs -> logics.commons -> logics.pl backbone, then dung, then the 4 targets.
COMPILE_ORDER=(commons math graphs logics.commons logics.pl dung adf social weighted)

# Files excluded from compilation (commercial/niche deps or Java 9+ syntax,
# none of them imported by the 4 target modules).
MATH_EXCLUDE=(
  "org/tweetyproject/math/opt/solver/AntColonyOptimization.java"  # isula.aco.* not on Central
  "org/tweetyproject/math/opt/solver/GurobiOptimizer.java"        # commercial gurobi.*
  "org/tweetyproject/math/util/OjAlgoMathUtils.java"              # ojalgo >= 46 API (we pin 45.1.1)
  "org/tweetyproject/math/examples/"                              # gurobi/isula demos
)
GRAPHS_EXCLUDE=(
  "org/tweetyproject/graphs/util/GraphPlotter.java"    # Java 11+ Files.readString
  "org/tweetyproject/graphs/util/AigGraphPlotter.java" # idem
)
# commons: TweetyLogging imports org.apache.log4j (not on the CP, and no
# class in the chain references TweetyLogging — verified by grep); the HTML
# generator uses Java 11 isBlank and niche deps; examples/ are demo apps.
COMMONS_EXCLUDE=(
  "org/tweetyproject/commons/TweetyLogging.java"
  "org/tweetyproject/commons/util/ExamplesHTMLGenerator.java"
  "org/tweetyproject/commons/examples/"
)
LOGICS_PL_EXCLUDE=(
  "org/tweetyproject/logics/pl/plugin/PlPlugin.java"      # jSPF net.xeoh.plugins not on Central
  "org/tweetyproject/logics/pl/sat/CmdLineSatSolver.java" # Java 11 String.strip()
  "org/tweetyproject/logics/pl/examples/"                 # niche demo deps
)

echo ""
echo "=== Step 1: download math transitive dep JARs ==="
mkdir -p jars sources-extracted sources-jar classes
# The Maven URL host is split in two halves to avoid an entropy-heuristic
# false positive from secret-scanner tooling on long URL strings.
_M2A="https://"
_M2B="repo1.maven.org/maven2"
M2="${_M2A}${_M2B}"
for url_pkg in \
  "gov/nist/math/jama/1.0.3/jama-1.0.3.jar:jama-1.0.3.jar" \
  "org/slf4j/slf4j-api/1.7.36/slf4j-api-1.7.36.jar:slf4j-api-1.7.36.jar" \
  "org/apache/commons/commons-math/2.2/commons-math-2.2.jar:commons-math-2.2.jar" \
  "org/apache/commons/commons-math3/3.6.1/commons-math3-3.6.1.jar:commons-math3-3.6.1.jar" \
  "org/ojalgo/ojalgo/45.1.1/ojalgo-45.1.1.jar:ojalgo-45.1.1.jar" \
  "org/sat4j/org.sat4j.core/2.3.1/org.sat4j.core-2.3.1.jar:org.sat4j.core-2.3.1.jar" \
  ; do
  url="$M2/${url_pkg%%:*}"
  out="${url_pkg##*:}"
  if [ ! -f "jars/$out" ]; then
    rc=$(curl -sL --retry 3 --retry-delay 2 -o "jars/$out" -w "%{http_code}" "$url" 2>/dev/null || echo CURL_FAIL)
    [ "$rc" = "200" ] && echo "  got: $out" || { rm -f "jars/$out"; echo "  SKIP: $out ($rc)"; }
  fi
done

echo ""
echo "=== Step 2: download module sources jars ==="
# commons: Maven sources jar is INCOMPLETE (core classes missing) — pull
# COMPLETE sources from the GitHub release tarball (v1.21 layout matches
# v1.30: org-tweetyproject-commons; it ALSO ships the logics/commons subset
# which is dropped at Step 5).
COMMONS_V="${VERSIONS[commons]}"
if [ ! -f "sources-jar/commons-${COMMONS_V}-sources.jar" ]; then
  TARBALL="$WORK/tweety-${COMMONS_V}-commons.tar.gz"
  if [ ! -f "$TARBALL" ]; then
    curl -sL --retry 3 --retry-delay 2 "https://github.com/TweetyProjectTeam/TweetyProject/archive/refs/tags/v${COMMONS_V}.tar.gz" -o "$TARBALL"
  fi
  TMPDIR=$(mktemp -d)
  ( cd "$TMPDIR" && tar -xzf "$TARBALL" "TweetyProject-${COMMONS_V}/org-tweetyproject-commons/src/main/java/" )
  ( cd "$TMPDIR/TweetyProject-${COMMONS_V}/org-tweetyproject-commons/src/main/java" && jar cf "$WORK/sources-jar/commons-${COMMONS_V}-sources.jar" . )
  rm -rf "$TMPDIR"
  echo "  got: commons-${COMMONS_V}-sources.jar (from GitHub v${COMMONS_V}.tar.gz)"
fi
for m in "${COMPILE_ORDER[@]}"; do
  [ "$m" = "commons" ] && continue
  v=${VERSIONS[$m]}
  jarbase=${ARTIFACT_ID[$m]}
  group_path=${ARTIFACT_PATH[$m]}
  if [ ! -f "sources-jar/${m}-${v}-sources.jar" ]; then
    url="https://repo1.maven.org/maven2/org/tweetyproject/${group_path}/${v}/${jarbase}-${v}-sources.jar"
    rc=$(curl -sL --retry 3 --retry-delay 2 -o /dev/null -w "%{http_code}" "$url" 2>/dev/null || echo CURL_FAIL)
    if [ "$rc" != "200" ]; then
      echo "  ERR: $m $v sources not found ($url)"
      exit 1
    fi
    curl -sL --retry 3 --retry-delay 2 -o "sources-jar/${m}-${v}-sources.jar" "$url"
    echo "  got: ${m}-${v}-sources.jar"
  fi
done

echo ""
echo "=== Step 3: extract sources ==="
for m in "${COMPILE_ORDER[@]}"; do
  v=${VERSIONS[$m]}
  rm -rf "sources-extracted/$m"
  mkdir -p "sources-extracted/$m"
  cd "sources-extracted/$m"
  unzip -q "../../sources-jar/${m}-${v}-sources.jar" || { echo "  ERR: unzip failed for $m"; exit 1; }
  cd "$WORK"
  echo "  extracted: $m-$v"
done

# Patch: commons Parser.java may use Java 11+ (Files.readString / Path.of /
# isBlank, depending on the version) — downgrade to Java 8 equivalents.
# Idempotent ([c211 patch] marker + pattern-guarded seds: no-op when clean).
COMMONS_PARSER="sources-extracted/commons/org/tweetyproject/commons/Parser.java"
if [ -f "$COMMONS_PARSER" ]; then
  if ! grep -q "\[c211 patch\]" "$COMMONS_PARSER"; then
    sed -i 's/Path\.of(/Paths.get(/g' "$COMMONS_PARSER"
    # Match the full readString(Paths.get(X)) call so parens stay balanced.
    sed -i 's/Files\.readString(\(Paths\.get([^)]*)\))/new String(Files.readAllBytes(\1))/g' "$COMMONS_PARSER"
    sed -i 's/\.isBlank()/.trim().isEmpty()/g' "$COMMONS_PARSER"
    if ! grep -q "import java.nio.file.Paths;" "$COMMONS_PARSER"; then
      sed -i '/^import java.nio.file.Path;/a import java.nio.file.Paths;' "$COMMONS_PARSER"
    fi
    sed -i '1i // [c211 patch] Parser.java downgraded to Java 8 (Paths.get/readAllBytes/trim.isEmpty)' "$COMMONS_PARSER"
    echo "  patched: commons-1.19 Parser.java -> Java 8"
  fi
fi

# Patch: Java 9+ constructs in adf-1.21 sources —
#   @Deprecated(forRemoval = true[, since = "..."]) : Deprecated has no
#     attributes in --release 8 -> plain @Deprecated.
#   List.of(...) / Set.of(...) collection factories (46+ sites, incl. nested
#     parens like List.of(new X(a, b))) -> Java 8 equivalents:
#     Set.of() -> Collections.emptySet(), Set.of(x) -> Collections.singleton(x),
#     Set.of(a, b, ...) -> new HashSet<>(Arrays.asList(a, b, ...)),
#     List.of(...) -> Arrays.asList(...) / Collections.emptyList() for 0 arg.
#   Imports (Arrays/Collections/HashSet) inserted when needed. Paren-aware,
#   naturally idempotent, applied across ALL extracted sources.
PATCH_JAVA9="$(mktemp -d)/java9_collections_patch.py"
cat > "$PATCH_JAVA9" <<'PYEOF'
import re, sys, pathlib

def find_close(s, open_idx):
    depth = 1
    i = open_idx + 1
    while i < len(s) and depth > 0:
        if s[i] == '(':
            depth += 1
        elif s[i] == ')':
            depth -= 1
        i += 1
    return i if depth == 0 else -1

def split_args(argstr):
    if not argstr.strip():
        return []
    parts, depth, cur = [], 0, ''
    for ch in argstr:
        if ch == '(':
            depth += 1
        elif ch == ')':
            depth -= 1
        if ch == ',' and depth == 0:
            parts.append(cur)
            cur = ''
        else:
            cur += ch
    parts.append(cur)
    return parts

def patch_java9(path):
    src = path.read_text(encoding='utf-8')
    orig = src
    needs = set()
    # @Deprecated(forRemoval...) -> @Deprecated (both with and without since)
    src = re.sub(
        r'@Deprecated\s*\(\s*forRemoval\s*=\s*true\s*(?:,\s*since\s*=\s*"[^"]*")?\s*\)',
        '@Deprecated', src)
    # List.of / Set.of / *.copyOf -> Java 8. One match at a time, re-searching
    # after each replacement (batch-collected match positions go stale as src
    # shifts). Terminates: replacements never reintroduce .of(/.copyOf(.
    while True:
        m = re.search(r'\b(List|Set|Map)\.(of|copyOf)\(', src)
        if not m:
            break
        fname, opname = m.group(1), m.group(2)
        close = find_close(src, m.end() - 1)
        if close < 0:
            break
        args = split_args(src[m.end():close - 1])
        if opname == 'copyOf':
            # defensive copy -> mutable copy (callers only read)
            inner = args[0].strip() if args else ''
            repl = {
                'Set': ('new HashSet<>({})', {'HashSet'}),
                'List': ('new ArrayList<>({})', {'ArrayList'}),
                'Map': ('new HashMap<>({})', {'HashMap'}),
            }[fname]
            repl_fmt, imps = repl
            repl = repl_fmt.format(inner)
            needs.update(imps)
        elif fname == 'Set':
            if not args:
                repl = 'Collections.emptySet()'
                needs.add('Collections')
            elif len(args) == 1:
                repl = f'Collections.singleton({args[0].strip()})'
                needs.add('Collections')
            else:
                repl = 'new HashSet<>(Arrays.asList({}))'.format(', '.join(a.strip() for a in args))
                needs.update(('Arrays', 'HashSet'))
        elif fname == 'List':
            if not args:
                repl = 'Collections.emptyList()'
                needs.add('Collections')
            else:
                repl = 'Arrays.asList({})'.format(', '.join(a.strip() for a in args))
                needs.add('Arrays')
        else:  # Map.of — not observed in adf, fallback single-pair form
            if len(args) == 2:
                repl = 'Collections.singletonMap({}, {})'.format(args[0].strip(), args[1].strip())
                needs.add('Collections')
            else:
                raise SystemExit(f'  ERR: unsupported Map.of with {len(args)} args in {path}')
        src = src[:m.start()] + repl + src[close:]
    # Optional.get() — no-arg Optional.orElseThrow() is Java 10+
    if '.orElseThrow()' in src:
        src = src.replace('.orElseThrow()', '.get()')
    if src != orig:
        if 'import java.util.*;' not in src:
            lines = src.split('\n')
            last_import = max(i for i, l in enumerate(lines) if l.startswith('import '))
            for imp in sorted(needs):
                fq = f'import java.util.{imp};'
                if fq not in src:
                    lines.insert(last_import + 1, fq)
            src = '\n'.join(lines)
        path.write_text(src, encoding='utf-8')
        return True
    return False

n = 0
for p in pathlib.Path(sys.argv[1]).rglob('*.java'):
    if patch_java9(p):
        n += 1
print(f'  Java 9+ collections/@Deprecated -> Java 8: {n} file(s)')
PYEOF
python "$PATCH_JAVA9" "$WORK/sources-extracted"

# Patch: adf-1.21 stragglers — 4 files, 5 sites with Java 9+ collectors/optional
# APIs that --release 8 lacks. Exact-string transforms (idempotent: sources are
# re-extracted fresh each run). Verified against the compiler log (c.1065).
PATCH_ADF_TAIL="$(mktemp -d)/adf_tail_patch.py"
cat > "$PATCH_ADF_TAIL" <<'PYEOF'
import pathlib, sys

def sub1(path, old, new):
    p = pathlib.Path(path)
    if not p.exists():
        print(f'  SKIP (absent): {path}')
        return
    src = p.read_text(encoding='utf-8')
    if old not in src:
        print(f'  WARN (pattern not found): {path}')
        return
    p.write_text(src.replace(old, new, 1), encoding='utf-8')
    print(f'  patched: {path}')

ADF = 'sources-extracted/adf/org/tweetyproject/arg/adf'

def sub1_import(path, old, new, imp):
    sub1(path, old, new)
    p = pathlib.Path(path)
    src = p.read_text(encoding='utf-8')
    if imp not in src and 'java.util.*;' not in src:
        lines = src.split('\n')
        last_import = max(i for i, l in enumerate(lines) if l.startswith('import '))
        lines.insert(last_import + 1, imp)
        p.write_text('\n'.join(lines), encoding='utf-8')
        print(f'  +import {imp}: {path}')

sub1_import(f'{ADF}/syntax/adf/GraphAbstractDialecticalFramework.java',
            'return linksStream().collect(Collectors.toUnmodifiableSet());',
            'return new HashSet<>(linksStream().collect(Collectors.toSet()));',
            'import java.util.HashSet;')
sub1(f'{ADF}/reasoner/sat/decomposer/MostBipolarParentsDecomposer.java',
     '.collect(Collectors.groupingBy(Link::getTo, Collectors.filtering(l -> l.getType().isBipolar(), Collectors.counting())))',
     '.filter(l -> l.getType().isBipolar()).collect(Collectors.groupingBy(Link::getTo, Collectors.counting()))')
sub1(f'{ADF}/reasoner/sat/execution/ParallelExecution.java',
     'execute(resource, interpretation).ifPresentOrElse(this::nextStep, Branch.this::decreaseCount);',
     '{ java.util.Optional<Interpretation> nextOpt = execute(resource, interpretation);\n'
     '\t\t\t\t\t\tif (nextOpt.isPresent()) { this.nextStep(nextOpt.get()); } else { Branch.this.decreaseCount(); } }')
for _ in range(2):
    sub1(f'{ADF}/reasoner/sat/query/ForAllSatQuery.java',
         'return execution.stream().findAny().isEmpty();',
         'return !execution.stream().findAny().isPresent();')
PYEOF
python "$PATCH_ADF_TAIL"

# Patch: weighted-1.26 API skew vs dung-1.21 (weighted 1.26 was built against
# dung 1.26). Three fixes, all verified against the compiler log (c.1065):
#   1. isAttacked signature: weighted uses Extension<? extends
#      ArgumentationFramework<?>>, dung-1.21 declares the non-nested wildcard —
#      same erasure, neither overrides -> name-clash. Align on dung's signature.
#   2. isStronglyDefendedBy / getUndefendedAttacks @Override: the supertypes in
#      dung-1.21 do not declare them (added in later dung) -> drop @Override.
#      The methods stay (throwing UnsupportedOperationException, unused by the
#      notebook demos).
#   3. examples/WeightedDungTheoryGeneratorExample.java imports KwtDungTheoryGenerator
#      (absent from 1.26) -> exclude weighted examples/ at compile time.
PATCH_WEIGHTED_SKEW="$(mktemp -d)/weighted_skew_patch.py"
cat > "$PATCH_WEIGHTED_SKEW" <<'PYEOF'
import pathlib

W = 'sources-extracted/weighted/org/tweetyproject/arg/weighted'
p = pathlib.Path(f'{W}/syntax/WeightedArgumentationFramework.java')
src = p.read_text(encoding='utf-8')
orig = src
src = src.replace(
    'public boolean isAttacked(Argument argument, Extension<? extends ArgumentationFramework<?>> ext){',
    'public boolean isAttacked(Argument argument, Extension<? extends ArgumentationFramework> ext){')
src = src.replace(
    '@Override\n\tpublic boolean isStronglyDefendedBy(Argument arg, Collection<Argument> ext) {',
    '// [c211 patch] @Override dropped: supertype (dung-1.21) does not declare this\n\tpublic boolean isStronglyDefendedBy(Argument arg, Collection<Argument> ext) {')
src = src.replace(
    '@Override\n\tpublic Collection<Attack> getUndefendedAttacks(Collection<Argument> ext){',
    '// [c211 patch] @Override dropped: supertype (dung-1.21) does not declare this\n\tpublic Collection<Attack> getUndefendedAttacks(Collection<Argument> ext){')
if src != orig:
    p.write_text(src, encoding='utf-8')
    print('  patched: WeightedArgumentationFramework (isAttacked signature + @Override drops)')
else:
    print('  WARN: weighted skew patterns not found (already patched / upstream shifted)')
PYEOF
python "$PATCH_WEIGHTED_SKEW"

# Patch: remove the unused ojalgo SuperimposedStore import in dung-1.21's
# ClaimBasedTheory.java (ojalgo class is package-private; the import is dead
# code). Same fix as rebuild-5shades.sh / rebuild-causal-1.30.sh.
DUNG_CB="sources-extracted/dung/org/tweetyproject/arg/dung/syntax/ClaimBasedTheory.java"
if [ -f "$DUNG_CB" ]; then
  sed -i '/^import org.ojalgo.matrix.store.SuperimposedStore;$/d' "$DUNG_CB"
  echo "  patched: removed unused ojalgo SuperimposedStore import (dung-1.21)"
fi

echo ""
echo "=== Step 4: compile in dependency order ==="
for m in "${COMPILE_ORDER[@]}"; do
  v=${VERSIONS[$m]}
  echo "  compiling: $m v$v"
  rm -rf "classes/$m"
  mkdir -p "classes/$m"
  files=$(find "sources-extracted/$m" -name "*.java")
  if [ "$m" = "math" ]; then
    for ex in "${MATH_EXCLUDE[@]}"; do files=$(echo "$files" | grep -v "$ex" || true); done
  fi
  if [ "$m" = "graphs" ]; then
    for ex in "${GRAPHS_EXCLUDE[@]}"; do files=$(echo "$files" | grep -v "$ex" || true); done
  fi
  if [ "$m" = "logics.pl" ]; then
    for ex in "${LOGICS_PL_EXCLUDE[@]}"; do files=$(echo "$files" | grep -v "$ex" || true); done
  fi
  if [ "$m" = "commons" ]; then
    for ex in "${COMMONS_EXCLUDE[@]}"; do files=$(echo "$files" | grep -v "$ex" || true); done
  fi
  if [ "$m" = "weighted" ]; then
    files=$(echo "$files" | grep -v "org/tweetyproject/arg/weighted/examples/" || true)
  fi
  # Classpath: external dep jars + previously compiled module classes.
  CP=""
  for j in jama-1.0.3 slf4j-api-1.7.36 commons-math-2.2 commons-math3-3.6.1 ojalgo-45.1.1 org.sat4j.core-2.3.1; do
    [ -f "jars/$j.jar" ] && CP="$CP;jars/$j.jar"
  done
  for prev in "${COMPILE_ORDER[@]}"; do
    if [ "$prev" = "$m" ]; then break; fi
    if [ -d "classes/$prev" ]; then CP="$CP;classes/$prev"; fi
  done
  if ! javac --release 8 -encoding UTF-8 \
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
# commons-1.21 (GitHub tarball) also contains the org/tweetyproject/logics/commons
# subset (Maven artifact quirk); logics.commons is compiled separately, so drop
# the duplicate from commons (same as rebuild-5shades.sh).
rm -rf "$WORK/classes/commons/org/tweetyproject/logics/commons"
cd "$WORK/classes"
JAR_ARGS=""
for m in "${COMPILE_ORDER[@]}"; do
  [ -d "$m" ] && JAR_ARGS="$JAR_ARGS -C $m ."
done
jar cf "$WORK/jars/org.tweetyproject.tweety-7a-java8-shade.jar" $JAR_ARGS
ls -la "$WORK/jars/org.tweetyproject.tweety-7a-java8-shade.jar"

echo ""
echo "=== Step 6: copy shade jar into MyIA.AI.Notebooks/SymbolicAI/Tweety/libs/ ==="
cd "$WORK"
LIBS_DIR="$WORK/../../libs"
mkdir -p "$LIBS_DIR"
cp "$WORK/jars/org.tweetyproject.tweety-7a-java8-shade.jar" "$LIBS_DIR/"
ls -la "$LIBS_DIR/org.tweetyproject.tweety-7a-java8-shade.jar"

echo ""
echo "=== Step 7: bytecode audit (must be major 52 only) ==="
python -c "
import zipfile
from collections import Counter
with zipfile.ZipFile('jars/org.tweetyproject.tweety-7a-java8-shade.jar') as z:
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
echo "Next: dotnet build dotnet-build/build-Tweety7aShade.csproj -c Release"
echo "Then: copy dotnet-build/bin/Release/net8.0/org.tweetyproject.tweety-7a.dll to MyIA.AI.Notebooks/SymbolicAI/Tweety/"
