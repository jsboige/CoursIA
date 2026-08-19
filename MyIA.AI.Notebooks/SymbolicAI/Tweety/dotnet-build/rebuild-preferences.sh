#!/bin/bash
# Rebuild the Tweety preferences shade jar for IKVM 8.x compilation.
# Mirrors rebuild-5shades.sh (issue #10411) for a single module.
#
# Why: TweetyProject Maven jars are bytecode major 59 (Java 15), and the v1.30
# sources compiled whole-tree need javac --release 11 (commons uses Java 11
# APIs => major 55). Either way IKVM 8.x silently drops every class with
# IKVM0101 "class format error 55.0/59.0" -- the DLL builds "successfully"
# with zero org.tweetyproject.* types. IKVM 8.x implements Java SE 8: the
# ceiling is major 52.
#
# Strategy (proven by rebuild-5shades.sh): source-recompile the dep chain at
# javac --release 8 using the Java-8-clean 1.21 sources for math/commons,
# mixed with 1.30 sources for plugin/preferences (both verified Java-8-clean):
#
#   COMPILE_ORDER = math-1.21 -> commons-1.21 -> plugin-1.30 -> preferences-1.30
#
# Output (gitignored): jars/org.tweetyproject.tweety-preferences-java8-shade.jar
# Copied into ../libs/ (gitignored) as the <IkvmReference> of
# build-TweetyPreferencesShade.csproj ->
#   bin/Release/net8.0/org.tweetyproject.tweety-preferences.dll
#
# Verdict bytecode (Step 6): expected {52: N} only per shade.
#
# NOTE: clear the IKVM MSBuild cache before rebuilding the csproj after any
# jar change:  rm -rf "$TMP/ikvm/cache/1/"
# (the cache is keyed on the jar hash and silently serves stale DLLs).

set -e
export JAVA_HOME="${JAVA_HOME:-/c/Users/jsboi/AppData/Local/Programs/Microsoft/jdk-17.0.10.7-hotspot}"
export PATH="$JAVA_HOME/bin:$PATH"

cd "$(dirname "$0")"
WORK=$(pwd)

mkdir -p jars sources-extracted sources-jar classes
cd "$WORK"

echo "=== Step 1: download dep binary jars (math transitives, same set as rebuild-5shades.sh) ==="
_M2A="https://"
_M2B="repo1.maven.org/maven2"
M2="${_M2A}${_M2B}"
for url_pkg in \
  "${_M2A}${_M2B}/gov/nist/math/jama/1.0.3/jama-1.0.3.jar|jama-1.0.3.jar" \
  "${_M2A}${_M2B}/org/slf4j/slf4j-api/1.7.36/slf4j-api-1.7.36.jar|slf4j-api-1.7.36.jar" \
  "${_M2A}${_M2B}/org/apache/commons/commons-math/2.2/commons-math-2.2.jar|commons-math-2.2.jar" \
  "${_M2A}${_M2B}/org/apache/commons/commons-math3/3.6.1/commons-math3-3.6.1.jar|commons-math3-3.6.1.jar" \
  "${_M2A}${_M2B}/org/ojalgo/ojalgo/45.1.1/ojalgo-45.1.1.jar|ojalgo-45.1.1.jar" \
  "${_M2A}${_M2B}/org/sat4j/org.sat4j.core/2.3.1/org.sat4j.core-2.3.1.jar|org.sat4j.core-2.3.1.jar" \
  "${_M2A}${_M2B}/org/tweetyproject/commons/1.21/commons-1.21.jar|commons-1.21.jar" \
  "https://tweetyproject.org/mvn/jspf/core/1.0.2/core-1.0.2.jar|jspf-core-1.0.2.jar" \
  ; do
  url="${url_pkg%%|*}"
  out="${url_pkg##*|}"
  if [ ! -f "jars/$out" ]; then
    rc=$(curl -sL -o "jars/$out" -w "%{http_code}" "$url")
    [ "$rc" = "200" ] && echo "  got: $out" || { rm -f "jars/$out"; echo "  ERR: $out ($rc)"; exit 1; }
  fi
done

echo ""
echo "=== Step 2: download sources ==="
# math-1.21 sources (Central, Java-8-clean per rebuild-5shades.sh)
if [ ! -f "sources-jar/math-1.21-sources.jar" ]; then
  curl -sL -o "sources-jar/math-1.21-sources.jar" "$M2/org/tweetyproject/math/1.21/math-1.21-sources.jar"
  echo "  got: math-1.21-sources.jar"
fi
# plugin-1.30 + preferences-1.30 sources (Central; verified Java-8-clean)
if [ ! -f "sources-jar/plugin-1.30-sources.jar" ]; then
  curl -sL -o "sources-jar/plugin-1.30-sources.jar" "$M2/org/tweetyproject/plugin/1.30/plugin-1.30-sources.jar"
  echo "  got: plugin-1.30-sources.jar"
fi
if [ ! -f "sources-jar/preferences-1.30-sources.jar" ]; then
  curl -sL -o "sources-jar/preferences-1.30-sources.jar" "$M2/org/tweetyproject/preferences/1.30/preferences-1.30-sources.jar"
  echo "  got: preferences-1.30-sources.jar"
fi
# commons-1.21 sources: NOT on Maven Central (binary only) -- pull from GitHub tag
if [ ! -f "sources-jar/commons-1.21-sources.jar" ]; then
  TARBALL="/tmp/tweety-1.21-commons.tar.gz"
  TMPDIR=$(mktemp -d)
  if [ ! -f "$TARBALL" ]; then
    curl -sL "https://github.com/TweetyProjectTeam/TweetyProject/archive/refs/tags/v1.21.tar.gz" -o "$TARBALL"
  fi
  cd "$TMPDIR"
  tar -xzf "$TARBALL" "TweetyProject-1.21/org-tweetyproject-commons/src/main/java/"
  cd "TweetyProject-1.21/org-tweetyproject-commons/src/main/java"
  jar cf "$WORK/sources-jar/commons-1.21-sources.jar" .
  cd "$WORK"
  rm -rf "$TMPDIR"
  echo "  got: commons-1.21-sources.jar (from GitHub v1.21.tar.gz)"
fi

echo ""
echo "=== Step 3: extract sources ==="
for entry in "math:1.21" "commons:1.21" "plugin:1.30" "preferences:1.30"; do
  m="${entry%%:*}"; v="${entry##*:}"
  rm -rf "sources-extracted/$m-$v"
  mkdir -p "sources-extracted/$m-$v"
  (cd "sources-extracted/$m-$v" && unzip -q "$WORK/sources-jar/${m}-${v}-sources.jar")
  echo "  extracted: $m-$v"
done

# Same math exclusions as rebuild-5shades.sh: AntColony/Gurobi/OjAlgoUtils
# reference commercial/niche libs; math/examples/* likewise.
MATH_EXCLUDE=(
  "org/tweetyproject/math/opt/solver/AntColonyOptimization.java"
  "org/tweetyproject/math/opt/solver/GurobiOptimizer.java"
  "org/tweetyproject/math/util/OjAlgoMathUtils.java"
  "org/tweetyproject/math/examples/"
)

# commons-1.21 exclusions: examples/* needs junit.jupiter (test-only).
COMMONS_EXCLUDE=(
  "org/tweetyproject/commons/examples/"
)

echo ""
echo "=== Step 3.5: patch commons-1.21 sources for javac --release 8 ==="
# The v1.21 GitHub tarball (tag since re-pointed upstream) carries Java 11
# calls in two files. Idempotent rewrites, semantics-preserving:
#   Files.readString(Path.of(f)) -> new String(Files.readAllBytes(Paths.get(f)), UTF_8)
#   s.isBlank()                  -> s.trim().isEmpty()
#   s.strip()                    -> s.trim()
PATCHED="sources-extracted/commons-1.21/org/tweetyproject/commons/Parser.java"
python - "$PATCHED" <<'PYEOF'
import sys, pathlib
p = pathlib.Path(sys.argv[1])
src = p.read_text(encoding='utf-8')
if '[prefs-java8 patch]' not in src:
    src = src.replace(
        'import java.nio.file.Files;\nimport java.nio.file.Path;\n',
        'import java.nio.charset.StandardCharsets;\nimport java.nio.file.Files;\nimport java.nio.file.Path;\nimport java.nio.file.Paths;\n')
    src = src.replace('Files.readString(Path.of(filename))',
                      'new String(Files.readAllBytes(Paths.get(filename)), StandardCharsets.UTF_8)  /* [prefs-java8 patch] */')
    src = src.replace('kb_string.isBlank()', 'kb_string.trim().isEmpty()  /* [prefs-java8 patch] */')
    p.write_text(src, encoding='utf-8')
    print('  patched: Parser.java')
else:
    print('  Parser.java already patched')
PYEOF
PATCHED2="sources-extracted/commons-1.21/org/tweetyproject/commons/util/ExamplesHTMLGenerator.java"
python - "$PATCHED2" <<'PYEOF'
import sys, pathlib
p = pathlib.Path(sys.argv[1])
src = p.read_text(encoding='utf-8')
if '[prefs-java8 patch]' not in src:
    src = src.replace('tweety_libraries_dir.isBlank()', 'tweety_libraries_dir.trim().isEmpty()  /* [prefs-java8 patch] */')
    src = src.replace('doc.substring(doc.indexOf("Copyright"), doc.indexOf("public class")).strip()',
                      'doc.substring(doc.indexOf("Copyright"), doc.indexOf("public class")).trim()  /* [prefs-java8 patch] */')
    src = src.replace('doc.substring(doc.indexOf("/**") + 1).strip()',
                      'doc.substring(doc.indexOf("/**") + 1).trim()  /* [prefs-java8 patch] */')
    src = src.replace('description.isBlank()', 'description.trim().isEmpty()  /* [prefs-java8 patch] */')
    p.write_text(src, encoding='utf-8')
    print('  patched: ExamplesHTMLGenerator.java')
else:
    print('  ExamplesHTMLGenerator.java already patched')
PYEOF

echo ""
echo "=== Step 4: compile chain (javac --release 8) ==="
COMPILE_ORDER=("math:1.21" "commons:1.21" "plugin:1.30" "preferences:1.30")
for entry in "${COMPILE_ORDER[@]}"; do
  m="${entry%%:*}"; v="${entry##*:}"
  echo "  compiling: $m v$v"
  rm -rf "classes/$m-$v"
  mkdir -p "classes/$m-$v"
  files=$(find "sources-extracted/$m-$v" -name "*.java")
  if [ "$m" = "math" ]; then
    for ex in "${MATH_EXCLUDE[@]}"; do
      files=$(echo "$files" | grep -v "$ex" || true)
    done
  fi
  if [ "$m" = "commons" ]; then
    for ex in "${COMMONS_EXCLUDE[@]}"; do
      files=$(echo "$files" | grep -v "$ex" || true)
    done
  fi
  # Classpath: math transitive deps + commons binary jar (for math compilation,
  # same as rebuild-5shades.sh) + jspf (plugin framework, from TweetyProject mvn
  # repo) + previously compiled module classes.
  CP=""
  for j in jama-1.0.3 slf4j-api-1.7.36 commons-math-2.2 commons-math3-3.6.1 ojalgo-45.1.1 org.sat4j.core-2.3.1 commons-1.21 jspf-core-1.0.2; do
    CP="$CP;jars/$j.jar"
  done
  for prev in "${COMPILE_ORDER[@]}"; do
    if [ "$prev" = "$entry" ]; then break; fi
    CP="$CP;classes/${prev%%:*}-${prev##*:}"
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
echo "=== Step 5: build shade jar ==="
# commons-1.21 sources embed a logics.commons subset (Maven artifact quirk);
# not needed by preferences -- drop it to keep the jar minimal and duplicate-free.
if [ -d "classes/commons-1.21/org/tweetyproject/logics/commons" ]; then
  rm -rf "classes/commons-1.21/org/tweetyproject/logics/commons"
fi
# Unpack jspf (plugin framework, bytecode major 50 = IKVM-clean) into the shade:
# preferences/plugin classes implement net.xeoh.plugins.base.* interfaces --
# without them IKVM0100 drops PreferencesPlugin from the DLL (43 instead of 44
# exposed types).
rm -rf classes/jspf-1.0.2
mkdir -p classes/jspf-1.0.2
(cd classes/jspf-1.0.2 && unzip -q "$WORK/jars/jspf-core-1.0.2.jar" && rm -rf META-INF)
cd "$WORK/classes"
JAR_ARGS=""
for entry in "${COMPILE_ORDER[@]}" "jspf:1.0.2"; do
  JAR_ARGS="$JAR_ARGS -C ${entry%%:*}-${entry##*:} ."
done
OUT_JAR="$WORK/jars/org.tweetyproject.tweety-preferences-java8-shade.jar"
jar cf "$OUT_JAR" $JAR_ARGS
cd "$WORK"
ls -la "$OUT_JAR"

echo ""
echo "=== Step 6: copy shade jar into ../libs/ ==="
LIBS_DIR="$WORK/../libs"
mkdir -p "$LIBS_DIR"
cp "$OUT_JAR" "$LIBS_DIR/"
ls -la "$LIBS_DIR/org.tweetyproject.tweety-preferences-java8-shade.jar"

echo ""
echo "=== Step 7: bytecode audit (must be major 52 only) ==="
WIN_OUT_JAR="$(cygpath -w "$OUT_JAR")"
python -c "
import zipfile
from collections import Counter
with zipfile.ZipFile(r'$WIN_OUT_JAR') as z:
    classes = [n for n in z.namelist() if n.endswith('.class')]
    c = Counter()
    for n in classes:
        data = z.read(n)
        major = (data[6] << 8) | data[7]
        c[major] += 1
    print(f'  Total: {len(classes)}, Distribution: {dict(c)}')
    bad = {m for m in c if m > 52}
    assert not bad, f'FAIL: bytecode above the IKVM Java-8 ceiling (52) present: {dict(c)}'
    print('  OK: all bytecode major <= 52 (IKVM Java-8 ceiling; jspf ships major 50)')
"
