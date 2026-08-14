#!/usr/bin/env bash
# ============================================================================
# rebuild-7a.sh — recette de build du shade `org.tweetyproject.tweety-7a`
# ============================================================================
# Issue #10450 (trou de reproductibilite Tweety-7a, design-gate ai-01
# 2026-08-14) : la DLL `org.tweetyproject.tweety-7a.dll` est committe a la
# racine de Tweety/ (pattern #4711). Ce script reproduit le fat-jar Java 8
# depuis les sources Maven Central, puis la DLL .NET via IKVM.
#
# Verifications firsthand (po-2023, cycle c.257, 2026-08-14) :
#   - Les 8 binaires Maven des modules du shade sont TOUS en bytecode
#     major 56/59 (Java 11/15) -> AUCUN utilisable tel quel par IKVM 8.x
#     (plafond major 52) -> recompilation complete des sources en
#     `javac --release 8` (pattern c.211 / rebuild-5shades.sh).
#   - Le jar authentique contient {52: 479} classes (audit zipfile).
#   - commons 1.19 : seuls 2 fichiers utilisent des API Java 11
#     (Parser.java + util/ExamplesHTMLGenerator.java : readString/Path.of/
#     isBlank/strip) -> patches Java 8 cibles (Step 3).
#   - dung 1.21 : import mort org.ojalgo.matrix.store.SuperimposedStore dans
#     ClaimBasedTheory.java a retirer (patch 5shades).
#   - Exclusions calibrees par diff binaire-vs-shade (Step 4) : dung 19,
#     social 1, weighted 2, graphs 5, commons 0, adf 113, math examples/.
#
# Pre-requis : JDK 17 (javac --release 8), .NET SDK 8+, bash + curl + python3.
# Usage : bash dotnet-build/rebuild-7a.sh [/tmp/tweety7a-work]
# ============================================================================
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"   # .../MyIA.AI.Notebooks/SymbolicAI/Tweety
WORK_DIR="${1:-/tmp/tweety7a-work}"
LIBS_DIR="$REPO_ROOT/libs"                                     # gitignored, jars intermediaires
OUT_JAR="org.tweetyproject.tweety-7a-java8-shade.jar"

_M2A="https://"
_M2B="repo1.maven.org/maven2"
GH_TARBALL="${_M2A}github.com/TweetyProject/TweetyProject/archive/refs/tags/v1.19.tar.gz"

mkdir -p "$WORK_DIR"/{bin,src,deps,logics,classes} "$LIBS_DIR"
cd "$WORK_DIR"

# --- Artefacts Maven (binaires + sources), chemins canoniques Maven Central --
declare -A BIN=(
  [adf]="org/tweetyproject/adf/1.21/adf-1.21.jar"
  [commons]="org/tweetyproject/commons/1.19/commons-1.19.jar"
  [dung]="org/tweetyproject/dung/1.21/dung-1.21.jar"
  [graphs]="org/tweetyproject/graphs/1.21/graphs-1.21.jar"
  [math-1.19]="org/tweetyproject/math/1.19/math-1.19.jar"
  [math-1.27]="org/tweetyproject/math/1.27/math-1.27.jar"
  [social]="org/tweetyproject/social/1.21/social-1.21.jar"
  [weighted]="org/tweetyproject/weighted/1.26/weighted-1.26.jar"
)
declare -A SRC=(
  [adf]="org/tweetyproject/adf/1.21/adf-1.21-sources.jar"
  [dung]="org/tweetyproject/dung/1.21/dung-1.21-sources.jar"
  [graphs]="org/tweetyproject/graphs/1.21/graphs-1.21-sources.jar"
  [math-1.19]="org/tweetyproject/math/1.19/math-1.19-sources.jar"
  [math-1.27]="org/tweetyproject/math/1.27/math-1.27-sources.jar"
  [social]="org/tweetyproject/social/1.21/social-1.21-sources.jar"
  [weighted]="org/tweetyproject/weighted/1.26/weighted-1.26-sources.jar"
)

# --- Deps externes (classpath compile-only, PAS incluses dans le shade) -----
declare -A DEPS=(
  [jama]="gov/nist/math/jama/1.0.3/jama-1.0.3.jar"
  [slf4j-api]="org/slf4j/slf4j-api/1.7.36/slf4j-api-1.7.36.jar"
  [commons-math]="org/apache/commons/commons-math/2.2/commons-math-2.2.jar"
  [commons-math3]="org/apache/commons/commons-math3/3.6.1/commons-math3-3.6.1.jar"
  [ojalgo]="org/ojalgo/ojalgo/45.1.1/ojalgo-45.1.1.jar"
  [org.sat4j.core]="org/ow2/sat4j/org.sat4j.core/2.3.1/org.sat4j.core-2.3.1.jar"
)

# logics 1.27 : compile-only (weighted 1.26 depend de logics 1.26 absents de
# Maven Central -> CP binaire a 1.27, classes jamais inclues dans le shade)
LOGICS="org/tweetyproject/logics.commons/1.27/logics.commons-1.27.jar org/tweetyproject/logics.pl/1.27/logics.pl-1.27.jar"

# --- Exclusions compile par module (classes absentes du shade authentique) --
# Calibrage : diff binaire-vs-shade (jar authentique c.208, audit zipfile).
# Adf 113 : examples/ + reasoner/sat/** + reasoner/query/** + heuristics/
# DegreeComparator + sat/solver/** + sat/state/** + semantics/interpretation/
# Interpretations* + syntax/pl/** + syntax/acc/BinaryAcceptanceCondition.
declare -A EXCL=(
  [commons]='$^'
  [math-1.19]='examples/|opt/solver/OjAlgoMathUtils'
  [math-1.27]='examples/|opt/solver/OjAlgoMathUtils'
  [graphs]='examples/|GraphPlotter|GraphUtil'
  [dung]='examples/|IsoSafeEnumeratingDungTheoryGenerator'
  [social]='examples/'
  [weighted]='examples/'
  [adf]='examples/|reasoner/sat/|reasoner/query/|heuristics/DegreeComparator|sat/solver/|sat/state/|semantics/interpretation/Interpretations|syntax/pl/|syntax/acc/BinaryAcceptanceCondition'
)

COMPILE_ORDER=(commons math-1.19 math-1.27 graphs dung social weighted adf)

# --- Utilitaire : telechargement avec cache + rapport HTTP -------------------
fetch() { # $1=dest_rel  $2=url
  local dest="$WORK_DIR/$1" url="$2"
  if [ -f "$dest" ]; then echo "  cached: $1"; return 0; fi
  local rc
  rc=$(curl -sL -o "$dest" -w "%{http_code}" "$url")
  if [ "$rc" = "200" ]; then echo "  got: $1"; else rm -f "$dest"; echo "  SKIP (HTTP $rc): $url"; return 1; fi
}

# ============================================================================
echo "=== Step 1: binaires Maven des modules (verification bytecode) ==="
for m in "${!BIN[@]}"; do
  fetch "bin/$m.jar" "${_M2A}${_M2B}/${BIN[$m]}"
done

echo "=== Step 2: sources jars + tarball commons ==="
for m in "${!SRC[@]}"; do
  fetch "src/$m-sources.jar" "${_M2A}${_M2B}/${SRC[$m]}"
done
fetch "src/TweetyProject-1.19.tar.gz" "$GH_TARBALL"

echo "=== Step 3: extraction + patches Java 8 ==="
for m in "${!SRC[@]}"; do
  if [ -d "src/$m" ]; then echo "  extracted: src/$m"; else
    (cd src && unzip -q -o "$m-sources.jar" -d "$m")
    echo "  extracted: src/$m"
  fi
done
if [ ! -d "src/commons" ]; then
  tar -xzf src/TweetyProject-1.19.tar.gz -C src
  ln -sfn TweetyProject-1.19/org-tweetyproject-commons/src/main/java src/commons
  echo "  extracted: src/commons (tarball v1.19)"
fi
COMMONS_SRC="src/commons"

# commons 1.19 -> Java 8 : readString/Path.of/isBlank/strip (API 11)
# 2 fichiers seulement (verifie par grep firsthand) :
#   Parser.java                : Files.readString(Path.of(x)) x2, isBlank x2
#   util/ExamplesHTMLGenerator.java : isBlank x2, strip x2
if ! grep -q "readAllBytes" "$COMMONS_SRC/org/tweetyproject/commons/Parser.java"; then
  sed -i 's/Files\.readString(Path\.of(filename))/new String(Files.readAllBytes(Paths.get(filename)))/g' \
    "$COMMONS_SRC/org/tweetyproject/commons/Parser.java"
  sed -i '/^import java\.nio\.file\.Path;$/a import java.nio.file.Paths;' \
    "$COMMONS_SRC/org/tweetyproject/commons/Parser.java"
  echo "  patch: Parser.java readString/Path.of -> readAllBytes/Paths.get"
fi
sed -i 's/\.isBlank()/.trim().isEmpty()/g' \
  "$COMMONS_SRC/org/tweetyproject/commons/Parser.java" \
  "$COMMONS_SRC/org/tweetyproject/commons/util/ExamplesHTMLGenerator.java"
sed -i 's/\.strip()/.trim()/g' \
  "$COMMONS_SRC/org/tweetyproject/commons/util/ExamplesHTMLGenerator.java"
echo "  patch: commons isBlank/strip -> trim().isEmpty()/trim()"

# dung 1.21 : import mort ojalgo (patch 5shades, loop 1.21/1.30)
DUNG_SRC="src/dung/org/tweetyproject/arg/dung"
if grep -q "ojalgo" "$DUNG_SRC/parser/ClaimBasedTheory.java" 2>/dev/null; then
  sed -i '/^import org\.ojalgo\.matrix\.store\.SuperimposedStore;$/d' \
    "$DUNG_SRC/parser/ClaimBasedTheory.java"
  echo "  patch: dung ClaimBasedTheory.java import ojalgo retire"
fi

# ============================================================================
echo "=== Step 4: compilation javac --release 8 (ordre de dependance) ==="
CP="$WORK_DIR/logics/$(basename "$LOGICS")"
# CP initial : deps externes + logics
for dep in "${!DEPS[@]}"; do
  fetch "deps/$dep.jar" "${_M2A}${_M2B}/${DEPS[$dep]}"
done
CP=""
for dep in "${!DEPS[@]}"; do CP="$CP:$WORK_DIR/deps/$dep.jar"; done
CP="$CP:$WORK_DIR/logics/$(basename "$LOGICS")"
for lg in $LOGICS; do
  fetch "logics/$(basename "$lg")" "${_M2A}${_M2B}/$lg"
done
CP="$CP:$WORK_DIR/logics"

for m in "${COMPILE_ORDER[@]}"; do
  SRC_DIR="src/$m"
  [ "$m" = "commons" ] && SRC_DIR="$COMMONS_SRC"
  [ -d "$SRC_DIR" ] || { echo "  SKIP $m (sources absentes)"; continue; }
  mapfile -t files < <(find "$SRC_DIR" -name '*.java' | grep -vE "${EXCL[$m]}")
  [ ${#files[@]} -eq 0 ] && { echo "  SKIP $m (0 fichier apres exclusions)"; continue; }
  echo "  compile $m : ${#files[@]} fichiers"
  mkdir -p "classes/$m"
  javac --release 8 -encoding UTF-8 -nowarn -cp "${CP#:}" -d "classes/$m" "${files[@]}"
  CP="$CP:classes/$m"
done

# ============================================================================
echo "=== Step 5: shade (jar cf consolide, derniere version gagnante) ==="
rm -rf shade && mkdir -p shade
for m in "${COMPILE_ORDER[@]}"; do
  [ -d "classes/$m" ] && cp -r "classes/$m"/. shade/
done
jar cf "$LIBS_DIR/$OUT_JAR" -C shade .

# ============================================================================
echo "=== Step 6: copie + audit bytecode (attendu {52: 479}) ==="
PY=$(command -v python3 || command -v python)
"$PY" - "$LIBS_DIR/$OUT_JAR" <<'PY'
import sys, zipfile, collections
jar = sys.argv[1]
c = collections.Counter()
with zipfile.ZipFile(jar) as z:
    for n in z.namelist():
        if n.endswith('.class') and not n.startswith('META-INF'):
            b = z.read(n)
            c[b[6]] += 1
obs = dict(c)
print('bytecode major -> count :', obs)
if obs == {52: 479}:
    print('OK: {52: 479} reproduit')
else:
    print('WARN: compte attendu {52: 479}, observe', obs)
    print('WARN: verifier les exclusions Step 4 (diff binaire-vs-shade)')
PY

# ============================================================================
echo "=== Step 7: pipeline DLL IKVM (.NET) ==="
cd "$REPO_ROOT/dotnet-build"
dotnet build build-Tweety7aShade.csproj -c Release
cp "bin/Release/net8.0/org.tweetyproject.tweety-7a.dll" "$REPO_ROOT/"
echo "DLL -> $REPO_ROOT/org.tweetyproject.tweety-7a.dll"
sha1sum "$REPO_ROOT/org.tweetyproject.tweety-7a.dll"

echo "=== DONE: shade + DLL regeneres ==="
