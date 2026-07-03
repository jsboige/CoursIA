#!/bin/bash
# Rebuild all 6 affected Tweety DLLs using the C190 recipe.
# Iterates over DL/CL/QBF/ML/MLN/RPCL shade POMs, applies shade + JvmDowngrader,
# then builds the corresponding csproj with IKVM 8.14.
#
# Pre-requisites:
#   - JAVA_HOME pointing to a JDK 17
#   - Maven 3.9.6 in /c/Users/jsboi/tools/maven/apache-maven-3.9.6/bin/mvn.cmd
#   - JvmDowngrader 1.3.6 in /tmp/jvmdowngrader.jar
#   - apply-c190-fix.sh already run on all 6 shade POMs
#
# Usage: rebuild-all-dlls.sh [module1 module2 ...]
#        (no args = all 6)

set -e

PROJ_ROOT="/c/dev/CoursIA-2-ikvm814/MyIA.AI.Notebooks/SymbolicAI/Tweety/dotnet-build"
JAVA_HOME="${JAVA_HOME:-C:/Users/jsboi/tools/jdk/zulu17.34.19-ca-jdk17.0.3-win_x64}"
MVN="/c/Users/jsboi/tools/maven/apache-maven-3.9.6/bin/mvn.cmd"
JVM_DOWNGRADER="${JVM_DOWNGRADER:-/tmp/jvmdowngrader.jar}"
JAVA="$JAVA_HOME/bin/java"
DOTNET="/c/Program Files/dotnet/dotnet.exe"

# Module configuration: <module-id>:<csproj>:<target-dll-name>
MODULES=(
    "advanced-logics:build-TweetyAdvancedLogicsShade.csproj:org.tweetyproject.tweety-advanced-logics.dll"
    "conditional-logics:build-TweetyConditionalLogicsShade.csproj:org.tweetyproject.tweety-conditional-logics.dll"
    "qbf:build-TweetyQbfShade.csproj:org.tweetyproject.tweety-qbf.dll"
    "ml:build-TweetyMlShade.csproj:org.tweetyproject.tweety-ml.dll"
    "mln:build-TweetyMlnShade.csproj:org.tweetyproject.tweety-mln.dll"
    "rpcl:build-TweetyRpclShade.csproj:org.tweetyproject.tweety-rpcl.dll"
)

cd "$PROJ_ROOT"

# Filter if args provided
REQUESTED="$@"
for entry in "${MODULES[@]}"; do
    IFS=':' read -r mid csproj dllname <<< "$entry"
    if [ -n "$REQUESTED" ] && ! echo " $REQUESTED " | grep -q " $mid "; then
        echo "[skip] $mid (not requested)"
        continue
    fi

    echo ""
    echo "===== Module: $mid ====="
    POM="build-tweety-${mid}-shade.pom.xml"
    JAR_NAME="tweety-${mid}-full-1.30.jar"

    if [ ! -f "$POM" ]; then
        echo "  [ERROR] $POM missing"
        continue
    fi

    echo "[1/3] Maven shade..."
    JAVA_HOME="$JAVA_HOME" "$MVN" -f "$POM" package -o -q 2>&1 | tail -3
    if [ ! -f "target/$JAR_NAME" ]; then
        echo "  [ERROR] JAR not built"
        continue
    fi
    echo "  -> target/$JAR_NAME ($(du -h target/$JAR_NAME | cut -f1))"

    echo "[2/3] JvmDowngrader (Java 15 -> Java 8)..."
    cp "target/$JAR_NAME" "target/$JAR_NAME.jdk15"
    "$JAVA" -jar "$JVM_DOWNGRADER" -c 52 downgrade \
        -t "target/$JAR_NAME.jdk15" \
        "target/$JAR_NAME" 2>&1 | grep -E "^ERROR" | head -3 || true

    echo "[3/3] dotnet build with IKVM 8.14..."
    cp "target/$JAR_NAME" .
    rm -rf bin obj
    "$DOTNET" build "$csproj" -c Release 2>&1 | grep -E "(error|Error|erreur|warning)" | tail -3 || true

    DLL="bin/Release/net8.0/$dllname"
    if [ -f "$DLL" ]; then
        echo "  -> $DLL ($(du -h "$DLL" | cut -f1))"
        echo "  -> copy to main repo DLL location"
        cp "$DLL" "/c/dev/CoursIA-2/MyIA.AI.Notebooks/SymbolicAI/Tweety/$dllname"
    else
        echo "  [ERROR] DLL not built"
    fi
done

echo ""
echo "===== DONE ====="