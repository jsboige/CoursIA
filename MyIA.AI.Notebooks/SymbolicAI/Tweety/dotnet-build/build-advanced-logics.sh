#!/bin/bash
# C190 build recipe for Tweety advanced-logics shade JAR.
# Three steps:
#   1. Maven shade with isula/lang3/gurobi exclusions
#   2. JvmDowngrader (Java 15 bytecode -> Java 8 bytecode)
#   3. dotnet build with IKVM 8.14
#
# Pre-requisites:
#   - JAVA_HOME pointing to a JDK 17 (used by Maven)
#   - Maven 3.9.6 in /c/Users/jsboi/tools/maven/apache-maven-3.9.6/bin/mvn.cmd
#   - JvmDowngrader 1.3.6 all-in-one JAR in /tmp/jvmdowngrader.jar
#
# Usage: build-advanced-logics.sh
#
# Output:
#   - target/tweety-advanced-logics-full-1.30.jar (downgraded JAR)
#   - bin/Release/net8.0/org.tweetyproject.tweety-advanced-logics.dll (~6 MB)

set -e

PROJ_ROOT="/c/dev/CoursIA-2-ikvm814/MyIA.AI.Notebooks/SymbolicAI/Tweety/dotnet-build"
JAVA_HOME="${JAVA_HOME:-C:/Users/jsboi/tools/jdk/zulu17.34.19-ca-jdk17.0.3-win_x64}"
MVN="/c/Users/jsboi/tools/maven/apache-maven-3.9.6/bin/mvn.cmd"
JVM_DOWNGRADER="${JVM_DOWNGRADER:-/tmp/jvmdowngrader.jar}"
JAVA="$JAVA_HOME/bin/java"

cd "$PROJ_ROOT"

echo "[1/3] Maven shade (excluding isula, commons-lang3, gurobi)..."
JAVA_HOME="$JAVA_HOME" "$MVN" -f build-tweety-advanced-logics-shade.pom.xml package -o -q
echo "  -> target/tweety-advanced-logics-full-1.30.jar ($(du -h target/tweety-advanced-logics-full-1.30.jar | cut -f1))"

echo "[2/3] JvmDowngrader (Java 15 -> Java 8 bytecode)..."
cp target/tweety-advanced-logics-full-1.30.jar target/tweety-advanced-logics-full-1.30-jdk15.jar
"$JAVA" -jar "$JVM_DOWNGRADER" -c 52 downgrade \
    -t target/tweety-advanced-logics-full-1.30-jdk15.jar \
    target/tweety-advanced-logics-full-1.30.jar 2>&1 | grep -E "^ERROR" | head -5 || true
echo "  -> target/tweety-advanced-logics-full-1.30.jar (downgraded)"

echo "[3/3] dotnet build with IKVM 8.14..."
cp target/tweety-advanced-logics-full-1.30.jar .
"/c/Program Files/dotnet/dotnet.exe" build build-TweetyAdvancedLogicsShade.csproj -c Release 2>&1 | tail -3

DLL="bin/Release/net8.0/org.tweetyproject.tweety-advanced-logics.dll"
echo "Done. DLL: $PROJ_ROOT/$DLL ($(du -h "$DLL" | cut -f1))"