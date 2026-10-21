#!/bin/bash
# Rebuild the 4 Maven-chain "famille A" fat-jars (pl, aspic, beliefdynamics, dung) for IKVM 8.15
# (#19673, gap 1 de #19880 : preuve de rebuild complete de la chaine Maven documentee).
#
# Why: IKVM 8.15 implements Java SE 8 (bytecode ceiling major 52). TweetyProject v1.30
# releases on Maven Central are bytecode major 55/59, and the parent pom compiles
# source/target 15 -- unusable as-is. This script clones the v1.30 tag, patches the
# parent pom to <release>8</release> and the handful of Java 9-14 syntax/API uses down
# to Java 8 (same rewrites as rebuild-5shades.sh / rebuild-preferences.sh), installs the
# dependency closure into ~/.m2, then drives the 4 shade poms + csproj of this folder.
#
# Measured closure (13 reactor modules): commons, math, logics-commons, plugin,
# logics-fol, agents, logics-pl, graphs, arg-dung, arg-deductive, comparator,
# beliefdynamics, arg-aspic. All artifacts verified bytecode major 52.
#
# Outputs (gitignored): clone under .familyA-clone/, fat-jars tweety-*-full-1.30.jar in
# this folder, DLLs under bin/Release/net8.0/ of each csproj.
#
# NOTE: clear the IKVM MSBuild cache before rebuilding a csproj after any jar change:
#   rm -rf "$TMP/ikvm/cache/1/"
# (the cache is keyed on the jar hash and silently serves stale DLLs).
#
# Prereqs: JDK 17 (JAVA_HOME), Maven 3.9+ on PATH, .NET SDK 8.0+, git.

set -e
export JAVA_HOME="${JAVA_HOME:-/c/Users/jsboi/AppData/Local/Programs/Microsoft/jdk-17.0.10.7-hotspot}"
export PATH="$JAVA_HOME/bin:$PATH"
command -v mvn >/dev/null 2>&1 || { echo "mvn (Maven 3.9+) introuvable sur PATH"; exit 1; }

cd "$(dirname "$0")"
WORK=$(pwd)
CLONE="$WORK/.familyA-clone/TweetyProject-1.30"
REPO_URL="https://github.com/TweetyProjectTeam/TweetyProject.git"  # repo renomme (ancien TweetyProject/tweety : 404)

echo "=== Step 1: clone v1.30 (si absent) ==="
if [ ! -f "$CLONE/pom.xml" ]; then
  mkdir -p "$(dirname "$CLONE")"
  git clone --depth 1 --branch v1.30 "$REPO_URL" "$CLONE"
else
  echo "  clone deja present: $CLONE"
fi

echo ""
echo "=== Step 2: patchs Java 8 (parent pom + sources, idempotents) ==="
python - "$CLONE" <<'PYEOF'
import pathlib, re, shutil, os, sys
clone = pathlib.Path(sys.argv[1])
MARK = '[familyA-java8 patch]'
def rd(p): return p.read_text(encoding='utf-8')
def wr(p, s): p.write_text(s, encoding='utf-8')

def patched_if(p, cond, fn, label):
    f = clone / p
    if not f.exists():
        print(f'  ABSENT (deja patche ?): {label}'); return
    s = rd(f)
    if cond(s):
        s2 = fn(s)
        if s2 != s: wr(f, s2); print(f'  patched: {label}')
        else: print(f'  rien a faire: {label}')
    else:
        print(f'  deja: {label}')

# 2a. parent pom : compiler 2.3.2 (source/target 15) -> 3.13.0 + release 8
f = clone / 'pom.xml'
s = rd(f)
if '<release>8</release>' not in s:
    old = ('        <artifactId>maven-compiler-plugin</artifactId>\n'
           '        <version>2.3.2</version>\n'
           '        <configuration>\n'
           '          <source>15</source>\n'
           '          <target>15</target>\n'
           '        </configuration>')
    new = ('        <artifactId>maven-compiler-plugin</artifactId>\n'
           '        <version>3.13.0</version>\n'
           '        <configuration>\n'
           '          <release>8</release>\n'
           '        </configuration>')
    assert old in s, 'bloc compiler du pom parent introuvable (upstream a bouge ?)'
    wr(f, s.replace(old, new)); print('  patched: pom parent (release 8)')
else:
    print('  deja: pom parent')

# 2b. commons/Parser.java : Files.readString(Path.of) + isBlank
def patch_parser(s):
    if 'import java.nio.file.Paths;' not in s:
        s = s.replace('import java.nio.file.Files;',
                      'import java.nio.charset.StandardCharsets;\nimport java.nio.file.Files;')
        s = s.replace('import java.nio.file.Path;', 'import java.nio.file.Path;\nimport java.nio.file.Paths;')
    s = s.replace('Files.readString(Path.of(filename))',
                  'new String(Files.readAllBytes(Paths.get(filename)), StandardCharsets.UTF_8)  /* ' + MARK + ' */')
    s = s.replace('if (!kb_string.isBlank())', 'if (!kb_string.trim().isEmpty())  /* ' + MARK + ' */')
    return s
patched_if('org-tweetyproject-commons/src/main/java/org/tweetyproject/commons/Parser.java',
           lambda s: 'Files.readString(Path.of(filename))' in s or 'kb_string.isBlank()' in s,
           patch_parser, 'commons/Parser.java')

# 2c. commons/util/ExamplesHTMLGenerator.java : isBlank x2, strip x2
def patch_htmlgen(s):
    for old, new in [
        ('if (tweety_libraries_dir.isBlank())', 'if (tweety_libraries_dir.trim().isEmpty())'),
        ('doc = doc.substring(doc.indexOf("Copyright"), doc.indexOf("public class")).strip();',
         'doc = doc.substring(doc.indexOf("Copyright"), doc.indexOf("public class")).trim();'),
        ('String spl = doc.substring(doc.indexOf("/**") + 1).strip();',
         'String spl = doc.substring(doc.indexOf("/**") + 1).trim();'),
        ('if (!description.isBlank())', 'if (!description.trim().isEmpty())'),
    ]:
        s = s.replace(old, new)
    return s
patched_if('org-tweetyproject-commons/src/main/java/org/tweetyproject/commons/util/ExamplesHTMLGenerator.java',
           lambda s: '.isBlank()' in s or '.strip()' in s,
           patch_htmlgen, 'commons/ExamplesHTMLGenerator.java')

# 2d. graphs/util/AigGraphPlotter.java : readString/writeString + Matcher StringBuilder (Java 9)
def patch_aig(s):
    s = s.replace('String template = Files.readString(Paths.get(getResource("aiggraph/graph.template")));',
                  'String template = new String(Files.readAllBytes(Paths.get(getResource("aiggraph/graph.template"))), StandardCharsets.UTF_8);  // ' + MARK)
    s = s.replace('Files.writeString(outputPath, output);',
                  'Files.write(outputPath, output.getBytes(StandardCharsets.UTF_8));  // ' + MARK)
    s = s.replace('        StringBuilder result = new StringBuilder();',
                  '        StringBuffer result = new StringBuffer();  // ' + MARK + ' appendReplacement(StringBuilder) = Java 9+')
    if 'import java.nio.charset.StandardCharsets;' not in s:
        s = re.sub(r'(import java\.nio\.file\.Files;\n)', r'\1import java.nio.charset.StandardCharsets;\n', s, count=1)
    return s
patched_if('org-tweetyproject-graphs/src/main/java/org/tweetyproject/graphs/util/AigGraphPlotter.java',
           lambda s: 'Files.readString' in s or 'Files.writeString' in s or 'StringBuilder result = new StringBuilder();' in s,
           patch_aig, 'graphs/AigGraphPlotter.java')

# 2e. dung/reasoner/AbstractExtensionReasoner.java : switch fleche -> if-else (meme rewrite que c211)
def patch_aer(s):
    new_method = (
        '    public static AbstractExtensionReasoner getSimpleReasonerForSemantics(Semantics semantics){\n'
        '        // ' + MARK + ' Java 14 switch expression -> if-else chain pour javac --release 8\n'
        '        if (semantics == Semantics.CO) return new SimpleCompleteReasoner();\n'
        '        if (semantics == Semantics.GR) return new SimpleGroundedReasoner();\n'
        '        if (semantics == Semantics.PR) return new SimplePreferredReasoner();\n'
        '        if (semantics == Semantics.ST) return new SimpleStableReasoner();\n'
        '        if (semantics == Semantics.ADM) return new SimpleAdmissibleReasoner();\n'
        '        if (semantics == Semantics.CF) return new SimpleConflictFreeReasoner();\n'
        '        if (semantics == Semantics.SST) return new SimpleSemiStableReasoner();\n'
        '        if (semantics == Semantics.ID) return new SimpleIdealReasoner();\n'
        '        if (semantics == Semantics.EA) return new SimpleEagerReasoner();\n'
        '        if (semantics == Semantics.STG) return new SimpleStageReasoner();\n'
        '        if (semantics == Semantics.STG2) return new Stage2Reasoner();\n'
        '        if (semantics == Semantics.CF2) return new SccCF2Reasoner();\n'
        '        if (semantics == Semantics.SCF2) return new SCF2Reasoner();\n'
        '        if (semantics == Semantics.WAD) return new WeaklyAdmissibleReasoner();\n'
        '        if (semantics == Semantics.WCO) return new WeaklyCompleteReasoner();\n'
        '        if (semantics == Semantics.WPR) return new WeaklyPreferredReasoner();\n'
        '        if (semantics == Semantics.WGR) return new WeaklyGroundedReasoner();\n'
        '        if (semantics == Semantics.NA) return new SimpleNaiveReasoner();\n'
        '        if (semantics == Semantics.SAD) return new StronglyAdmissibleReasoner();\n'
        '        if (semantics == Semantics.UD) return new UndisputedReasoner();\n'
        '        if (semantics == Semantics.SUD) return new StronglyUndisputedReasoner();\n'
        '        if (semantics == Semantics.IS) return new SimpleInitialReasoner();\n'
        '        if (semantics == Semantics.UC) throw new IllegalArgumentException('
        '"UC semantics unsupported in this build (SerialisedExtensionReasoner excluded).");\n'
        '        throw new IllegalArgumentException("Unknown semantics.");\n'
        '    }')
    m = re.search(r'public static AbstractExtensionReasoner getSimpleReasonerForSemantics', s)
    assert m, 'anchor AbstractExtensionReasoner introuvable'
    i = s.find('{', m.end()); depth, j = 1, i + 1
    while j < len(s) and depth > 0:
        if s[j] == '{': depth += 1
        elif s[j] == '}': depth -= 1
        j += 1
    return s[:m.start()] + new_method + s[j:]
patched_if('org-tweetyproject-arg-dung/src/main/java/org/tweetyproject/arg/dung/reasoner/AbstractExtensionReasoner.java',
           lambda s: 'return switch (semantics)' in s,
           patch_aer, 'dung/AbstractExtensionReasoner.java')

# 2f. dung/reasoner/ExtensionRankingReasoner.java : switch fleche -> if-else
def patch_err(s):
    m = re.search(r'switch \(semantics\) \{', s)
    assert m, 'anchor ExtensionRankingReasoner introuvable'
    i = m.end(); depth, j = 1, i
    while j < len(s) and depth > 0:
        if s[j] == '{': depth += 1
        elif s[j] == '}': depth -= 1
        j += 1
    new_block = (
        '// ' + MARK + ' Java 14 switch expression -> if-else chain pour javac --release 8\n'
        '        if (semantics == ExtensionRankingSemantics.R_CF) {\n'
        '            methods.add(ExtensionRankingReasoner.class.getMethod("getConflicts", Extension.class, DungTheory.class));\n'
        '        } else if (semantics == ExtensionRankingSemantics.R_AD || semantics == ExtensionRankingSemantics.R_PR) {\n'
        '            methods.add(ExtensionRankingReasoner.class.getMethod("getConflicts", Extension.class, DungTheory.class));\n'
        '            methods.add(ExtensionRankingReasoner.class.getMethod("getUndefended", Extension.class, DungTheory.class));\n'
        '        } else if (semantics == ExtensionRankingSemantics.R_CO || semantics == ExtensionRankingSemantics.R_GR) {\n'
        '            methods.add(ExtensionRankingReasoner.class.getMethod("getConflicts", Extension.class, DungTheory.class));\n'
        '            methods.add(ExtensionRankingReasoner.class.getMethod("getUndefended", Extension.class, DungTheory.class));\n'
        '            methods.add(ExtensionRankingReasoner.class.getMethod("getDefendedNotIn", Extension.class, DungTheory.class));\n'
        '        } else if (semantics == ExtensionRankingSemantics.R_SST) {\n'
        '            methods.add(ExtensionRankingReasoner.class.getMethod("getConflicts", Extension.class, DungTheory.class));\n'
        '            methods.add(ExtensionRankingReasoner.class.getMethod("getUndefended", Extension.class, DungTheory.class));\n'
        '            methods.add(ExtensionRankingReasoner.class.getMethod("getDefendedNotIn", Extension.class, DungTheory.class));\n'
        '            methods.add(ExtensionRankingReasoner.class.getMethod("getUnattacked", Extension.class, DungTheory.class));\n'
        '        } else {\n'
        '            throw new IllegalArgumentException("Unknown semantics.");\n'
        '        }')
    return s[:m.start()] + new_block + s[j:]
patched_if('org-tweetyproject-arg-dung/src/main/java/org/tweetyproject/arg/dung/reasoner/ExtensionRankingReasoner.java',
           lambda s: re.search(r'case R_AD, R_PR ->', s) is not None,
           patch_err, 'dung/ExtensionRankingReasoner.java')

# 2g. var -> types explicites (DungTheory, EnumeratingDilationGenerator)
def patch_var_dungtheory(s):
    return s.replace('var tempArgsToRemove', 'HashSet<Argument> tempArgsToRemove')
patched_if('org-tweetyproject-arg-dung/src/main/java/org/tweetyproject/arg/dung/syntax/DungTheory.java',
           lambda s: 'var tempArgsToRemove' in s,
           patch_var_dungtheory, 'dung/DungTheory.java')

def patch_var_dilation(s):
    for old, new in [
        ('for(var arg : frameworkOriginal)', 'for(Argument arg : frameworkOriginal)'),
        ('for(var a : this.arguments)', 'for(Argument a : this.arguments)'),
        ('for(var b : this.arguments)', 'for(Argument b : this.arguments)'),
    ]:
        s = s.replace(old, new)
    return s
patched_if('org-tweetyproject-arg-dung/src/main/java/org/tweetyproject/arg/dung/util/EnumeratingDilationGenerator.java',
           lambda s: 'for(var ' in s,
           patch_var_dilation, 'dung/EnumeratingDilationGenerator.java')

# 2h. arg-deductive/util/RandomDeductiveKnowledgeBaseGenerator.java : switch rules -> switch classique
def patch_deductive_switch(s):
    old = ('            switch (random.nextInt(8)) {\n'
           '                case 0,1 -> kb.add(new Conjunction(f1, f2));\n'
           '                case 2,3 -> kb.add(new Disjunction(f1, f2));\n'
           '                case 4,5,6 -> kb.add(new Implication(f1, f2));\n'
           '                case 7 -> kb.add(new Equivalence(f1, f2));\n'
           '            }')
    new = ('            // ' + MARK + ' Java 14 switch rules -> switch classique pour javac --release 8\n'
           '            switch (random.nextInt(8)) {\n'
           '                case 0: case 1: kb.add(new Conjunction(f1, f2)); break;\n'
           '                case 2: case 3: kb.add(new Disjunction(f1, f2)); break;\n'
           '                case 4: case 5: case 6: kb.add(new Implication(f1, f2)); break;\n'
           '                case 7: kb.add(new Equivalence(f1, f2)); break;\n'
           '                default: break;\n'
           '            }')
    assert old in s, 'bloc switch deductive introuvable'
    return s.replace(old, new)
patched_if('org-tweetyproject-arg-deductive/src/main/java/org/tweetyproject/arg/deductive/util/RandomDeductiveKnowledgeBaseGenerator.java',
           lambda s: 'case 0,1 ->' in s,
           patch_deductive_switch, 'deductive/RandomDeductiveKnowledgeBaseGenerator.java')

# 2i. suppressions (meme strategie que DUNG_130_EXCLUDE de rebuild-5shades.sh + pl/beliefdynamics examples)
base = clone / 'org-tweetyproject-arg-dung/src/main/java/org/tweetyproject/arg/dung'
for sub in ['equivalence', 'learning', 'serialisability', 'examples', 'divisions', 'principles']:
    d = base / sub
    if d.is_dir(): shutil.rmtree(d); print(f'  rm -rf dung/{sub}/')
for f in ['reasoner/SerialisedExtensionReasoner.java', 'reasoner/FudgeAcceptabilityReasoner.java',
          'reasoner/AbstractSatExtensionReasoner.java', 'reasoner/SatCompleteReasoner.java',
          'reasoner/SatStableReasoner.java', 'reasoner/ProboI23Reasoner.java',
          'writer/TikzWriter.java', 'util/DungTheoryPlotter.java']:
    fp = base / f
    if fp.is_file(): fp.unlink(); print(f'  rm dung/{f}')
fp = clone / 'org-tweetyproject-logics-pl/src/main/java/org/tweetyproject/logics/pl/sat/CmdLineSatSolver.java'
if fp.is_file(): fp.unlink(); print('  rm logics-pl/CmdLineSatSolver.java')
d = clone / 'org-tweetyproject-logics-pl/src/main/java/org/tweetyproject/logics/pl/examples'
if d.is_dir(): shutil.rmtree(d); print('  rm -rf logics-pl/examples/')
d = clone / 'org-tweetyproject-beliefdynamics/src/main/java/org/tweetyproject/beliefdynamics/examples'
if d.is_dir(): shutil.rmtree(d); print('  rm -rf beliefdynamics/examples/')
print('PATCHES DONE')
PYEOF

echo ""
echo "=== Step 3: mvn install (closure 13 modules, bytecode major 52) ==="
(cd "$CLONE" && mvn -B install \
   -DskipTests -Dmaven.test.skip=true -Dgpg.skip=true \
   -Dmaven.javadoc.skip=true -Dmaven.source.skip=true \
   -pl org-tweetyproject-logics-pl,org-tweetyproject-arg-dung,org-tweetyproject-arg-aspic,org-tweetyproject-beliefdynamics \
   -am)
echo "  mvn install: OK"

echo ""
echo "=== Step 4: shade poms -> fat-jars ==="
for pom in build-tweety-pl-shade.pom.xml build-tweety-aspic-shade.pom.xml \
           build-tweety-beliefdynamics-shade.pom.xml build-tweety-dung-shade.pom.xml; do
  echo "  shade: $pom"
  mvn -B -f "$pom" clean package -Dgpg.skip=true -Dmaven.test.skip=true
  final=$(sed -n 's/.*<finalName>\([^<]*\)<\/finalName>.*/\1/p' "$pom" | head -1)
  jar="target/${final}.jar"
  cp "$jar" .
  echo "    -> $(basename "$jar")"
done

echo ""
echo "=== Step 5: dotnet build (DLL 8.15) ==="
rm -rf "$TMP/ikvm/cache/1/" 2>/dev/null || true
for cs in build-TweetyShade.csproj build-TweetyAspicShade.csproj \
          build-TweetyBeliefDynamicsShade.csproj build-TweetyDungShade.csproj; do
  echo "  dotnet build: $cs"
  dotnet build "$cs" -c Release
done

echo ""
echo "=== Step 6: bytecode audit des fat-jars (major <= 52) ==="
for j in tweety-pl-full-1.30.jar tweety-aspic-full-1.30.jar tweety-beliefdynamics-full-1.30.jar tweety-dung-full-1.30.jar; do
  [ -f "$j" ] || { echo "  MANQUANT: $j"; exit 1; }
  WIN_JAR="$(cygpath -w "$WORK/$j")"
  python -c "
import zipfile
from collections import Counter
with zipfile.ZipFile(r'$WIN_JAR') as z:
    classes = [n for n in z.namelist() if n.endswith('.class')]
    c = Counter()
    for n in classes:
        data = z.read(n)
        c[(data[6] << 8) | data[7]] += 1
    print(f'  $j: {len(classes)} classes, distribution: {dict(c)}')
    bad = {m for m in c if m > 52}
    assert not bad, f'FAIL: bytecode > 52 present: {dict(c)}'
"
done

echo ""
echo "=== DONE ==="
echo "DLLs: bin/Release/net8.0/org.tweetyproject.tweety-{pl,aspic,beliefdynamics,dung}.dll (a copier alongside the notebooks)"
