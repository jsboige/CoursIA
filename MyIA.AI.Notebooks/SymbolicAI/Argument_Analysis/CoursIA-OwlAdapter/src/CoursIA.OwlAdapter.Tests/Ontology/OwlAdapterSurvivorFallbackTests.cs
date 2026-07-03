// Copyright (c) 2026 CoursIA — port verbatim from Argumentum under LGPL-3.0 + AGPL-3.0
// See NOTICE in this directory for full attribution.
//
// Verbatim port of OwlAdapterSurvivorFallbackTests.cs from
// Argumentum.AssetConverter.Tests.Ontology (commit ac33f607).
// Modifications disclosed: namespace change only.

using System.Linq;
using CoursIA.SymbolicAI.Argument_Analysis.AssetConverter.Ontology;
using FluentAssertions;
using OWLSharp.Ontology;
using RDFSharp.Model;
using Xunit;

namespace CoursIA.SymbolicAI.Argument_Analysis.AssetConverter.Tests.Ontology
{
    /// <summary>
    /// Unit-isolation regression suite for the OWL2XML round-trip SURVIVOR fallback in
    /// <see cref="OwlAdapter"/> — dispatch #204 primaire (durcit #133 / #489), cont. po-2024.
    ///
    /// The #489 read-path fix (pinned end-to-end on the real 5 MB ontology by
    /// <see cref="OwlE2EGenerationValidationTests"/>) made the production validators stop
    /// silent-false-passing: OWLSharp's OWL2XML serializer drops <c>rdf:type</c> from the reloaded
    /// annotation stream, so <see cref="OwlAdapter.GetResourcesByType"/> /
    /// <see cref="OwlAdapter.GetConcepts"/> — which locate entities by scanning for <c>rdf:type</c> —
    /// returned empty on any LOADED file. The fix adds a SURVIVOR fallback: when the type scan is
    /// empty, resolve <c>skos:Concept</c> as the distinct subjects of <c>skos:prefLabel</c> and
    /// <c>skos:ConceptScheme</c> as the subject of <c>skos:hasTopConcept</c> (both survive the
    /// round-trip). <see cref="OwlAdapter.GetExactMatchConcepts"/> and its match-family siblings carry
    /// the same survivor shape (SKOSHelper-then-annotation-scan) for the AIF mappings.
    ///
    /// WHAT THIS FILE ADDS that the e2e suite cannot pin:
    /// <list type="bullet">
    /// <item>The survivor fallback BRANCH (<c>OwlAdapter.cs</c> lines ~424-441) is never reached by
    /// <see cref="OwlAdapterRegressionTests"/> — those build ontologies WITH <c>rdf:type</c> (via
    /// <c>DeclareConcept</c>), so <c>GetResourcesByType</c> always early-returns on the type scan.
    /// The fallback code was unit-uncovered before this file.</item>
    /// <item>The e2e asserts coarse counts (<c>&gt;1000</c>) on the real file because TextEn URI
    /// collisions aggregate subjects unpredictably. Here a synthetic ontology pins the EXACT dedup
    /// contract (3 concepts × fr+en prefLabel = 6 assertions → exactly 3 distinct subjects).</item>
    /// <item>The e2e cannot prove the fallback is SECONDARY — on the real file <c>rdf:type</c> is
    /// entirely absent, so the type-scan path is never the governing one. Here a mixed ontology
    /// (one concept WITH <c>rdf:type</c>, one with ONLY <c>prefLabel</c>) proves the type scan
    /// governs when present and the fallback is skipped — i.e. the fix did not change in-memory
    /// semantics where <c>rdf:type</c> survives.</item>
    /// <item>Unknown-type isolation and ConceptScheme-via-hasTopConcept-subject-exactness are
    /// uncovered by the e2e (which only queries Concept and ConceptScheme, and only coarsely).</item>
    /// </list>
    ///
    /// TECHNIQUE: a survivor-only ontology is built in-memory WITHOUT <c>DeclareConcept</c> /
    /// <c>DeclareConceptScheme</c> (which emit <c>rdf:type</c>) — only the literal/resource
    /// annotations that survive the round-trip are added (<c>AnnotateConceptPreferredLabel</c>,
    /// <c>AnnotateConceptWithResource</c>). This reproduces the post-reload annotation graph without
    /// loading a 5 MB file, so the tests are fast and deterministic.
    /// Additive only: no production code or existing test is modified.
    /// </summary>
    public class OwlAdapterSurvivorFallbackTests
    {
        private const string Ns = "http://argumentum.test/survivor#";

        private static OwlAdapter NewAdapter() => new OwlAdapter(Ns);

        private static RDFResource Res(string local) => new RDFResource(Ns + local);

        private static RDFPlainLiteral Lit(string value) => new RDFPlainLiteral(value);

        // ─────────────────────────────────────────────────────────────────────────────
        // (1) THE HEADLINE — Concept survivor fallback + dedup. A survivor-only ontology (no
        //     rdf:type) with 3 concepts × fr+en prefLabel = 6 assertions. GetResourcesByType(Concept)
        //     must resolve exactly the 3 distinct concept subjects via the prefLabel fallback. The
        //     6→3 delta is the GetAnnotationSubjectsByProperty .Distinct() contract — a regression
        //     that dropped the dedup would return 6, and a regression that disabled the fallback
        //     would return 0.
        // ─────────────────────────────────────────────────────────────────────────────

        [Fact]
        public void Concept_ResolvedViaPrefLabelSubjects_WhenRdfTypeAbsent_Deduped()
        {
            var adapter = NewAdapter();
            // Survivor-only: prefLabel added directly, NO DeclareConcept (so no rdf:type).
            for (int i = 1; i <= 3; i++)
            {
                var concept = Res($"C{i}");
                adapter.AnnotateConceptPreferredLabel(concept, Lit($"Concept {i} (fr)"));
                adapter.AnnotateConceptPreferredLabel(concept, Lit($"Concept {i} (en)"));
            }

            // Precondition: the type scan genuinely has nothing to find (rdf:type absent) — this is
            // what makes the survivor fallback the governing path, exactly like a reloaded ontology.
            int rdfTypeConcepts = adapter.GetOntology().AnnotationAxioms.OfType<OWLAnnotationAssertion>()
                .Count(a => a.AnnotationProperty.GetIRI().ToString() == RDFVocabulary.RDF.TYPE.ToString()
                         && a.ValueIRI?.ToString() == SKOSVocabulary.Concept.ToString());
            rdfTypeConcepts.Should().Be(0,
                "precondition: no rdf:type=skos:Concept in a survivor-only ontology (mimics the OWL2XML drop); " +
                "without this the fallback is unreachable and the test would not exercise the fix");

            // 6 prefLabel assertions exist (3 concepts × fr+en)...
            int prefLabelAssertions = adapter.GetOntology().AnnotationAxioms.OfType<OWLAnnotationAssertion>()
                .Count(a => a.AnnotationProperty.GetIRI().ToString() == SKOSVocabulary.PrefLabel.ToString());
            prefLabelAssertions.Should().Be(6,
                "3 concepts × fr+en prefLabel = 6 raw assertions — the input to the dedup");

            // ...but the reader resolves exactly 3 DISTINCT concept subjects (the dedup contract).
            var concepts = adapter.GetResourcesByType(SKOSVocabulary.Concept);
            concepts.Should().HaveCount(3,
                "GetAnnotationSubjectsByProperty dedupes prefLabel subjects by URI string — 6 assertions " +
                "collapse to 3 distinct concepts. A dropped .Distinct() would return 6; a disabled fallback 0.");
            concepts.Select(c => c.ToString())
                .Should().BeEquivalentTo(new[] { Ns + "C1", Ns + "C2", Ns + "C3" },
                    "the survivor fallback resolves the prefLabel subjects verbatim");
        }

        // ─────────────────────────────────────────────────────────────────────────────
        // (2) ConceptScheme survivor fallback — the scheme resolves as the SUBJECT of the surviving
        //     skos:hasTopConcept annotation (the scheme owns the top link). Exact-subject pin the e2e
        //     cannot do (it only asserts NotBeEmpty on the real file where hasTopConcept count == 1).
        // ─────────────────────────────────────────────────────────────────────────────

        [Fact]
        public void ConceptScheme_ResolvedViaHasTopConceptSubject_WhenRdfTypeAbsent()
        {
            var adapter = NewAdapter();
            var scheme = Res("Scheme");
            var top = Res("Top");
            // Survivor-only: the hasTopConcept link added directly, NO DeclareConceptScheme (no rdf:type).
            adapter.AnnotateConceptWithResource(scheme, SKOSVocabulary.HasTopConcept, top);
            // Reciprocal topConceptOf is irrelevant to the fallback (it keys on hasTopConcept subject).

            var schemes = adapter.GetResourcesByType(SKOSVocabulary.ConceptScheme);
            schemes.Should().ContainSingle(s => s.ToString() == Ns + "Scheme",
                "the scheme resolves as the SUBJECT of skos:hasTopConcept (it owns the top link), not as " +
                "the object — a subject/object swap in GetAnnotationSubjectsByProperty would return the top " +
                "concept instead of the scheme");
        }

        // ─────────────────────────────────────────────────────────────────────────────
        // (3) Unknown-type isolation — a type that is neither Concept nor ConceptScheme returns EMPTY
        //     even when the survivor annotations are present. Pins that the fallback does not
        //     over-resolve (a regression that made any query fall through to prefLabel subjects would
        //     silently leak concepts into unrelated type lookups). Uncovered by the e2e.
        // ─────────────────────────────────────────────────────────────────────────────

        [Fact]
        public void UnknownType_ReturnsEmpty_EvenWhenSurvivorAnnotationsPresent()
        {
            var adapter = NewAdapter();
            // Populate survivor annotations so there IS something to (wrongly) resolve.
            adapter.AnnotateConceptPreferredLabel(Res("C1"), Lit("Concept 1"));
            adapter.AnnotateConceptWithResource(Res("Scheme"), SKOSVocabulary.HasTopConcept, Res("C1"));

            var unknown = new RDFResource("http://argumentum.test/survivor#UnknownType");
            var result = adapter.GetResourcesByType(unknown);
            result.Should().BeEmpty(
                "an unknown type with no rdf:type match and no Concept/ConceptScheme survivor branch must " +
                "return the empty type-scan result — the fallback must not over-resolve prefLabel subjects " +
                "for unrelated type queries");
        }

        // ─────────────────────────────────────────────────────────────────────────────
        // (4) Type-scan GOVERNS when present — fallback is secondary. A mixed ontology: concept_A
        //     carries rdf:type=Concept (via DeclareConcept), concept_B carries ONLY prefLabel (no
        //     rdf:type). GetResourcesByType(Concept) must return [concept_A] ALONE — concept_B is
        //     absent, proving the fallback was skipped the moment the type scan yielded a result.
        //     This is the decisive proof the fix did NOT change in-memory semantics (where rdf:type
        //     survives): the original type-scan path is still authoritative when non-empty. The e2e
        //     cannot test this — the real file has zero rdf:type, so the type scan is never the
        //     governing path there.
        // ─────────────────────────────────────────────────────────────────────────────

        [Fact]
        public void RdfTypePresent_TakesTypeScanPath_FallbackSkipped()
        {
            var adapter = NewAdapter();
            var scheme = Res("Scheme");
            // concept_A: rdf:type=Concept present (DeclareConcept emits it).
            var conceptA = Res("A");
            adapter.DeclareConcept(conceptA, scheme);
            // concept_B: ONLY prefLabel, no rdf:type — would be picked up by the survivor fallback
            // IF the fallback were consulted despite the non-empty type scan.
            var conceptB = Res("B");
            adapter.AnnotateConceptPreferredLabel(conceptB, Lit("Concept B (fr)"));

            var concepts = adapter.GetResourcesByType(SKOSVocabulary.Concept);
            concepts.Should().ContainSingle(c => c.ToString() == Ns + "A",
                "the type scan finds concept_A (rdf:type=Concept present) and early-returns");
            concepts.Should().NotContain(c => c.ToString() == Ns + "B",
                "the survivor fallback is SKIPPED once the type scan yields a result — concept_B (prefLabel " +
                "only, no rdf:type) must NOT leak in. A regression that always unioned type-scan + fallback " +
                "would include concept_B and silently change in-memory resolution semantics");
        }

        // ─────────────────────────────────────────────────────────────────────────────
        // (5) GetConcepts() survivor tail — the public GetConcepts() reader (used by the production
        //     validators) hits the same survivor fallback on a survivor-only ontology via its
        //     `GetAnnotationSubjectsByProperty(PrefLabel)` tail. Distinct path from
        //     GetResourcesByType (it tries SKOSHelper.GetConceptsInScheme first), same dedup contract.
        // ─────────────────────────────────────────────────────────────────────────────

        [Fact]
        public void GetConcepts_ResolvedViaPrefLabelSurvivorTail_WhenRdfTypeAbsent()
        {
            var adapter = NewAdapter();
            // 2 concepts × fr+en prefLabel, no declarations (so SKOSHelper.GetConceptsInScheme has no
            // scheme to iterate → empty → falls through to the prefLabel survivor tail).
            adapter.AnnotateConceptPreferredLabel(Res("C1"), Lit("C1 fr"));
            adapter.AnnotateConceptPreferredLabel(Res("C1"), Lit("C1 en"));
            adapter.AnnotateConceptPreferredLabel(Res("C2"), Lit("C2 fr"));
            adapter.AnnotateConceptPreferredLabel(Res("C2"), Lit("C2 en"));

            var concepts = adapter.GetConcepts();
            concepts.Should().HaveCount(2,
                "GetConcepts() survivor tail (GetAnnotationSubjectsByProperty(PrefLabel)) dedupes — 4 " +
                "prefLabel assertions collapse to 2 distinct concepts");
            concepts.Select(c => c.ToString())
                .Should().BeEquivalentTo(new[] { Ns + "C1", Ns + "C2" });
        }

        // ─────────────────────────────────────────────────────────────────────────────
        // (6) AIF survivor — the match-family readers (exactMatch/closeMatch/relatedMatch) carry the
        //     same survivor shape (SKOSHelper-then-annotation-scan). On a synthetic ontology with
        //     only the raw match annotation (no full SKOS declarations), the annotation-scan fallback
        //     resolves the mapping. This is the AIF half of "Ontology/AIF survivor coverage".
        // ─────────────────────────────────────────────────────────────────────────────

        [Fact]
        public void ExactMatch_ResolvedViaAnnotationScan_WhenSkosHelperEmpty()
        {
            var adapter = NewAdapter();
            var en = Res("Concept_EN");
            var fr = Res("Concept_FR");
            // Only the raw exactMatch annotation — no declarations. SKOSHelper.GetExactMatchConcepts
            // returns empty/null on a bare ontology, so the annotation-scan fallback must resolve it.
            adapter.DeclareExactMatchConcepts(en, fr);
            // prefLabel so the concepts are also survivor-resolvable (mirrors a real loaded ontology).
            adapter.AnnotateConceptPreferredLabel(en, Lit("Ad Hominem"));
            adapter.AnnotateConceptPreferredLabel(fr, Lit("Attaque personnelle"));

            var matches = adapter.GetExactMatchConcepts(en);
            matches.Should().NotBeEmpty("the annotation-scan fallback must resolve exactMatch when SKOSHelper is empty");
            matches.Should().ContainSingle(c => c.ToString() == Ns + "Concept_FR",
                "exactMatch en→fr resolves via the surviving annotation");
        }

        [Fact]
        public void CloseMatch_ResolvedViaAnnotationScan_WhenSkosHelperEmpty()
        {
            // Same survivor shape as exactMatch — proves the pattern holds across the match family
            // (GetCloseMatchConcepts shares the SKOSHelper-then-GetResourceAnnotations structure).
            var adapter = NewAdapter();
            var c1 = Res("Concept_A");
            var c2 = Res("Concept_B");
            adapter.DeclareCloseMatchConcepts(c1, c2);

            var matches = adapter.GetCloseMatchConcepts(c1);
            matches.Should().NotBeEmpty("closeMatch resolves via the annotation-scan fallback");
            matches.Should().ContainSingle(c => c.ToString() == Ns + "Concept_B");
        }
    }
}
