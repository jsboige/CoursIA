// Copyright (c) 2026 CoursIA — port verbatim from Argumentum under LGPL-3.0 + AGPL-3.0
// See NOTICE in this directory for full attribution.
//
// Verbatim port of OwlAdapterRegressionTests.cs from
// Argumentum.AssetConverter.Tests.Ontology (commit ac33f607).
// Modifications disclosed: namespace change only.

using System;
using System.IO;
using System.Linq;
using CoursIA.SymbolicAI.Argument_Analysis.AssetConverter.Ontology;
using FluentAssertions;
using RDFSharp.Model;
using Xunit;

namespace CoursIA.SymbolicAI.Argument_Analysis.AssetConverter.Tests.Ontology
{
    /// <summary>
    /// Regression / characterization tests for <see cref="OwlAdapter"/> — dispatch #204 (primaire, cont.).
    ///
    /// NEW additive file. The Ontology subsystem had zero xUnit coverage prior to this (the
    /// production-side <c>Tests/OwlOntologyValidationTests.cs</c> module is NOT an xUnit suite).
    /// CLAUDE.md flags the SKOS/OWL layer as fragile: <c>OwlAdapter</c> bypasses the broken
    /// <c>SKOSHelper</c> extension methods in OWLSharp and self-retrieves concepts via fallback
    /// annotation scanners (<c>GetAnnotationSubjects</c> / <c>GetResourceAnnotations</c> /
    /// <c>GetLiteralAnnotations</c>).
    ///
    /// ✅ BUG FOUND then FIXED. PR #480 surfaced a real bug (not greenwashed): every fallback
    /// reader compared <c>a.ValueIRI.Equals(value.URI)</c> / <c>a.SubjectIRI.Equals(subject.URI)</c>
    /// where <c>.URI</c> is a <b>string</b> and <c>ValueIRI</c>/<c>SubjectIRI</c> are
    /// <c>RDFResource</c>. <c>RDFResource.Equals(string)</c> returns <b>false by type-mismatch</b>,
    /// so every read returned empty — the root cause behind the production validation module
    /// silently reporting "no concepts → skip → PASS" on annotation/AIF checks. See
    /// <see cref="Diag_RDFResource_Equals_String_Is_False_By_Type_Mismatch"/>.
    ///
    /// This PR applies the fix: drop <c>.URI</c> on the right-hand side of every reader comparison
    /// (14 sites in <c>OwlAdapter.cs</c>), so readers compare <c>RDFResource.Equals(RDFResource)</c>.
    /// The section-(A) tests below WERE the [BUG] characterization suite from #480; they are now
    /// flipped to proper round-trip assertions and serve as the regression suite guarding the fix.
    /// Section (C) write-path + serialization tests (unchanged) prove the fix did not regress the
    /// write side.
    ///
    /// Deterministic, key-free, release-independent.
    /// </summary>
    public class OwlAdapterRegressionTests
    {
        private const string Ns = "http://argumentum.test/onto#";

        private static OwlAdapter NewAdapter() => new OwlAdapter(Ns);

        private static RDFResource Res(string local) => new RDFResource(Ns + local);

        private static RDFPlainLiteral Lit(string value) => new RDFPlainLiteral(value);

        // ─────────────────────────────────────────────────────────────────────────────
        // (B) Root-cause probe — the comparison semantics the readers depend on.
        // ─────────────────────────────────────────────────────────────────────────────

        [Fact]
        public void Diag_RDFResource_Equals_String_Is_False_By_Type_Mismatch()
        {
            // ROOT CAUSE of the [BUG]: RDFResource.Equals(object) requires the argument to BE an
            // RDFResource with the same URI. Passing a string (which is what `.URI` yields) returns
            // false on every comparison. The OwlAdapter fallback readers all do
            // `a.ValueIRI.Equals(value.URI)` and `a.SubjectIRI.Equals(subject.URI)` — so they never
            // match. This test pins the RDFSharp semantics so the root cause is undeniable.
            var r = new RDFResource(Ns + "X");
            var sameUriString = Ns + "X";

            r.Equals(sameUriString).Should().BeFalse(
                "RDFResource.Equals(string) is false by type-mismatch — the read-path bug");
            r.Equals(new RDFResource(sameUriString)).Should().BeTrue(
                "RDFResource.Equals(RDFResource) is true when URIs match — what the readers SHOULD compare against");
            (r.ToString() == sameUriString).Should().BeTrue(
                "ToString() yields the plain URI string — the correct string basis for comparison");
        }

        // ─────────────────────────────────────────────────────────────────────────────
        // (A) Reader round-trip — was the [BUG] characterization suite in #480 (asserted the
        //     BROKEN empty/false behavior). Now flipped by the fix in this PR: these verify the
        //     readers correctly retrieve what the write path declared. Regression suite for the fix.
        // ─────────────────────────────────────────────────────────────────────────────

        [Fact]
        public void GetConcepts_RoundTrips_Declared_Concepts_After_Fix()
        {
            // Write 3 concepts; the reader must return all 3 (was returning 0 before the fix
            // because the fallback scanner compared RDFResource.Equals(string)).
            var adapter = NewAdapter();
            var scheme = Res("Scheme");
            adapter.DeclareConceptScheme(scheme);
            adapter.DeclareConcept(Res("C1"), scheme);
            adapter.DeclareConcept(Res("C2"), scheme);
            adapter.DeclareConcept(Res("C3"), scheme);

            var concepts = adapter.GetConcepts();
            concepts.Should().NotBeEmpty("GetConcepts must retrieve declared concepts (fix: RDFResource.Equals(RDFResource))");
            concepts.Should().HaveCount(3);
            concepts.Select(c => c.ToString()).Should().BeEquivalentTo(new[] { Ns + "C1", Ns + "C2", Ns + "C3" });
        }

        [Fact]
        public void GetResourcesByType_RoundTrips_Concepts_And_Schemes_After_Fix()
        {
            // Same root cause, different reader. ValidateOwlOntologyStructure relies on this.
            // Was returning empty before the fix (RDFResource.Equals(string)).
            var adapter = NewAdapter();
            var scheme = Res("Scheme");
            adapter.DeclareConceptScheme(scheme);
            adapter.DeclareConcept(Res("C1"), scheme);

            adapter.GetResourcesByType(SKOSVocabulary.Concept)
                .Should().NotBeEmpty("Concept type resolves after the fix")
                .And.ContainSingle(c => c.ToString() == Ns + "C1");
            adapter.GetResourcesByType(SKOSVocabulary.ConceptScheme)
                .Should().NotBeEmpty("ConceptScheme type resolves after the fix")
                .And.ContainSingle(c => c.ToString() == Ns + "Scheme");
        }

        [Fact]
        public void GetTopConcepts_RoundTrips_Declared_Top_Concepts_After_Fix()
        {
            var adapter = NewAdapter();
            adapter.DeclareTopConcept(Res("Top1"), Res("Scheme"));
            adapter.DeclareTopConcept(Res("Top2"), Res("Scheme"));

            var tops = adapter.GetTopConcepts();
            tops.Should().NotBeEmpty("GetTopConcepts must retrieve declared top concepts after the fix");
            tops.Select(c => c.ToString()).Should().BeEquivalentTo(new[] { Ns + "Top1", Ns + "Top2" });
        }

        [Fact]
        public void HasAnnotation_Finds_The_Annotation_After_Fix()
        {
            var adapter = NewAdapter();
            var scheme = Res("Scheme");
            adapter.DeclareConceptScheme(scheme);

            // The annotation IS written (write-path test confirms it); HasAnnotation must now find it
            // (was false before the fix: ValueIRI.Equals(value.URI string)).
            adapter.HasAnnotation(scheme, RDFVocabulary.RDF.TYPE, SKOSVocabulary.ConceptScheme)
                .Should().BeTrue("HasAnnotation must match rdf:type=skos:ConceptScheme after the fix");
        }

        [Fact]
        public void CheckIsNarrowerConcept_Detects_The_Edge_After_Fix()
        {
            var adapter = NewAdapter();
            var parent = Res("Fallacies");
            var child = Res("AdHominem");
            adapter.DeclareNarrowerConcepts(parent, child);

            // CheckIsNarrowerConcept's try/except fallback ALSO used .Equals(string.URI) and failed;
            // after the fix the fallback scanner matches correctly.
            adapter.CheckIsNarrowerConcept(child, parent)
                .Should().BeTrue("child IS a narrower of parent after the fix");
            adapter.CheckIsNarrowerConcept(Res("Unrelated"), parent)
                .Should().BeFalse("an unrelated concept is NOT a narrower of parent");
        }

        [Fact]
        public void GetConceptPreferredLabels_RoundTrips_The_Label_After_Fix()
        {
            var adapter = NewAdapter();
            var concept = Res("C");
            adapter.DeclareConcept(concept, Res("Scheme"));
            adapter.AnnotateConceptPreferredLabel(concept, Lit("Ad Hominem"));

            adapter.GetConceptPreferredLabels(concept)
                .Should().NotBeEmpty("prefLabel must be retrievable after the fix")
                .And.ContainSingle(l => l.ToString().StartsWith("Ad Hominem"));
        }

        [Fact]
        public void GetConceptDocumentation_RoundTrips_The_Definition_After_Fix()
        {
            var adapter = NewAdapter();
            var concept = Res("C");
            adapter.DeclareConcept(concept, Res("Scheme"));
            adapter.DocumentConcept(concept, SKOSDocumentationTypes.Definition, Lit("A fallacy..."));

            adapter.GetConceptDocumentation(concept, SKOSDocumentationTypes.Definition)
                .Should().NotBeEmpty("definition must be retrievable after the fix")
                .And.ContainSingle(l => l.ToString().StartsWith("A fallacy"));
        }

        [Fact]
        public void GetExactMatchConcepts_RoundTrips_The_Match_After_Fix()
        {
            var adapter = NewAdapter();
            var c1 = Res("EN");
            var c2 = Res("FR");
            adapter.DeclareExactMatchConcepts(c1, c2);

            adapter.GetExactMatchConcepts(c1)
                .Should().NotBeEmpty("exactMatch must be retrievable after the fix")
                .And.ContainSingle(c => c.ToString() == Ns + "FR");
        }

        // ─────────────────────────────────────────────────────────────────────────────
        // (C) Write-path + serialization — these WORK (the ontology is correctly built in
        //     memory; only the self-retrieval readers are broken). Pinned so a fix doesn't
        //     regress the write side.
        // ─────────────────────────────────────────────────────────────────────────────

        [Fact]
        public void Constructor_Produces_An_Adapter_With_The_Declared_Namespace_Uri()
        {
            var adapter = NewAdapter();
            adapter.Uri.ToString().Should().Be(Ns);
            adapter.GetOntology().Should().NotBeNull();
        }

        [Fact]
        public void DeclareConcept_Appends_AnnotationAxioms_To_The_Ontology()
        {
            // The WRITE side is correct: DeclareConcept adds real annotation axioms to the
            // ontology (verifiable by inspecting the underlying graph directly). These write-path
            // tests guard that the reader fix did not regress the graph construction.
            var adapter = NewAdapter();
            var scheme = Res("Scheme");
            var concept = Res("C1");

            adapter.DeclareConceptScheme(scheme);
            adapter.DeclareConcept(concept, scheme);

            var onto = adapter.GetOntology();
            onto.AnnotationAxioms.Should().NotBeEmpty("DeclareConcept writes annotation axioms");

            // Verify by ToString() comparison (the correct basis), not the broken reader.
            var hasConceptType = onto.AnnotationAxioms.OfType<OWLSharp.Ontology.OWLAnnotationAssertion>()
                .Any(a => a.AnnotationProperty.GetIRI().ToString() == RDFVocabulary.RDF.TYPE.URI.ToString()
                       && a.SubjectIRI.ToString() == concept.URI.ToString()
                       && a.ValueIRI?.ToString() == SKOSVocabulary.Concept.URI.ToString());
            hasConceptType.Should().BeTrue(
                "the concept's rdf:type=skos:Concept axiom IS present in the graph (write works; reader is broken)");
        }

        [Fact]
        public void DeclareNarrowerConcepts_Appends_Both_Directional_Axioms()
        {
            var adapter = NewAdapter();
            var parent = Res("P");
            var child = Res("C");
            adapter.DeclareNarrowerConcepts(parent, child);

            var onto = adapter.GetOntology();
            var hasNarrower = onto.AnnotationAxioms.OfType<OWLSharp.Ontology.OWLAnnotationAssertion>()
                .Any(a => a.AnnotationProperty.GetIRI().ToString() == SKOSVocabulary.Narrower.URI.ToString()
                       && a.SubjectIRI.ToString() == parent.URI.ToString()
                       && a.ValueIRI?.ToString() == child.URI.ToString());
            var hasBroader = onto.AnnotationAxioms.OfType<OWLSharp.Ontology.OWLAnnotationAssertion>()
                .Any(a => a.AnnotationProperty.GetIRI().ToString() == SKOSVocabulary.Broader.URI.ToString()
                       && a.SubjectIRI.ToString() == child.URI.ToString()
                       && a.ValueIRI?.ToString() == parent.URI.ToString());

            hasNarrower.Should().BeTrue("skos:narrower parent→child written");
            hasBroader.Should().BeTrue("skos:broader child→parent written (reciprocal)");
        }

        [Fact]
        public void AnnotateConceptPreferredLabel_Appends_The_PrefLabel_Axiom()
        {
            // Write-path verification via direct graph inspection (bypassing the broken reader).
            // Assert the prefLabel axiom exists for the concept — the literal value rendering
            // format is OWLSharp-internal, so we only assert the property+subject binding.
            var adapter = NewAdapter();
            var concept = Res("C");
            adapter.DeclareConcept(concept, Res("Scheme"));
            adapter.AnnotateConceptPreferredLabel(concept, Lit("Ad Hominem"));

            var onto = adapter.GetOntology();
            var hasLabel = onto.AnnotationAxioms.OfType<OWLSharp.Ontology.OWLAnnotationAssertion>()
                .Any(a => a.AnnotationProperty.GetIRI().ToString() == SKOSVocabulary.PrefLabel.URI.ToString()
                       && a.SubjectIRI.ToString() == concept.URI.ToString()
                       && a.ValueLiteral != null);
            hasLabel.Should().BeTrue("skos:prefLabel axiom written to the graph (write works; reader broken)");
        }

        [Fact]
        public void CheckHasClass_Finds_The_Declared_Class_After_Fix()
        {
            // CheckHasClass uses DeclarationAxioms and compared cls.GetIRI().Equals(resource.URI)
            // where .URI is a System.Uri — RDFResource.Equals(Uri) was false by type-mismatch (the
            // SAME root cause as the annotation readers). After the fix it compares RDFResource.Equals(RDFResource).
            var adapter = NewAdapter();
            var declared = Res("DeclaredClass");
            adapter.DeclareClass(declared);

            // The class IS declared in DeclarationAxioms:
            var onto = adapter.GetOntology();
            onto.DeclarationAxioms.Should().NotBeEmpty("DeclareClass wrote the declaration axiom");

            // ...and CheckHasClass now finds it:
            adapter.CheckHasClass(declared).Should().BeTrue(
                "CheckHasClass must match the declared class after the fix (RDFResource.Equals(RDFResource))");
            adapter.CheckHasClass(Res("UndeclaredClass")).Should().BeFalse(
                "an undeclared class is not found");
        }

        [Fact]
        public void DocumentConcept_Unknown_Type_Throws()
        {
            var adapter = NewAdapter();
            var concept = Res("C");
            var invalid = (SKOSDocumentationTypes)999;

            Action act = () => adapter.DocumentConcept(concept, invalid, Lit("x"));
            act.Should().Throw<ArgumentOutOfRangeException>();
        }

        [Fact]
        public void ToFileAsync_Writes_A_Non_Empty_OWL2XML_File()
        {
            // Serialization works end-to-end (this is why #133 ships a non-empty ontology despite
            // the readers being broken — the graph is correctly built, only self-retrieval fails).
            var adapter = NewAdapter();
            var scheme = Res("Scheme");
            adapter.DeclareConceptScheme(scheme);
            adapter.DeclareConcept(Res("C1"), scheme);
            adapter.AnnotateConceptPreferredLabel(Res("C1"), Lit("Test Concept"));

            var tempPath = Path.Combine(Path.GetTempPath(), $"arg_onto_test_{Guid.NewGuid():N}.owl");
            try
            {
                adapter.ToFileAsync(OWLSharp.OWLEnums.OWLFormats.OWL2XML, tempPath).Wait();
                File.Exists(tempPath).Should().BeTrue();
                var content = File.ReadAllText(tempPath);
                content.Should().NotBeNullOrEmpty("the serialized ontology must be non-empty");
                content.Should().Match(s => s.Contains("<rdf:RDF") || s.Contains("xmlns"),
                    "the OWL2XML output must be RDF/XML");
            }
            finally
            {
                if (File.Exists(tempPath)) File.Delete(tempPath);
            }
        }
    }
}
