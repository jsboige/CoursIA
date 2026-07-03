// Copyright (c) 2026 CoursIA — port verbatim from Argumentum under LGPL-3.0 + AGPL-3.0
// See NOTICE in this directory for full attribution.
//
// ============================================================================
// Port notes (C175/C176, po-2025)
// ----------------------------------------------------------------------------
// Verbatim port of Argumentum.AssetConverter.Ontology (C# .NET), commit
//   ac33f607a4889d8a982093c413804ed25bef3dc0
// from the Argumentum submodule at
//   MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argumentum
//   Generation/Converters/Argumentum.AssetConverter/Ontology/OwlAdapter.cs
//
// Modifications (disclosed in NOTICE, summary):
//   1. Namespace Argumentum.AssetConverter.Ontology
//        -> CoursIA.SymbolicAI.Argument_Analysis.AssetConverter.Ontology
//   2. Logger.LogProblem(...) (internal Argumentum utility, not public)
//        -> _logger.LogProblem(...) against a private field initialised to
//           NullLegacyLogger.Instance (see ILegacyLogger.cs in this directory).
//   3. SKOSDocumentationTypes enum + SKOSVocabulary static class + OwlAdapter
//        class are kept in this single file (verbatim split from upstream).
//
// EVERYTHING ELSE IS UNCHANGED. The 8+ workaround comments for SKOSHelper
// 4.9.0 bugs, the 6+ empty try/catch blocks, the OWL2XML round-trip
// survivor fallback, the .ToString() RDFResource comparison fix — all
// preserved bit-for-bit. Do NOT refactor without re-running the 8 upstream
// test files (1654 LOC, ported verbatim) GREEN.
// ============================================================================

using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Threading.Tasks;
using System.Reflection;
using OWLSharp;
using OWLSharp.Ontology;
using OWLSharp.Extensions.SKOS;
using RDFSharp.Model;
using VDS.RDF;
using VDS.RDF.Parsing;

namespace CoursIA.SymbolicAI.Argument_Analysis.AssetConverter.Ontology
{
    /// <summary>
    /// Types de documentation SKOS
    /// </summary>
    public enum SKOSDocumentationTypes
    {
        Definition,
        Example
    }

    /// <summary>
    /// SKOS vocabulary constants (http://www.w3.org/2004/02/skos/core#)
    /// Used to add SKOS triples as raw OWL annotation assertions,
    /// bypassing the broken SKOSHelper extension methods in OWLSharp 4.9.0.
    /// </summary>
    public static class SKOSVocabulary
    {
        private const string NS = "http://www.w3.org/2004/02/skos/core#";

        public static readonly RDFResource ConceptScheme = new RDFResource($"{NS}ConceptScheme");
        public static readonly RDFResource Concept = new RDFResource($"{NS}Concept");
        public static readonly RDFResource InScheme = new RDFResource($"{NS}inScheme");
        public static readonly RDFResource HasTopConcept = new RDFResource($"{NS}hasTopConcept");
        public static readonly RDFResource TopConceptOf = new RDFResource($"{NS}topConceptOf");
        public static readonly RDFResource Narrower = new RDFResource($"{NS}narrower");
        public static readonly RDFResource Broader = new RDFResource($"{NS}broader");
        public static readonly RDFResource PrefLabel = new RDFResource($"{NS}prefLabel");
        public static readonly RDFResource Definition = new RDFResource($"{NS}definition");
        public static readonly RDFResource Example = new RDFResource($"{NS}example");
        public static readonly RDFResource ExactMatch = new RDFResource($"{NS}exactMatch");
        public static readonly RDFResource CloseMatch = new RDFResource($"{NS}closeMatch");
        public static readonly RDFResource BroadMatch = new RDFResource($"{NS}broadMatch");
        public static readonly RDFResource NarrowMatch = new RDFResource($"{NS}narrowMatch");
        public static readonly RDFResource RelatedMatch = new RDFResource($"{NS}relatedMatch");
    }

    /// <summary>
    /// Adaptateur pour la bibliothèque OWLSharp 4.9.0
    /// </summary>
    public class OwlAdapter
    {
        private OWLOntology _ontology;
        private string _namespace;
        private readonly ILegacyLogger _logger;

        public OwlAdapter(string ontologyNamespace)
            : this(ontologyNamespace, NullLegacyLogger.Instance)
        {
        }

        public OwlAdapter(string ontologyNamespace, ILegacyLogger logger)
        {
            _logger = logger ?? NullLegacyLogger.Instance;
            _namespace = ontologyNamespace;
            Uri = new Uri(ontologyNamespace);

            try
            {
                Type owlOntologyType = Type.GetType("OWLSharp.Ontology.OWLOntology, OWLSharp");
                if (owlOntologyType == null)
                {
                    owlOntologyType = Type.GetType("OWLOntology, OWLSharp");
                }

                if (owlOntologyType != null)
                {
                    var constructor = owlOntologyType.GetConstructor(new[] { typeof(Uri), typeof(Uri) });
                    if (constructor == null)
                    {
                        constructor = owlOntologyType.GetConstructor(new[] { typeof(Uri) });
                        if (constructor == null)
                        {
                           throw new InvalidOperationException("Impossible de trouver un constructeur approprié pour OWLOntology.");
                        }
                        _ontology = (OWLOntology)constructor.Invoke(new object[] { Uri });
                    }
                    else
                    {
                        _ontology = (OWLOntology)constructor.Invoke(new object[] { Uri, null });
                    }

                    if (_ontology == null)
                    {
                        throw new InvalidOperationException("La création de l'ontologie vide a échoué.");
                    }
                }
                else
                {
                    throw new InvalidOperationException("Type OWLOntology non trouvé");
                }
            }
            catch (Exception ex)
            {
                _logger.LogProblem($"Erreur lors de la création de l'ontologie OWL : {ex.Message}");
                throw;
            }
        }

        public Uri Uri { get; private set; }

        public static OwlAdapter FromFile(string filePath)
        {
            return FromFile(filePath, NullLegacyLogger.Instance);
        }

        public static OwlAdapter FromFile(string filePath, ILegacyLogger logger)
        {
            var safeLogger = logger ?? NullLegacyLogger.Instance;
            try
            {
                OWLOntology ontology = OWLOntology.FromFileAsync(OWLEnums.OWLFormats.OWL2XML, filePath).GetAwaiter().GetResult();

                if (ontology == null)
                {
                    throw new InvalidOperationException("Le chargement de l'ontologie a retourné null.");
                }

                var adapter = new OwlAdapter(ontology.IRI.ToString(), safeLogger);
                adapter._ontology = ontology;
                adapter._namespace = ontology.IRI.ToString();

                return adapter;
            }
            catch (Exception ex)
            {
                safeLogger.LogProblem($"Erreur lors du chargement de l'ontologie: {ex.Message}");
                throw new InvalidOperationException("Impossible de charger l'ontologie OWL à partir du fichier", ex);
            }
        }

        public void Annotate(RDFResource property, RDFPlainLiteral value)
        {
            _ontology.Annotate(new OWLAnnotation(new OWLAnnotationProperty(property), new OWLLiteral(value)));
        }

        public void DeclareClass(RDFResource resource)
        {
            _ontology.DeclarationAxioms.Add(new OWLDeclaration(new OWLClass(resource)));
        }

        public void DeclareObjectProperty(RDFResource resource)
        {
            _ontology.DeclarationAxioms.Add(new OWLDeclaration(new OWLObjectProperty(resource)));
        }

        public void DeclareConceptScheme(RDFResource scheme)
        {
            DeclareClass(scheme);
            // SKOSHelper.DeclareConceptScheme is broken in OWLSharp 4.9.0 — emit rdf:type directly
            AnnotateConceptWithResource(scheme, RDFVocabulary.RDF.TYPE, SKOSVocabulary.ConceptScheme);
        }

        public void DeclareConcept(RDFResource concept, RDFResource scheme)
        {
            DeclareClass(concept);
            // SKOSHelper.DeclareConcept is broken in OWLSharp 4.9.0 — emit rdf:type + skos:inScheme directly
            AnnotateConceptWithResource(concept, RDFVocabulary.RDF.TYPE, SKOSVocabulary.Concept);
            AnnotateConceptWithResource(concept, SKOSVocabulary.InScheme, scheme);
        }

        public void DeclareTopConcept(RDFResource concept, RDFResource scheme)
        {
            // SKOSHelper has no DeclareTopConcept — use raw annotations
            AnnotateConceptWithResource(scheme, SKOSVocabulary.HasTopConcept, concept);
            AnnotateConceptWithResource(concept, SKOSVocabulary.TopConceptOf, scheme);
        }

        public void DeclareNarrowerConcepts(RDFResource parentConcept, RDFResource childConcept)
        {
            // SKOSHelper has no DeclareNarrowerConcept — use raw annotations
            AnnotateConceptWithResource(parentConcept, SKOSVocabulary.Narrower, childConcept);
            AnnotateConceptWithResource(childConcept, SKOSVocabulary.Broader, parentConcept);
        }

        public void DeclareExactMatchConcepts(RDFResource concept1, RDFResource concept2)
        {
            AnnotateConceptWithResource(concept1, SKOSVocabulary.ExactMatch, concept2);
        }

        public void DeclareCloseMatchConcepts(RDFResource concept1, RDFResource concept2)
        {
            AnnotateConceptWithResource(concept1, SKOSVocabulary.CloseMatch, concept2);
        }

        public void DeclareBroadMatchConcepts(RDFResource concept1, RDFResource concept2)
        {
            AnnotateConceptWithResource(concept1, SKOSVocabulary.BroadMatch, concept2);
        }

        public void DeclareNarrowMatchConcepts(RDFResource concept1, RDFResource concept2)
        {
            AnnotateConceptWithResource(concept1, SKOSVocabulary.NarrowMatch, concept2);
        }

        public void DeclareRelatedMatchConcepts(RDFResource concept1, RDFResource concept2)
        {
            AnnotateConceptWithResource(concept1, SKOSVocabulary.RelatedMatch, concept2);
        }

        public void DeclareQualifiedCardinalityRestriction(RDFResource restrictionClass, RDFResource onProperty, int cardinality, RDFResource onClass)
        {
            var onPropertyExpression = new OWLObjectProperty(onProperty);
            var onClassExpression = new OWLClass(onClass);
            var cardinalityRestriction = new OWLObjectExactCardinality(onPropertyExpression, (uint)cardinality, onClassExpression);
            var subClass = new OWLClass(restrictionClass);
            _ontology.ClassAxioms.Add(new OWLSubClassOf(subClass, cardinalityRestriction));
        }

        public void DeclareIntersectionClass(RDFResource intersectionClass, List<RDFResource> intersectionClassMembers)
        {
            var intersectionOf = new OWLObjectIntersectionOf(intersectionClassMembers.Select(m => new OWLClass(m)).ToList<OWLClassExpression>());
            var classExpressions = new List<OWLClassExpression> { new OWLClass(intersectionClass), intersectionOf };
            var equivalentClassesAxiom = new OWLEquivalentClasses(classExpressions);
            _ontology.ClassAxioms.Add(equivalentClassesAxiom);
        }

        public void DeclareUnionClass(RDFResource unionClass, List<RDFResource> unionClassMembers)
        {
            var unionOf = new OWLObjectUnionOf(unionClassMembers.Select(m => new OWLClass(m)).ToList<OWLClassExpression>());
            var classExpressions = new List<OWLClassExpression> { new OWLClass(unionClass), unionOf };
            var equivalentClassesAxiom = new OWLEquivalentClasses(classExpressions);
            _ontology.ClassAxioms.Add(equivalentClassesAxiom);
        }

        public void AnnotateConceptPreferredLabel(RDFResource concept, RDFPlainLiteral label)
        {
            AnnotateConcept(concept, SKOSVocabulary.PrefLabel, label);
        }

        public void AnnotateConcept(RDFResource concept, RDFResource property, RDFPlainLiteral value)
        {
            _ontology.AnnotationAxioms.Add(new OWLAnnotationAssertion(new OWLAnnotationProperty(property), concept, new OWLLiteral(value)));
        }

        public void AnnotateConceptWithResource(RDFResource subject, RDFResource property, RDFResource value)
        {
            _ontology.AnnotationAxioms.Add(new OWLAnnotationAssertion(new OWLAnnotationProperty(property), subject, value));
        }

        public void DocumentConcept(RDFResource concept, SKOSDocumentationTypes documentationType, RDFPlainLiteral value)
        {
            var property = documentationType switch
            {
                SKOSDocumentationTypes.Definition => SKOSVocabulary.Definition,
                SKOSDocumentationTypes.Example => SKOSVocabulary.Example,
                _ => throw new ArgumentOutOfRangeException(nameof(documentationType))
            };
            AnnotateConcept(concept, property, value);
        }

        public Task ToFileAsync(OWLEnums.OWLFormats format, string filePath)
        {
            return _ontology.ToFileAsync(format, filePath);
        }

        public List<RDFResource> GetConcepts()
        {
            // Try SKOSHelper first, fall back to raw annotation scan
            try
            {
                var schemes = _ontology.DeclarationAxioms
                    .Where(ax => ax.Entity is OWLClass)
                    .Select(ax => new RDFResource(((OWLClass)ax.Entity).GetIRI().ToString()))
                    .ToList();
                foreach (var scheme in schemes)
                {
                    var concepts = SKOSHelper.GetConceptsInScheme(_ontology, scheme);
                    if (concepts.Count > 0) return concepts;
                }
            }
            catch { }
            // Round-trip survivor fallback (see GetResourcesByType): on a loaded ontology rdf:type is
            // absent, so concepts resolve via their surviving skos:prefLabel subjects.
            var byType = GetAnnotationSubjects(SKOSVocabulary.Concept);
            return byType.Count > 0 ? byType : GetAnnotationSubjectsByProperty(SKOSVocabulary.PrefLabel);
        }

        public List<RDFResource> GetTopConcepts()
        {
            return GetAnnotationObjects(SKOSVocabulary.HasTopConcept);
        }

        public bool CheckIsNarrowerConcept(RDFResource concept, RDFResource parentConcept)
        {
            try
            {
                if (SKOSHelper.CheckHasNarrowerConcept(_ontology, parentConcept, concept)) return true;
            }
            catch { }
            // SKOSHelper may return false silently (no exception) — fall back to annotation scanning.
            // The annotation scanner now uses .ToString() comparison (RDFResource type-mismatch fix).
            return _ontology.AnnotationAxioms.OfType<OWLAnnotationAssertion>()
                .Any(a => a.AnnotationProperty.GetIRI().ToString() == SKOSVocabulary.Narrower.ToString()
                    && a.SubjectIRI.ToString() == parentConcept.ToString()
                    && a.ValueIRI != null && a.ValueIRI.ToString() == concept.ToString());
        }

        public List<RDFPlainLiteral> GetConceptPreferredLabels(RDFResource concept)
        {
            return GetLiteralAnnotations(concept, SKOSVocabulary.PrefLabel);
        }

        public List<RDFPlainLiteral> GetConceptDocumentation(RDFResource concept, SKOSDocumentationTypes documentationType)
        {
            var property = documentationType switch
            {
                SKOSDocumentationTypes.Definition => SKOSVocabulary.Definition,
                SKOSDocumentationTypes.Example => SKOSVocabulary.Example,
                _ => throw new ArgumentOutOfRangeException(nameof(documentationType))
            };
            return GetLiteralAnnotations(concept, property);
        }

        public List<RDFResource> GetExactMatchConcepts(RDFResource concept)
        {
            try
            {
                var result = SKOSHelper.GetExactMatchConcepts(_ontology, concept);
                if (result != null && result.Count > 0) return result;
            }
            catch { }
            // SKOSHelper may return empty silently — fall back to annotation scanning (.ToString() fix).
            return GetResourceAnnotations(concept, SKOSVocabulary.ExactMatch);
        }

        public List<RDFResource> GetCloseMatchConcepts(RDFResource concept)
        {
            try
            {
                var result = SKOSHelper.GetCloseMatchConcepts(_ontology, concept);
                if (result != null && result.Count > 0) return result;
            }
            catch { }
            return GetResourceAnnotations(concept, SKOSVocabulary.CloseMatch);
        }

        public List<RDFResource> GetRelatedMatchConcepts(RDFResource concept)
        {
            try
            {
                var result = SKOSHelper.GetRelatedMatchConcepts(_ontology, concept);
                if (result != null && result.Count > 0) return result;
            }
            catch { }
            return GetResourceAnnotations(concept, SKOSVocabulary.RelatedMatch);
        }

        private List<RDFResource> GetAnnotationSubjects(RDFResource typeResource)
        {
            return _ontology.AnnotationAxioms.OfType<OWLAnnotationAssertion>()
                .Where(a => a.AnnotationProperty.GetIRI().ToString() == RDFVocabulary.RDF.TYPE.ToString()
                    && a.ValueIRI != null && a.ValueIRI.ToString() == typeResource.ToString())
                .Select(a => new RDFResource(a.SubjectIRI.ToString()))
                .ToList();
        }

        /// <summary>
        /// Distinct subjects carrying the given annotation property. Used by the OWL2XML round-trip
        /// survivor fallback in <see cref="GetResourcesByType"/> / <see cref="GetConcepts"/>: concepts
        /// are the distinct subjects of skos:prefLabel, the scheme the subject of skos:hasTopConcept.
        /// Deduped by URI string (not RDFResource.Equals) to avoid the RDFResource equality class of
        /// bugs — a concept carries prefLabel fr+en, i.e. two assertions yielding one distinct subject.
        /// </summary>
        private List<RDFResource> GetAnnotationSubjectsByProperty(RDFResource property)
        {
            var propertyUri = property.ToString();
            return _ontology.AnnotationAxioms.OfType<OWLAnnotationAssertion>()
                .Where(a => a.AnnotationProperty.GetIRI().ToString() == propertyUri)
                .Select(a => a.SubjectIRI.ToString())
                .Distinct()
                .Select(uri => new RDFResource(uri))
                .ToList();
        }

        private List<RDFResource> GetAnnotationObjects(RDFResource property)
        {
            return _ontology.AnnotationAxioms.OfType<OWLAnnotationAssertion>()
                .Where(a => a.AnnotationProperty.GetIRI().ToString() == property.ToString()
                    && a.ValueIRI != null)
                .Select(a => new RDFResource(a.ValueIRI.ToString()))
                .ToList();
        }

        private List<RDFResource> GetResourceAnnotations(RDFResource subject, RDFResource property)
        {
            return _ontology.AnnotationAxioms.OfType<OWLAnnotationAssertion>()
                .Where(a => a.AnnotationProperty.GetIRI().ToString() == property.ToString()
                    && a.SubjectIRI.ToString() == subject.ToString()
                    && a.ValueIRI != null)
                .Select(a => new RDFResource(a.ValueIRI.ToString()))
                .ToList();
        }

        private List<RDFPlainLiteral> GetLiteralAnnotations(RDFResource subject, RDFResource property)
        {
            return _ontology.AnnotationAxioms.OfType<OWLAnnotationAssertion>()
                .Where(a => a.AnnotationProperty.GetIRI().ToString() == property.ToString()
                    && a.SubjectIRI.ToString() == subject.ToString()
                    && a.ValueLiteral != null)
                .Select(a => {
                    var literal = a.ValueLiteral.GetLiteral();
                    return literal is RDFPlainLiteral plain ? plain : new RDFPlainLiteral(literal.Value);
                })
                .ToList();
        }

        public bool CheckHasClass(RDFResource resource)
        {
            return _ontology.DeclarationAxioms.Any(ax => ax.Entity is OWLClass cls && cls.GetIRI().ToString() == resource.ToString());
        }

        public OWLOntology GetOntology()
        {
            return _ontology;
        }

        public List<RDFResource> GetResourcesByType(RDFResource typeResource)
        {
            var byType = GetAnnotationSubjects(typeResource);
            if (byType.Count > 0)
                return byType;

            // OWL2XML round-trip survivor fallback (READ-PATH ONLY — the serializer is not touched).
            // On a LOADED ontology OWLSharp drops rdf:type from the reloaded annotation stream, so the
            // type scan above is empty (measured on the real generated ontology: rdf:type==0 and
            // skos:inScheme==0 among AnnotationAxioms). Locate the entities via the SKOS annotations
            // that DO survive the round-trip instead:
            //   - skos:Concept       → distinct subjects of skos:prefLabel (each concept carries fr+en)
            //   - skos:ConceptScheme → subject of skos:hasTopConcept (the scheme owns the top link)
            // Verified survivors as OWLAnnotationAssertion after reload: prefLabel(2816),
            // definition(2816), example(2816), narrower/broader(1407), broadMatch(57), closeMatch(10),
            // narrowMatch(3), hasTopConcept(1). See OwlE2EGenerationValidationTests (#486).
            // In-memory ontologies (rdf:type present) take the early-return above and are unaffected.
            var typeUri = typeResource.ToString();
            if (typeUri == SKOSVocabulary.Concept.ToString())
                return GetAnnotationSubjectsByProperty(SKOSVocabulary.PrefLabel);
            if (typeUri == SKOSVocabulary.ConceptScheme.ToString())
                return GetAnnotationSubjectsByProperty(SKOSVocabulary.HasTopConcept);
            return byType;
        }

        public bool HasAnnotation(RDFResource subject, RDFResource property, RDFResource value)
        {
            return _ontology.AnnotationAxioms.OfType<OWLAnnotationAssertion>()
                .Any(a => a.AnnotationProperty.GetIRI().ToString() == property.ToString()
                    && a.SubjectIRI.ToString() == subject.ToString()
                    && a.ValueIRI != null && a.ValueIRI.ToString() == value.ToString());
        }
    }
}
