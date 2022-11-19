package org.snomed.otf.owltoolkit.conversion;

import com.google.common.collect.Sets;
import org.ihtsdo.otf.snomedboot.ReleaseImportException;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.reasoner.*;
import org.semanticweb.owlapi.reasoner.structural.StructuralReasonerFactory;
import org.semanticweb.owlapi.search.EntitySearcher;
import org.semanticweb.owlapi.search.Filters;
import org.semanticweb.owlapi.util.DefaultPrefixManager;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.snomed.otf.owltoolkit.constants.Concepts;
import org.snomed.otf.owltoolkit.ontology.OntologyService;
import org.snomed.otf.owltoolkit.ontology.render.SnomedPrefixManager;
import org.snomed.otf.owltoolkit.service.ReasonerServiceException;
import org.snomed.otf.owltoolkit.service.SnomedReasonerService;
import org.snomed.otf.owltoolkit.taxonomy.SnomedTaxonomy;
import org.snomed.otf.owltoolkit.taxonomy.SnomedTaxonomyBuilder;
import org.snomed.otf.owltoolkit.taxonomy.SnomedTaxonomyLoader;
import org.snomed.otf.owltoolkit.util.InputStreamSet;
import org.snomed.otf.owltoolkit.util.OptionalFileInputStream;
import org.springframework.util.FileCopyUtils;
import uk.ac.manchester.cs.owlapi.modularity.ModuleType;
import uk.ac.manchester.cs.owlapi.modularity.SyntacticLocalityModuleExtractor;

import java.io.*;
import java.util.*;
import java.util.stream.Collectors;

import static org.semanticweb.owlapi.model.parameters.Imports.INCLUDED;

public class RF2ToOWLService {

	private static final Set<String> DEFAULT_NAMESPACES = Sets.newHashSet(
			"Prefix(xml:=<http://www.w3.org/XML/1998/namespace>)",
			"Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)",
			"Prefix(owl:=<http://www.w3.org/2002/07/owl#>)",
			"Prefix(rdf:=<http://www.w3.org/1999/02/22-rdf-syntax-ns#>)",
			"Prefix(rdfs:=<http://www.w3.org/2000/01/rdf-schema#>)",
			"Prefix(:=<http://snomed.info/id/>)"
	);

	private final Logger logger = LoggerFactory.getLogger(getClass());
	public static final String HEADER_PREFIX = "Ontology(<";
	public static final String HEADER_SUFFIX = ">)";

	public void convertRF2ArchiveToOWL(String ontologyUriOverride, String versionDate, boolean includeDescriptions, InputStreamSet snomedRf2SnapshotArchives,
			OptionalFileInputStream deltaStream, OutputStream owlFileOutputStream,
									   String filter) throws ConversionException {

		// Load required parts of RF2 into memory
		logger.info("Loading RF2 files");
		SnomedTaxonomy snomedTaxonomy;
		try {
			snomedTaxonomy = new SnomedTaxonomyBuilder().build(snomedRf2SnapshotArchives, deltaStream.getInputStream().orElse(null), includeDescriptions);
		} catch (ReleaseImportException e) {
			throw new ConversionException("Failed to load RF2 archive.", e);
		}


		if (snomedTaxonomy.getStatedRelationships().isEmpty() && snomedTaxonomy.getAxiomCount() == 0) {
			throw new ConversionException("No Stated Relationships or Axioms were found. An Ontology file can not be produced.");
		}

		String ontologyUri;
		if (ontologyUriOverride != null && !ontologyUriOverride.isEmpty()) {
			ontologyUri = ontologyUriOverride;
		} else {
			Collection<String> ontologyHeaders = snomedTaxonomy.getOntologyHeader().values();
			String ontologyHeader;
			if (ontologyHeaders.size() > 1) {
				throw new ConversionException("Multiple active Ontology identifiers found. " +
						"An extension should make other Ontology identifier records inactive when adding its own. " + ontologyHeaders.toString());
			} else if (ontologyHeaders.isEmpty()) {
				logger.warn("No Ontology identifier found. Using default identifier {}", OntologyService.SNOMED_INTERNATIONAL_EDITION_URI);
				ontologyHeader = HEADER_PREFIX + OntologyService.SNOMED_INTERNATIONAL_EDITION_URI + HEADER_SUFFIX;
			} else {
				ontologyHeader = ontologyHeaders.iterator().next();
			}
			if (!ontologyHeader.startsWith(HEADER_PREFIX) || !ontologyHeader.endsWith(HEADER_SUFFIX)) {
				throw new ConversionException(String.format("Ontology header should start with '%s' and end with '%s' but this found '%s'", HEADER_PREFIX, HEADER_SUFFIX, ontologyHeader));
			}
			ontologyUri = ontologyHeader.substring(HEADER_PREFIX.length(), ontologyHeader.length() - 2);
		}

		// Fetch attributes which are not grouped within the MRCM Attribute Domain International reference set.
		Set<Long> neverGroupedRoles = snomedTaxonomy.getUngroupedRolesForContentTypeOrDefault(Long.parseLong(Concepts.ALL_PRECOORDINATED_CONTENT));

		// Create OWL Ontology from stated relationships and OWL Axiom reference set
		// using list of never grouped roles during relationship to axiom conversion
		logger.info("Building Ontology");
		OntologyService ontologyService = new OntologyService(neverGroupedRoles);
		OWLOntology ontology;
		try {
			ontology = ontologyService.createOntology(snomedTaxonomy, ontologyUri, versionDate, includeDescriptions);
			OWLDataFactory df = OWLManager.getOWLDataFactory();
			SnomedPrefixManager prefixManager = ontologyService.getSnomedPrefixManager();
			OWLClass filteredClass = df.getOWLClass(":"+ filter, prefixManager);

			Set<OWLEntity> sig = new HashSet<>();
			sig.add(filteredClass);
			// We now add all subclasses (direct and indirect) of the chosen
			// classes.
			Set<OWLEntity> seedSig = new HashSet<>();
			OWLReasonerFactory reasonerFactory = null;
			try {
				reasonerFactory = getOWLReasonerFactory(SnomedReasonerService.ELK_REASONER_FACTORY.toString());
			} catch (ReasonerServiceException e) {
				throw new RuntimeException(e);
			}
			final OWLReasonerConfiguration configuration = new SimpleConfiguration(new ConsoleProgressMonitor());
			OWLReasoner reasoner = reasonerFactory.createReasoner(ontology, configuration);
			for (OWLEntity ent : sig) {
				seedSig.add(ent);
				// Retrieve the sub and super classes
				if (ent.isOWLClass()) {
					NodeSet<OWLClass> subClasses = reasoner.getSubClasses(ent.asOWLClass(), false);
					seedSig.addAll(subClasses.getFlattened());
					NodeSet<OWLClass> superClasses = reasoner.getSuperClasses(ent.asOWLClass(), false);
					seedSig.addAll(superClasses.getFlattened());
				}
			}

			// Retrieve a specific module
			SyntacticLocalityModuleExtractor sme =
					new SyntacticLocalityModuleExtractor(ontologyService.getManager(), ontology, ModuleType.STAR);
			Set<OWLAxiom> reasonedAxioms = sme.extract(seedSig);

			// Get all subclass and superclass axioms for selected class
			Collection<OWLAxiom> subClassOfFilterAxioms =
					ontology.filterAxioms(Filters.subClassWithSub, filteredClass, INCLUDED);
			reasonedAxioms.addAll(subClassOfFilterAxioms);
			Collection<OWLAxiom> superClassOfFilterAxioms =
					ontology.filterAxioms(Filters.subClassWithSuper, filteredClass, INCLUDED);
			reasonedAxioms.addAll(superClassOfFilterAxioms);
			/*Collection<OWLAxiom> axioms3 =
					ontology.filterAxioms(Filters.axiomsFromTBoxAndRBox, filteredClass, INCLUDED);
			Collection<OWLAxiom> axioms4 =
					ontology.filterAxioms(Filters.axiomsNotInTBoxOrRBox, filteredClass, INCLUDED);
			Collection<OWLAxiom> axioms5 =
					ontology.filterAxioms(Filters.apDomainFilter, filteredClass, INCLUDED);*/

			// Get all relevant Annotation Axioms
			Set<OWLAnnotationAssertionAxiom> annotationFilterAxioms = ontology.getAnnotationAssertionAxioms(filteredClass.getIRI());
			reasonedAxioms.addAll(annotationFilterAxioms);

			OWLOntologyManager owlOntologyManager = OWLManager.createOWLOntologyManager();
			ontology = owlOntologyManager.createOntology(reasonedAxioms);
		} catch (OWLOntologyCreationException e) {
			throw new ConversionException("Failed to build OWL Ontology from SNOMED taxonomy.", e);
		}

		// Write to any non-default namespaces to OutputStream
		Set<String> extraOntologyNamespaces = snomedTaxonomy.getOntologyNamespaces().values().stream()
				.filter(namespace -> !DEFAULT_NAMESPACES.contains(namespace)).collect(Collectors.toSet());
		if (!extraOntologyNamespaces.isEmpty()) {
			try {
				BufferedWriter writer = new BufferedWriter(new OutputStreamWriter(owlFileOutputStream));
				writer.write(getCopyrightNotice());
				writer.newLine();
				for (String extraOntologyNamespace : extraOntologyNamespaces) {
					writer.write(extraOntologyNamespace);
					writer.newLine();
				}
				writer.flush();
			} catch (IOException e) {
				throw new ConversionException("Failed to write ontology namespaces to output stream.", e);
			}
		}

		// Write ontology to OutputStream
		try {
			ontologyService.saveOntology(ontology, owlFileOutputStream);
		} catch (OWLOntologyStorageException e) {
			throw new ConversionException("Failed to serialise and write OWL Ontology to output stream.", e);
		}

		logger.info("RF2 to OWL Ontology conversion complete.");
	}

	protected String getCopyrightNotice() throws IOException {
		return FileCopyUtils.copyToString(new InputStreamReader(getClass().getResourceAsStream("/owl-file-copyright-notice.txt")));
	}

	private OWLReasonerFactory getOWLReasonerFactory(String reasonerFactoryClassName) throws ReasonerServiceException {
		Class<?> reasonerFactoryClass = null;
		try {
			reasonerFactoryClass = Class.forName(reasonerFactoryClassName);
			return (OWLReasonerFactory) reasonerFactoryClass.newInstance();
		} catch (ClassNotFoundException e) {
			throw new ReasonerServiceException(String.format("Requested reasoner class '%s' not found.", reasonerFactoryClassName), e);
		} catch (InstantiationException | IllegalAccessException e) {
			throw new ReasonerServiceException(String.format("An instance of requested reasoner '%s' could not be created.", reasonerFactoryClass), e);
		}
	}

}
