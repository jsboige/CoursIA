# -*- coding: utf-8 -*-
"""Tests de la chaine d'etiquetage humour par LLM local (#26911, etape 2).

Les tests sont **hors reseau** : un faux annotateur remplace l'endpoint, et
ce qui est verifie ici est le contrat de la chaine -- tracabilite, taxonomie
lue chez l'organe (pas recopiee), echantillon deterministe, marquage de la
provenance et invariant "donnees augmentees hors du jeu d'evaluation" -- plus
la compatibilite de format avec l'instrument d'accord existant
(``ict.humor_agreement``), qui lit les enregistrements produits ici.
"""

from __future__ import annotations

import json
import re
import tempfile
import unittest
from pathlib import Path

from ict.humor_agreement import (
    chance_kappa_distribution,
    cohen_kappa,
    read_annotations_jsonl,
)
from ict.humor_llm_chain import (
    PROMPT_VERSION,
    SOURCE_AUGMENTED,
    SOURCE_REAL,
    LocalLLMAnnotator,
    build_evaluation_sample,
    build_evaluation_set,
    build_prompt,
    build_rubric,
    build_rubric_reversed,
    portable_pointer,
    read_env_value,
    reference_nature,
    sample_stratified,
    taxonomy_labels,
    validate_provenance,
)
from ict.humor_llm_chain import annotate_items, augment_items, write_campaign


class FakeAnnotator(LocalLLMAnnotator):
    """Annotateur de substitution : aucun appel reseau, sortie deterministe."""

    def __init__(self, labels: list[str] | None = None, **kwargs):
        super().__init__(**kwargs)
        self._labels = labels or []
        self.calls: list[tuple[str, str]] = []

    def label(self, text: str, *, variant: str = "principal"):
        self.calls.append((text, variant))
        label = self._labels[(len(self.calls) - 1) % len(self._labels)] if self._labels else "rien"
        return {
            "label": label,
            "raison": "raison de test",
            "served_model": "fake-model",
            "prompt_tokens": 10,
            "completion_tokens": 2,
            "prompt_version": PROMPT_VERSION,
            "variant": variant,
            "seed": self.seed,
            "temperature": self.temperature,
            "top_p": self.top_p,
            "max_tokens": self.max_tokens,
        }

    def augment(self, text: str):
        self.calls.append((text, "augment"))
        return {
            "paraphrase": f"paraphrase de {text}",
            "served_model": "fake-model",
            "prompt_tokens": 8,
            "completion_tokens": 4,
            "prompt_version": PROMPT_VERSION,
            "seed": self.seed,
            "source": SOURCE_AUGMENTED,
        }


ITEMS = [
    {"id": "i1", "texte": "une blague"},
    {"id": "i2", "texte": "une phrase plate"},
    {"id": "i3", "texte": "une autre blague"},
]


class TestTaxonomie(unittest.TestCase):
    def test_taxonomie_lue_chez_organe(self):
        # La taxonomie n'est pas recopiee : elle vient de l'organe du banc.
        from ict.humor_pairs import LABELS

        self.assertEqual(tuple(taxonomy_labels()), tuple(LABELS))
        self.assertEqual(len(set(taxonomy_labels())), 5)

    def test_rubric_couvre_la_taxonomie(self):
        rubric = build_rubric()
        self.assertEqual(
            [entry.label for entry in rubric], list(taxonomy_labels())
        )
        for entry in rubric:
            self.assertTrue(entry.description.strip())

    def test_rubric_inverse_est_la_permutation(self):
        forward = [entry.label for entry in build_rubric()]
        backward = [entry.label for entry in build_rubric_reversed()]
        self.assertEqual(backward, list(reversed(forward)))


class TestPrompt(unittest.TestCase):
    def test_prompt_principal_contient_texte_et_version(self):
        prompt = build_prompt("un texte a etiqueter")
        self.assertIn("un texte a etiqueter", prompt)
        self.assertIn(PROMPT_VERSION, prompt)
        for label in taxonomy_labels():
            self.assertIn(label, prompt)

    def test_prompt_de_controle_diffeere_du_principal(self):
        principal = build_prompt("t", variant="principal")
        controle = build_prompt("t", variant="controle")
        self.assertNotEqual(principal, controle)
        # l'ordre de presentation est inverse dans la variante de controle
        self.assertLess(
            principal.index(taxonomy_labels()[0]), principal.index(taxonomy_labels()[1])
        )
        self.assertLess(
            controle.index(taxonomy_labels()[1]), controle.index(taxonomy_labels()[0])
        )

    def test_variante_inconnue_refusee(self):
        with self.assertRaises(ValueError):
            build_prompt("t", variant="inconnue")


class TestEnv(unittest.TestCase):
    def test_lecture_cle(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / ".env"
            path.write_text('VLLM_API_KEY="secret-test"\n# comment\nOTHER=1\n', encoding="utf-8")
            # Forme NON interpolante (#17276) : une assertion qui interpole la
            # valeur lue la fait sortir en clair dans le log d'ECHEC. On
            # compare donc par un booleen -- le message reste
            # "False is not true" et ne contient aucune valeur.
            valeur = read_env_value(path, "VLLM_API_KEY")
            self.assertTrue(valeur == "secret-test")
            self.assertTrue(read_env_value(path, "ABSENT") is None)

    def test_fichier_absent(self):
        self.assertTrue(
            read_env_value("/chemin/qui/nexiste/pas.env", "VLLM_API_KEY") is None
        )

    def test_trace_ne_contient_pas_la_cle(self):
        annotator = LocalLLMAnnotator(api_key="secret-test")
        self.assertNotIn("secret-test", repr(annotator.trace()))
        self.assertNotIn("api_key", annotator.trace())


class TestRubriqueCalibration(unittest.TestCase):
    """Garde-fou contre la classe de defaut de la version 1 du prompt.

    La version 1 exigeait un « marqueur de rire explicite » pour
    ``humour_reussi`` et ``rire_sans_recadrage``. Verification a la source sur
    le corpus **commite** : aucune des 30 blagues manuelles ne porte de
    marqueur de rire litteral. Une rubrique qui exige un marqueur absent du
    corpus rend la categorie inatteignable et ecrase l'echantillon vers
    « rien » -- le desaccord mesure etait alors un desaccord de definition.

    Ces deux tests sont le **temoin** de ce constat : ils lisent le corpus du
    depot, ils ne se fient ni a la memoire ni a une intention declaree.
    """

    #: Marqueurs de rire litteraux, tous graphies confondues.
    _MARKER = re.compile(r"hah|heh|hihihi|lol|\bxd\b|wdt|:p", re.IGNORECASE)

    @staticmethod
    def _corpus():
        from ict.humor_pairs import load_corpus_dur

        return load_corpus_dur()

    def test_le_corpus_ne_contient_presque_pas_de_marqueur_de_rire(self):
        """Fait mesure sur le corpus : une rubrique « marqueur » serait vaine."""
        corpus = self._corpus()
        manual = [item for item in corpus if item.get("source") != "ArgumentumGames/Argumentum"]
        self.assertEqual(len(manual), 60)
        with_marker = [
            item for item in manual if self._MARKER.search(str(item["texte"]))
        ]
        self.assertEqual(
            len(with_marker),
            0,
            "le corpus manuel contient des marqueurs de rire : la rubrique "
            "v2 ne doit plus en dépendre",
        )

    def test_la_rubrique_n_exige_pas_de_marqueur_de_rire(self):
        for entry in build_rubric():
            self.assertNotIn(
                "marqueur de rire explicite",
                entry.description,
                f"la rubrique de {entry.label} exige un marqueur de rire : "
                "c'est la definition v1, mesuree non satisfiable sur le corpus",
            )
        # ... et elle dit explicitement ce qu'elle entend par « rire ».
        humour = next(
            entry for entry in build_rubric() if entry.label == "humour_reussi"
        )
        self.assertIn("construit pour faire rire", humour.description)


class TestPopulationReference(unittest.TestCase):
    """La population d'evaluation distingue les deux origines de label."""

    @staticmethod
    def _corpus():
        from ict.humor_pairs import load_corpus_dur

        return load_corpus_dur()

    def test_echantillon_Contient_tous_les_items_a_etiquette_humaine(self):
        corpus = self._corpus()
        sample, manual, heuristic = build_evaluation_sample(
            corpus, arg_per_label=3, seed=20261116
        )
        self.assertEqual(len(manual), 60)
        self.assertEqual(len(heuristic), 15)
        self.assertEqual(len(sample), 75)
        # l'echantillon est la concatenation des deux populations, sans doublon
        self.assertEqual(
            len({str(item["id"]) for item in sample}), len(sample)
        )

    def test_nature_de_la_reference_est_lue_dans_le_corpus(self):
        nature = reference_nature(self._corpus())
        self.assertEqual(nature["heuristique-declaree"]["n"], 60)
        self.assertEqual(nature["jugement-manuel"]["n"], 60)


class TestEchantillon(unittest.TestCase):
    def test_echantillon_deterministe(self):
        corpus = [
            {"id": f"x{index}", "label": "a" if index % 2 else "b"} for index in range(20)
        ]
        first = sample_stratified(
            corpus, label_of=lambda item: item["label"], per_label=3, seed=7
        )
        second = sample_stratified(
            corpus, label_of=lambda item: item["label"], per_label=3, seed=7
        )
        self.assertEqual([item["id"] for item in first], [item["id"] for item in second])

    def test_echantillon_stratifie(self):
        corpus = [
            {"id": f"x{index}", "label": "a" if index % 2 else "b"} for index in range(20)
        ]
        sample = sample_stratified(
            corpus, label_of=lambda item: item["label"], per_label=3, seed=7
        )
        counts = {"a": 0, "b": 0}
        for item in sample:
            counts[item["label"]] += 1
        self.assertEqual(counts, {"a": 3, "b": 3})

    def test_graine_differente_donne_un_autre_echantillon(self):
        corpus = [
            {"id": f"x{index}", "label": "a" if index % 2 else "b"} for index in range(20)
        ]
        first = sample_stratified(
            corpus, label_of=lambda item: item["label"], per_label=3, seed=7
        )
        second = sample_stratified(
            corpus, label_of=lambda item: item["label"], per_label=3, seed=8
        )
        self.assertNotEqual([item["id"] for item in first], [item["id"] for item in second])


class TestProvenance(unittest.TestCase):
    def _records(self):
        annotator = FakeAnnotator(labels=["humour_reussi", "rien"])
        records = annotate_items(
            ITEMS,
            annotator,
            annotator_name="vllm:fake:p1",
            corpus="humour_banc",
            label_of=lambda item: "rien",
        )
        return annotator, records

    def test_enregistrements_lisibles_par_l_instrument(self):
        annotator, records = self._records()
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "annotations.jsonl"
            written = write_campaign(records, path)
            self.assertEqual(written, len(records))
            relu = read_annotations_jsonl(path)
            self.assertEqual(len(relu), len(records))
            self.assertEqual(relu[0]["annotator"], "vllm:fake:p1")
            self.assertIn("label", relu[0])

    def test_trace_dans_chaque_enregistrement(self):
        _, records = self._records()
        for record in records:
            self.assertEqual(record["prompt_version"], PROMPT_VERSION)
            self.assertEqual(record["served_model"], "fake-model")
            self.assertEqual(record["seed"], 20261116)
            self.assertIn("temperature", record)
            self.assertIn("top_p", record)

    def test_augmente_hors_du_jeu_evaluation(self):
        annotator = FakeAnnotator()
        records = augment_items(
            ITEMS, annotator, annotator_name="vllm:fake:aug", corpus="humour_banc"
        )
        for record in records:
            self.assertEqual(record["source"], SOURCE_AUGMENTED)
            self.assertFalse(record["in_evaluation_set"])
        evaluation = build_evaluation_set(records)
        self.assertEqual(evaluation, [])

    def test_augmente_declare_dans_le_jeu_evaluation_refuse(self):
        annotator = FakeAnnotator()
        records = augment_items(
            ITEMS, annotator, annotator_name="vllm:fake:aug", corpus="humour_banc"
        )
        records[0]["in_evaluation_set"] = True
        with self.assertRaises(ValueError):
            build_evaluation_set(records)

    def test_source_inconnue_refusee(self):
        _, records = self._records()
        records[0]["source"] = "banc-ampoule"
        with self.assertRaises(ValueError):
            validate_provenance(records)

    def test_champ_manquant_refuse(self):
        _, records = self._records()
        del records[0]["in_evaluation_set"]
        with self.assertRaises(ValueError):
            validate_provenance(records)

    def test_reels_conserves_augmentes_exclus(self):
        annotator = FakeAnnotator()
        reels = annotate_items(
            ITEMS, annotator, annotator_name="vllm:fake:p1", corpus="humour_banc"
        )
        augmentes = augment_items(
            ITEMS, annotator, annotator_name="vllm:fake:aug", corpus="humour_banc"
        )
        evaluation = build_evaluation_set(reels + augmentes)
        self.assertEqual(len(evaluation), len(reels))
        self.assertTrue(all(record["source"] == SOURCE_REAL for record in evaluation))


class TestTemoinNegatif(unittest.TestCase):
    """Un annotateur nul ne doit pas produire d'accord hors de la bande."""

    def test_annotateur_permute_ne_produit_pas_d_accord(self):
        reference = ["humour_reussi", "rien"] * 8
        nul = list(reversed(reference))
        summary = cohen_kappa(reference, nul)
        chance = chance_kappa_distribution(reference, nul)
        self.assertLessEqual(summary["kappa"], chance["p95"] + 1e-9)

    def test_bande_du_hasard_est_calculee(self):
        reference = ["humour_reussi", "rien"] * 8
        chance = chance_kappa_distribution(reference, list(reference), n_draws=50, seed=1)
        self.assertEqual(chance["n_draws"], 50)
        self.assertIsNotNone(chance["p95"])


class TestPointeurPortable(unittest.TestCase):
    """Un rapport commite ne porte ni chemin de poste ni disposition du siege.

    Le pointeur d'un artefact de campagne est un **nom de fichier** : le
    chemin local devient faux des le premier nettoyage du scratch, et il
    expose la disposition de la machine qui a produit le rapport. L'identite
    du corpus est portee par son URL et son empreinte.
    """

    #: Rapport(s) produit(s) par la campagne, tel(s) qu'il(s) sont commites.
    RAPPORTS = ("humor_llm_chain_c26911.json", "humor_llm_chain_c26911_v1.json")

    @staticmethod
    def _strings(payload):
        if isinstance(payload, str):
            yield payload
        elif isinstance(payload, dict):
            for value in payload.values():
                yield from TestPointeurPortable._strings(value)
        elif isinstance(payload, list):
            for value in payload:
                yield from TestPointeurPortable._strings(value)

    def test_portable_pointer_ne_garde_que_le_nom(self):
        self.assertEqual(
            portable_pointer("D:\\poste-de-test\\scratch\\humor_chain\\annotations.jsonl"),
            "annotations.jsonl",
        )
        self.assertEqual(
            portable_pointer("/home/agent/.tmp/humor_chain/dialogs_from_jokes.dataset.json"),
            "dialogs_from_jokes.dataset.json",
        )
        self.assertEqual(portable_pointer("annotations.jsonl"), "annotations.jsonl")
        # Separateurs melanges : le pointeur doit les traiter tous les deux,
        # quelle que soit la plateforme qui a produit le chemin.
        self.assertEqual(
            portable_pointer("D:/poste-de-test\\scratch/annotations.jsonl"),
            "annotations.jsonl",
        )

    def test_rapports_commites_ne_portent_aucun_chemin_de_poste(self):
        results_dir = Path(__file__).resolve().parents[1] / "results"
        for nom in self.RAPPORTS:
            chemin = results_dir / nom
            self.assertTrue(chemin.is_file(), f"rapport absent : {nom}")
            brut = chemin.read_text(encoding="utf-8")
            for valeur in self._strings(json.loads(brut)):
                self.assertIsNone(
                    re.match(r"^[A-Za-z]:[\\/]", valeur),
                    f"chemin de poste dans {nom} : {valeur!r}",
                )

    def test_pointeurs_des_rapports_sont_des_noms_de_fichier(self):
        results_dir = Path(__file__).resolve().parents[1] / "results"
        for nom in self.RAPPORTS:
            rapport = json.loads((results_dir / nom).read_text(encoding="utf-8"))
            pointeurs = [
                rapport["artifacts"]["annotations_jsonl"],
                rapport["corpora"]["cc0"]["local_copy"],
            ]
            for pointeur in pointeurs:
                self.assertNotIn("/", pointeur)
                self.assertNotIn("\\", pointeur)
            self.assertEqual(
                rapport["corpora"]["cc0"]["local_copy"],
                "dialogs_from_jokes.dataset.json",
            )
            self.assertEqual(
                rapport["artifacts"]["annotations_jsonl"], "annotations.jsonl"
            )


if __name__ == "__main__":
    unittest.main()
