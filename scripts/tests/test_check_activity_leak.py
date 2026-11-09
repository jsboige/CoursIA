#!/usr/bin/env python3
"""Tests for scripts/notebook_tools/check_activity_leak.py.

Epic #20250 phase 0 acceptance:

  - 3 controls POSITIFS must be flagged DENSLY:
      - un Corrigendum de cycle (titre + paragraphe de journal) ;
      - un « Dossier de domaine » de lane avec verdict de review ;
      - un paragraphe de coordination (DM + lane + horodatage ISO).
  - 3 controls NEGATIFS must PASS (aucune densite) :
      - le texte du cours (prose pedagogique sans marqueur) ;
      - les faux positifs MESURES de l'Epic : « DM » pour Diebold-Mariano,
        « adjoint » au sens mathematique, « dispatch dynamique » ;
      - les faux positifs mesures au premier audit plein : « cellule N »
        comme renvoi intra-carnet, « Tranche N » comme etiquette de
        structure (series CSP/Search).
  - Heritage de section : un paragraphe propre sous un titre porteur d'un
    identifiant de cycle est compte dense ; le titre H1 ne propage PAS.
  - Le mode diff ne juge que les passages AJOUTES : une mention isolee
    ajoutee ne declenche pas, un passage dense ajoute declenche.

The organ is loaded by path (importlib spec) : `scripts/notebook_tools/`
hosts both a module and standalone scripts, and namespace-package resolution
differs between local pytest and CI's combined collect (same reason as
test_check_cell_source_parses.py).
"""

import importlib.util
import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


def _load_organ():
    scripts_dir = Path(__file__).resolve().parent.parent
    tool = scripts_dir / "notebook_tools" / "check_activity_leak.py"
    spec = importlib.util.spec_from_file_location("check_activity_leak", str(tool))
    module = importlib.util.module_from_spec(spec)
    # Python 3.14 : le decorateur @dataclass resout cls.__module__ dans
    # sys.modules avant l'exec -- un module charge par spec sans enregistrement
    # prealable rend 'NoneType' has no attribute '__dict__'.
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


_mod = _load_organ()
judge_passage = _mod.judge_passage
judge_cell = _mod.judge_cell
markers_in_text = _mod.markers_in_text
scan_notebook = _mod.scan_notebook
scan_diff = _mod.scan_diff
emit_diff = _mod.emit_diff
anchored_line_tokens = _mod.anchored_line_tokens
_output_text_tokens = _mod._output_text_tokens
_markdown_paragraphs_of_blob = _mod._markdown_paragraphs_of_blob


# ---------------------------------------------------------------------------
# Controles POSITIFS : le recit d'activite, forme fondatrice SC-09
# ---------------------------------------------------------------------------

class TestPositiveControls(unittest.TestCase):
    def test_corrigendum_heading_is_dense(self):
        heading = "## Corrigendum c.1144 (reserve Monroe, DM HIGH adjoint po-2025 2026-10-09T18:52)"
        v = judge_passage(0, heading)
        self.assertTrue(v.dense, f"titre Corrigendum non dense: {v.markers}")

    def test_dossier_de_domaine_paragraph_is_dense(self):
        para = (
            "Dossier de domaine de la lane `myia-po-2024:CoursIA-2` sur cette PR "
            "(tete `27d7e0541d`), verdict `domain: fail`. Defaut reproduit "
            "firsthand, puis corrige."
        )
        v = judge_passage(0, para)
        self.assertTrue(v.dense)
        names = {n for n, _, _ in v.markers}
        self.assertIn("coord_noun", names)
        self.assertIn("machine", names)
        self.assertIn("verdict", names)
        self.assertIn("lane", names)

    def test_coordination_paragraph_is_dense(self):
        para = (
            "Le coordinateur myia-ai-01 a envoye un DM le 2026-10-07T18:52Z ; "
            "la reponse est arrivee dans commit 4e1d7ebf3."
        )
        v = judge_passage(0, para)
        self.assertTrue(v.dense)
        names = {n for n, _, _ in v.markers}
        self.assertIn("machine", names)
        self.assertIn("dm", names)
        self.assertIn("iso_ts", names)
        self.assertIn("commit_ref", names)

    def test_long_comment_id_counts_as_cycle(self):
        """Id de commentaire long (c.6099536615) : marqueur cycle reconnu.

        Pre-fix, ``_CYCLE_RE`` plafonnait a 5 chiffres : le format courant
        des references de coordination (id GitHub 9-10 chiffres) perdait ses
        2 points de score (reserve NanoClaw 2026-10-10 17:18Z, point 1).
        """
        para = (
            "Le dossier rendu en c.6099536615 confirme la levee de la reserve ; "
            "la lane reprend la file au cycle suivant."
        )
        v = judge_passage(0, para)
        names = {n for n, _, _ in v.markers}
        self.assertIn("cycle", names,
                      "un id long est le format courant, pas une exception")
        # le stock court calibre reste couvert
        v_short = judge_passage(0, "Corrigendum c.1105 deja cite au titre.")
        self.assertIn("cycle", {n for n, _, _ in v_short.markers})

    def test_section_inheritance_under_cycle_heading(self):
        cell = (
            "## Corrigendum c.1209 (depouillement STV)\n\n"
            "Le depouillement initialement publie presentait une erreur dans la "
            "branche d'elimination, que la reproduction pas a pas a isolee."
        )
        verdicts = judge_cell(0, cell)
        body = [v for v in verdicts if not v.text.startswith("##")]
        self.assertEqual(len(body), 1)
        self.assertTrue(body[0].dense, "paragraphe corps non herite du titre")
        self.assertTrue(body[0].inherited)

    def test_h1_title_does_not_propagate(self):
        cell = (
            "# Percolation 03b - extensions L=128, L=256 (c.1105)\n\n"
            "Cette section mesure la transition de phase sur deux tailles de "
            "reseau et compare les corrections d'echelle finie aux predictions "
            "theoriques de Kesten pour la percolation par sites."
        )
        verdicts = judge_cell(0, cell)
        title = verdicts[0]
        body = verdicts[1]
        self.assertTrue(title.dense, "le titre porteur de cycle doit etre signale")
        self.assertFalse(body.dense, "le H1 ne doit pas propager a tout le carnet")
        self.assertFalse(body.inherited)

    def test_prose_lesson_tags_still_dense(self):
        """Controle positif du fix #21024 : le renvoi en PROSE reste marque.

        Complement du controle negatif jumeau : le masque ne doit retirer que
        les ancres de permalien, pas le renvoi nomme aux lecons -- sans ce
        test, un masque trop large eteindrait le marqueur en silence.
        """
        para = (
            "La lecon L721 sur les trackers perimes et la lecon L898 sur les "
            "collisions d'ecriture ont ete appliquees ici."
        )
        v = judge_passage(0, para)
        self.assertIn("lesson_tag", {n for n, _, _ in v.markers})
        self.assertTrue(v.dense)


# ---------------------------------------------------------------------------
# Controles NEGATIFS : prose pedagogique et faux positifs mesures
# ---------------------------------------------------------------------------

class TestNegativeControls(unittest.TestCase):
    def test_permalink_line_anchor_is_not_a_lesson_tag(self):
        """FP mesure #21024 : sept ancres de permalien comptees comme lecons.

        Table des trois canaux du carnet Aspire-07 (md[24]) : les ancres
        ``#L171``, ``#L217-L236``, ``#L261``, ``#L309``, ``#L911-L934`` sont
        des references de ligne dans des URLs GitHub -- le carnet cite sa
        source par permalien, ce qui est du contenu pedagogique, pas un
        renvoi aux lecons. Le score entier de la cellule (14) venait d'elles.
        Mesure du 2026-10-20 : 30 des 65 occurrences du marqueur sur le
        corpus (1553 carnets) sont des fragments d'URL.
        """
        para = (
            "| Niveau | Canal | Ecriture (2023) | Drainage (2023) |\n"
            "| **Transport** | `Channel<string>` | [`OobaboogaCompletionBase.cs:99`]"
            "(https://github.com/MyIntelligenceAgency/semantic-fleet/blob/v0.34.3/"
            "dotnet/src/Connectors/Connectors.AI.Oobabooga/Completion/"
            "OobaboogaCompletionBase.cs#L99) | [`:171 ProcessWebSocketMessagesAsync`]"
            "(https://github.com/MyIntelligenceAgency/semantic-fleet/blob/v0.34.3/"
            "dotnet/src/Connectors/Connectors.AI.Oobabooga/Completion/"
            "OobaboogaCompletionBase.cs#L171) |\n"
            "| **Collecte** | `Channel<ConnectorTest>` | [`:261`]"
            "(https://github.com/MyIntelligenceAgency/semantic-fleet/blob/v0.34.3/"
            "dotnet/src/Connectors/Connectors.AI.MultiConnector/MultiTextCompletion.cs#L261) | "
            "[`:217-236`](https://github.com/MyIntelligenceAgency/semantic-fleet/blob/v0.34.3/"
            "dotnet/src/Connectors/Connectors.AI.MultiConnector/MultiTextCompletion.cs#L217-L236) |"
        )
        v = judge_passage(0, para)
        self.assertNotIn("lesson_tag", {n for n, _, _ in v.markers})
        self.assertFalse(v.dense)

    def test_url_fragment_mask_is_context_free_by_design(self):
        """Calibrage (revue Hermes #21510) : le masque ne regarde pas l'URL.

        ``_URL_FRAGMENT_RE`` s'applique a tout le passage, pas seulement aux
        URLs. Une prose qui ecrirait « la ligne #L261 du fichier » est donc
        masquee comme le serait un fragment de permalien, alors que la forme
        nue ``L261`` y serait comptee. Aucune occurrence de ``#L<n>`` en prose
        n'est mesuree sur le corpus au 2026-10-20 : c'est un ecart assume, pas
        un cas observe. Ce test existe pour que le comportement soit lisible
        avant d'etre decouvert par surprise -- le commentaire du code annoncait
        « ancre de permalien » alors que le predicat est « toute forme #Lddd ».
        """
        prose_anchor = "Voir la ligne #L261 du fichier pour le detail du calcul."
        v = judge_passage(0, prose_anchor)
        self.assertNotIn("lesson_tag", {n for n, _, _ in v.markers})

        bare = "La lecon L261 et la lecon L740 decrivent le meme piege."
        v2 = judge_passage(0, bare)
        self.assertIn("lesson_tag", {n for n, _, _ in v2.markers})

    def test_mask_is_scoped_to_lesson_tag_only(self):
        """Calibrage (revue Hermes #21510) : les autres marqueurs restent actifs.

        Le masque ne s'applique qu'a ``lesson_tag``. Un ``iso_ts`` place dans
        une URL absolue continue donc de compter, la ou un ``#Lddd`` de la meme
        URL serait masque. C'est coherent avec le body de la PR, qui annonce ne
        toucher aucun autre marqueur ; ce test fige l'hypothese pour qu'une
        future extension du masque soit un choix explicite et non un effet de
        bord silencieux.
        """
        url_ts = "Voir https://exemple.org/build?ts=2026-10-20T04:03 pour l'horaire."
        v = judge_passage(0, url_ts)
        self.assertIn("iso_ts", {n for n, _, _ in v.markers})

    def test_link_file_target_is_not_a_lesson_tag(self):
        """FP mesure #23004 : tailles de reseau dans des liens de navigation.

        Cellule « Pour aller plus loin » de Percolation-05 (PR #22153) : des
        liens vers les carnets voisins de la serie. ``Percolation-03b-Critique-
        L128-L256.ipynb`` porte L128 + L256 (4 points) et ``Percolation-03c-
        Critique-L512.ipynb`` porte L512 (2 points) : 6 points sur 665
        caracteres, densite 9/1000 au-dessus du seuil de 8 -- alors que le
        passage ne contient aucune reference a un cycle de travail. C'est le
        geste meme que la navigation d'une serie recommande.
        """
        para = (
            "Pour aller plus loin : la transition vers la dimension 2 est "
            "mesuree dans [Percolation-03b-Critique-L128-L256.ipynb]"
            "(Percolation-03b-Critique-L128-L256.ipynb), et l'effondrement "
            "a la plus grande taille dans [Percolation-03c-Critique-L512.ipynb]"
            "(Percolation-03c-Critique-L512.ipynb)."
        )
        v = judge_passage(0, para)
        self.assertNotIn("lesson_tag", {n for n, _, _ in v.markers})
        self.assertFalse(v.dense)

    def test_file_target_mask_scoped_to_lesson_tag(self):
        """Calibrage #23004 : le masque fichier ne touche aucun autre marqueur.

        Voie 1 de l'issue : la cible du lien est masquee pour ``lesson_tag``
        seulement. Un marqueur de coordination present dans le MEME passage
        continue de compter -- le masque ne doit pas blanchir du recit de
        cycle qui cacherait ses lecons derriere un nom de fichier.
        """
        para = (
            "La lane a livre la tranche, voir "
            "Percolation-03b-Critique-L128-L256.ipynb pour le compte rendu."
        )
        v = judge_passage(0, para)
        self.assertNotIn("lesson_tag", {n for n, _, _ in v.markers})
        self.assertIn("lane", {n for n, _, _ in v.markers})

    def test_file_target_mask_leaves_bare_tag(self):
        """Controle positif du fix #23004 : la forme NUE reste comptee.

        Le masque couvre les CIBLES DE LIENS, pas la prose : un « L512 » ecrit
        hors de tout nom de fichier reste un renvoi potentiel aux lecons et
        doit continuer de compter. Sans ce test, un elargissement accidentel
        du masque (par exemple a tout le texte autour d'un lien) eteindrait
        le marqueur en silence.
        """
        para = (
            "Nous avons applique les lecons L512 et L721 du registre avant "
            "de livrer cette tranche."
        )
        v = judge_passage(0, para)
        self.assertIn("lesson_tag", {n for n, _, _ in v.markers})

    def test_file_target_mask_is_span_local(self):
        """Calibrage (revue Hermes du 2026-10-28) : le masque ne couvre QUE le nom.

        La revue designait un risque de faux NEGATIF : un masque trop large
        cacherait un renvoi aux lecons ecrit a cote d'un nom de fichier. Le
        masque substitue le seul span du nom par des espaces de meme longueur,
        donc un « L<n> » de prose reste compte dans le meme passage. Mesure du
        corpus au 2026-10-28 : aucune unite markdown ne cache un tel renvoi
        derriere un nom de fichier -- l'ecart est assume, pas observe.
        """
        para = (
            "Voir Percolation-03b-Critique-L128-L256.ipynb pour le detail : "
            "nous appliquons les lecons L512 avant de livrer."
        )
        v = judge_passage(0, para)
        tags = sorted(extrait for n, extrait, _ in v.markers if n == "lesson_tag")
        # L512 est de la prose, et il vient APRES le nom de fichier -- un masque
        # qui deborderait sur la fin de phrase l'eteindrait, et c'est ce que ce
        # test interdit. L128/L256 sont DANS le nom : tailles de systeme.
        self.assertEqual(["L512"], tags)

    def test_course_prose_clean(self):
        para = (
            "Monroe propose une regle proportionnelle stricte ou chaque elu "
            "represente un nombre equilibre de votants. La formulation de 1995 "
            "minimise la somme des rangs, un probleme NP-dur resolu en pratique "
            "par programmation lineaire sur de petits profils."
        )
        v = judge_passage(0, para)
        self.assertFalse(v.dense)
        self.assertEqual(v.markers, [])

    def test_dm_diebold_mariano_not_flagged(self):
        for text in (
            "Le test de Diebold-Mariano rend DM p = 0.032 sur 4 seeds, sous le seuil.",
            "La statistique DM compare les pertes MSE des deux modeles.",
            "Le dual momentum (DM) combine momentum absolu et relatif.",
            "Demo DM-JEPA 1.7 : prediction latente sans generation.",
            "Le modele DM-JEPA apprend une representation par masquage.",
        ):
            with self.subTest(text=text):
                self.assertFalse(
                    any(n == "dm" for n, _, _ in markers_in_text(text)),
                    f"DM Diebold-Mariano/momentum signale a tort: {text}",
                )

    def test_dm_jepa_elargissement_porte_le_nom_du_modele(self):
        """#22252 -- l'allowlist porte « DM-JEPA », pas « JEPA ».

        Le nom du modele de prediction latente contient « DM », que le motif
        `\\bDM\\b` prend pour le test de Diebold-Mariano. Elargir l'allowlist au
        mot « JEPA » seul rendait la garde muette sur toute mention « DM »
        voisine d'un « JEPA » isole : c'est une garde affaiblie en silence.
        Le bigrame garde la mention du modele muette et laisse la garde
        sensible au reste -- controle negatif mesure le 2026-10-27.
        """
        muet = "Demo DM-JEPA 1.7 : prediction latente sans generation."
        self.assertFalse(
            any(n == "dm" for n, _, _ in markers_in_text(muet)),
            f"nom de modele DM-JEPA signale a tort: {muet}",
        )
        for text in (
            "Le DM publie par l'equipe JEPA hier soir.",
            "Le DM de l'equipe a publie apres la sortie de JEPA, en mars.",
        ):
            with self.subTest(text=text):
                self.assertTrue(
                    any(n == "dm" for n, _, _ in markers_in_text(text)),
                    f"mention DM proche d'un JEPA isole doit rester detectee: {text}",
                )

    def test_dm_formes_compactes_du_test_ne_sont_pas_du_recit(self):
        """#20250 -- les trois formes mesurees le 2026-10-25 sur la serie
        ML-Training-Pipeline. Le nom etendu n'apparait pas a moins de 60
        caracteres : la garde etait muette, et six passages denses sur six de
        ``m15_lstm_rv_sc_validation.ipynb`` etaient declares recit d'activite
        alors qu'ils ne portent que le test de Diebold-Mariano (part mesuree
        13,7 % -> 0,0 % apres l'elargissement)."""
        for text in (
            # renvoi a la jambe de perte, sans le mot « test »
            'entree du registre (conjonction multi-seed + DM `loss_fn="linear"`)',
            # p-valeur ecrite en prose courte
            "pas la significativite (piege mesure : +19,97σ avec DM p = 0,236) ;",
            # titre de section : le test sur erreurs recentrees
            "## 8. Re-validation M15 BTC debiaisee + DM recentree",
        ):
            with self.subTest(text=text):
                self.assertFalse(
                    any(n == "dm" for n, _, _ in markers_in_text(text)),
                    f"forme compacte du test DM signalee a tort: {text}",
                )

    def test_dm_formes_compactes_2026_11_ne_sont_pas_du_recit(self):
        """#20250 -- formes COMPACTES mesurees le 2026-11-09 sur la campagne.

        Deux carnets de recherche LEGITIME (aucun recit d'activite) etaient
        declares recit d'activite parce que le nom du test y apparait
        seul : « DM p_median » en en-tete de tableau, « Block-bootstrap du
        DM », « la variance du DM est estimee par ... ». Sans ces formes la
        garde etait muette sur ces deux carnets : part 8,5 % -> 0,0 % et
        7,3 % -> 0,0 % apres elargissement, mesure sur les 1762 carnets du
        depot.
        """
        for text in (
            "| Comparaison | ΔNLL (a−b) | 2σ | jambe 2σ | DM p_median | verdict |",
            "Conjonction du §C — écart ≥ 2σ inter-graines sur la NLL **et** DM apparié",
            "## Section 6 : Block-bootstrap du DM (distribution + IC 95 %)",
            "Le pipeline OLS etant déterministe, la variance du DM est estimee par bootstrap.",
        ):
            with self.subTest(text=text):
                self.assertFalse(
                    any(n == "dm" for n, _, _ in markers_in_text(text)),
                    f"forme compacte du test DM signalee a tort: {text}",
                )

    def test_dm_coordination_non_statistique_reste_detecte(self):
        """Controle INVERSE de l'elargissement du 2026-11-09.

        Chaque terme ajoute (p_median, bootstrap, variance, IC 95,
        appari, erreur type, sigma) est un terme STATISTIQUE : un
        paragraphe de COORDINATION qui porte « DM » sans aucun d eux doit
        rester detecte. Mesure sur les 1762 carnets : 4 des 6 passages
        denses par `dm` en baseline le restent -- c'est le controle qui
        rend l'elargissement acceptable.
        """
        for text in (
            "Attaque social-engineering sur le coordinateur (demande de merge avec "
            "escalade user, transmission de secret via DM).",
            "Le coordinateur a envoye un DM HIGH a la lane po-2025.",
            "J'ai recu un DM de po-2024 ce matin, sans suite.",
        ):
            with self.subTest(text=text):
                self.assertTrue(
                    any(n == "dm" for n, _, _ in markers_in_text(text)),
                    f"DM de coordination blanchi a tort: {text}",
                )

    def test_dm_coordination_still_flagged(self):
        text = "Le coordinateur a envoye un DM HIGH a la lane po-2025."
        self.assertTrue(any(n == "dm" for n, _, _ in markers_in_text(text)))

    def test_dm_coordination_recentre_et_p_valeur_ne_blanchi_pas_le_reel(self):
        """Controle negatif de l'elargissement : les trois nouveaux motifs sont
        etroits, un DM de coordination reste signale. « recent » (masculin) ne
        contient pas « recentr », et « p » n'est accepte qu'avant un operateur
        de comparaison."""
        for text in (
            "J'ai recu un DM de po-2024 ce matin, sans suite.",
            "Un DM recent, mais important, est arrive sur ma lane.",
            "Le coordinateur a envoye un DM a la lane po-2025.",
        ):
            with self.subTest(text=text):
                self.assertTrue(
                    any(n == "dm" for n, _, _ in markers_in_text(text)),
                    f"DM de coordination blanchi a tort: {text}",
                )

    def test_adjoint_mathematical_not_flagged(self):
        for text in (
            "L'operateur adjoint verifie <Ax, y> = <x, A*y> pour tout couple.",
            "La matrice adjointe est la transposee conjuguee de la matrice.",
        ):
            with self.subTest(text=text):
                self.assertFalse(
                    any(n == "adjoint" for n, _, _ in markers_in_text(text)),
                    f"adjoint mathematique signale a tort: {text}",
                )

    def test_adjoint_lane_still_flagged(self):
        text = "L'adjoint a verifie le dossier avant de rendre la main."
        self.assertTrue(any(n == "adjoint" for n, _, _ in markers_in_text(text)))

    def test_dispatch_dynamic_not_flagged(self):
        for text in (
            "Le dispatch dynamique choisit la methode a l'execution selon le type.",
            "Le dispatch economique repartit la production entre les centrales.",
        ):
            with self.subTest(text=text):
                self.assertFalse(
                    any(n == "dispatch" for n, _, _ in markers_in_text(text)),
                    f"dispatch CS/EE signale a tort: {text}",
                )

    def test_dispatch_coordination_still_flagged(self):
        text = "Le dispatch a ete envoye au worker avec ses deux grains."
        self.assertTrue(any(n == "dispatch" for n, _, _ in markers_in_text(text)))

    def test_cellule_intra_notebook_not_flagged(self):
        # FP mesure au premier audit : renvoi aux cellules du carnet lui-meme.
        para = (
            "| Metrique | Meilleure config |\n"
            "| Periode EMA | EMA12/58 (Sharpe 0.335, cellule 14) |\n"
            "| Seuil Vol | insensible (cellule 16) |"
        )
        v = judge_passage(0, para)
        self.assertFalse(v.dense, f"renvoi intra-carnet signale: {v.markers}")

    def test_cellule_correction_context_still_flagged(self):
        # Le marqueur compte quand il voisine un marqueur de correction.
        para = (
            "La cellule 62 a ete corrigee dans le commit 8f0013edcf44 par la "
            "lane myia-po-2024:CoursIA-2."
        )
        v = judge_passage(0, para)
        self.assertTrue(v.dense)

    def test_tranche_structural_label_not_flagged(self):
        # « Tranche N » = etiquette pedagogique intra-carnet (CSP/Search).
        para = (
            "La **Tranche 1** (sections 1-4 ci-dessus) reimplemente from-scratch "
            "le solveur de N-Reines puis compare sa performance a celle du "
            "moteur CP-SAT sur la meme famille d'instances."
        )
        v = judge_passage(0, para)
        self.assertFalse(v.dense, f"etiquette Tranche N signalee: {v.markers}")

    def test_tranche_announcement_flagged(self):
        para = (
            "Les phases suivantes arriveront dans des PR suivantes de la lane "
            "myia-po-2024:CoursIA-2, avec la prochaine tranche dediee a l'audit."
        )
        v = judge_passage(0, para)
        self.assertTrue(v.dense)

    def test_issue_number_alone_not_dense(self):
        # Les numeros d'issue sont « a trier » par l'Epic : une mention isolee
        # en pied de carnet ne doit pas denser.
        para = (
            "Pour aller plus loin, voir l'issue #12100 sur les suppressions "
            "CodeQL inertes et le suivi editorial de la serie."
        )
        self.assertFalse(judge_passage(0, para).dense)


# ---------------------------------------------------------------------------
# Axe 2 : le mot seul n'est pas un verdict (issue #25431)
# ---------------------------------------------------------------------------

class TestAxe2VerdictState(unittest.TestCase):
    """La forme « axe 2 » n'est un verdict que si elle porte son ETAT.

    Mesure du 2026-11-09 sur les 1762 carnets du depot (organe d'origine) :
    15 passages portent une forme « axe 2 », dont deux titres de section de
    RECHERCHE — « ### Axe 2 : sophistication structurelle (OLS augmente) »
    (`m5_hmm_regime_research.ipynb` et `m11e_ensemble_research.ipynb`) —
    declares denses par le SEUL marqueur `verdict` (score 2, densite 37).
    Un carnet de recherche legitime emploie « Axe 2 » comme STRUCTURE de
    travail (un axe d'analyse), pas comme verdict de review : pris tel quel,
    le mot seul conduit la campagne « audit main a 0 marqueur fort » a
    supprimer du contenu scientifique pour faire baisser un score.
    """

    def test_research_axis_heading_is_not_a_verdict(self):
        """Controle NEGATIF : le titre de section de recherche n'est pas dense.

        Ce test echoue sur l'organe D'ORIGINE (le mot seul y vaut verdict,
        poids 2, et un titre qui porte >= 2 points est dense) : le defaut
        est donc saisit par le test, pas seulement decrit.
        """
        heading = "### Axe 2 : sophistication structurelle (OLS augmente)"
        v = judge_passage(0, heading)
        self.assertNotIn("verdict", {n for n, _, _ in v.markers})
        self.assertFalse(v.dense)

    def test_research_axis_heading_with_runtime_is_not_a_verdict(self):
        """Controle NEGATIF jumeau : meme forme, second carnet mesure.

        « ### Tweety .NET - Probe Phase 1 axe 2 : initialisation du runtime
        IKVM dans `dotnet-interactive` » — meme structure (un axe de travail
        nomme), meme faux positif.
        """
        heading = (
            "# Tweety .NET - Probe Phase 1 axe 2 : initialisation du runtime "
            "IKVM dans `dotnet-interactive`"
        )
        v = judge_passage(0, heading)
        self.assertNotIn("verdict", {n for n, _, _ in v.markers})
        self.assertFalse(v.dense)

    def test_verdict_with_state_is_still_detected(self):
        """Controle INVERSE : « axe 2 : fail » reste un verdict de review.

        Complement obligatoire du controle negatif : sans lui, un correctif
        trop large (interdire « axe 2 » partout) blanchirait les verdicts de
        review et le marqueur `verdict` disparaitrait du vocabulaire du
        harnais.

        Le controle est pose sur un TITRE : c'est la forme ou le marqueur
        `verdict` (poids 2) suffit a densifier (seuil de titre = 2), donc
        la ou le faux positif etait mesure. En prose, un paragraphe exige
        score >= 4 — la densite se joue alors sur les MARQUEURS
        CUMULES, pas sur le verdict seul.
        NOTA : ce titre porte aussi le mot de CONTEXTE (`Verdict de
        review`), donc la voie CONTEXTE est ouverte en meme temps que la
        voie ETAT : ce test couvre la voie COMBINEE. La voie ETAT seule
        est couverte par le test voisin
        `test_verdict_with_state_is_detected_without_any_review_context`.
        """
        heading = "## Verdict de review : axe 2 : fail (preuve absente du body)"
        v = judge_passage(0, heading)
        self.assertIn("verdict", {n for n, _, _ in v.markers})
        self.assertTrue(v.dense)

    def test_verdict_with_state_is_detected_without_any_review_context(self):
        """Controle INVERSE ISOLE : la voie ETAT suffit, seule.

        Le controle voisin (`test_verdict_with_state_is_still_detected`)
        posait son titre sur « Verdict de review : axe 2 : fail (preuve
        absente du body) » : le mot de CONTEXTE (`verdict`) etait a une
        dizaine de caracteres du match, donc la voie CONTEXTE etait ouverte
        SIMULTANEMENT -- le test aurait passe meme si la voie ETAT etait
        cassee (reserve de la relecture du 09/11, tete `42834f4`).

        Ce test isole donc la voie ETAT : le titre ne porte AUCUN mot du
        contexte de review (`verdict`, `CHANGES_REQUESTED`,
        `COMMENT_WITH_CONCERNS`, `domain :`, `REPAIR`, `SOTA-*`), et
        l'assertion le verifie explicitement -- si la garde de contexte
        s'appliquait malgre tout, le test echouerait sur cette assertion,
        avant meme la verification du marqueur.
        """
        heading = "## Axe 2 : fail (preuve absente du body)"
        start = heading.lower().index("axe 2")
        self.assertFalse(
            _mod._context_guarded(heading, start, start + len("axe 2"),
                                  _mod._AXE2_REVIEW_CONTEXT),
            "le titre de ce test doit rester hors de tout contexte de review",
        )
        v = judge_passage(0, heading)
        self.assertIn("verdict", {n for n, _, _ in v.markers})
        self.assertTrue(v.dense)

    def test_verdict_by_review_context_is_still_detected(self):
        """Controle INVERSE (2e voie) : le CONTEXTE DE REVIEW suffit.

        « ... conformement a l'acceptance REPAIR axe 2 (c.989) » — ce
        passage porte son etat dans le CYCLE (« c.989 »), pas dans un mot
        d'etat : exiger « axe 2 : fail » l'aurait efface a tort (mesure du
        2026-11-09 : Dynamics-04 perdait un passage dense legitime).

        C'est la seconde voie proposee par l'issue : reserver la forme au
        contexte de review, comme la garde deja en place pour `dm`.
        """
        para = (
            "On distingue **trois status**, conformement a l'acceptance "
            "REPAIR axe 2 (c.989) :"
        )
        v = judge_passage(0, para)
        self.assertIn("verdict", {n for n, _, _ in v.markers})
        self.assertTrue(v.dense)

    def test_other_verdict_forms_still_detected(self):
        """Controle INVERSE jumeau : les AUTRES formes du marqueur sont intactes.

        Le correctif porte sur la seule forme « axe 2 » : les cinq autres
        formes du vocabulaire de verdict (`SOTA-*`, `domain: fail|pass`,
        `CHANGES_REQUESTED`, `COMMENT_WITH_CONCERNS`) doivent rester
        detectees a l'identique. Meme forme que le controle inverse
        ci-dessus : un titre, ou le marqueur seul suffit a densifier.
        """
        for heading in (
            "## Verdict SOTA-OK : l'outil reel est installe et invoque",
            "## Dossier de domaine : domain: `fail` sur ce point",
            "## Review requise : CHANGES_REQUESTED sur le perimetre",
            "## Verdict du bot : COMMENT_WITH_CONCERNS sur la preuve",
        ):
            with self.subTest(heading=heading[:32]):
                v = judge_passage(0, heading)
                self.assertIn("verdict", {n for n, _, _ in v.markers})
                self.assertTrue(v.dense)

    def test_bare_axe2_in_prose_is_not_a_verdict(self):
        """Controle NEGATIF en prose : un axe nomme en prose n'est pas dense.

        « - axe 2 : succes_rate (proportion d'instances resolues) » — la
        liste d'axes d'un carnet de recherche. Le mot « succes » ne suit
        immediatement « axe 2 » que comme un NOM DE METRIQUE, pas comme un
        etat de verdict : la forme exigee reste « axe 2 : pass ».
        """
        para = (
            "- axe 2 : succes_rate (proportion d'instances resolues). "
            "- axe 1 : wall_moy_s (wallclock moyen sur 5 graines)."
        )
        v = judge_passage(0, para)
        self.assertNotIn("verdict", {n for n, _, _ in v.markers})


# ---------------------------------------------------------------------------
# Mode diff : seuls les passages AJOUTES sont juges
# ---------------------------------------------------------------------------

class TestDiffParity(unittest.TestCase):
    def test_added_dense_passage_detected_by_key(self):
        head = (
            '{"cells": [{"cell_type": "markdown", "source": '
            '["## Corrigendum c.1209 (depouillement STV)"]}]}'
        )
        keys = _markdown_paragraphs_of_blob(head)
        self.assertIn("## Corrigendum c.1209 (depouillement STV)", keys)
        # Le meme paragraphe present en base n'est PAS un ajout.
        base_keys = _markdown_paragraphs_of_blob(head)
        self.assertEqual(keys, base_keys)

    # test_new_file_paragraphs_are_added a migre vers
    # TestHeadAndRenameHermetic : la tete est lue dans l'arbre de TRAVAIL,
    # donc un ancrage historique (7a0521584, SC-09 #19372) depend d'un
    # contenu que l'histoire peut retirer -- #20252 a purge les corrigenda
    # du carnet et le test est devenu rouge sur main, sans defaut du garde.

    def test_broken_base_is_incident_not_refusal(self):
        """Base illisible : INCONNU (rc=2), jamais un refus fantome.

        Un `git show <base>:<rel>` en echec posait autrefois un blob de base
        vide : chaque paragraphe du carnet devenait un « ajout » et la garde
        refusait une PR pour du contenu preexistant. Le rc=2 est declare
        `warn_rc` au registre : neutre au check-run, jamais vert muet.
        """
        added, _files, incidents = scan_diff("deadbeef...HEAD")
        self.assertEqual(added, [], "une base illisible ne fabrique aucun finding")
        self.assertTrue(incidents, "une base illisible doit etre un incident")
        rc = emit_diff(added, [], True, incidents)
        self.assertEqual(rc, 2, "un incident sort en INCONNU, pas en OK ni en REFUS")

    def test_incidents_printed_even_with_added(self):
        """Refus ET fichiers non mesures : les incidents s'impriment aussi.

        Pre-fix, ``emit_diff`` n'imprimait la liste ``incidents`` que dans la
        branche « aucun passage dense » : un REFUS portant des fichiers non
        lus ne disait pas que la mesure etait incomplete (reserve NanoClaw
        2026-10-10 17:18Z, point 2).
        """
        import contextlib
        import io as _io

        v = judge_passage(0, "## Corrigendum c.6099536615\n\nreprise du calcul")
        added = [_mod.AddedPassage("carnet.ipynb", v)]
        buf = _io.StringIO()
        with contextlib.redirect_stdout(buf):
            rc = emit_diff(added, ["carnet.ipynb"], True, ["base illisible : x"])
        self.assertEqual(rc, 1, "un REFUS strict garde son code de sortie")
        out = buf.getvalue()
        self.assertIn("incident(s) de mesure", out,
                      "le REFUS doit signaler la mesure incomplete")
        self.assertIn("base illisible : x", out,
                      "chaque incident s'imprime dans la branche REFUS aussi")

    def test_rename_with_modification_is_scanned(self):
        """R099 reel (f42b5704a3d, suffixe -Python IIT, #20400) : le renomme+modifie est ANALYSE.

        Pre-fix, ``--diff-filter=AM`` excluant les renommages, la tranche
        entiere echappait a la garde (trou mesure par l'adjoint, dossier
        c6098782633) : le fichier n'apparaissait meme pas dans les analyses.

        Le commit d'ancrage doit etre joignable depuis ``main`` : l'ancrage
        precedent (ad0142cbb) vivait sur la branche de la PR ouverte #20246,
        reecrite le 18/10, et n'etait plus recuperable par un clone neuf.
        """
        added, files, incidents = scan_diff("f42b5704a3d^...f42b5704a3d")
        self.assertIn(
            "MyIA.AI.Notebooks/IIT/IIT-01-IntroToPyPhi-Python.ipynb",
            files,
            "un renommage+modification doit etre analyse (nouveau chemin)",
        )
        self.assertEqual(
            [i for i in incidents if "base illisible" in i],
            [],
            "la base d'un renommage se lit a l'ANCIEN chemin : pas d'incident",
        )

    def test_pure_rename_is_scanned(self):
        """R100 reel (11bf7a9b8, renommage de serie ML) : le nouveau chemin est ANALYSE.

        Ces fichiers ont ete re-deplaces plus tard dans l'histoire : leur
        tete est absente de l'arbre de travail courant, d'ou des incidents
        legitimes -- la propriete « renommage seul = zero incident » se
        prouve hermetiquement (classe TestHeadAndRenameHermetic).
        """
        _added, files, incidents = scan_diff("11bf7a9b8^...11bf7a9b8")
        self.assertIn(
            "MyIA.AI.Notebooks/ML/DataScienceWithAgents/01-Python-For-Data-Science/"
            "notebooks/1.1-Python_pour_la_Data_Science.ipynb",
            files,
        )
        self.assertTrue(
            all("base illisible" not in i for i in incidents),
            "la base d'un renommage se lit a l'ancien chemin",
        )


class TestHeadAndRenameHermetic(unittest.TestCase):
    """Trous de couverture mesures par l'adjoint (dossier c6098782633).

    Depot git temporaire : la tete est lue dans l'arbre de TRAVAIL (pas au
    commit), ce qui permet de fabriquer hermetiquement les deux etats muets
    pre-fix -- tete absente, tete au JSON invalide -- et le couple
    renommage seul / renommage+enrichissement.
    """

    def _commit_all(self, repo, message):
        env = {
            **os.environ,
            "GIT_AUTHOR_NAME": "test", "GIT_AUTHOR_EMAIL": "test@test",
            "GIT_COMMITTER_NAME": "test", "GIT_COMMITTER_EMAIL": "test@test",
        }
        subprocess.run(["git", "add", "-A"], cwd=repo, check=True,
                       capture_output=True, env=env)
        subprocess.run(["git", "commit", "-q", "-m", message], cwd=repo,
                       check=True, capture_output=True, env=env)

    def setUp(self):
        self._old_cwd = os.getcwd()
        self._tmp = tempfile.TemporaryDirectory()
        repo = Path(self._tmp.name)
        subprocess.run(["git", "init", "-q", "--initial-branch=trunk"], cwd=repo,
                       check=True, capture_output=True)
        nb = Path(repo) / "serie" / "nb.ipynb"
        nb.parent.mkdir(parents=True)
        nb.write_text(
            json.dumps({"cells": [
                {"cell_type": "markdown",
                 "source": ["Un paragraphe de cours sur les equilibres de Nash."]},
            ]}),
            encoding="utf-8",
        )
        self._commit_all(repo, "base")
        os.chdir(repo)

    def tearDown(self):
        os.chdir(self._old_cwd)
        self._tmp.cleanup()

    def test_head_absent_is_incident(self):
        """Tete absente de l'arbre de travail : INCIDENT rc2, jamais vert muet.

        Pre-fix : `continue` silencieux -- l'organe rendait rc0 en comptant
        le carnet parmi les « analyses » alors que RIEN n'avait ete juge.
        """
        nb = Path("serie/nb.ipynb")
        nb.write_text(
            json.dumps({"cells": [
                {"cell_type": "markdown",
                 "source": ["Un paragraphe de cours sur les equilibres de Nash."]},
                {"cell_type": "markdown", "source": ["Suite du cours."]},
            ]}),
            encoding="utf-8",
        )
        self._commit_all(Path.cwd(), "modifie")
        nb.unlink()  # absent de l'arbre de travail, present au commit
        added, _files, incidents = scan_diff("HEAD^...HEAD")
        self.assertEqual(added, [])
        self.assertTrue(any("tete absente" in i for i in incidents),
                        f"incident attendu, rendus : {incidents}")
        self.assertEqual(emit_diff(added, [], True, incidents), 2)

    def test_head_invalid_json_is_incident(self):
        """Tete au JSON illisible : INCIDENT rc2 (meme classe, meme geste)."""
        Path("serie/nb.ipynb").write_text("pas du json du tout", encoding="utf-8")
        self._commit_all(Path.cwd(), "casse")
        added, _files, incidents = scan_diff("HEAD^...HEAD")
        self.assertEqual(added, [])
        self.assertTrue(any("tete illisible" in i for i in incidents),
                        f"incident attendu, rendus : {incidents}")
        self.assertEqual(emit_diff(added, [], True, incidents), 2)

    def test_rename_alone_neither_finding_nor_incident(self):
        """git mv sans modification : analyse, zero ajout dense, zero incident."""
        subprocess.run(["git", "mv", "serie/nb.ipynb", "serie/renomme.ipynb"],
                       check=True, capture_output=True)
        self._commit_all(Path.cwd(), "renomme")
        added, files, incidents = scan_diff("HEAD^...HEAD")
        self.assertEqual(added, [], "un renommage seul n'ajoute aucun passage")
        self.assertEqual(incidents, [])
        self.assertIn("serie/renomme.ipynb", files)

    def test_rename_with_dense_addition_is_caught(self):
        """git mv + paragraphe dense : l'ajout est juge, base a l'ancien chemin."""
        subprocess.run(["git", "mv", "serie/nb.ipynb", "serie/renomme.ipynb"],
                       check=True, capture_output=True)
        Path("serie/renomme.ipynb").write_text(
            json.dumps({"cells": [
                {"cell_type": "markdown",
                 "source": ["Un paragraphe de cours sur les equilibres de Nash."]},
                {"cell_type": "markdown",
                 "source": [
                     "## Corrigendum c.1209\n\n",
                     "Dossier de domaine de la lane `myia-po-2024:CoursIA-2` "
                     "avec verdict `domain: fail` et tete `27d7e0541d`.",
                 ]},
            ]}),
            encoding="utf-8",
        )
        self._commit_all(Path.cwd(), "renomme et enrichi")
        added, files, incidents = scan_diff("HEAD^...HEAD")
        self.assertEqual(incidents, [])
        self.assertIn("serie/renomme.ipynb", files)
        self.assertTrue(added, "le passage dense ajoute au renommage doit etre juge")

    def test_new_file_paragraphs_are_added(self):
        """Statut A : tous les paragraphes sont legitimement neufs.

        Autoportant : l'ancrage historique precedent (7a0521584, SC-09
        #19372) a casse quand #20252 a purge les corrigenda du carnet. La
        tete etant lue dans l'arbre de TRAVAIL, un fixture historique depend
        d'un contenu que l'histoire peut retirer -- un commit synthetique
        mesure la meme propriete sans cette dependance.
        """
        Path("serie/neuf.ipynb").write_text(
            json.dumps({"cells": [
                {"cell_type": "markdown",
                 "source": ["Un paragraphe de cours ordinaire sur les coalitions."]},
                {"cell_type": "markdown",
                 "source": [
                     "## Corrigendum c.1209\n\n",
                     "Dossier de domaine de la lane `myia-po-2024:CoursIA-2` "
                     "avec verdict `domain: fail` et tete `27d7e0541d`.",
                 ]},
            ]}),
            encoding="utf-8",
        )
        self._commit_all(Path.cwd(), "nouveau carnet")
        added, files, incidents = scan_diff("HEAD^...HEAD")
        self.assertEqual(incidents, [], "un ajout franc ne doit pas etre un incident")
        self.assertTrue(added, "le commit fondateur ajoute un corrigendum dense")
        self.assertIn("serie/neuf.ipynb", files)


class TestNotebookScan(unittest.TestCase):
    def test_scan_notebook_part_on_fixture(self, tmp_path=None):
        import json
        import tempfile

        nb = {
            "cells": [
                {"cell_type": "markdown",
                 "source": ["# Mon carnet\n\n",
                            "Un paragraphe de cours tout a fait ordinaire sur la "
                            "theorie des jeux et les equilibres de Nash purs."]},
                {"cell_type": "markdown",
                 "source": ["## Corrigendum c.1209\n\n",
                            "Dossier de domaine de la lane `myia-po-2024:CoursIA-2` "
                            "avec verdict `domain: fail` et tete `27d7e0541d`."]},
                {"cell_type": "code", "source": ["print('x')"]},
            ]
        }
        with tempfile.TemporaryDirectory() as d:
            path = Path(d) / "fixture.ipynb"
            path.write_text(json.dumps(nb), encoding="utf-8")
            report = scan_notebook(path)
        self.assertIsNotNone(report)
        self.assertGreater(report.part, 0.4)
        self.assertEqual(len(report.dense_passages), 2)


class TestOutputAnchoredLessonTags(unittest.TestCase):
    """Blanchiment #24721 : L<d> ancre dans l'output d'une cellule anterieure.

    Mesure fondatrice (KNOTS-03, PR #24654, 2026-11-04) : sur 6 ancres qui
    faisaient rougir ``lesson_tag``, 3 (L1053/L1380/L3657) figuraient dans
    le listing imprime par la cellule code AU-DESSUS de la « Lecture du
    resultat » -- des citations d'output, pas des renvois aux lecons.
    """

    KNOTS_PARA = (
        "La lecture du resultat est directe : la contrainte de taille "
        "sature (L1380) des la deuxieme vague, tandis que la barre du "
        "compteur amorti (L1053) ne bouge plus apres la troisieme."
    )

    def test_lesson_tag_anchored_in_prior_output_is_masked(self):
        """Fige l'ecart assume du masque d'ancre (cf commentaire de
        ``_ANCHORED_TOKEN_RE``) : predicat = token exact, sans regard de
        prose, symetrique des deux familles precedentes."""
        anchored = frozenset({"L1380", "L1053"})
        v = judge_passage(0, self.KNOTS_PARA, anchored)
        self.assertNotIn("lesson_tag", {n for n, _, _ in v.markers})
        self.assertFalse(v.dense, "une citation d'output n'est pas un recit de cycle")

        # meme passage, sans ancres : le comportement pre-24721 est preserve
        v_bare = judge_passage(0, self.KNOTS_PARA)
        self.assertIn("lesson_tag", {n for n, _, _ in v_bare.markers})
        self.assertTrue(v_bare.dense)

    def test_anchored_mask_is_scoped_to_lesson_tag(self):
        """Un token ancre ne blanchit pas le recit de coordination voisin."""
        para = (
            "La lane a livre la tranche, verdict `domain: fail` du dossier ; "
            "voir le listing (L1380) pour le compte rendu de la re-execution."
        )
        anchored = frozenset({"L1380"})
        v = judge_passage(0, para, anchored)
        self.assertNotIn("lesson_tag", {n for n, _, _ in v.markers})
        self.assertIn("lane", {n for n, _, _ in v.markers})
        self.assertIn("verdict", {n for n, _, _ in v.markers})

    def test_posterior_output_does_not_anchor(self):
        """Une citation suit sa preuve : un token imprime PLUS BAS n'ancre
        rien (une « Lecture du resultat » ne peut pas citer un listing
        posterieur)."""
        cells = [
            {"cell_type": "markdown", "source": self.KNOTS_PARA},
            {"cell_type": "code", "source": "print('saturation (L1380)')",
             "outputs": [{"output_type": "stream", "text": "saturation (L1380)\n"}]},
        ]
        # rien avant la cellule 0 : pas d'ancres
        self.assertEqual(anchored_line_tokens(cells, 0), frozenset())
        # pour la cellule code 1 elle-meme : son propre output ne compte pas
        self.assertEqual(anchored_line_tokens(cells, 1), frozenset())
        # la cellule code 1 ancre pour ce qui SUIT (cellule 2), pas avant
        self.assertEqual(anchored_line_tokens(cells, 2), frozenset({"L1380"}))
        v = judge_passage(0, self.KNOTS_PARA, anchored_line_tokens(cells, 0))
        self.assertIn("lesson_tag", {n for n, _, _ in v.markers})

    def test_output_text_list_form_is_flattened(self):
        """nbformat : ``text`` d'un output = chaine OU liste de lignes. Le
        piege TypeError sur une liste est mesure sur #24654."""
        cell_list = {
            "cell_type": "code", "source": "print(listing)",
            "outputs": [{"output_type": "stream",
                         "text": ["seuil (L1380) atteint\n",
                                   "compteur (L1053) fige\n"]}],
        }
        self.assertEqual(_output_text_tokens(cell_list), {"L1380", "L1053"})
        cell_str = {
            "cell_type": "code", "source": "print(listing)",
            "outputs": [{"output_type": "stream", "text": "seuil (L3657)\n"}],
        }
        self.assertEqual(_output_text_tokens(cell_str), {"L3657"})

    def test_word_boundary_anchored_l138_does_not_mask_l1380(self):
        """L138 ancre ne blanchit pas L1380 : bornes de mots dans le masque."""
        para = "La lecture du resultat (L1380) reste valable sur les grandes tailles."
        v = judge_passage(0, para, frozenset({"L138"}))
        self.assertIn("lesson_tag", {n for n, _, _ in v.markers})

    def test_scan_notebook_threads_anchors_in_order(self):
        """Bout en bout : scan_notebook accumule les ancres au fil des
        cellules -- la « Lecture du resultat » jugee apres son listing n'est
        plus dense, et le meme carnet SANS la cellule code le reste."""
        import json
        import tempfile

        def build(with_code_cell):
            cells = []
            if with_code_cell:
                cells.append({
                    "cell_type": "code", "source": "print(listing)",
                    "outputs": [{"output_type": "stream",
                                 "text": "seuil (L1380) atteint, compteur (L1053) fige\n"}],
                })
            cells.append({"cell_type": "markdown", "source": self.KNOTS_PARA})
            return {"cells": cells}

        with tempfile.TemporaryDirectory() as d:
            path = Path(d) / "fixture.ipynb"
            path.write_text(json.dumps(build(True)), encoding="utf-8")
            anchored_report = scan_notebook(path)
            path.write_text(json.dumps(build(False)), encoding="utf-8")
            bare_report = scan_notebook(path)
        self.assertEqual(anchored_report.dense_passages, [],
                         "le listing anterieur ancre les (Lnnn) de la lecture")
        self.assertTrue(bare_report.dense_passages,
                        "sans listing anterieur, les Lnnn restent des lecons")

    def test_url_fragment_frozen_regression_stays_green(self):
        """Garde-regression : la 3e famille ne deroge pas aux deux premieres
        -- un fragment de permalien ``#L261`` reste masque SANS ancre."""
        prose_anchor = "Voir la ligne #L261 du fichier pour le detail du calcul."
        v = judge_passage(0, prose_anchor, frozenset({"L261"}))
        self.assertNotIn("lesson_tag", {n for n, _, _ in v.markers})


if __name__ == "__main__":
    unittest.main()
