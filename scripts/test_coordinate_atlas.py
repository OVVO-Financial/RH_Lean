#!/usr/bin/env python3
"""Tests for the coordinate atlas and the static search corpus generator."""

import copy
import json
import unittest

import coordinate_atlas as atlas_mod
import search_catalog as catalog


def coord(atlas, i):
    return next(c for c in atlas["coordinates"] if c["id"] == i)


def crosswalk(atlas, i):
    return next(x for x in atlas["crosswalks"] if x["id"] == i)


class CoordinateAtlasTests(unittest.TestCase):
    def setUp(self):
        self.atlas = atlas_mod.load()
        self.registry = json.loads(atlas_mod.REGISTRY.read_text(encoding="utf-8"))

    def errors(self, mutate):
        atlas = copy.deepcopy(self.atlas)
        mutate(atlas)
        return "\n".join(atlas_mod.validate(atlas, registry=self.registry))

    def assertRejects(self, mutate, needle):
        self.assertIn(needle, self.errors(mutate))

    def test_atlas_is_valid_and_page_is_current(self):
        self.assertEqual(atlas_mod.validate(self.atlas, registry=self.registry), [])
        self.assertFalse(atlas_mod.sync(self.atlas, write=False))

    def test_llms_txt_links_resolve(self):
        self.assertEqual(atlas_mod.check_entry_points(), [])

    def test_every_coordinate_reaches_an_anchor(self):
        def isolate(a):
            a["crosswalks"] = [x for x in a["crosswalks"] if "COORD-NYMAN" not in (x["from"], x["to"])]
        self.assertRejects(isolate, "COORD-NYMAN: no crosswalk path to any anchor")

    def test_barriers_are_not_crossed_and_not_contradicted(self):
        steps = atlas_mod.path(self.atlas, "COORD-915-SOURCE", "COORD-SAT-MERTENS")
        self.assertTrue(steps)
        self.assertNotIn("X-NOT-915-SAT", [s["crosswalk"] for s in steps])

        def contradict(a):
            a["crosswalks"].append({"id": "X-BAD", "from": "COORD-915-SOURCE", "relation": "EXACT_IDENTITY",
                                    "to": "COORD-SAT-MERTENS", "formula": "f", "status": "PAPER",
                                    "source": ["CURRENT_PROOF_CONTRACT.md"]})
        self.assertRejects(contradict, "contradicts a NOT_EQUIVALENT barrier")

    def test_undeclared_notation_collision_is_rejected(self):
        self.assertRejects(lambda a: coord(a, "COORD-NYMAN")["symbols"].append("D_N"),
                           "undeclared notation collision 'D'")

    def test_lean_links_and_sources_are_checked(self):
        self.assertRejects(lambda a: coord(a, "COORD-CORR4-PARENT")["lean"][0].update(name="noSuchDeclaration"),
                           "noSuchDeclaration not found")
        self.assertRejects(lambda a: crosswalk(a, "X-PNT-FIRST").update(source=[]), "needs a source document")
        self.assertRejects(lambda a: crosswalk(a, "X-CORR4-C").update(lean=[]), "needs a declaration")
        self.assertRejects(lambda a: coord(a, "COORD-FINITE-AC")["proof_nodes"].append("NO-SUCH-NODE"),
                           "unknown proof-obligation node NO-SUCH-NODE")

    def test_collision_lookup_lists_every_reading(self):
        hits, collisions, _ = atlas_mod.lookup(self.atlas, "D_R")
        self.assertEqual(len(collisions), 1)
        readings = {m.get("coordinate") for m in collisions[0]["meanings"]}
        self.assertTrue({"COORD-VF-CAN-DEFECT", "COORD-MOBIUS-COVARIANCE", "COORD-CORR4-REMAINDER"} <= readings)
        ids = {c["id"] for c, _ in atlas_mod.lookup(self.atlas, "squareRootCanonicalRoughCorrelation")[0]}
        self.assertIn("COORD-CORR4-PARENT", ids)

    def test_lean_only_bridge_between_the_two_faces(self):
        steps = atlas_mod.path(self.atlas, "COORD-VF-CAN-DEFECT", "ANCHOR-MERTENS", lean_only=True)
        self.assertTrue(steps)
        self.assertTrue(all(s["status"] in atlas_mod.LEAN_ONLY for s in steps))
        self.assertFalse(all(s["invertible"] for s in steps), "the bridge is navigation, not an equivalence")

    def test_finite_c_newton_lift_and_corr4_share_one_object(self):
        steps = atlas_mod.path(self.atlas, "COORD-EULER-SELF-DUAL", "COORD-CORR4-PARENT", lean_only=True)
        self.assertEqual([s["crosswalk"] for s in steps], ["X-EULER-QR", "X-FINITE-AC-DEF", "X-CORR4-C"])

    def test_expand_returns_aliases_and_lean_names(self):
        terms, ids, _ = atlas_mod.expand(self.atlas, "q2 daughter")
        self.assertEqual(ids, ["COORD-CORR4-DAUGHTERS"])
        self.assertIn("canonicalRoughLowQ2DaughterEnergy", terms)

    def test_notation_head(self):
        for symbol, expected in (("D_R^can", "D"), ("C6(z)", "C"), ("Γ_R", "Γ"), ("VF_can(x)", "VF"), ("K1", "K")):
            self.assertEqual(atlas_mod.head(symbol), expected)


class SearchCatalogTests(unittest.TestCase):
    def test_lean_comment_stripping_follows_lean(self):
        self.assertEqual(catalog.strip_lean_comments("/-- Möbius--rough -/\ndef f := 1"), "\ndef f := 1")
        self.assertEqual(catalog.strip_lean_comments("a /- /- -/ x -/ b -- c\nd"), "a  b \nd")

    def test_rewrite_families_follow_the_naming_convention(self):
        text = ("def foo := 1\ndef bar := 2\n"
                "theorem foo_eq_bar : foo = 1 := rfl\n"
                "theorem foo_zero_eq_one : foo = 1 := rfl\n"
                "theorem foo_otherQuantity_eq_two : 2 = 2 := rfl\n"
                "theorem bar_iff_true : True := trivial\n")
        families = {f["definition"]: f for f in catalog.rewrite_families({"X.lean": catalog.strip_lean_comments(text)})}
        self.assertEqual(families["foo"]["rewrites"], {"X.lean": ["foo_eq_bar", "foo_zero_eq_one"]})
        self.assertEqual(families["bar"]["rewrites"], {"X.lean": ["bar_iff_true"]})

    def test_titles_and_dates(self):
        self.assertEqual(catalog.title_of("a.md", "intro\n# Heading here\n"), "Heading here")
        self.assertEqual(catalog.title_of("a.lean", "/-!\n# Module title\n-/\n"), "Module title")
        self.assertEqual(catalog.title_of("a.py", '#!/usr/bin/env python3\n"""Doc line.\n\nMore."""\n'), "Doc line.")
        self.assertEqual(catalog.date_of("research/X_20261024.md", ""), "2026-10-24")
        self.assertEqual(catalog.date_of("research/X_2026_10_15.md", ""), "2026-10-15")

    def test_identifier_aliases_match_whole_tokens(self):
        atlas = atlas_mod.load()
        registry = json.loads(atlas_mod.REGISTRY.read_text(encoding="utf-8"))
        tagger = catalog.Tagger(atlas, registry)
        self.assertNotIn("COORD-VF-MID", tagger.coordinates("vfMidFoo vfMidBar vfMidBaz"))
        self.assertIn("COORD-CORR4-DAUGHTERS", tagger.coordinates("the q2 daughter energy of the q2 daughters"))
        self.assertNotIn("RH", tagger.proof_nodes("RH is open; see OPEN-CORR4"))
        self.assertIn("OPEN-CORR4", tagger.proof_nodes("RH is open; see OPEN-CORR4"))


if __name__ == "__main__":
    unittest.main()
