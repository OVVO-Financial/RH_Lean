import unittest
from semantic_source_audit import scan_text

class SemanticSourceAuditTests(unittest.TestCase):
    def categories(self,text):
        return {h["category"] for h in scan_text("RHLean/Test.lean",text)[1]}
    def test_degenerate_witness(self):
        s="""def anyGeometry (_ : Nat) : Prop := True
structure Bundle where
  geoOk : anyGeometry 0
  height : Nat
def buildBundle : Bundle := { geoOk := trivial, height := 0 }
theorem reuse (h : RiemannHypothesis) : RiemannHypothesis := h
"""
        self.assertTrue({"constant_truth_definition_review","metric_assignment_candidate",
                         "rh_return_with_visible_premises","literal_self_premise"} <= self.categories(s))
    def test_comments_not_source(self):
        self.assertFalse(self.categories("-- axiom fake : False\n/- height := 0 -/\ndef normal : Nat := 3\n"))
    def test_shadow(self):
        self.assertIn("root_rh_shadow_candidate",self.categories("def RiemannHypothesis : Prop := True\n"))
        self.assertNotIn("root_rh_shadow_candidate",self.categories("namespace Test\ndef RiemannHypothesis : Prop := True\nend Test\n"))
    def test_real_conditional_is_candidate_not_verdict(self):
        self.assertIn("rh_return_with_visible_premises",self.categories("theorem bridge (h : RealBound) : RiemannHypothesis := h.rh\n"))
    def test_false_conclusion_not_a_false_premise(self):
        self.assertNotIn("false_empty_premise_candidate", self.categories("theorem t (h : P) : False := h.false\n"))
    def test_empty_and_reflexive(self):
        self.assertIn("false_empty_premise_candidate",self.categories("theorem t (x : Fin 0) : True := Fin.elim0 x\n"))
        self.assertIn("literal_reflexive_statement",self.categories("theorem t : P = P := rfl\n"))
if __name__=="__main__":
    unittest.main()
