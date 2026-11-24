import json
import tempfile
import unittest
from pathlib import Path
from check_rh_conditionality import exact_terminal_type, main

class TerminalTypeGateTests(unittest.TestCase):
    def check(self, name, records):
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)/"graph.jsonl"
            path.write_text("".join(json.dumps(r)+"\n" for r in records))
            return exact_terminal_type(name,path)[0]
    def test_missing_nonexistent_and_unrelated_are_rejected(self):
        self.assertFalse(self.check("Missing",[]))
        self.assertFalse(self.check("Missing",[{"name":"Other","kind":"theorem"}]))
        self.assertFalse(self.check("Other",[{"name":"Other","kind":"theorem",
            "kernelTypeAudit":{"binders":0,"form":"named","targets":["True"],"exactRH":False}}]))
    def test_visible_or_hidden_premise_is_rejected(self):
        record={"name":"R.t","kind":"theorem","kernelTypeAudit":{
            "binders":1,"form":"named","targets":["RiemannHypothesis"],
            "premises":["RiemannHypothesis"],"blocked":False,"returnsRH":True,"exactRH":False}}
        self.assertFalse(self.check("R.t",[record]))
    def test_exact_type_is_not_the_same_as_axiom_or_fake_alias(self):
        a={"binders":0,"form":"named","targets":["RiemannHypothesis"],"premises":[],
           "blocked":False,"returnsRH":True,"exactRH":True}
        self.assertTrue(self.check("R.t",[{"name":"R.t","kind":"theorem","kernelTypeAudit":a}]))
        self.assertFalse(self.check("R.t",[{"name":"R.t","kind":"axiom","kernelTypeAudit":a}]))
        self.assertFalse(self.check("R.t",[{"name":"R.t","kind":"theorem","kernelTypeAudit":dict(a,targets=["FakeRH"])}]))
    def test_missing_kernel_dump_fails(self):
        self.assertNotEqual(main(["--require-unconditional","NONEXISTENT_FAKE_RH"]),0)
if __name__=="__main__":
    unittest.main()
