#!/usr/bin/env python3
"""Bind an external Lean 4 NDJSON kernel check to the requested literal theorem."""
import json
import sys


def check_export(lines):
    names = {}
    rh_expressions = set()
    roots = 0
    for line in lines:
        row = json.loads(line)
        if "str" in row:
            name = row["str"]
            if name["pre"] == 0 and name["str"] in {"native_riemannHypothesis", "RiemannHypothesis"}:
                names[row["in"]] = name["str"]
        if "const" in row:
            value = row["const"]
            if names.get(value["name"]) == "RiemannHypothesis" and value["us"] == []:
                rh_expressions.add(row["ie"])
        if "thm" in row:
            thm = row["thm"]
            if names.get(thm["name"]) == "native_riemannHypothesis":
                if (thm["levelParams"] or thm["type"] not in rh_expressions
                        or type(thm.get("value")) is not int):
                    raise ValueError("Exported terminal theorem has the wrong type or lacks a proof")
                roots += 1
    if roots != 1:
        raise ValueError("Export does not contain exactly one native_riemannHypothesis theorem")


if __name__ == "__main__":
    with open(sys.argv[1], encoding="utf8") as source:
        check_export(source)
    print("Independent checker input contains the closed theorem of literal Mathlib RH")
