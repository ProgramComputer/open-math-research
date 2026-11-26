"""Exercise the export inventory and its rejection paths without Lean binaries."""

import importlib.util
import json
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest


HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location("audit_export", HERE / "audit_export.py")
AUDIT = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(AUDIT)

METADATA = {
    "meta": {
        "lean": {"version": "4.36.0", "githash": AUDIT.LEAN_COMMIT},
        "exporter": {"name": "lean4export", "version": "3.1.0"},
        "format": {"version": "3.1.0"},
    }
}


def name(i, segment, parent=0):
    return {"in": i, "str": {"pre": parent, "str": segment}}


def axiom(i):
    return {"axiom": {"name": i, "type": 0, "isUnsafe": False}}


def theorem(i, body):
    return {"thm": {"name": i, "type": 0, "value": body}}


def constant(i, declaration):
    return {"ie": i, "const": {"name": declaration, "us": []}}


BASE = [METADATA, {"ie": 0, "sort": 0}, name(1, "propext"), axiom(1),
        name(2, "Example"), name(3, "root", 2), constant(1, 1), theorem(3, 1)]


class ExportInventoryTests(unittest.TestCase):
    def audit(self, rows=BASE, roots=("Example.root",)):
        with TemporaryDirectory() as scratch:
            path = Path(scratch) / "example.ndjson"
            path.write_text("".join(row if isinstance(row, str) else json.dumps(row) + "\n"
                                    for row in rows), encoding="utf-8")
            return AUDIT.inspect(path, roots)

    def test_reports_exact_names_and_reachable_axioms(self):
        report = self.audit()
        root = report["roots"]["Example.root"]
        self.assertEqual(root["axioms"], ["propext"])
        self.assertEqual(root["reachable_declarations"], [("Example", "root"), ("propext",)])
        self.assertEqual(report["declaration_count"], 2)

    def test_does_not_accept_an_axiom_as_target(self):
        with self.assertRaisesRegex(ValueError, "missing theorem with a proof body"):
            self.audit(roots=("propext",))

    def test_rejects_unknown_axiom_even_if_unreachable(self):
        with self.assertRaisesRegex(ValueError, "unexpected axiom"):
            self.audit(BASE + [name(4, "sorryAx"), axiom(4)])

    def test_counts_extra_kernel_checked_groups(self):
        report = self.audit(BASE + [name(4, "extra"), theorem(4, 1)])
        self.assertEqual(report["additional_checked_groups"], 1)

    def test_rejects_missing_dependencies(self):
        with self.assertRaisesRegex(ValueError, "missing referenced declaration"):
            self.audit(BASE[:3] + BASE[4:])

    def test_rejects_duplicate_json_keys(self):
        with self.assertRaisesRegex(ValueError, "repeated JSON key"):
            self.audit(BASE + ['{"ie":2,"ie":3,"sort":0}\n'])

    def test_counts_all_members_of_reachable_inductive_groups(self):
        rows = [
            METADATA, {"ie": 0, "sort": 0}, name(1, "Nat"), name(2, "zero", 1),
            name(3, "rec", 1), constant(1, 1), constant(2, 2),
            {"inductive": {
                "types": [{"name": 1, "type": 0}],
                "ctors": [{"name": 2, "type": 1}],
                "recs": [{"name": 3, "type": 0, "rules": [{"rhs": 2}]}],
            }},
            {"ie": 3, "natVal": "0"}, name(4, "Example"), name(5, "root", 4), theorem(5, 3),
        ]
        self.assertEqual(self.audit(rows)["declaration_count"], 4)


if __name__ == "__main__":
    unittest.main()
