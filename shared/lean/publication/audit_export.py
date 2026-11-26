"""Inventory the transitive declaration closure in a Lean 4.36 NDJSON export."""

import argparse
from array import array
import hashlib
import json
from pathlib import Path
import sys


LEAN_COMMIT = "611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9"
ALLOWED_AXIOMS = {("propext",), ("Classical", "choice"), ("Quot", "sound")}
QUOT_NAMES = {("Quot",), ("Quot", "mk"), ("Quot", "lift"), ("Quot", "ind")}
STRING_NAMES = (("Char", "ofNat"), ("String", "ofList"))
EXPR_CHILD_FIELDS = {
    "app": ("fn", "arg"),
    "lam": ("type", "body"),
    "forallE": ("type", "body"),
    "letE": ("type", "value", "body"),
    "proj": ("struct",),
    "mdata": ("expr",),
    "sort": (),
    "bvar": (),
    "const": (),
    "natVal": (),
    "strVal": (),
}


def expect(condition, message):
    if not condition:
        raise ValueError(message)


def unique_object(pairs):
    result = dict(pairs)
    expect(len(result) == len(pairs), "repeated JSON key")
    return result


def index(value, size):
    expect(type(value) is int and 0 <= value < size, f"invalid index {value!r}")
    return value


class Export:
    def __init__(self):
        self.names = [()]
        self.levels = 1
        # Three child expression indices and one declaration name index per row.
        self.expressions = array("i")
        self.groups = []
        self.declarations = {}
        self.axioms = set()
        self.theorems = set()
        self.quot_rows = []

    def name(self, value):
        return self.names[index(value, len(self.names))]

    def expr(self, value):
        return index(value, len(self.expressions) // 4)

    def add_group(self, names, exprs, constants=()):
        for name in names:
            expect(name and name not in self.declarations, f"duplicate declaration {name!r}")
            self.declarations[name] = len(self.groups)
        self.groups.append((tuple(names), tuple(exprs), tuple(constants)))

    def expression_row(self, tag, obj):
        val = obj[tag]
        children = [self.expr(val[field]) for field in EXPR_CHILD_FIELDS[tag]]
        constant = -1
        if tag in ("const", "proj"):
            constant = index(val["name" if tag == "const" else "typeName"], len(self.names))
        elif tag == "natVal":
            constant = -2
        elif tag == "strVal":
            constant = -3
        self.expressions.extend(children + [-1] * (3 - len(children)) + [constant])

    def read(self, obj):
        if "in" in obj:
            expect(obj["in"] == len(self.names) and len(obj) == 2, "unexpected name index")
            val = obj["str"] if "str" in obj else obj["num"]
            item = val["str"] if "str" in obj else val["i"]
            expect(type(item) is (str if "str" in obj else int), "invalid name segment")
            self.names.append(self.name(val["pre"]) + (item,))
        elif "il" in obj:
            expect(obj["il"] == self.levels and len(obj) == 2, "unexpected level index")
            self.levels += 1
        elif "ie" in obj:
            expect(obj["ie"] * 4 == len(self.expressions) and len(obj) == 2,
                   "unexpected expression index")
            self.expression_row(next(k for k in obj if k != "ie"), obj)
        else:
            expect(len(obj) == 1, "invalid declaration row")
            tag, val = next(iter(obj.items()))
            if tag == "inductive":
                members = val["types"] + val["ctors"] + val["recs"]
                names = [self.name(member["name"]) for member in members]
                exprs = [self.expr(member["type"]) for member in members]
                exprs += [self.expr(rule["rhs"]) for rec in val["recs"] for rule in rec["rules"]]
                self.add_group(names, exprs)
            elif tag == "quot":
                self.quot_rows.append((self.name(val["name"]), self.expr(val["type"])))
            elif tag in ("axiom", "def", "opaque", "thm"):
                name = self.name(val["name"])
                exprs = [self.expr(val["type"])]
                if tag != "axiom":
                    exprs.append(self.expr(val["value"]))
                else:
                    expect(name in ALLOWED_AXIOMS, f"unexpected axiom {name!r}")
                    expect(val["isUnsafe"] is False, f"unsafe axiom {name!r}")
                    self.axioms.add(name)
                if tag == "thm":
                    self.theorems.add(name)
                self.add_group([name], exprs)
            else:
                raise ValueError(f"unknown declaration tag {tag!r}")

    def finish(self):
        if self.quot_rows:
            names, exprs = zip(*self.quot_rows)
            expect(len(names) == len(QUOT_NAMES) and set(names) == QUOT_NAMES,
                   "incomplete or duplicate quotient package")
            self.add_group(names, exprs, [("Eq",)])

    def closure(self, root):
        expect(root in self.theorems, f"missing theorem with a proof body: {root!r}")
        seen_groups = set()
        seen_exprs = bytearray(len(self.expressions) // 4)
        expressions = []
        constants = [root]
        while constants or expressions:
            while constants:
                name = constants.pop()
                expect(name in self.declarations, f"missing referenced declaration {name!r}")
                group = self.declarations[name]
                if group not in seen_groups:
                    seen_groups.add(group)
                    _, exprs, extra = self.groups[group]
                    expressions.extend(exprs)
                    constants.extend(extra)
            if expressions:
                expr = expressions.pop()
                if seen_exprs[expr]:
                    continue
                seen_exprs[expr] = 1
                offset = 4 * expr
                child0, child1, child2, constant = self.expressions[offset : offset + 4]
                expressions.extend(child for child in (child0, child1, child2) if child >= 0)
                if constant >= 0:
                    constants.append(self.names[constant])
                elif constant == -2:
                    constants.append(("Nat",))
                elif constant == -3:
                    constants.extend(STRING_NAMES)
        return seen_groups


def inspect(path, roots):
    export = Export()
    digest = hashlib.sha256()
    with path.open("rb") as source:
        first = next(source)
        digest.update(first)
        row = json.loads(first, object_pairs_hook=unique_object)
        expect(set(row) == {"meta"}, "missing Lean export metadata")
        meta = row["meta"]
        expect(meta["lean"] == {"version": "4.36.0", "githash": LEAN_COMMIT},
               f"unexpected Lean version or commit: {meta['lean']!r}")
        expect(meta["format"]["version"] == "3.1.0", "unexpected NDJSON format version")
        expect(meta["exporter"] == {"name": "lean4export", "version": "3.1.0"},
               "unexpected exporter")
        for line_num, line in enumerate(source, 2):
            digest.update(line)
            try:
                export.read(json.loads(line, object_pairs_hook=unique_object))
            except (KeyError, ValueError, TypeError, StopIteration) as error:
                raise ValueError(f"line {line_num}: {error}") from error
    export.finish()
    audited = {}
    union = set()
    for root in roots:
        closure = export.closure(tuple(root.split(".")))
        union.update(closure)
        declarations = [name for group in closure for name in export.groups[group][0]]
        audited[root] = {
            "declaration_count": len(declarations),
            "axioms": sorted(".".join(name) for name in export.axioms.intersection(declarations)),
            "reachable_declarations": sorted(declarations, key=repr),
        }
    extra = set(range(len(export.groups))) - union
    return {
        "additional_checked_groups": len(extra),
        "export_sha256": digest.hexdigest(),
        "meta": meta,
        "declaration_count": len(export.declarations),
        "expression_count": len(export.expressions) // 4,
        "roots": audited,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("export", type=Path)
    parser.add_argument("theorems", nargs="+")
    args = parser.parse_args()
    try:
        report = inspect(args.export, args.theorems)
    except (OSError, ValueError, KeyError, TypeError, StopIteration) as error:
        sys.exit(f"export audit failed: {error}")
    print(json.dumps(report, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
