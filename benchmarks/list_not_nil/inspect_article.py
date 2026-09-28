#!/usr/bin/env python3
"""Structurally inspect an OpenTheory v6 article, without checking its proofs."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


SPECIAL = {"=", "HOL4.min.==>"}


def decode_name(line: str) -> str:
    chars = iter(line[1:-1])
    decoded = []
    for char in chars:
        if char == "\\":
            try:
                char = next(chars)
            except StopIteration as error:
                raise ValueError("dangling escape in name") from error
        decoded.append(char)
    return "".join(decoded)


def equality(left: tuple, right: tuple) -> tuple:
    return ("app", ("app", ("const", "=", None), left), right)


def sides(term: tuple) -> tuple[tuple, tuple]:
    if term[0] != "app" or term[1][0] != "app":
        raise ValueError(f"expected equality, got {repr(term)[:300]}")
    if term[1][1][0] != "const" or term[1][1][1] != "=":
        raise ValueError("expected equality constant")
    return term[1][2], term[2]


def replace(term: tuple, substitutions: dict[tuple, tuple]) -> tuple:
    if term in substitutions:
        return substitutions[term]
    if term[0] == "app":
        return ("app", replace(term[1], substitutions),
                replace(term[2], substitutions))
    if term[0] == "abs":
        bound = term[1]
        inner = {key: value for key, value in substitutions.items() if key != bound}
        return ("abs", bound, replace(term[2], inner))
    return term


def replace_type(ty: tuple, substitutions: dict[str, tuple]) -> tuple:
    if ty[0] == "typevar":
        return substitutions.get(ty[1], ty)
    return ("type", ty[1], tuple(replace_type(t, substitutions) for t in ty[2]))


def replace_term_types(term: tuple, substitutions: dict[str, tuple]) -> tuple:
    if term[0] in ("const", "var"):
        return (term[0], term[1], replace_type(term[2], substitutions)
                if term[2] is not None else None)
    if term[0] == "app":
        return ("app", replace_term_types(term[1], substitutions),
                replace_term_types(term[2], substitutions))
    if term[0] == "abs":
        return ("abs", replace_term_types(term[1], substitutions),
                replace_term_types(term[2], substitutions))
    raise ValueError(f"unknown term node {term[0]}")


def special_head(term: tuple) -> tuple[str, int] | None:
    args = 0
    while term[0] == "app":
        args += 1
        term = term[1]
    if term[0] == "const" and term[1] in SPECIAL and args < 2:
        return term[1], args
    return None


def constants(term: tuple) -> set[str]:
    if term[0] == "const":
        return {term[1]}
    if term[0] in ("typevar", "type", "var"):
        return set()
    if term[0] in ("app", "abs"):
        return constants(term[1]) | constants(term[2])
    raise ValueError(f"unknown term node {term[0]}")


def inspect(path: Path) -> dict:
    stack: list[tuple] = []
    dictionary: dict[int, tuple] = {}
    axioms: list[dict] = []
    partial: dict[str, list[dict]] = {"refl": [], "appThm": [], "absThm": []}
    command_counts: dict[str, int] = {}
    exported: list[tuple] = []

    def pop(kind: str) -> tuple:
        value = stack.pop()
        if value[0] != kind:
            raise ValueError(f"expected {kind}, got {value[0]}")
        return value[1]

    with path.open(encoding="utf-8") as source:
        for line_number, raw in enumerate(source, 1):
            line = raw.rstrip("\n")
            try:
                if line.startswith('"') and line.endswith('"'):
                    stack.append(("name", decode_name(line)))
                elif line.isdecimal():
                    stack.append(("num", int(line)))
                elif line == "nil":
                    stack.append(("list", ()))
                elif line == "cons":
                    tail = pop("list")
                    head = stack.pop()
                    stack.append(("list", (head,) + tail))
                elif line == "def":
                    key = pop("num")
                    dictionary[key] = stack[-1]
                elif line == "ref":
                    stack.append(dictionary[pop("num")])
                elif line == "pop":
                    stack.pop()
                elif line == "version":
                    if pop("num") != 6:
                        raise ValueError("unsupported article version")
                elif line in ("const", "typeOp"):
                    stack.append(("const" if line == "const" else "typeop",
                                  pop("name")))
                elif line == "varType":
                    stack.append(("type", ("typevar", pop("name"))))
                elif line == "opType":
                    args = tuple(item[1] for item in pop("list"))
                    stack.append(("type", ("type", pop("typeop"), args)))
                elif line == "var":
                    ty = pop("type")
                    stack.append(("var", ("var", pop("name"), ty)))
                elif line == "varTerm":
                    stack.append(("term", pop("var")))
                elif line == "constTerm":
                    ty = pop("type")
                    stack.append(("term", ("const", pop("const"), ty)))
                elif line == "appTerm":
                    argument = pop("term")
                    stack.append(("term", ("app", pop("term"), argument)))
                elif line == "absTerm":
                    body = pop("term")
                    stack.append(("term", ("abs", pop("var"), body)))
                elif line in ("assume", "axiom"):
                    conclusion = pop("term")
                    if line == "axiom":
                        hyps = tuple(item[1] for item in pop("list"))
                        serial = repr((hyps, conclusion)).encode("utf-8")
                        axioms.append({
                            "line": line_number,
                            "sha256": hashlib.sha256(serial).hexdigest(),
                            "assumptions": hyps,
                            "conclusion": conclusion,
                            "constants": sorted(set().union(*(constants(t) for t in
                                hyps + (conclusion,)))),
                        })
                    stack.append(("thm", conclusion))
                elif line in ("refl", "betaConv"):
                    term = pop("term")
                    if line == "refl":
                        head = special_head(term)
                        if head:
                            partial["refl"].append({"line": line_number,
                                                     "constant": head[0], "arity": head[1]})
                        result = term
                    else:
                        if term[0] != "app" or term[1][0] != "abs":
                            raise ValueError("betaConv did not receive a redex")
                        result = replace(term[1][2], {term[1][1]: term[2]})
                    stack.append(("thm", equality(term, result)))
                elif line == "deductAntisym":
                    first = pop("thm")
                    second = pop("thm")
                    stack.append(("thm", equality(second, first)))
                elif line == "eqMp":
                    pop("thm")
                    stack.append(("thm", sides(pop("thm"))[1]))
                elif line == "sym":
                    left, right = sides(pop("thm"))
                    stack.append(("thm", equality(right, left)))
                elif line == "trans":
                    second = sides(pop("thm"))
                    first = sides(pop("thm"))
                    stack.append(("thm", equality(first[0], second[1])))
                elif line == "appThm":
                    argument = sides(pop("thm"))
                    function = sides(pop("thm"))
                    for side in function:
                        head = special_head(side)
                        if head:
                            partial["appThm"].append({"line": line_number,
                                "constant": head[0], "arity": head[1]})
                    stack.append(("thm", equality(
                        ("app", function[0], argument[0]),
                        ("app", function[1], argument[1]))))
                elif line == "absThm":
                    left, right = sides(pop("thm"))
                    variable = pop("var")
                    for side in (left, right):
                        head = special_head(side)
                        if head:
                            partial["absThm"].append({"line": line_number,
                                "constant": head[0], "arity": head[1]})
                    stack.append(("thm", equality(("abs", variable, left),
                                                   ("abs", variable, right))))
                elif line == "subst":
                    conclusion = pop("thm")
                    type_pairs, term_pairs = tuple(item[1] for item in pop("list"))
                    type_substitutions = {pair[0][1]: pair[1][1]
                                          for pair in (item[1] for item in type_pairs)}
                    conclusion = replace_term_types(conclusion, type_substitutions)
                    term_substitutions = {pair[0][1]: pair[1][1]
                                          for pair in (item[1] for item in term_pairs)}
                    stack.append(("thm", replace(conclusion, term_substitutions)))
                elif line == "thm":
                    expected = pop("term")
                    assumptions = pop("list")
                    actual = pop("thm")
                    exported.append((expected, actual, assumptions))
                elif line.startswith("#"):
                    continue
                else:
                    raise ValueError(f"unsupported command {line!r}")
                if line and line[0].isalpha():
                    command_counts[line] = command_counts.get(line, 0) + 1
            except (IndexError, KeyError, TypeError, ValueError) as error:
                raise ValueError(f"article line {line_number}: {error}") from error

    return {"article_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            "commands": command_counts, "axioms": axioms,
            "partial_special": partial, "exports": len(exported),
            "export_assumptions_empty": all(not assumptions for _, _, assumptions in exported),
            "final_conclusion_matches": all(actual == expected for expected, actual, _ in exported)}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("article", type=Path)
    parser.add_argument("--json", type=Path, help="write the complete axiom inventory")
    args = parser.parse_args()
    result = inspect(args.article)
    if args.json:
        args.json.write_text(json.dumps(result, indent=2) + "\n")
    print(f"axioms: {len(result['axioms'])}")
    print(f"exports: {result['exports']}")
    print(f"export assumptions empty: {result['export_assumptions_empty']}")
    print(f"final conclusion matches: {result['final_conclusion_matches']}")
    if (result["exports"] != 1 or not result["export_assumptions_empty"] or
            not result["final_conclusion_matches"]):
        raise SystemExit("article final export failed structural checks")
    for command, uses in result["partial_special"].items():
        print(f"partial equality/implication in {command}: {len(uses)}")
        for item in uses[:10]:
            print(f"  line {item['line']}: {item['constant']} arity {item['arity']}")


if __name__ == "__main__":
    main()
