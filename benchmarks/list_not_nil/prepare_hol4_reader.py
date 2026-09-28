#!/usr/bin/env python3
"""Generate a HOL4 article reader with the two exporter-only rule commands."""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path


SOURCE_RELATIVE = Path("src/opentheory/reader/OpenTheoryReader.sml")
STRUCTURE = "structure OpenTheoryReader :> OpenTheoryReader = struct"
ANCHOR = (
    '    | f "thm"    '
    '{stack=OTerm c::OList ls::OThm th::os,dict,thms,...} = let'
)
EXTRA_RULES = '''    | f "sym" (st as {stack=OThm th::os,...}) =
        st_(OThm(Thm.SYM th)::os,st)
    | f "trans" (st as {stack=OThm th2::OThm th1::os,...}) =
        st_(OThm(Thm.TRANS th1 th2)::os,st)
'''


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--hol4-root", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()

    source = args.hol4_root / SOURCE_RELATIVE
    original = source.read_text()
    if original.count(STRUCTURE) != 1 or original.count(ANCHOR) != 1:
        raise SystemExit("unexpected HOL4 OpenTheoryReader source shape")
    if 'f "sym"' in original or 'f "trans"' in original:
        raise SystemExit("HOL4 reader already supports sym/trans")

    adapted = original.replace(
        STRUCTURE, "structure ListNotNilReader :> OpenTheoryReader = struct"
    ).replace(ANCHOR, EXTRA_RULES + ANCHOR)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(adapted)
    print(f"HOL4 reader source SHA-256: {hashlib.sha256(original.encode()).hexdigest()}")
    print(f"Adapted reader SHA-256: {hashlib.sha256(adapted.encode()).hexdigest()}")


if __name__ == "__main__":
    main()
