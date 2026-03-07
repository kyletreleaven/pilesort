#!/usr/bin/env python3
"""Regenerate the PileSort theorem dependency graph.

Runs tools/graph.lean via `lake env lean --run` to extract dependencies
from the elaborated Lean environment, then renders with Graphviz.

Usage:
  python tools/graph.py              # render SVG and open in browser
  python tools/graph.py --dot        # print DOT source to stdout
  python tools/graph.py -o out.svg   # write SVG to file

Requires: graphviz (dot) on PATH.
"""

import argparse
import subprocess
import sys
import tempfile
import webbrowser
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LEAN_SCRIPT = ROOT / "tools" / "graph.lean"


def lean_extract() -> str:
    """Run the Lean extractor and return the DOT source."""
    result = subprocess.run(
        ["lake", "env", "lean", "--run", str(LEAN_SCRIPT)],
        cwd=ROOT,
        capture_output=True,
        text=True,
    )
    if result.stderr:
        sys.stderr.write(result.stderr)
    if result.returncode != 0:
        sys.exit(result.returncode)
    return result.stdout


def dot_render(dot_src: str, out: Path, fmt: str = "svg") -> None:
    """Render DOT source to a file using Graphviz."""
    result = subprocess.run(
        ["dot", f"-T{fmt}", "-o", str(out)],
        input=dot_src,
        capture_output=True,
        text=True,
    )
    if result.returncode != 0:
        sys.stderr.write(result.stderr)
        sys.exit(result.returncode)


def main() -> None:
    p = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    p.add_argument(
        "--dot", action="store_true",
        help="print DOT source to stdout instead of rendering",
    )
    p.add_argument(
        "-o", "--output", metavar="FILE",
        help="write rendered output to FILE (format inferred from extension)",
    )
    args = p.parse_args()

    print("Extracting from Lean environment...", file=sys.stderr)
    dot = lean_extract()

    if args.dot:
        print(dot, end="")
        return

    if args.output:
        out = Path(args.output)
        fmt = out.suffix.lstrip(".") or "svg"
        dot_render(dot, out, fmt)
        print(f"Wrote {out}")
    else:
        with tempfile.NamedTemporaryFile(suffix=".svg", delete=False) as f:
            out = Path(f.name)
        dot_render(dot, out, "svg")
        print(f"Opening {out}", file=sys.stderr)
        webbrowser.open(out.as_uri())


if __name__ == "__main__":
    main()
