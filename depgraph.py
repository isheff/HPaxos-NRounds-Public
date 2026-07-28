#!/usr/bin/env python3
"""Draw the EXTENDS dependency graph of a TLA+ module.

Given any module in the directory -- a top-level theorem like Termination, or a
single lemma buried in the middle of the tree -- this collects every module the
root reaches through EXTENDS, directly or transitively, and renders them as an
SVG.

Layout conventions:
  * the root is the single sink at the BOTTOM;
  * modules that extend nothing local sit at the TOP;
  * an edge A -> B means "A EXTENDS B";
  * edges already implied by a longer path are removed (transitive reduction),
    so every arrow drawn is a dependency you cannot reach any other way;
  * modules that state a THEOREM, or that introduce operator definitions, are
    drawn in bold (amber and blue respectively); plain LEMMA modules are grey.

Standard-library modules (Naturals, FiniteSetTheorems, ...) are referenced but
not drawn, since they do not live in the directory being graphed. Pass
--list-external to see which ones were skipped.

Every node links to its module on GitHub, so the SVG is clickable wherever it is
embedded. Point --base-url elsewhere, or --no-links to drop the anchors.

Requires Graphviz (`dot`) on PATH, or --engine to point at it.

Modules are read from TLA/ by default; use --dir for anything else.

Examples:
    python3 depgraph.py Termination
    python3 depgraph.py EventuallyKnown --dir split -o ek.svg --theme dark
    python3 depgraph.py Termination --format dot -o termination.dot
"""

import argparse
import os
import re
import shutil
import subprocess
import sys

# --------------------------------------------------------------------------- #
# Palettes.  Baked into the SVG as presentation attributes so the file renders
# standalone; CSS classes (nlem / nthm / ndef) are emitted too, so a host page
# can re-theme it by overriding fill/stroke.
# --------------------------------------------------------------------------- #

DEFAULT_BASE_URL = "https://github.com/isheff/HPaxos-NRounds-TLA/blob/main/TLA/"
DEFAULT_DIR = "TLA"

THEMES = {
    "light": {
        "lem": ("#f4f7fa", "#a3aebc", "#2b3441"),
        "thm": ("#f7e2b8", "#a3620c", "#5a3403"),
        "def": ("#d3e0f8", "#2b4fae", "#152b63"),
        "edge": "#9aa5b4",
    },
    "dark": {
        "lem": ("#1d2632", "#4a5666", "#cdd6e1"),
        "thm": ("#4a3208", "#e0a63f", "#f5cf88"),
        "def": ("#1b2c56", "#7d9fea", "#bcd0f6"),
        "edge": "#56616f",
    },
}


# --------------------------------------------------------------------------- #
# Parsing
# --------------------------------------------------------------------------- #

def strip_comments(text):
    """Remove (* ... *) block comments and \\* line comments, preserving newlines.

    Nesting is tracked, since TLA+ block comments nest. Characters inside a
    comment become spaces so that column/line positions stay usable.
    """
    out = []
    i, n, depth = 0, len(text), 0
    while i < n:
        if text.startswith("(*", i):
            depth += 1
            i += 2
            continue
        if text.startswith("*)", i) and depth > 0:
            depth -= 1
            i += 2
            continue
        if depth == 0 and text.startswith("\\*", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
            continue
        ch = text[i]
        out.append(ch if depth == 0 else ("\n" if ch == "\n" else " "))
        i += 1
    return "".join(out)


def module_body(text, name):
    """Text following this file's own `---- MODULE <name> ----` header."""
    m = re.search(r"-{4,}\s*MODULE\s+" + re.escape(name) + r"\s*-{4,}", text)
    return text[m.end():] if m else text


def parse_extends(body):
    """Names listed in the first EXTENDS clause, which may span several lines.

    A clause continues onto the next line exactly when what we have so far ends
    in a comma, which is how TLA+ writes multi-line EXTENDS.
    """
    m = re.search(r"\bEXTENDS\b", body)
    if not m:
        return []
    acc = ""
    for line in body[m.end():].split("\n"):
        acc += line
        if not acc.rstrip().endswith(","):
            break
        acc += " "
    names = (p.strip() for p in acc.split(","))
    return [p for p in names if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", p)]


def parse_definitions(body):
    """Top-level operator definitions: `Name ==` or `Name(args) ==`.

    The negative lookahead rejects `==` that is really the start of a `====`
    module-terminator rule.
    """
    pat = r"^([A-Za-z_][A-Za-z0-9_]*)\s*(?:\([^)]*\))?\s*==(?!=)"
    return [m.group(1) for m in re.finditer(pat, body, re.M)]


def scan(directory):
    """Read every .tla in `directory` -> {name: {extends, defs, theorem}}."""
    mods = {}
    for fname in sorted(os.listdir(directory)):
        if not fname.endswith(".tla"):
            continue
        name = fname[:-4]
        with open(os.path.join(directory, fname), encoding="utf-8",
                  errors="replace") as fh:
            body = module_body(strip_comments(fh.read()), name)
        mods[name] = {
            "extends": parse_extends(body),
            "defs": parse_definitions(body),
            "theorem": bool(re.search(r"^\s*THEOREM\b", body, re.M)),
        }
    return mods


# --------------------------------------------------------------------------- #
# Graph
# --------------------------------------------------------------------------- #

def closure(mods, root):
    """Modules reachable from `root` via EXTENDS, restricted to local modules."""
    seen, stack = set(), [root]
    while stack:
        cur = stack.pop()
        if cur in seen:
            continue
        seen.add(cur)
        stack.extend(m for m in mods[cur]["extends"] if m in mods)
    return seen


def reachability(adj):
    """{node: set of nodes reachable by one or more edges}. Cycle-tolerant."""
    reach, active = {}, set()

    def walk(n):
        if n in reach:
            return reach[n]
        if n in active:            # cycle: contribute nothing extra
            return set()
        active.add(n)
        acc = set()
        for m in adj[n]:
            acc.add(m)
            acc |= walk(m)
        active.discard(n)
        reach[n] = acc
        return acc

    for n in adj:
        walk(n)
    return reach


def transitive_reduction(adj):
    """Drop each edge n->m that some sibling edge n->k already reaches."""
    reach = reachability(adj)
    return {
        n: [m for m in kids
            if not any(m in reach[k] for k in kids if k != m)]
        for n, kids in adj.items()
    }


def longest_chain(adj, root):
    """Deepest EXTENDS path starting at `root`, as a list of module names."""
    depth = {}

    def d(n, path=()):
        if n in depth:
            return depth[n]
        if n in path:              # cycle guard
            return 0
        depth[n] = 1 + max([d(m, path + (n,)) for m in adj[n]], default=-1)
        return depth[n]

    for n in adj:
        d(n)
    chain, cur = [root], root
    while adj[cur]:
        cur = max(adj[cur], key=lambda m: depth[m])
        chain.append(cur)
    return chain


# --------------------------------------------------------------------------- #
# Rendering
# --------------------------------------------------------------------------- #

def kind(entry):
    """Which of the three visual classes a module belongs to."""
    if entry["theorem"]:
        return "thm"
    if entry["defs"]:
        return "def"
    return "lem"


def build_dot(adj, mods, theme, root, base_url):
    pal = THEMES[theme]
    lem_fill, lem_line, lem_text = pal["lem"]
    out = [
        "digraph deps {",
        f"  // EXTENDS dependencies of {root}, transitively reduced",
        "  rankdir=BT;",           # root at the bottom, roots-of-the-DAG on top
        "  splines=spline;",
        "  nodesep=0.16;",
        "  ranksep=0.75;",
        "  newrank=true;",
        "  bgcolor=\"transparent\";",
        f'  node [shape=box, style="rounded,filled", fillcolor="{lem_fill}",'
        f' color="{lem_line}", fontcolor="{lem_text}", fontname="Helvetica",'
        ' fontsize=11, height=0.30, margin="0.10,0.045", class="nlem"];',
        f'  edge [color="{pal["edge"]}", arrowsize=0.55, penwidth=0.85];',
    ]
    for name in sorted(adj):
        attrs = []
        if base_url:
            # Graphviz wraps the node in <a xlink:href=...> in SVG output.
            attrs.append(f'URL="{base_url}{name}.tla"')
            attrs.append('target="_blank"')
        k = kind(mods[name])
        if k != "lem":                     # "lem" is the node default
            fill, line, text = pal[k]
            attrs += [f'class="n{k}"', 'fontname="Helvetica-Bold"',
                      f'fillcolor="{fill}"', f'color="{line}"',
                      f'fontcolor="{text}"', "penwidth=1.5"]
        if attrs:
            out.append(f'  "{name}" [{", ".join(attrs)}];')
    for name in sorted(adj):
        for dep in sorted(adj[name]):
            out.append(f'  "{name}" -> "{dep}";')
    out.append("}")
    return "\n".join(out) + "\n"


def run_dot(dot_source, engine, fmt):
    """Pipe DOT through Graphviz. Returns bytes."""
    proc = subprocess.run(
        [engine, f"-T{fmt}",
         # Extra effort on crossing minimization and rank assignment; these
         # graphs have hub modules that otherwise produce long sweeping edges.
         "-Gmclimit=20", "-Gnslimit=20", "-Gnslimit1=20"],
        input=dot_source.encode("utf-8"),
        stdout=subprocess.PIPE, stderr=subprocess.PIPE,
    )
    if proc.returncode != 0:
        sys.exit("dot failed:\n" + proc.stderr.decode("utf-8", "replace"))
    return proc.stdout


# --------------------------------------------------------------------------- #

def main():
    ap = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    ap.add_argument("module", help="root module name, e.g. Termination or "
                                   "FreshDef (the .tla suffix is optional)")
    ap.add_argument("-d", "--dir", default=None, metavar="DIR",
                    help=f"directory holding the .tla modules "
                         f"(default: {DEFAULT_DIR}/, relative to the current "
                         "directory; a path given with the module name is "
                         "used instead when --dir is omitted)")
    ap.add_argument("-o", "--output", default=None,
                    help="output file (default: <module>_deps.<format>; "
                         "use - for stdout)")
    ap.add_argument("--format", default="svg",
                    help="svg (default), png, pdf, or dot to emit the DOT "
                         "source without invoking Graphviz")
    ap.add_argument("--theme", choices=sorted(THEMES), default="light",
                    help="baked-in palette (default: light)")
    ap.add_argument("--engine", default="dot", help="path to Graphviz dot")
    ap.add_argument("--base-url", default=DEFAULT_BASE_URL, metavar="URL",
                    help="each node links to <URL><Module>.tla "
                         f"(default: {DEFAULT_BASE_URL})")
    ap.add_argument("--no-links", action="store_true",
                    help="draw plain nodes with no hyperlinks")
    ap.add_argument("--no-reduce", action="store_true",
                    help="draw every EXTENDS edge, including ones already "
                         "implied by a longer path")
    ap.add_argument("--list-external", action="store_true",
                    help="also report referenced modules outside the directory")
    ap.add_argument("-q", "--quiet", action="store_true",
                    help="suppress the summary on stderr")
    args = ap.parse_args()

    root = os.path.basename(args.module)
    if root.endswith(".tla"):
        root = root[:-4]

    # An explicit --dir always wins; otherwise a path written alongside the
    # module name (TLA/Termination.tla) picks the directory; otherwise TLA/.
    directory = args.dir
    if directory is None:
        directory = (os.path.dirname(os.path.abspath(args.module))
                     if os.sep in args.module else DEFAULT_DIR)

    if not os.path.isdir(directory):
        sys.exit(f"no such directory: {directory!r}"
                 " -- pass -d/--dir to point at the .tla modules")

    mods = scan(directory)
    if root not in mods:
        near = [m for m in mods if m.lower().startswith(root.lower()[:4])][:8]
        hint = ("\nDid you mean: " + ", ".join(sorted(near))) if near else ""
        sys.exit(f"no module {root!r} in {directory}{hint}")

    local = closure(mods, root)
    full = {n: sorted({m for m in mods[n]["extends"] if m in local})
            for n in local}
    adj = full if args.no_reduce else transitive_reduction(full)

    n_full = sum(len(v) for v in full.values())
    n_drawn = sum(len(v) for v in adj.values())

    if not args.quiet:
        roots = sorted(n for n in local if not full[n])
        chain = longest_chain(full, root)
        counts = {"thm": 0, "def": 0, "lem": 0}
        for n in local:
            counts[kind(mods[n])] += 1
        print(f"{root}: {len(local)} modules, {n_drawn} edges drawn "
              f"({n_full} EXTENDS, {n_full - n_drawn} redundant)",
              file=sys.stderr)
        print(f"  bold: {counts['thm']} theorem, {counts['def']} definition; "
              f"{counts['lem']} lemma-only", file=sys.stderr)
        print(f"  roots ({len(roots)}): {', '.join(roots)}", file=sys.stderr)
        print(f"  longest chain ({len(chain)}): {' -> '.join(chain)}",
              file=sys.stderr)
        if args.list_external:
            ext = sorted({m for n in local for m in mods[n]["extends"]
                          if m not in mods})
            print(f"  external (not drawn): {', '.join(ext) or 'none'}",
                  file=sys.stderr)

    base_url = "" if args.no_links else args.base_url
    if base_url and not base_url.endswith("/"):
        base_url += "/"

    dot_source = build_dot(adj, mods, args.theme, root, base_url)

    if args.format == "dot":
        data = dot_source.encode("utf-8")
    else:
        engine = shutil.which(args.engine)
        if engine is None:
            sys.exit(f"Graphviz {args.engine!r} not found on PATH "
                     "(brew install graphviz), or pass --engine")
        data = run_dot(dot_source, engine, args.format)

    dest = args.output or f"{root}_deps.{args.format}"
    if dest == "-":
        sys.stdout.buffer.write(data)
    else:
        with open(dest, "wb") as fh:
            fh.write(data)
        if not args.quiet:
            print(f"  wrote {dest}", file=sys.stderr)


if __name__ == "__main__":
    main()
