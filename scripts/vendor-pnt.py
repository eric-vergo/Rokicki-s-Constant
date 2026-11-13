#!/usr/bin/env python3
"""Regenerate `vendor/PrimeNumberTheoremAnd/` from the PrimeNumberTheoremAnd project.

The second proof of the main theorem (`RokickiConstantPNT`) uses the prime number theorem in
arithmetic progressions, `WeakPNT_AP`, from
https://github.com/AlexKontorovich/PrimeNumberTheoremAnd. That project annotates its declarations
with LeanArchitect, whose `blueprint` attribute clashes with the one of Verso Blueprint, so the
project cannot be imported next to our blueprint. This script copies the files `WeakPNT_AP`
needs, at a pinned commit, and removes the LeanArchitect layer. Nothing else is changed: every
proof that is kept is kept verbatim.

Transformations, in order:

1. Take the import closure of `PrimeNumberTheoremAnd.Wiener` inside the project.
2. Remove `import Architect`.
3. Remove every `@[blueprint ...]` attribute and every `blueprint_comment /-- ... -/` command.
4. Truncate `Wiener.lean` after the proof of `WeakPNT_AP` (the rest of the file, on the
   Chebotarev density theorem, is not needed).
5. Remove the declarations listed in `DROP`: two lemmas stated with `sorry` and the one lemma
   that uses them. `WeakPNT_AP` does not depend on them.
6. Prepend a provenance line to each file.

Usage:  scripts/vendor-pnt.py [--source PATH]     (from the repository root)

Without `--source`, the pinned commit is cloned into a temporary directory. After running, check
the result with `lake build RokickiConstantPNT`.
"""

import argparse
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

REPO = "https://github.com/AlexKontorovich/PrimeNumberTheoremAnd"
COMMIT = "c39a751132c88b6e8080b74c74023fd95b3d8be0"  # tag v4.34.0
ROOT_MODULE = "PrimeNumberTheoremAnd.Wiener"
# file (relative to the project root) -> the declaration after whose proof the file is cut
TRUNCATE_AFTER = {"PrimeNumberTheoremAnd/Wiener.lean": "WeakPNT_AP"}
# file -> declarations to remove
DROP = {"PrimeNumberTheoremAnd/Wiener.lean": ["prelim_decay_2", "prelim_decay_3", "decay_alt"]}
DEST = Path("vendor")

IMPORT_RE = re.compile(r"^(?:public\s+)?import\s+(\S+)\s*$", re.M)


def module_path(module: str) -> str:
    return module.replace(".", "/") + ".lean"


def import_closure(src: Path) -> list[str]:
    seen, todo = set(), [ROOT_MODULE]
    while todo:
        module = todo.pop()
        if module in seen:
            continue
        seen.add(module)
        text = (src / module_path(module)).read_text()
        todo += [m for m in IMPORT_RE.findall(text) if m.startswith("PrimeNumberTheoremAnd.")]
    return sorted(seen)


def skip_doc_comment(text: str, i: int) -> int:
    """`text[i:]` starts with `/-`; return the index just past the matching `-/`."""
    depth, i = 1, i + 2
    while depth:
        if text.startswith("/-", i):
            depth, i = depth + 1, i + 2
        elif text.startswith("-/", i):
            depth, i = depth - 1, i + 2
        else:
            i += 1
    return i


def skip_string(text: str, i: int) -> int:
    """`text[i]` is `"`; return the index just past the closing quote."""
    i += 1
    while text[i] != '"':
        i += 2 if text[i] == "\\" else 1
    return i + 1


def strip_blueprint_attributes(text: str, name: str) -> tuple[str, int]:
    """Remove each `@[blueprint ...]` at the start of a line, up to its matching `]`."""
    out, pos, count = [], 0, 0
    for m in re.finditer(r"^@\[blueprint\b", text, re.M):
        if m.start() < pos:
            continue
        i, depth = m.start() + 2, 1
        while depth:
            if text.startswith("/-", i):
                i = skip_doc_comment(text, i)
            elif text[i] == '"':
                i = skip_string(text, i)
            else:
                if text[i] == ",":
                    # `@[blueprint ..., other]`: the other attribute would be lost.
                    if depth == 1:
                        sys.exit(f"{name}: `@[blueprint]` shares its brackets with another "
                                 f"attribute near offset {i}; extend the script")
                depth += {"[": 1, "]": -1}.get(text[i], 0)
                i += 1
        if text[i] != "\n":
            sys.exit(f"{name}: text after `@[blueprint ...]` on the same line near offset {i}")
        out.append(text[pos:m.start()])
        pos, count = i + 1, count + 1
    out.append(text[pos:])
    return "".join(out), count


def strip_blueprint_comments(text: str, name: str) -> tuple[str, int]:
    """Remove each `blueprint_comment /-- ... -/` command."""
    out, pos, count = [], 0, 0
    for m in re.finditer(r"^blueprint_comment\s*(?=/-)", text, re.M):
        i = skip_doc_comment(text, m.end())
        if text[i] != "\n":
            sys.exit(f"{name}: text after `blueprint_comment` near offset {i}")
        out.append(text[pos:m.start()])
        pos, count = i + 1, count + 1
    out.append(text[pos:])
    return "".join(out), count


def declaration_span(lines: list[str], decl: str, name: str) -> tuple[int, int]:
    """Lines `[start, end)` of the declaration `decl`: from its keyword line (and any modifier
    lines directly above it) to the next line that starts a new command in column 0."""
    starts = [k for k, line in enumerate(lines)
              if re.match(rf"(?:theorem|lemma)\s+{re.escape(decl)}\b", line)]
    if len(starts) != 1:
        sys.exit(f"{name}: expected exactly one declaration `{decl}`, found {len(starts)}")
    start = starts[0]
    while start > 0 and re.match(r"(set_option .* in|@\[.*\])\s*$", lines[start - 1]):
        start -= 1
    end = starts[0] + 1
    while end < len(lines) and (lines[end].strip() == "" or lines[end][0] in " \t"):
        end += 1
    return start, end


def squeeze_blank_lines(text: str) -> str:
    return re.sub(r"\n{3,}", "\n\n", text).rstrip("\n") + "\n"


def transform(rel: str, text: str) -> tuple[str, str]:
    notes = []
    text, n = re.subn(r"^import Architect\n", "", text, flags=re.M)
    if n:
        notes.append("removed `import Architect`")
    text, n = strip_blueprint_attributes(text, rel)
    if n:
        notes.append(f"removed {n} `@[blueprint]` attributes")
    text, n = strip_blueprint_comments(text, rel)
    if n:
        notes.append(f"removed {n} `blueprint_comment`s")
    if rel in TRUNCATE_AFTER:
        lines = text.split("\n")
        _, end = declaration_span(lines, TRUNCATE_AFTER[rel], rel)
        text = "\n".join(lines[:end])
        notes.append(f"truncated after `{TRUNCATE_AFTER[rel]}`")
    for decl in DROP.get(rel, []):
        lines = text.split("\n")
        start, end = declaration_span(lines, decl, rel)
        text = "\n".join(lines[:start] + lines[end:])
        notes.append(f"removed `{decl}`")
    if re.search(r"\bblueprint|\bArchitect\b", text):
        sys.exit(f"{rel}: LeanArchitect syntax is left after stripping")
    return squeeze_blank_lines(text), "; ".join(notes) or "unchanged"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--source", type=Path,
                        help="an existing checkout of PrimeNumberTheoremAnd at the pinned commit")
    args = parser.parse_args()
    if not Path("lakefile.toml").exists():
        sys.exit("run this script from the repository root")

    tmp = None
    if args.source is None:
        tmp = tempfile.mkdtemp(prefix="pnt-")
        subprocess.run(["git", "clone", "--quiet", "--filter=blob:none", REPO, tmp], check=True)
        subprocess.run(["git", "-C", tmp, "checkout", "--quiet", COMMIT], check=True)
        src = Path(tmp)
    else:
        src = args.source
    head = subprocess.run(["git", "-C", str(src), "rev-parse", "HEAD"], check=True,
                          capture_output=True, text=True).stdout.strip()
    if head != COMMIT:
        sys.exit(f"{src} is at {head}, expected {COMMIT}")

    out_dir = DEST / "PrimeNumberTheoremAnd"
    if out_dir.exists():
        shutil.rmtree(out_dir)
    report = []
    for module in import_closure(src):
        rel = module_path(module)
        text, notes = transform(rel, (src / rel).read_text())
        banner = (f"-- Vendored from {REPO}\n-- (commit {COMMIT}, file `{rel}`)\n"
                  f"-- by `scripts/vendor-pnt.py`: {notes}. Do not edit; see `vendor/README.md`.\n")
        dest = DEST / rel
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_text(banner + text)
        report.append(f"{rel}: {notes}")
    shutil.copyfile(src / "LICENSE", DEST / "LICENSE.PrimeNumberTheoremAnd")
    if tmp:
        shutil.rmtree(tmp)
    print("\n".join(report))


if __name__ == "__main__":
    main()
