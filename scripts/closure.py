#!/usr/bin/env python3
"""Import closure of the FHX release roots across the workspace Lake packages.

Usage:
    closure.py [--workspace DIR] [--json OUT] [--quiet] [--extra-root MODULE ...]

In the release repository, `python3 scripts/closure.py` checks the repository itself (same layout
as the development workspace): every import resolves to a file of the repository.

Resolves every `import` of the release roots (Lean 4 header syntax: optional `module`/`prelude`,
then `[public] [meta] import [all] M` lines; comments are stripped first) to a `.lean` file of one of
the Lake packages of the `EnvelopeProperty` workspace (read from `EnvelopeProperty/lake-manifest.json`
and each package's `lakefile.toml`).  Modules of external packages (Mathlib, Batteries, Aesop, Qq,
ProofWidgets, Plausible, ImportGraph, LeanSearchClient, Cli, Lean, Init, Std, Lake) end the
traversal.  Any import that resolves to no file, or to more than one package, is an error.

Output (stdout): per-package counts.  With --json: a machine-readable closure used by assemble.sh:
    {"roots": [...], "packages": {name: {"dir": rel, "libs": [...], "modules": [...], "files": [...]}},
     "external_prefixes": {...}, "edges": n}
"""
import argparse
import json
import os
import re
import sys
import tomllib

RELEASE_ROOTS = [
    "EnvelopeProperty.MainTheoremFullyUnconditional",
    "EnvelopeProperty.MainTheorem",
    "EnvelopeProperty.Global.MainTheorem",
    "EnvelopeProperty.MainTheoremUnconditional",
    "EnvelopeProperty.Source.MainTheorem",
    "EnvelopeProperty.Source.Characterization",
    # errata certificates
    "EnvelopeProperty.Global.Lemma46Counterexample",
    "EnvelopeProperty.Global.PSH2HomogeneousMajorant",
    "EnvelopeProperty.Projective.Remark73ProjectiveLine",
    # supporting results (PSH2 for decreasing limits; FHX 2026-10-28 Lemma 7.4)
    "EnvelopeProperty.Global.EPDecreasingLimits",
    "EnvelopeProperty.Global.HomogeneousCarrierLimit",
    # definition fidelity: Variety.IsPSH is BJ22 Definition 4.1 when N^1(X)_R is finite dimensional
    "EnvelopeProperty.Source.FiniteDimensionalTopology",
]

EXTERNAL_PREFIXES = {
    "Mathlib", "Batteries", "Aesop", "Qq", "ProofWidgets", "Plausible", "ImportGraph",
    "LeanSearchClient", "Cli", "Lean", "Init", "Std", "Lake",
}

ROOT_PACKAGE_DIR = "EnvelopeProperty"


def strip_comments(src: str) -> str:
    """Remove (nested) block comments and line comments; keep string-free header text."""
    out = []
    i, n, depth = 0, len(src), 0
    while i < n:
        if src.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if depth > 0:
            if src.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                i += 1
            continue
        if src.startswith("--", i):
            j = src.find("\n", i)
            i = n if j < 0 else j
            continue
        out.append(src[i])
        i += 1
    return "".join(out)


IDENT = r"(?:«[^»]*»|[^\s«»]+)"
TOKEN_RE = re.compile(r"\s*(" + IDENT + r")")


def header_imports(path: str):
    """Return the imported module names of a Lean file (header only)."""
    with open(path, encoding="utf-8") as fh:
        text = strip_comments(fh.read())
    toks = []
    pos = 0
    while True:
        m = TOKEN_RE.match(text, pos)
        if not m:
            break
        toks.append(m.group(1))
        pos = m.end()
        if len(toks) > 20000:
            break
    imports = []
    i = 0
    if i < len(toks) and toks[i] == "module":
        i += 1
    if i < len(toks) and toks[i] == "prelude":
        i += 1
    while i < len(toks):
        j = i
        while j < len(toks) and toks[j] in ("public", "private", "meta"):
            j += 1
        if j < len(toks) and toks[j] == "import":
            j += 1
            if j < len(toks) and toks[j] == "all":
                j += 1
            if j >= len(toks):
                raise SystemExit(f"{path}: dangling import")
            imports.append(toks[j].replace("«", "").replace("»", ""))
            i = j + 1
        else:
            break
    return imports


def load_packages(ws: str):
    """Packages of the EnvelopeProperty Lake workspace: name -> (abs dir, [lib configs])."""
    root = os.path.join(ws, ROOT_PACKAGE_DIR)
    with open(os.path.join(root, "lake-manifest.json")) as fh:
        manifest = json.load(fh)
    dirs = {manifest["name"]: root}
    for p in manifest["packages"]:
        if p["type"] == "path":
            dirs[p["name"]] = os.path.normpath(os.path.join(root, p["dir"]))
    pkgs = {}
    for name, d in dirs.items():
        with open(os.path.join(d, "lakefile.toml"), "rb") as fh:
            cfg = tomllib.load(fh)
        libs = []
        for lib in cfg.get("lean_lib", []):
            roots = lib.get("roots", [lib["name"]])
            libs.append({"name": lib["name"], "roots": roots, "globs": lib.get("globs"),
                         "srcDir": lib.get("srcDir", ".")})
        pkgs[name] = {"dir": d, "config_name": cfg.get("name"), "libs": libs,
                      "srcDir": cfg.get("srcDir", ".")}
    return pkgs


def glob_matches(glob: str, mod: str) -> bool:
    if glob.endswith(".+"):
        return mod.startswith(glob[:-2] + ".")
    if glob.endswith(".*"):
        return mod == glob[:-2] or mod.startswith(glob[:-2] + ".")
    return mod == glob


def lib_owns(lib, mod: str) -> bool:
    """Lake's `LeanLib.isLocalModule`: a root is a prefix of `mod`, or a glob matches."""
    parts = mod.split(".")
    for r in lib["roots"]:
        rp = r.split(".")
        if parts[: len(rp)] == rp:
            return True
    for g in lib["globs"] or []:
        if glob_matches(g, mod):
            return True
    return False


def resolve(pkgs, mod: str):
    hits = []
    for pname, p in pkgs.items():
        for lib in p["libs"]:
            if lib_owns(lib, mod):
                base = os.path.join(p["dir"], p["srcDir"], lib["srcDir"])
                f = os.path.normpath(os.path.join(base, *mod.split(".")) + ".lean")
                if os.path.isfile(f):
                    hits.append((pname, lib["name"], f))
    uniq = {(h[0], h[2]) for h in hits}
    if len(uniq) > 1:
        raise SystemExit(f"ambiguous module {mod}: {sorted(uniq)}")
    return hits[0] if hits else None


def compute(ws: str, roots=RELEASE_ROOTS):
    pkgs = load_packages(ws)
    seen = {}
    ext = {}
    edges = 0
    stack = list(roots)
    importers = {r: "<release root>" for r in roots}
    while stack:
        mod = stack.pop()
        if mod in seen:
            continue
        top = mod.split(".")[0]
        if top in EXTERNAL_PREFIXES:
            ext[top] = ext.get(top, 0) + 1
            seen[mod] = None
            continue
        hit = resolve(pkgs, mod)
        if hit is None:
            raise SystemExit(f"unresolved import {mod} (imported by {importers.get(mod)})")
        seen[mod] = hit
        for imp in header_imports(hit[2]):
            edges += 1
            if imp not in seen:
                importers.setdefault(imp, mod)
                stack.append(imp)
    out = {"roots": list(roots), "workspace": ws, "packages": {}, "external_prefixes": ext,
           "edges": edges}
    for pname, p in pkgs.items():
        mods = sorted(m for m, h in seen.items() if h and h[0] == pname)
        out["packages"][pname] = {
            "dir": os.path.relpath(p["dir"], ws),
            "config_name": p["config_name"],
            "libs": sorted({seen[m][1] for m in mods}),
            "modules": mods,
            "files": [os.path.relpath(seen[m][2], ws) for m in mods],
        }
    return out


def main():
    ap = argparse.ArgumentParser()
    here = os.path.dirname(os.path.abspath(__file__))
    repo = os.path.dirname(here)
    default_ws = (repo if os.path.basename(here) == "scripts"
                  and os.path.isfile(os.path.join(repo, ROOT_PACKAGE_DIR, "lake-manifest.json"))
                  else ".")
    ap.add_argument("--workspace", default=default_ws)
    ap.add_argument("--json")
    ap.add_argument("--quiet", action="store_true")
    ap.add_argument("--extra-root", action="append", default=[],
                    help="additional root module (repeatable); also EXTRA_ROOTS=A,B in the environment")
    a = ap.parse_args()
    extra = a.extra_root + [r for r in os.environ.get("EXTRA_ROOTS", "").split(",") if r.strip()]
    res = compute(a.workspace, RELEASE_ROOTS + [r.strip() for r in extra if r.strip() not in RELEASE_ROOTS])
    if a.json:
        with open(a.json, "w") as fh:
            json.dump(res, fh, indent=1)
            fh.write("\n")
    if not a.quiet:
        total = 0
        print(f"{'package':28} {'dir':42} {'modules':>8}  libs")
        for pname, p in res["packages"].items():
            n = len(p["modules"])
            total += n
            print(f"{pname:28} {p['dir']:42} {n:8d}  {','.join(p['libs'])}")
        print(f"{'TOTAL':28} {'':42} {total:8d}")
        print("external import roots reached:", ", ".join(sorted(res["external_prefixes"])))
        print("import edges:", res["edges"])


if __name__ == "__main__":
    main()
