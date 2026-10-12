"""Print the import graph of the LocalAlgebrasLean library as an indented list, grouped by folder.

Usage: python tools/depgraph.py

Each Lean file's line lists the LocalAlgebrasLean files it imports directly (Mathlib imports are
not listed). Folders in the order of the library's construction: Region -> Net -> Lattice ->
Qudit. Adapted from LocalityLean's tool of the same name.
"""
import os
import re

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
SRC = os.path.join(ROOT, 'LocalAlgebrasLean')
FOLDERS = ['Region', 'Net', 'Lattice', 'Qudit']


def modules():
    out = {}
    for dirpath, _, files in os.walk(SRC):
        for f in sorted(files):
            if not f.endswith('.lean'):
                continue
            path = os.path.join(dirpath, f)
            name = os.path.relpath(path, ROOT)[:-5].replace(os.sep, '.')
            with open(path, encoding='utf-8') as fh:
                text = fh.read()
            out[name] = re.findall(r'(?m)^import (LocalAlgebrasLean\.\S+)', text)
    return out


def main():
    mods = modules()
    for folder in FOLDERS:
        names = sorted(n for n in mods if n.split('.')[1] == folder)
        if not names:
            continue
        print(f'- `{folder}/`')
        for n in names:
            deps = ', '.join('`' + d.split('.', 1)[1] + '`' for d in mods[n]) or 'Mathlib only'
            print(f"  - `{n.split('.', 1)[1]}` imports {deps}")


if __name__ == '__main__':
    main()
