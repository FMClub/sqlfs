#!/usr/bin/env python3
"""Post-processing of the extracted OCaml (TODO 6.6): a definition [let x = f a] (a partial application)
gets a weak type in OCaml; the type written by Coq's extraction in the comment [(** val x : t **)] above it
is added as an annotation, [let x : t =], so that the module type checks.

Usage: fix_weak.py sqlfs.ml
"""
import re
import sys

path = sys.argv[1]
lines = open(path, encoding='utf-8').read().split('\n')
out = []
pending = None
n = 0
for l in lines:
    m = re.match(r'^(\s*)\(\*\* val (\w+) : (.*) \*\*\)\s*$', l)
    if m:
        pending = (m.group(2), m.group(3))
        out.append(l)
        continue
    m2 = re.match(r'^(\s*)let (\w+) =\s*$', l) or re.match(r'^(\s*)let (\w+) = (.*)$', l)
    if pending and m2 and m2.group(2) == pending[0] and "'" not in pending[1]:
        indent, name = m2.group(1), m2.group(2)
        rest = l[l.index('=') + 1:]
        out.append('%slet %s : %s =%s' % (indent, name, pending[1], rest))
        n += 1
    else:
        out.append(l)
    if l.strip():
        pending = None if not m else pending
open(path, 'w', encoding='utf-8').write('\n'.join(out))
print('%d definitions annotated' % n)
