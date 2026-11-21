#!/usr/bin/env python3
"""Check the output of [Print Assumptions] (TODO 6.7): every axiom which it lists must be in the allowed set.

  coqc -R . SQLFS testing/AssumptionsExt.v > out.txt; python3 ../tools/check_axioms.py < out.txt

The congruence of the evaluation ([SqlCongruence.v]) and the refinement between dialects ([Refinement.v]) rewrite
under the binders of the evaluation, with functional extensionality; they use no other axiom."""
import re
import sys

ALLOWED = {'FunctionalExtensionality.functional_extensionality_dep'}

bad, section = [], False
for line in sys.stdin:
    sys.stdout.write(line)
    if line.startswith('Axioms:'):
        section = True
        continue
    if line.startswith('Closed under the global context'):
        section = False
        continue
    m = re.match(r'^([A-Za-z_][A-Za-z0-9_.\']*)( :|\s*$)', line)
    if section and m:
        if m.group(1) not in ALLOWED:
            bad.append(m.group(1))
if bad:
    sys.exit('axioms outside the allowed set: ' + ', '.join(sorted(set(bad))))
