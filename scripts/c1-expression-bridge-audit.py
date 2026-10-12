#!/usr/bin/env python3
"""Audit the independent expression-to-ConLeche refinement proof."""
import importlib.util
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('independent_c1', ROOT / 'scripts/c1-independent-audit.py')
assert spec and spec.loader
helper = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helper)

SOURCE = ROOT / 'bridge/pskernel-c1/ExprBridge.lean'
text = helper.code_only(SOURCE.read_text())
if re.search(r'\b(sorry|admit|axiom|unsafe|implemented_by|native_decide|extern)\b', text):
    raise ValueError('untrusted proof construct in expression bridge')
imports = set(re.findall(r'^\s*(?:(?:public|meta)\s+)*import\s+([\w.]+)', text, re.M))
if imports != {'ConLeche.Kernel.ExprOps', 'PskernelC1Independent.ExprSubstProofs',
               'PskernelC1Independent.ExprAbstractProofs'}:
    raise ValueError(f'unexpected proof bridge imports: {imports}')

EXPECTED = {'name_roundtrip', 'name_translation_injective',
            'literal_roundtrip', 'literal_translation_injective',
            'scoped_reference_bvars', 'instantiateAt_reference_closed',
            'instantiate1_reference_closed', 'instantiate1_checked_reference',
            'abstractAt_reference', 'abstract1_reference'}
ALLOWED = helper.ALLOWED_AXIOMS
log = Path(sys.argv[1]).read_text()
seen = {}
for name, raw in re.findall(
        r"'PskernelC1ExprBridge\.([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",
        log):
    axioms = sorted(x.strip() for x in raw.split(',') if x.strip())
    if set(axioms) - ALLOWED:
        raise ValueError(f'extra proof assumption in {name}: {axioms}')
    seen[name] = axioms
if set(seen) != EXPECTED:
    raise ValueError(f'partial theorem census: {seen}')
# All six source-level bridge theorems had exactly the standard footprint
# in cloud run 38195107226; any subsequent change requires explicit review.
# Exact observed footprints at source 9a58dbb6, run 38195409790.
EXPECTED_AXIOMS = {name: sorted(ALLOWED) for name in EXPECTED}
for name in ('name_roundtrip', 'name_translation_injective'):
    EXPECTED_AXIOMS[name] = ['propext']
for name in ('literal_roundtrip', 'literal_translation_injective'):
    EXPECTED_AXIOMS[name] = []
for name, actual in seen.items():
    if actual != EXPECTED_AXIOMS[name]:
        raise ValueError(f'changed exact bridge axiom footprint: {name}: {actual}')
print(json.dumps({'scope': 'expression mapping and closed-substitution refinement',
                  'proofs': seen}, indent=2))
