#!/usr/bin/env python3
"""Audit the concrete proof-only universe bridge, never runtime delegation."""
import argparse
import importlib.util
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('c1_independent_audit', ROOT / 'scripts/c1-independent-audit.py')
assert spec is not None and spec.loader is not None
helper = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helper)
EXPECTED = {'toReference_eval', 'fromReference_eval', 'source_roundtrip',
            'normalize_reference_sound', 'compareFast_reference_sound',
            'compareFast_source_sound', 'compareFast_inputs_sound',
            'encodeReferenceFinite_roundtrip', 'encodeReferenceFinite_eval',
            'encodeReferenceFinite_complete', 'compareSourceWith_sound',
            'compareSourceWith_different', 'compareSource_encoding_total',
            'compareSource_sound', 'compareSource_different',
            'compareSourceExactWith_true', 'compareSourceExactWith_false',
            'compareSourceExact_total', 'compareSourceExact_correct',
            'compareSourceExact_different'}

# Exact dependencies observed in warning-free semantic bridge run 38178500807.
ONLY_PROPEXT = {'toReference_eval', 'fromReference_eval', 'source_roundtrip'}
PROPEXT_QUOT = {'compareSourceExact_total', 'encodeReferenceFinite_roundtrip', 'encodeReferenceFinite_eval',
                'encodeReferenceFinite_complete', 'compareSourceWith_sound',
                'compareSource_encoding_total', 'compareSource_sound'}
EXPECTED_AXIOMS = {name: ['propext'] for name in ONLY_PROPEXT}
EXPECTED_AXIOMS.update({name: ['Quot.sound', 'propext'] for name in PROPEXT_QUOT})
EXPECTED_AXIOMS.update({name: sorted(helper.ALLOWED_AXIOMS)
                        for name in EXPECTED - ONLY_PROPEXT - PROPEXT_QUOT})
if set(EXPECTED_AXIOMS) != EXPECTED:
    raise ValueError('bridge theorem pin census is incomplete')

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('log', type=Path)
args = parser.parse_args()
source = ROOT / 'bridge/pskernel-c1/UniverseBridge.lean'
code = helper.code_only(source.read_text())
if re.search(r'\b(sorry|admit|axiom|unsafe|implemented_by|native_decide|extern)\b', code) or 'skipKernelTC' in code:
    raise ValueError('forbidden proof-bridge trust construct')
imports = re.findall(r'^\s*(?:(?:public|meta)\s+)*import\s+(?:all\s+)?([A-Za-z0-9_.]+)', code, re.M)
if set(imports) != {'ConLeche.Verify.Level', 'PskernelC1Independent.UniverseProofs',
                    'PskernelC1Independent.UniversePolynomialProofs',
                    'PskernelC1Independent.NameCodecProofs',
                    'PskernelC1Independent.UniverseAllSignsProofs'}:
    raise ValueError(f'bridge dependency change requires review: {imports}')
seen = {}
pattern = r"'PskernelC1Bridge\.([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)"
for name, raw in re.findall(pattern, args.log.read_text()):
    axioms = sorted(a.strip() for a in raw.split(',') if a.strip())
    if set(axioms) - helper.ALLOWED_AXIOMS:
        raise ValueError(f'unapproved bridge assumptions: {name}: {axioms}')
    seen[name] = axioms
if set(seen) != EXPECTED:
    raise ValueError(f'bridge theorem census mismatch: {sorted(seen)}')
for name in EXPECTED:
    if seen[name] != EXPECTED_AXIOMS[name]:
        raise ValueError(f'bridge axiom footprint changed: {name}: {seen[name]}')
print(json.dumps({'scope': 'universe semantic/input-fidelity bridge, not full kernel',
                  'theorem_axioms': seen}, indent=2))
