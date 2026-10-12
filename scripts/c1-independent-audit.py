#!/usr/bin/env python3
"""Check the independent component's source fence and named theorem footprints."""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
BASE_CAPSTONES = {
    'eval_substitute', 'substitute_identity', 'substitute_compose', 'eval_rename',
    'eval_maxSmart', 'eval_imaxSmart', 'eval_normalize', 'normalize_sound',
    'compareFast_sound', 'compareFast_reflexive', 'unknown_can_be_equivalent',
}
POLYNOMIAL_CAPSTONES = {'toPolynomial_sound', 'comparePolynomial_sound',
                       'comparePolynomial_different', 'comparePolynomial_complete',
                       'comparePolynomial_decides'}
SIGN_CAPSTONES = {'zeroAtSigns_spec', 'compileSigned_eval',
                   'compareSigned_correct', 'compareSigned_successor_different'}
ALL_SIGN_CAPSTONES = {'eval_ext_parameterIds', 'signed_reconstruct', 'signPatterns_cover', 'compareExhaustive_correct', 'compareExhaustive_different'}
CAPSTONES = BASE_CAPSTONES | POLYNOMIAL_CAPSTONES | SIGN_CAPSTONES | ALL_SIGN_CAPSTONES
PREFIX = 'PskernelC1Independent.Level.'
CODEC_PREFIX = 'PskernelC1Independent.NameCodec.'
CODEC_CAPSTONES = {'get?_mem', 'index?_sound', 'index?_complete', 'index?_none_iff', 'index?_injective', 'index?_append_left'}
# Observed on 2026-10-12 in source run 38178205029: these are exact, not merely an allowlist.
CODEC_EXPECTED_AXIOMS = {short: ['propext'] for short in CODEC_CAPSTONES}
CODEC_EXPECTED_AXIOMS['index?_append_left'] = sorted(['propext', 'Quot.sound'])
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
EXPECTED_AXIOMS = {name: ['propext'] for name in BASE_CAPSTONES}
EXPECTED_AXIOMS['eval_maxSmart'] = sorted(['propext', 'Quot.sound'])
for _name in ('eval_imaxSmart', 'eval_normalize', 'normalize_sound', 'compareFast_sound'):
    EXPECTED_AXIOMS[_name] = sorted(ALLOWED_AXIOMS)
# Exact polynomial footprints observed in the successful warning-free build
# at a2476126606850347c8a209f9ebd8adb56fecd1c, run 38173757176.
for _name in ('toPolynomial_sound', 'comparePolynomial_sound', 'comparePolynomial_decides'):
    EXPECTED_AXIOMS[_name] = sorted(['propext', 'Quot.sound'])
for _name in ('comparePolynomial_different', 'comparePolynomial_complete'):
    EXPECTED_AXIOMS[_name] = sorted(ALLOWED_AXIOMS)
for _name in SIGN_CAPSTONES:
    EXPECTED_AXIOMS[_name] = sorted(ALLOWED_AXIOMS)  # Exact results observed in run 38179075499.
# Exact capstone footprints observed in proof run 38179321642.
EXPECTED_AXIOMS['eval_ext_parameterIds'] = ['propext']
for _name in ('signed_reconstruct', 'signPatterns_cover'):
    EXPECTED_AXIOMS[_name] = sorted(['propext', 'Quot.sound'])
for _name in ('compareExhaustive_correct', 'compareExhaustive_different'):
    EXPECTED_AXIOMS[_name] = sorted(ALLOWED_AXIOMS)
CONTEXT_CAPSTONES = {'LocalContext.lookup_bounded', 'LocalContext.lookup_unique',
                     'Expr.inferHeadIn_sound', 'Expr.inferHeadIn_complete',
                     'Expr.inferHeadIn_iff', 'Expr.inferHeadIn_unique'}
INFER_CAPSTONES = {'Scoped.weakenFVars', 'inferHead_sound', 'inferHead_complete',
                    'inferHead_iff', 'inferHead_output_scoped', 'inferHead_invalidScope',
                    'inferHead_unsupported_scoped'}
EXPR_CAPSTONES = {'checkScoped_sound', 'checkScoped_complete', 'checkScoped_iff', 'Scoped.lift', 'checkScoped_lift',
                   'lift_zero', 'instantiate1_bvar0', 'instantiateAt_preserves_scope',
                   'instantiate1_preserves_scope', 'lift_above_scope', 'lift_closed', 'abstractAt_preserves_scope',
                   'abstract1_preserves_scope', 'checkScoped_abstract1'}
EXPR_PREFIX = 'PskernelC1Independent.Expr.'
# New expression proof assumptions are audited by exact output after first CI compilation.
if set(EXPECTED_AXIOMS) != CAPSTONES:
    raise ValueError('every active capstone must have an exact dependency pin')


def code_only(text: str) -> str:
    """Preserve lines while omitting nested comments and quoted strings."""
    out: list[str] = []
    i, depth = 0, 0
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                depth += 1
                i += 2
            elif text.startswith('-/', i):
                depth -= 1
                i += 2
            else:
                out.append('\n' if text[i] == '\n' else ' ')
                i += 1
        elif text.startswith('/-', i):
            depth = 1
            out.append(' ')
            i += 2
        elif text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        elif text[i] == '"':
            i += 1
            while i < len(text) and text[i] != '"':
                if text[i] == '\\':
                    i += 2
                else:
                    out.append('\n' if text[i] == '\n' else ' ')
                    i += 1
            i += 1
            out.append(' ')
        else:
            out.append(text[i])
            i += 1
    if depth:
        raise ValueError('unterminated source comment')
    return ''.join(out)


def audit_source() -> list[dict]:
    files = sorted(p for p in (ROOT / 'independent').rglob('*.lean')
                   if '.lake' not in p.parts)
    if not files:
        raise ValueError('independent source is missing')
    report = []
    for path in files:
        text = path.read_text()
        code = code_only(text)
        if re.search(r'\b(sorry|admit|axiom|unsafe|implemented_by|native_decide|extern)\b', code):
            raise ValueError(f'forbidden trust construct in {path.relative_to(ROOT)}')
        if 'skipKernelTC' in code:
            raise ValueError('kernel checking must not be disabled')
        imports = re.findall(r'^\s*(?:(?:public|meta)\s+)*import\s+(?:all\s+)?([A-Za-z0-9_.]+)', code, re.M)
        if any(not (i == 'Init' or i.startswith('Init.') or
                    i == 'PskernelC1Independent' or i.startswith('PskernelC1Independent.'))
               for i in imports):
            raise ValueError(f'unapproved dependency in {path.relative_to(ROOT)}: {imports}')
        if path.name in ('Universe.lean', 'UniversePolynomial.lean', 'Expr.lean', 'ExprSubst.lean', 'ExprAbstract.lean', 'InferHead.lean', 'InferContext.lean') and any('Proof' in i for i in imports):
            raise ValueError('executable universe operations import proofs')
        report.append({'path': str(path.relative_to(ROOT)), 'imports': imports,
                       'sha256': hashlib.sha256(text.encode()).hexdigest()})
    manifest = ROOT / 'independent/lake-manifest.json'
    if manifest.exists() and json.loads(manifest.read_text()).get('packages'):
        raise ValueError('independent component unexpectedly has external packages')
    return report


def audit_axioms(log: str) -> dict[str, list[str]]:
    pattern = r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)"
    seen: dict[str, list[str]] = {}
    for name, raw in re.findall(pattern, log):
        if name.startswith(PREFIX) or name.startswith(CODEC_PREFIX) or name.startswith(EXPR_PREFIX) or name.startswith('PskernelC1Independent.LocalContext.'):
            axioms = sorted(a.strip() for a in raw.split(',') if a.strip())
            if set(axioms) - ALLOWED_AXIOMS:
                raise ValueError(f'unapproved theorem dependency: {name}: {axioms}')
            if name in seen and seen[name] != axioms:
                raise ValueError(f'inconsistent repeated audit: {name}')
            seen[name] = axioms
    expected = {PREFIX + name for name in CAPSTONES} | {CODEC_PREFIX + name for name in CODEC_CAPSTONES} | {EXPR_PREFIX + name for name in EXPR_CAPSTONES | INFER_CAPSTONES} | {'PskernelC1Independent.' + name for name in CONTEXT_CAPSTONES}
    if set(seen) != expected:
        raise ValueError(f'capstone census mismatch; missing={sorted(expected-set(seen))}, extra={sorted(set(seen)-expected)}')
    for short, axioms in EXPECTED_AXIOMS.items():
        if seen[PREFIX + short] != axioms:
            raise ValueError(f'changed axiom footprint: {short}: {seen[PREFIX + short]}')
    for short, axioms in CODEC_EXPECTED_AXIOMS.items():
        if seen[CODEC_PREFIX + short] != axioms:
            raise ValueError(f'changed source-name codec axiom footprint: {short}: {seen[CODEC_PREFIX + short]}')
    return seen


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--axioms', type=Path)
    parser.add_argument('--output', type=Path, default=ROOT / '_tmp/c1-next/independent-audit.json')
    args = parser.parse_args()
    report = {'scope': 'independent universe components, not full kernel',
              'sources': audit_source()}
    if args.axioms:
        report['theorem_axioms'] = audit_axioms(args.axioms.read_text())
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
