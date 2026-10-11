#!/usr/bin/env bash
# tests/shake.sh — THE IMPORT GATE (task #235): `lake shake` proposals and
# `public import` demotability, both pinned.
#
# TWO HALVES, and they are orthogonal.  `shake` decides import LINES (is this
# edge needed at all?); the `public` keyword on a line is decided by
# `scripts/pub-import-plan.py`'s four-constraint fixpoint (is this edge a
# RE-EXPORT something else's public statement needs?).  Neither sees the
# other's question, so the gate runs both.
#
# ---------------------------------------------------------------------
# HALF (a): `lake shake --keep-implied`
#
# `shake` was upstreamed into Lake (`mathlib4#27632`) and ships with the
# toolchain; since task #231 made every file a `module` it runs on this tree
# unpatched (task #223 needed a vendored, patched copy for the classic tree,
# and `scripts/shake-setup.sh` is kept only as that record).
#
# IT IS A MINIMIZER, NOT AN UNUSED-IMPORT REMOVER.  Its default job is to
# relocate imports downward, so most of its `remove` lines come PAIRED with a
# compensating `add` somewhere in the tree and are refactorings, not
# findings.  Task #223's criterion is therefore the rule:
#
#     an import `I` of `M` may be removed only when the run
#     `lake shake --keep-implied --only M <roots>` reports the tree's NOISE
#     FLOOR and nothing more — no compensating addition anywhere.
#
# (The noise floor is what a run that minimizes nothing —
# `--only ConLeche.NoSuchModule` — still proposes: ~180 `add` lines, mostly
# `Std` internals a `grind`/`omega` proof term mentions.  Those adds are
# false: the tree builds without them.)
#
# Running that criterion is ~300 shake invocations, minutes of CPU — too slow
# for the standard battery.  So the gate pins the CHEAP half: one full run
# per executable entry point,
# and every `remove` it proposes must be on `tests/shake-allowlist.txt`,
# which is exactly the set the criterion rejected, one line of reason each.
# A NEW removal is therefore a gate failure, and the response is to run the
# criterion on that one module:
#
#     lake shake --keep-implied --only <Module> <common roots> <one entry point>
#
# and compare with the `--only ConLeche.NoSuchModule` floor.  If it is clean,
# delete the import; if it is compensated, add the line to the allowlist with
# the compensating addition as its reason.
#
# TWO CLASSES THE CRITERION STILL MISSES (task #223 §6), which is why the
# cold build is the arbiter and not this script: a bare `open N` needs `N` to
# EXIST and no constant analysis records that, and two individually-clean
# removals can JOINTLY orphan a third module.  Task #235 adds a third: a need
# that arises only INSIDE an elaboration-time splice (`#annotate_basis`'s
# `meta def`s over `eqA`) stores no constant, so shake does not see it — the
# build asked for `ConLeche/Kernel/StdAxioms.lean`'s `public meta import`
# back by name.
#
# WHAT `--keep-implied` COSTS, measured.  It preserves an import another
# import already implies, which is what keeps the proposal set from being a
# whole-tree restructuring — but it also means an unused import whose module
# is in some other import's closure is NOT proposed, and this gate is blind to
# it.  Probed: adding `import ConLeche.Kernel.PropWhen` (implied) to
# `ConLeche/MainTheorem.lean` passes; adding `import ConLeche.Frontend.Export`
# (not implied) fails with that line named.
#
# NOT SHAKEN.  `PinDump.lean` is a classic file (`lake shake` still
# refuses a non-`module` closure; `tests/ProofDeps.lean` was the other one
# until its gate retired at task #305), and `tests/*` is blind
# to shake anyway: the suite is `#guard`/`example`-based and an `example`
# stores no constant, so `moduleData.constants` sees nothing of it (#223 §8).
#
# ---------------------------------------------------------------------
# HALF (b): `scripts/pub-import-plan.py --check`
#
# `public import X` is for a re-export; a plain `import X` still resolves
# every name, so an over-public tree does not fail to build — it fails
# NOTHING, which is why this needs a model rather than the compiler.  The
# check starts from the tree's actual `public` set and reports any edge that
# can be demoted on its own.  Its two inputs are dumped here from the built
# oleans (~1 min); `PUBPLAN_DIR` says where.
#
# ---------------------------------------------------------------------
# Needs a built tree (`lake build`).  Called by `tests/arena.sh`.

set -uo pipefail
cd "$(dirname "$0")/.."

# The executables each declare global `main`, so they cannot share a Lean
# environment.  Audit each against the FULL common proof/runtime roots;
# neither entry point loses coverage and neither is renamed for the audit.
COMMON_ROOTS=(ConLeche.MainTheorem ConLeche.Verify.Cached ConLeche.Model
              ConLeche.Semantics ConLeche.Complete ConLeche.SetModel
              ConLeche.Term ConLeche ConLeche.PinGen.Certs PskernelC1.Soundness)
ENTRIES=(Main PskernelC1.Main)

ALLOW=tests/shake-allowlist.txt
WORK=${PUBPLAN_DIR:-_tmp/shake-gate}
mkdir -p "$WORK" || exit 3
fail=0

# --- (a) shake ------------------------------------------------------
: > "$WORK/shake.txt" || exit 3
for entry in "${ENTRIES[@]}"; do
  if ! shake_out=$(lake shake --keep-implied "${COMMON_ROOTS[@]}" "$entry" 2>&1); then :; fi
  if printf '%s\n' "$shake_out" | grep -q '^error:'; then
    echo "SHAKE GATE ERROR — lake shake did not run for $entry:"
    printf '%s\n' "$shake_out" | sed 's/^/    /' | head -10
    exit 3
  fi
  printf '%s\n' "$shake_out" >> "$WORK/shake.txt" || exit 3
done

python3 - "$ALLOW" "$PWD" "$WORK/shake.txt" "$WORK/new-modules.txt" <<'PY' || fail=1
import sys
allow_path, root, shake_out, new_modules = sys.argv[1], sys.argv[2].rstrip('/') + '/', sys.argv[3], sys.argv[4]
allowed = set()
for line in open(allow_path):
    line = line.split('#', 1)[0].strip()
    if line:
        allowed.add(tuple(x.strip() for x in line.split('\t') if x.strip()))
cur, props = None, []
for line in open(shake_out).read().split('\n'):
    if line.startswith('/'):
        cur = line.rstrip(':').replace(root, '')
    elif line.strip().startswith('remove #[') and cur:
        body = line.strip().split('#[', 1)[1].rstrip(']')
        for item in body.split(', '):
            if item.strip():
                props.append((cur, item.strip()))
# Common modules occur in both environments; an import edge is one proposal.
props = sorted(set(props))
new = [p for p in props if p not in allowed]
stale = sorted(allowed - set(props))
with open(new_modules, 'w') as out:
    for path in sorted({f for f, _ in new}):
        out.write(path.removesuffix('.lean').replace('/', '.') + '\n')
if new:
    print(f'SHAKE GATE FAIL — {len(new)} import removal(s) not on {allow_path}:')
    for f, i in new:
        print(f'    {f}: {i}')
    print('    Run the task #223 criterion on each module before deleting it')
    print('    (see this script\'s header), then either remove the import or')
    print('    record it in the allowlist with its compensating addition.')
if stale:
    print(f'SHAKE GATE FAIL — {len(stale)} allowlist line(s) no longer proposed:')
    for f, i in stale:
        print(f'    {f}: {i}')
    print(f'    Delete them from {allow_path}.')
if not new and not stale:
    print(f'shake: {len(props)} removals proposed, all {len(allowed)} allowlisted')
sys.exit(1 if (new or stale) else 0)
PY

# A new C1 proof-edge proposal needs the documented per-module criterion.
# Print its exact difference from the noise floor in both executable views.
# This diagnoses the failure; it neither changes the allowance nor passes it.
if grep -Fxq 'PskernelC1.Soundness' "$WORK/new-modules.txt"; then
  for entry in "${ENTRIES[@]}"; do
    floor="$WORK/noise.$entry.txt"
    candidate="$WORK/soundness.$entry.txt"
    lake shake --keep-implied --only ConLeche.NoSuchModule \
      "${COMMON_ROOTS[@]}" "$entry" > "$floor" 2>&1
    lake shake --keep-implied --only PskernelC1.Soundness \
      "${COMMON_ROOTS[@]}" "$entry" > "$candidate" 2>&1
    echo "C1 proof import criterion ($entry): difference from the noise floor"
    diff -u "$floor" "$candidate" || true
  done
fi

# --- (b) the `public` keyword ---------------------------------------
COMMON_MODS=$(git ls-files 'ConLeche/*.lean' 'PskernelC1/*.lean' | sed 's/\.lean$//;s|/|.|g' \
        | grep -Ev '^(ConLeche\.Challenge|PskernelC1\.Main)$'; echo ConLeche)
: > "$WORK/census.tsv" || exit 3
: > "$WORK/pub.tsv" || exit 3
: > "$WORK/contexts.tsv.tmp" || exit 3
for entry in "${ENTRIES[@]}"; do
  census="census.$entry.tsv"
  pub="pub.$entry.tsv"
  : > "$WORK/$pub.err" || exit 3
  if ! lake env lean --run scripts/dead-census.lean $COMMON_MODS "$entry" \
        > "$WORK/$census" 2> "$WORK/$census.err" \
     || ! lake env lean --run scripts/pub-iface.lean $COMMON_MODS "$entry" \
        > "$WORK/$pub" 2> "$WORK/$pub.err"; then
    echo "SHAKE GATE ERROR — the census/interface dump failed for $entry:"
    cat "$WORK/$census.err" "$WORK/$pub.err" 2>/dev/null | sed 's/^/    /' | head -10
    exit 3
  fi
  cat "$WORK/$census" >> "$WORK/census.tsv" || exit 3
  cat "$WORK/$pub" >> "$WORK/pub.tsv" || exit 3
  printf '%s\t%s\t%s\n' "$entry" "$census" "$pub" >> "$WORK/contexts.tsv.tmp" || exit 3
done
# Keep combined dumps for inspection, but preserve each context for name
# resolution and source-only obligations in the planner.  Publish its input
# manifest only after all context pairs have completed successfully.
mv "$WORK/contexts.tsv.tmp" "$WORK/contexts.tsv" || exit 3
pubout=$(PUBPLAN_DIR="$WORK" python3 scripts/pub-import-plan.py --check 2>&1); pubst=$?
printf '%s\n' "$pubout" | grep -v '^model imprecision (' | grep -v '^model imprecision at'
[ "$pubst" = 0 ] || fail=1

exit $fail
