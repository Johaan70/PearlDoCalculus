#!/usr/bin/env bash
# Gate for every cleanup commit. Ends with "CHECK OK" or "CHECK FAILED".
#   scripts/check.sh             full check
#   scripts/check.sh --baseline  (owner only) write verification/public_statements.txt
set -u
cd "$(git rev-parse --show-toplevel)" || exit 1
BASE=v4.85   # tag where the gate and the reference statements were frozen
LOG=/tmp/pdc_check_build.log
fail=0
bad() { echo "FAIL: $*"; fail=1; }

echo "== 1. full build"
lake build > "$LOG" 2>&1
grep -q "Build completed successfully" "$LOG" || { tail -40 "$LOG"; echo "FAIL: build did not complete"; echo "CHECK FAILED"; exit 1; }
if grep -nE "^error|: error" "$LOG" | head -5 | grep -q .; then bad "errors in build log"; fi
n=$(grep -c "declaration uses 'sorry'" "$LOG"); [ "$n" -eq 0 ] || bad "$n sorry warnings"

echo "== 2. forbidden constructs (outside comments)"
python3 - << 'PY' || fail=1
import re, pathlib, sys
words = re.compile(r"\b(sorry|admit|native_decide|implemented_by|unsafe)\b|@\[extern|^\s*(private\s+|noncomputable\s+)?axiom\b", re.M)
hits = 0
for p in [pathlib.Path("PearlDoCalculus.lean"), *sorted(pathlib.Path("PearlDoCalculus").rglob("*.lean"))]:
    s = p.read_text()
    # strip block comments (nested) and line comments, keep line structure
    out, depth, i = [], 0, 0
    while i < len(s):
        if s.startswith("/-", i): depth += 1; i += 2; continue
        if depth and s.startswith("-/", i): depth -= 1; i += 2; continue
        if depth: out.append("\n" if s[i] == "\n" else " "); i += 1; continue
        if s.startswith("--", i):
            j = s.find("\n", i); j = len(s) if j < 0 else j
            out.append(" " * (j - i)); i = j; continue
        out.append(s[i]); i += 1
    code = "".join(out)
    for m in words.finditer(code):
        hits += 1; print(f"  {p}:{code.count(chr(10), 0, m.start()) + 1}: {m.group(0).strip()}")
print(f"  hits: {hits}")
sys.exit(1 if hits else 0)
PY

echo "== 3. audit and axioms"
lake env lean verification/AuditV480.lean > /tmp/pdc_check_audit.log 2>&1 || bad "AuditV480.lean did not run"
grep -q "error" /tmp/pdc_check_audit.log && bad "errors in audit"
good=$(grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]$" /tmp/pdc_check_audit.log)
all=$(grep -c "depends on axioms" /tmp/pdc_check_audit.log)
[ "$good" -eq 15 ] && [ "$all" -eq 15 ] || bad "axioms: $good of $all lines standard, expected 15 of 15"

echo "== 4. public statements"
lake env lean verification/PublicStatements.lean > /tmp/pdc_public.txt 2>&1 || bad "PublicStatements.lean did not run"
if [ "${1:-}" = "--baseline" ]; then
  cp /tmp/pdc_public.txt verification/public_statements.txt
  echo "  baseline written ($(wc -l < verification/public_statements.txt) lines)"
else
  diff -u verification/public_statements.txt /tmp/pdc_public.txt > /tmp/pdc_public.diff || { head -40 /tmp/pdc_public.diff; bad "a public statement changed"; }
  git diff --quiet "$BASE" -- scripts/check.sh verification/AuditV480.lean verification/PublicStatements.lean verification/public_statements.txt \
    || bad "a frozen file differs from $BASE"
fi

if [ "$fail" -eq 0 ]; then echo "CHECK OK"; else echo "CHECK FAILED"; exit 1; fi
