#!/usr/bin/env python3
"""Ensure the source check rejects real holes but ignores explanatory text."""
from pathlib import Path
import importlib.util

path = Path(__file__).with_name("check-source.py")
spec = importlib.util.spec_from_file_location("source_guard", path)
guard = importlib.util.module_from_spec(spec)
spec.loader.exec_module(guard)

bad = ["theorem gap : False := by sorry", "axiom gap : False",
       "example : True := by native_decide", "def bad := Lean.ofReduceBool"]
good = ['/- sorry /- axiom -/ native_decide -/ theorem ok : True := True.intro',
        'def description := "sorry is forbidden" -- axiom gap\n']
for source in bad:
    if not guard.violations(source):
        raise SystemExit(f"Forbidden source passed: {source}")
for source in good:
    if guard.violations(source):
        raise SystemExit("Explanatory text was mistaken for proof code")
try:
    guard.violations('/- unfinished')
except ValueError:
    pass
else:
    raise SystemExit("Malformed source passed the lexical guard")
print("All 7 source-guard controls passed.")
