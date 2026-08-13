from pathlib import Path

TARGET = Path('RHLean/Analysis/PrimeSievePNTGoodMassChargeAttack.lean')
FRAGMENT = Path('.github/good_mass_append.leanfrag')
END = 'end RHLean.Analysis\n'

if not FRAGMENT.exists():
    raise SystemExit(0)

fragment = FRAGMENT.read_text()
lines = fragment.splitlines()
assert lines and lines[0].startswith('-- ATTACK_PATCH: '), 'missing attack patch sentinel'
sentinel = lines[0]

text = TARGET.read_text()
if sentinel in text:
    raise SystemExit(0)
assert text.endswith(END), 'attack target no longer has expected namespace terminator'

body = text[:-len(END)].rstrip() + '\n\n' + fragment.rstrip() + '\n\n' + END
TARGET.write_text(body)
