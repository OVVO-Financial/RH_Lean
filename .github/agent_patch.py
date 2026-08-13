from pathlib import Path

TARGET = Path('RHLean/Analysis/PrimeSievePNTGoodMassChargeAttack.lean')
FRAGMENT = Path('.github/good_mass_append.leanfrag')
END = 'end RHLean.Analysis\n'

if not FRAGMENT.exists():
    raise SystemExit(0)

fragment = FRAGMENT.read_text()
lines = fragment.splitlines()
assert lines, 'empty attack patch fragment'
mode = lines[0]
text = TARGET.read_text()
assert text.endswith(END), 'attack target no longer has expected namespace terminator'

if mode.startswith('-- ATTACK_PATCH: '):
    sentinel = mode
    if sentinel in text:
        raise SystemExit(0)
    body = text[:-len(END)].rstrip() + '\n\n' + fragment.rstrip() + '\n\n' + END
    TARGET.write_text(body)
    raise SystemExit(0)

if mode.startswith('-- ATTACK_REPLACE_TAIL: '):
    assert len(lines) >= 3 and lines[1].startswith('-- REPLACE_FROM: '), \
        'replacement patch missing REPLACE_FROM marker'
    old_sentinel = lines[1][len('-- REPLACE_FROM: '):]
    replacement = '\n'.join(lines[2:]).rstrip()
    pos = text.find(old_sentinel)
    assert pos >= 0, f'replacement sentinel not found: {old_sentinel}'
    prefix = text[:pos].rstrip()
    body = prefix + '\n\n' + replacement + '\n\n' + END
    TARGET.write_text(body)
    raise SystemExit(0)

raise AssertionError('unknown attack patch mode')
