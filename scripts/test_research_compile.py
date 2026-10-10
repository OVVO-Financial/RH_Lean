"""Cache regressions with a deterministic compiler stand-in, no Lean install."""
import contextlib
import io
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import compile_research_import_closure as cc


class ResearchCacheTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        (self.root / 'research').mkdir()
        (self.root / 'RHLean').mkdir()
        (self.root / 'scripts' / 'strongpnt_424').mkdir(parents=True)
        for name in ('lean-toolchain', 'lakefile.lean', 'lake-manifest.json', 'RHLean.lean'):
            (self.root / name).write_text(name)
        self.write('D', 'import Mathlib.Data.Nat.Basic\ndef d := 1\n')
        self.write('B', 'import «research.D»\ndef b := d\n')
        self.write('A', 'import research.B RHLean.Native\ndef a := b\n')
        self.write('C', 'import Mathlib.Data.Nat.Basic\ndef c := 4\n')
        (self.root / 'RHLean' / 'Native.lean').write_text('def native := 0\n')
        self.calls = []
        self.fake = patch.object(cc.subprocess, 'run', side_effect=self.compiler)
        self.fake.start()
        self.addCleanup(self.fake.stop)

    def write(self, name, text):
        (self.root / 'research' / f'{name}.lean').write_text(text)

    def compiler(self, command, cwd, check):
        self.assertEqual(command[:3], ['lake', 'env', 'lean'])
        self.assertIn('-DwarningAsError=true', command)
        self.assertTrue(check)
        self.assertEqual(cwd, self.root)
        source = Path(command[-1])
        self.calls.append(source.stem)
        out = Path(command[command.index('-o') + 1])
        out.write_bytes(b'compiled:' + source.read_bytes())
        if 'FAIL' in source.read_text():
            raise subprocess.CalledProcessError(1, command)

    def compile(self, targets=('A',), force=False):
        closure = cc.Closure(self.root)
        plan = closure.plan([self.root / 'research' / f'{t}.lean' for t in targets])
        with contextlib.redirect_stdout(io.StringIO()):
            result = closure.compile(force=force)
        return result, plan

    def artifact(self, name, suffix='.olean'):
        return self.root / '.lake/build/lib/lean' / f'research.{name}{suffix}'

    def test_warm_checkout_ignores_source_timestamps(self):
        self.assertEqual(self.compile()[0], (3, 0))
        self.assertEqual(self.calls, ['D', 'B', 'A'])
        for source in (self.root / 'research').glob('*.lean'):
            os.utime(source, (2_000_000_000, 2_000_000_000))
        self.assertEqual(self.compile()[0], (0, 3))

    def test_leaf_edit_reuses_ancestors(self):
        self.compile()
        self.write('A', 'import research.B RHLean.Native\ndef a := b + 1\n')
        self.assertEqual(self.compile()[0], (1, 2))

    def test_transitive_import_edit_rebuilds_descendants(self):
        self.compile()
        self.write('D', 'import Mathlib.Data.Nat.Basic\ndef d := 2\n')
        self.assertEqual(self.compile()[0], (3, 0))

    def test_unrelated_research_edit_keeps_closure(self):
        self.compile()
        self.write('C', 'def c := 42\n')
        self.assertEqual(self.compile()[0], (0, 3))

    def test_native_source_change_invalidates_research(self):
        self.compile()
        (self.root / 'RHLean' / 'Native.lean').write_text('def native := 1\n')
        self.assertEqual(self.compile()[0], (3, 0))

    def test_toolchain_manifest_lakefile_and_patch_changes(self):
        self.compile()
        for path in [self.root / 'lean-toolchain', self.root / 'lake-manifest.json',
                     self.root / 'lakefile.lean', self.root / 'scripts/strongpnt_424/apply.py']:
            with self.subTest(path=path.name):
                path.write_text('changed')
                self.assertEqual(self.compile()[0], (3, 0))

    def test_compiler_flags_change_invalidates_artifacts(self):
        self.compile()
        with patch.object(cc, 'FLAGS', ['-DwarningAsError=true', '-DmaxRecDepth=2048']):
            self.assertEqual(self.compile()[0], (3, 0))

    def test_missing_or_corrupt_artifact_is_rebuilt(self):
        self.compile()
        self.artifact('B').write_bytes(b'corrupt')
        self.assertEqual(self.compile()[0], (1, 2))
        self.artifact('D').unlink()
        self.assertEqual(self.compile()[0], (1, 2))

    def test_old_unverified_olean_and_invalid_record_are_rebuilt(self):
        self.compile()
        record = self.artifact('B', '.olean.json')
        for data in ['', '[]', '{"schema":"old"}']:
            with self.subTest(data=data):
                record.write_text(data)
                self.assertEqual(self.compile()[0], (1, 2))

    def test_failed_leaf_removes_stale_output_but_retains_ancestors(self):
        self.compile()
        self.write('A', 'import research.B\nFAIL\n')
        with self.assertRaises(subprocess.CalledProcessError):
            self.compile()
        self.assertFalse(self.artifact('A').exists())
        self.assertFalse(self.artifact('A', '.olean.json').exists())
        self.write('A', 'import research.B\ndef a := b\n')
        self.assertEqual(self.compile()[0], (1, 2))

    def test_multiple_roots_share_one_traversal(self):
        result, plan = self.compile(('A', 'B', 'C', 'A'))
        self.assertEqual(result, (4, 0))
        self.assertEqual(plan['library'], ['RHLean.Native'])
        self.assertEqual(plan['targets'], ['research.A', 'research.B', 'research.C'])
        self.assertEqual([m['module'] for m in plan['modules']], ['research.D', 'research.B', 'research.A', 'research.C'])

    def test_another_closure_reuses_verified_shared_prerequisites(self):
        _, first = self.compile(('A',))
        result, second = self.compile(('B', 'C'))
        self.assertEqual(result, (1, 2))
        self.assertEqual(first['environment'], second['environment'])
        self.assertEqual(first['modules'][:2], second['modules'][:2])
        self.assertEqual(self.compile(('A',))[0], (0, 3))

    def test_import_parser_ignores_comments_and_body(self):
        self.write('A', '/- nested /- import research.Absent -/ comment -/\n'
                   'module\npublic import «research.B» RHLean.Native -- import research.Absent\n'
                   'def a := "import research.Absent"\n')
        self.assertEqual(self.compile()[0], (3, 0))

    def test_cycles_and_missing_imports_fail_before_compilation(self):
        for source, exception in [('import research.A\n', ValueError),
                                  ('import research.Missing\n', FileNotFoundError)]:
            with self.subTest(source=source):
                self.write('D', source)
                with self.assertRaises(exception):
                    self.compile()
                self.assertEqual(self.calls, [])

    def test_targets_stay_inside_research(self):
        for source in [self.root / 'RHLean/Native.lean', self.root.parent / 'outside.lean']:
            with self.subTest(source=source), self.assertRaises(ValueError):
                cc.module_for_source(source, self.root)
        for module in ['RHLean.Native', 'research../bad', 'research.']:
            with self.subTest(module=module), self.assertRaises(ValueError):
                cc.source_for(module, self.root)

    def test_force_recompiles_verified_closure(self):
        self.compile()
        self.assertEqual(self.compile(force=True)[0], (3, 0))

    def test_source_changed_after_planning_is_never_stamped(self):
        closure = cc.Closure(self.root)
        closure.plan([self.root / 'research/A.lean'])
        self.write('A', 'import research.B\ndef a := b + 7\n')
        with self.assertRaisesRegex(RuntimeError, 'source changed after planning'):
            closure.compile()
        self.assertFalse(self.artifact('A', '.olean.json').exists())

    def test_source_changed_during_compile_discards_output(self):
        original = self.compiler
        def edit_during_compile(command, **kwargs):
            original(command, **kwargs)
            Path(command[-1]).write_text('def changed := 42\n')
        self.fake.side_effect = None
        with patch.object(cc.subprocess, 'run', side_effect=edit_during_compile):
            with self.assertRaisesRegex(RuntimeError, 'source changed during compilation'):
                self.compile()
        self.assertFalse(self.artifact('D').exists())
        self.assertFalse(self.artifact('D', '.olean.json').exists())

    def test_dag_routing_includes_transitive_inputs(self):
        _, plan = self.compile()
        for source in ['research/A.lean', 'research/B.lean', 'research/D.lean',
                       'RHLean/Native.lean', 'lakefile.lean', 'lean-toolchain',
                       'scripts/strongpnt_424/apply.py', '.github/actions/lean-setup/action.yml']:
            with self.subTest(source=source):
                self.assertTrue(cc.affected(plan, [source]))
        for source in ['research/C.lean', 'docs/example.md', 'export_other/Lean.lean']:
            with self.subTest(source=source):
                self.assertFalse(cc.affected(plan, [source]))

    def test_plan_keys_track_leaf_content_not_mtimes(self):
        _, initial = self.compile()
        os.utime(self.root / 'research/A.lean', None)
        self.assertEqual(initial, self.compile()[1])
        self.write('A', 'import research.B\ndef a := b + 5\n')
        changed = self.compile()[1]
        self.assertEqual(initial['environment'], changed['environment'])
        self.assertEqual(initial['modules'][:2], changed['modules'][:2])
        self.assertNotEqual(initial['modules'][-1]['key'], changed['modules'][-1]['key'])


if __name__ == '__main__':
    unittest.main()
