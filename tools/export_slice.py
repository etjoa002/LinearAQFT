"""Export a slice as a standalone Lake package.

Usage: python tools/export_slice.py slices/dimock-abstract.toml --out <new directory>

Copies, verbatim, the LinearAQFT modules in the slice's closure (as checked by
tools/slice_closure.py) and the facade into a new directory, with a lakefile that pins the
same Mathlib, LocalAlgebrasLean, BosonicLean and Lean toolchain as this repository, and a
README naming the source commit, the targets and the lecture-notes labels. Build the result with
`lake exe cache get && lake build`; the facade's `#print axioms` output must match the
library's.

Safety: the target directory must not exist, and this script never deletes anything (a
recursive delete can follow directory links into a shared package store). The export stays local: nothing is pushed or published.
"""
import argparse
import json
import os
import shutil
import subprocess
import sys
import tomllib

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from slice_closure import ROOT, check, closure  # noqa: E402


def lakefile_header(name):
    """This repository's lakefile up to its first `[[lean_lib]]` (options and pinned
    requirements unchanged), with the package name and default targets replaced."""
    text = open(os.path.join(ROOT, 'lakefile.toml'), encoding='utf-8').read()
    head = text.split('[[lean_lib]]')[0]
    lines, renamed = [], False
    for line in head.splitlines():
        if line.startswith('name = ') and not renamed:
            line, renamed = f'name = "{name}"', True
        elif line.startswith('defaultTargets = '):
            line = 'defaultTargets = ["LinearAQFT", "Facade"]'
        lines.append(line)
    return '\n'.join(lines).rstrip() + '\n'


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument('manifest')
    ap.add_argument('--out', required=True)
    args = ap.parse_args()

    out = os.path.abspath(args.out)
    if os.path.exists(out):
        sys.exit(f'refusing: {out} exists (this script never overwrites or deletes)')
    if not check(args.manifest):
        sys.exit('refusing: the slice closure does not match its manifest')
    with open(args.manifest, 'rb') as fh:
        m = tomllib.load(fh)

    mods, _ = closure(os.path.join(ROOT, m['facade']))
    ours = sorted(x for x in mods if x.startswith('LinearAQFT.'))
    os.makedirs(out)
    for mod in ours:
        rel = mod.replace('.', os.sep) + '.lean'
        os.makedirs(os.path.dirname(os.path.join(out, rel)), exist_ok=True)
        shutil.copy2(os.path.join(ROOT, rel), os.path.join(out, rel))
    facade_rel = m['facade']
    os.makedirs(os.path.dirname(os.path.join(out, facade_rel)), exist_ok=True)
    shutil.copy2(os.path.join(ROOT, facade_rel), os.path.join(out, facade_rel))
    for f in ('lean-toolchain', 'LICENSE'):
        if os.path.exists(os.path.join(ROOT, f)):
            shutil.copy2(os.path.join(ROOT, f), os.path.join(out, f))

    facade_mod = os.path.splitext(os.path.relpath(facade_rel, 'slices'))[0].replace(os.sep, '.')
    name = 'Slice' + ''.join(p.capitalize() for p in m['name'].split('-'))
    # The same pinned revisions as this repository, under the new package name.
    with open(os.path.join(ROOT, 'lake-manifest.json'), encoding='utf-8') as fh:
        manifest = json.load(fh)
    manifest['name'] = name
    with open(os.path.join(out, 'lake-manifest.json'), 'w', encoding='utf-8') as fh:
        json.dump(manifest, fh, indent=2)
        fh.write('\n')
    mod_list = ', '.join(f'"{x}"' for x in ours)
    lakefile = (
        lakefile_header(name)
        + f'\n[[lean_lib]]\nname = "LinearAQFT"\nroots = [{mod_list}]\nmoreLeanArgs = ["-j1"]\n'
        + f'\n[[lean_lib]]\nname = "Facade"\nsrcDir = "slices"\nroots = ["{facade_mod}"]\n')
    open(os.path.join(out, 'lakefile.toml'), 'w', encoding='utf-8').write(lakefile)

    commit = subprocess.run(['git', '-C', ROOT, 'rev-parse', 'HEAD'],
                            capture_output=True, text=True).stdout.strip()
    dirty = subprocess.run(['git', '-C', ROOT, 'status', '--porcelain'],
                           capture_output=True, text=True).stdout.strip()
    readme = [f"# Slice `{m['name']}` of LinearAQFT", '',
              f"Exported from LinearAQFT commit `{commit}`"
              + (' (with uncommitted changes)' if dirty else '') + ' by `tools/export_slice.py`.',
              'The files are copied verbatim; the lakefile pins the same Mathlib, BosonicLean and',
              'Lean toolchain. Build with `lake exe cache get && lake build`.', '',
              f"Source: {m['source']}.", f"Differences from the source: {m['differences']}.", '',
              '## Targets', ''] + [f'- `{t}`' for t in m['targets']] + [
              '', '## Lecture-notes labels', ''] + [f'- `{x}`' for x in m['notes_labels']] + [
              '', '## Modules', ''] + [f'- `{x}`' for x in ours] + ['']
    open(os.path.join(out, 'README.md'), 'w', encoding='utf-8').write('\n'.join(readme))
    print(f'exported {len(ours)} modules and {facade_rel} to {out}')


if __name__ == '__main__':
    main()
