"""Check the module closure of a slice against its manifest.

Usage: python tools/slice_closure.py slices/dimock-abstract.toml [more manifests ...]
       python tools/slice_closure.py --all          (every slices/*.toml)
       python tools/slice_closure.py --decls slices/<name>.toml
                                                    (declaration closure; needs a built library)

A slice manifest (slices/<name>.toml) names a facade file and the exact set of LinearAQFT
modules the facade may depend on (`allowed_modules`). This script follows `import` lines
from the facade through LinearAQFT, LocalAlgebrasLean and BosonicLean sources (no Lean needed)
and fails if the LinearAQFT part of the closure differs from `allowed_modules`. It guards a
slice, for example the theorem of Dimock (1980), against later stages leaking into it. The
modules of the two sibling libraries in the closure are listed for information (LocalAlgebrasLean
since 13 Oct 2026: nets moved there on 6 Oct); Mathlib and Lean core are not followed. It also checks that every target
has a lecture-notes correspondence entry (docs/lecture-notes/correspondence.json) under one of
the manifest's `notes_labels`.

With --decls it also computes the exact declaration closure of the targets (scripts/SliceDecls.lean,
run through `lake env lean` after `lake build LinearAQFT SliceTools`) and writes
slices/<name>.closure.json.
"""
import glob
import json
import os
import re
import subprocess
import sys
import tempfile
import tomllib

ROOT = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
BOSONIC = os.path.join(ROOT, '.lake', 'packages', 'BosonicLean')
FOUNDATION = os.path.join(ROOT, '.lake', 'packages', 'LocalAlgebrasLean')
IMPORT = re.compile(r'^\s*import\s+([\w.]+)')


def module_file(mod):
    """Source file of a LinearAQFT, LocalAlgebrasLean or BosonicLean module, or None if not
    followed."""
    rel = mod.replace('.', os.sep) + '.lean'
    if mod.startswith('LinearAQFT.'):
        return os.path.join(ROOT, rel)
    if mod.startswith('BosonicLean.'):
        return os.path.join(BOSONIC, rel)
    if mod.startswith('LocalAlgebrasLean.'):
        return os.path.join(FOUNDATION, rel)
    return None


def imports(path):
    out = []
    with open(path, encoding='utf-8') as fh:
        for line in fh:
            m = IMPORT.match(line)
            if m:
                out.append(m.group(1))
    return out


def closure(facade):
    seen, stack, missing = set(), imports(facade), []
    while stack:
        mod = stack.pop()
        if mod in seen:
            continue
        path = module_file(mod)
        if path is None:
            continue
        seen.add(mod)
        if os.path.exists(path):
            stack.extend(imports(path))
        else:
            missing.append(mod)
    return seen, missing


def notes_labels_ok(m):
    """Every target appears in a correspondence claim whose label is in `notes_labels`."""
    path = os.path.join(ROOT, 'docs', 'lecture-notes', 'correspondence.json')
    with open(path, encoding='utf-8') as fh:
        claims = json.load(fh)['claims']
    bad = []
    for t in m['targets']:
        labels = {c['tex_label'] for c in claims
                  if t in (d.strip() for d in c['declaration'].split(','))}
        if not labels & set(m['notes_labels']):
            bad.append((t, sorted(labels)))
    for t, labels in bad:
        print(f"  target without a listed notes label: {t} (found under {labels or 'none'})")
    return not bad


def check(manifest_path):
    with open(manifest_path, 'rb') as fh:
        m = tomllib.load(fh)
    mods, missing = closure(os.path.join(ROOT, m['facade']))
    ours = {x for x in mods if x.startswith('LinearAQFT.')}
    bosonic = sorted(x for x in mods if x.startswith('BosonicLean.'))
    foundation = sorted(x for x in mods if x.startswith('LocalAlgebrasLean.'))
    allowed = set(m['allowed_modules'])
    extra, absent = sorted(ours - allowed), sorted(allowed - ours)
    ok = not extra and not absent and not [x for x in missing if x.startswith('LinearAQFT.')]
    ok = notes_labels_ok(m) and ok
    print(f"{m['name']}: {len(ours)} LinearAQFT modules, {len(foundation)} LocalAlgebrasLean "
          f"modules, {len(bosonic)} BosonicLean modules"
          f" -> {'PASS' if ok else 'FAIL'}")
    for x in extra:
        print(f"  not allowed (leaked into the slice): {x}")
    for x in absent:
        print(f"  allowed but not reached (update the manifest): {x}")
    for x in missing:
        print(f"  source not found: {x}")
    if foundation:
        print('  LocalAlgebrasLean: ' +
              ', '.join(b.removeprefix('LocalAlgebrasLean.') for b in foundation))
    if bosonic:
        print('  BosonicLean: ' + ', '.join(b.removeprefix('BosonicLean.') for b in bosonic))
    return ok


def decls(manifest_path):
    """Write slices/<name>.closure.json with the declaration closure of the targets."""
    with open(manifest_path, 'rb') as fh:
        m = tomllib.load(fh)
    out = os.path.join(ROOT, 'slices', m['name'] + '.closure.json')
    names = ', '.join('`' + t for t in m['targets'])
    driver = ('import LinearAQFT\nimport SliceDecls\n\n'
              f'#eval SliceDecls.run "{out.replace(os.sep, "/")}" [{names}]\n')  # Lean string: no backslashes
    with tempfile.TemporaryDirectory() as tmp:
        path = os.path.join(tmp, 'Driver.lean')
        with open(path, 'w', encoding='utf-8') as fh:
            fh.write(driver)
        res = subprocess.run(['lake', 'env', 'lean', path], cwd=ROOT,
                             capture_output=True, text=True)
    print(res.stdout.strip() or res.stderr.strip())
    return res.returncode == 0


def main(argv):
    if argv and argv[0] == '--decls':
        return 0 if all(decls(p) for p in argv[1:]) else 1
    paths = sorted(glob.glob(os.path.join(ROOT, 'slices', '*.toml'))) if argv == ['--all'] else argv
    if not paths:
        print(__doc__)
        return 2
    results = [check(p) for p in paths]
    return 0 if all(results) else 1


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
