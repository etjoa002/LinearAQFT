"""Consistency of the lecture notes with the Lean library (run before every PDF review).

Checks that each correspondence entry names declarations that exist in their source files and
in the index, that its label exists in the notes, that every marked label has an entry and an
index target and is not a definition, and that every theorem-like label is marked.
"""
import json
import re
from pathlib import Path

repo = Path(__file__).resolve().parents[2]  # repository root, wherever it is cloned
notes = repo / 'docs/lecture-notes'
PREFIX = 'LinearAQFT.'
# Chapter files, in order: extend this list with every new chapter.
CHAPTERS = ['nets.tex', 'weyl.tex', 'lattice.tex', 'phasespace.tex', 'latticenet.tex', 'simple.tex', 'green.tex',
            'minkowski.tex', 'mass.tex']

# Sources in the dependency BosonicLean (moved there on 29 Sep 2026) are named from the package
# root, e.g. BosonicLean/Weyl/Basic.lean, and read from the pinned checkout under .lake/packages.
DEPENDENCIES = {'BosonicLean/': repo / '.lake/packages/BosonicLean'}


def source(s):
    for prefix, root in DEPENDENCIES.items():
        if s.startswith(prefix):
            return root / s
    return repo / s


corr = json.load(open(notes / 'correspondence.json', encoding='utf-8'))
labels = set(re.findall(r'\\AQFTCheckedLabel\{([^}]*)\}',
                        (notes / 'checked-labels.tex').read_text(encoding='utf-8')))
index = (notes / 'lean-index.tex').read_text(encoding='utf-8')
indexed = set(re.findall(r'\\detokenize\{([^}]*)\}', index))
tex = ''.join((notes / f).read_text(encoding='utf-8') for f in CHAPTERS)
main = (notes / 'LinearAQFT.tex').read_text(encoding='utf-8')
problems = []
for f in CHAPTERS:
    if '\\input{' + f[:-4] + '}' not in main:
        problems.append(f'chapter {f} not input in LinearAQFT.tex')
seen = {}
for c in corr['claims']:
    label = c['tex_label']
    decls = [d.strip() for d in c['declaration'].split(',')]
    srcs = [s.strip() for s in c['source'].split(',')]
    texts = {s: source(s).read_text(encoding='utf-8') for s in srcs if source(s).is_file()}
    for s in srcs:
        if s not in texts:
            problems.append(f'{label}: missing source file {s}')
    for d in decls:
        short = d[len(PREFIX):] if d.startswith(PREFIX) else d
        parts = short.split('.')
        cands = {'.'.join(parts[i:]) for i in range(len(parts))}
        pats = [re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(?:protected\s+)?'
                           r'(?:def|theorem|lemma|abbrev|structure|instance)\s+'
                           + re.escape(x) + r"(?![A-Za-z0-9_'.])", re.M) for x in cands]
        if not any(p.search(t) for p in pats for t in texts.values()):
            problems.append(f'{label}: declaration {d} not found in {srcs}')
        if d not in indexed:
            problems.append(f'{label}: {d} not in lean-index.tex')
    if f'\\label{{{label}}}' not in tex:
        problems.append(f'{label}: label not in notes')
    seen[label] = decls
for lab in labels:
    if lab not in seen:
        problems.append(f'checked label {lab} has no correspondence entry')
    if f'lean:{lab}' not in index:
        problems.append(f'checked label {lab} has no index target')
    if lab.startswith('def:'):
        problems.append(f'{lab}: a definition carries a mark')
for m in re.finditer(r'\\begin\{(theorem|lemma|proposition|corollary)\}[^\n]*\\label\{([^}]*)\}',
                     tex):
    if m.group(2) not in labels:
        problems.append(f'{m.group(2)} ({m.group(1)}) is unmarked')
# Every example carries exactly one status: Lean (a checked label) or script or paper.
status = dict(re.findall(r'\\AQFTExampleStatus\{([^}]*)\}\{([^}]*)\}',
                         (notes / 'checked-labels.tex').read_text(encoding='utf-8')))
for lab, st in status.items():
    if st not in ('script', 'paper'):
        problems.append(f'{lab}: unknown example status {st}')
    if lab in labels:
        problems.append(f'{lab}: both a Lean mark and a {st} status')
for m in re.finditer(r'\\begin\{example\}[^\n]*\\label\{([^}]*)\}', tex):
    if m.group(1) not in labels and m.group(1) not in status:
        problems.append(f'{m.group(1)} (example) has no status')
print('claims', len(corr['claims']), 'marked labels', len(labels))
print('\n'.join(problems) if problems else 'consistent')
