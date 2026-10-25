#!/usr/bin/env python3
"""Check the challenge of `lake comparator` against the formal-conjectures file.

Challenge.lean is the challenge module of `lake comparator`. It is made from the file of Open
Quantum Problem 23 in formal-conjectures, kept in vendor/, by keeping the definitions and the
twelve open theorems and replacing the module header and imports by `import Mathlib`. This script
checks the copy and comparator.json:

- the file in vendor/ is `FormalConjectures/OpenQuantumProblems/23.lean` at formal-conjectures
  commit 90d18f666eb98adec4eee4d12f1d37e30b4eb204, whose Git blob hash it has;
- apart from comments, Challenge.lean begins with exactly `import Mathlib`, `noncomputable section`
  and `namespace OpenQuantumProblem23`, and the original opens the same namespace in a
  noncomputable section;
- every declaration of Challenge.lean, with its docstring, is a whole declaration in the namespace
  of the original, verbatim and in the same order, after the attribute lines of the original are
  removed. These are its classification tags (`@[category ...]`) and `@[expose] public section`.
  A whole declaration follows a blank line and is followed by a blank line and an unindented line,
  so that a truncated copy or a copy without its docstring fails;
- the theorems of Challenge.lean are exactly the theorems that the original tags as open
  (`@[category research open, ...]`);
- comparator.json has exactly four entries, none of them twice: it compares SICLean.Solution with
  Challenge, names each of these theorems once and no other, and permits only the axioms propext,
  Quot.sound and Classical.choice, both as lists of strings. Further entries, such as definition
  holes (`definition_names`), which let the solution change the bodies of the listed definitions,
  are rejected.

Run from the root of the repository: python3 verification/check_challenge.py
"""
import hashlib
import json
import re
import sys

CHALLENGE = 'Challenge.lean'
ORIGINAL = 'vendor/formal-conjectures-OQP23.lean'
CONFIG = 'comparator.json'
COMMIT = '90d18f666eb98adec4eee4d12f1d37e30b4eb204'
BLOB = '6e3d4f42e066f7d4de45b44f2cebdc0bf2fc9c85'
CONTEXT = 'noncomputable section\nnamespace OpenQuantumProblem23\n'
NAMESPACE = 'namespace OpenQuantumProblem23\n'
END = 'end OpenQuantumProblem23'
PREFIX = 'OpenQuantumProblem23.'
DECLARATION = re.compile(r'(/--|abbrev |def |instance |theorem |lemma |noncomputable def )')
OPEN_TAG = re.compile(r'(?m)^@\[category research open\b.*\n')
OPEN_THEOREM = re.compile(r'(?m)^@\[category research open\b.*\ntheorem (\S+)')
ITEM_END = re.compile(r'\n(?:[ \t]*\n)+\S')
AXIOMS = {'propext', 'Quot.sound', 'Classical.choice'}
ENTRIES = {'challenge_module', 'solution_module', 'theorem_names', 'permitted_axioms'}


def fail(message):
    print(f'FAILED: {message}')
    sys.exit(1)


def find_whole(text, block, start):
    """Return the first position at or after start where block occurs in text as a whole item,
    following a blank line and followed by a blank line and an unindented line, or -1."""
    index = text.find(block, start)
    while index >= 0:
        if text.endswith('\n\n', 0, index) and ITEM_END.match(text, index + len(block)):
            return index
        index = text.find(block, index + 1)
    return -1


def strip_comments(text):
    """Remove Lean comments from text: line comments and block comments, which nest."""
    kept, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith('/-', i):
            depth, i = depth + 1, i + 2
        elif depth and text.startswith('-/', i):
            depth, i = depth - 1, i + 2
        elif depth:
            i += 1
        elif text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        else:
            kept.append(text[i])
            i += 1
    if depth:
        fail(f'unclosed comment in {CHALLENGE}')
    return ''.join(kept)


def without_repeats(pairs):
    keys = [key for key, _ in pairs]
    if len(set(keys)) != len(keys):
        fail(f'{CONFIG} repeats an entry: {keys}')
    return dict(pairs)


def main():
    challenge = open(CHALLENGE, encoding='utf-8').read()
    data = open(ORIGINAL, 'rb').read()
    if hashlib.sha1(b'blob %d\0' % len(data) + data).hexdigest() != BLOB:
        fail(f'{ORIGINAL} is not the file of formal-conjectures commit {COMMIT}')
    original = data.decode('utf-8')
    open_theorems = OPEN_THEOREM.findall(original)
    if len(open_theorems) != len(OPEN_TAG.findall(original)):
        fail(f'an open problem of {ORIGINAL} is not a theorem directly after its tags')
    # The attribute lines of the original are the classification tags of formal-conjectures,
    # such as `@[category research open, question, AMS 15 47 81]`, and `@[expose] public section`
    # of its module system.
    original = re.sub(r'(?m)^@\[.*\n', '', original)

    head, found, rest = challenge.partition(NAMESPACE)
    if not found:
        fail(f'{CHALLENGE} does not open the namespace')
    # The line that opens the namespace is checked as well, so that it cannot sit in a comment.
    code = strip_comments(head + NAMESPACE)
    lines = [line.strip() for line in code.splitlines() if line.strip()]
    if lines != ['import Mathlib', 'noncomputable section', NAMESPACE.strip()]:
        fail(f'unexpected text before the declarations of {CHALLENGE}: {lines}')
    if CONTEXT not in original:
        fail(f'{ORIGINAL} does not open the namespace in a noncomputable section')

    body, found, tail = rest.partition(END)
    if not found or tail.strip():
        fail(f'{CHALLENGE} must end with the end of the namespace')
    position = original.index(CONTEXT) + len(CONTEXT)
    # Only the namespace of the original, up to and including its end, is searched.
    original = original[:original.index('\n' + END, position) + 1 + len(END)]
    theorems = []
    blocks = [block.strip('\n') for block in body.split('\n\n') if block.strip()]
    for block in blocks:
        first_line = block.splitlines()[0]
        if not DECLARATION.match(block):
            fail(f'not a declaration in {CHALLENGE}: {first_line}')
        index = find_whole(original, block, position)
        if index < 0:
            fail(f'not a whole declaration of {ORIGINAL}, verbatim and in order: {first_line}')
        position = index + len(block)
        theorems += re.findall(r'(?m)^theorem (\S+)', block)
    if sorted(theorems) != sorted(open_theorems):
        fail(f'the theorems of {CHALLENGE}, {theorems}, are not the open theorems of {ORIGINAL}, '
             f'{open_theorems}')

    with open(CONFIG, encoding='utf-8') as file:
        config = json.load(file, object_pairs_hook=without_repeats)
    if set(config) != ENTRIES:
        fail(f'{CONFIG} must have exactly the entries {sorted(ENTRIES)}: {sorted(config)}')
    for key in ('theorem_names', 'permitted_axioms'):
        if not (isinstance(config[key], list) and all(isinstance(x, str) for x in config[key])):
            fail(f'{CONFIG}: {key} must be a list of strings')
    if (config['challenge_module'], config['solution_module']) != ('Challenge', 'SICLean.Solution'):
        fail(f'{CONFIG} does not compare SICLean.Solution with Challenge')
    if sorted(config['theorem_names']) != sorted(PREFIX + name for name in open_theorems):
        fail(f'{CONFIG} does not name each open theorem once and no other: '
             f'{config["theorem_names"]}')
    if sorted(config['permitted_axioms']) != sorted(AXIOMS):
        fail(f'{CONFIG} does not permit exactly the axioms {sorted(AXIOMS)}: '
             f'{config["permitted_axioms"]}')
    print(f'{len(blocks)} declarations of {CHALLENGE} are whole declarations of {ORIGINAL} '
          f'(formal-conjectures commit {COMMIT[:7]}), verbatim and in order, among them its '
          f'{len(open_theorems)} open theorems, each named once in {CONFIG}.')


if __name__ == '__main__':
    main()
