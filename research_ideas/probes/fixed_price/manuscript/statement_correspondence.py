"""Extract the current TeX-to-Lean correspondence for review.

This is a source-navigation check, not a proof of semantic equivalence. The
mapping and scope descriptions come from formalization_supplement.tex; evidence
and verification status remain in factgraph.toml and the shared ledger.
"""
from __future__ import annotations

import argparse
import json
import re
import tomllib
from pathlib import Path

HERE = Path(__file__).resolve().parent
LEAN = HERE.parent / "lean" / "FixedPrice"


def lean_mask(source: str) -> str:
    """Blank nested comments and strings while preserving source positions."""
    out = list(source)
    i = depth = 0
    quoted = False
    while i < len(source):
        n = 1
        hide = depth > 0 or quoted
        if depth:
            if source.startswith('/-', i):
                depth += 1
                n = 2
            elif source.startswith('-/', i):
                depth -= 1
                n = 2
        elif quoted:
            if source[i] == '\\':
                n = 2
            elif source[i] == '"':
                quoted = False
        elif source.startswith('/-', i):
            depth = 1
            n = 2
            hide = True
        elif source.startswith('--', i):
            end = source.find('\n', i)
            n = (len(source) if end < 0 else end) - i
            hide = True
        elif source[i] == '"':
            quoted = True
            hide = True
        if hide:
            for j in range(i, min(i + n, len(out))):
                if out[j] != '\n':
                    out[j] = ' '
        i += n
    return ''.join(out)


def declaration_index() -> list[dict]:
    result = []
    pattern = re.compile(
        r'(?m)^(?:(?:private|protected|noncomputable)\s+)*'
        r'(theorem|lemma|def|abbrev|structure)\s+([^\s:({\[]+)')
    for path in sorted(LEAN.rglob('*.lean')):
        source = path.read_text(encoding='utf-8')
        masked = lean_mask(source)
        matches = list(pattern.finditer(masked))
        for i, m in enumerate(matches):
            end = matches[i + 1].start() if i + 1 < len(matches) else len(source)
            # The next namespace/section command is not part of this declaration.
            next_command = re.search(r'(?m)^(?:end|namespace|section|variable|open)\b', masked[m.end():end])
            if next_command:
                end = m.end() + next_command.start()
            code = masked[m.start():end]
            if m[1] in {'theorem', 'lemma'}:
                depth = 0
                for j, char in enumerate(code):
                    if char in '([{⦃':
                        depth += 1
                    elif char in ')]}⦄':
                        depth -= 1
                    elif depth == 0 and code.startswith(':=', j):
                        end = m.start() + j
                        break
            # Use masked text: no trailing docstrings and no example declarations.
            text = masked[m.start():end].strip()
            context = re.findall(r'(?m)^variable[^\n]*', masked[:m.start()])
            result.append(dict(name=m[2], kind=m[1], file=path.relative_to(LEAN).as_posix(),
                               line=source.count('\n', 0, m.start()) + 1,
                               text=text, file_variable_context=context))
    return result


def tex_index(directory: Path) -> dict[str, dict]:
    result = {}
    for filename in ['paper.tex', 'two_units.tex', 'two_unit_family.tex',
                     'two_unit_pricing_proofs.tex', 'two_unit_computation.tex']:
        path = directory / filename
        if not path.exists():
            continue
        source = path.read_text(encoding='utf-8')
        env = r'(theorem[A-Z]?(?:intro)?|lemma|proposition|corollary[A-Z]?|conjecture)'
        for m in re.finditer(r'\\begin\{' + env + r'\}.*?\\end\{\1\}', source, re.S):
            labels = re.findall(r'\\label\{([^}]+)\}', m[0])
            if labels:
                result[labels[0]] = dict(file=filename, line=source.count('\n', 0, m.start()) + 1,
                                         text=m[0], kind=m[1])
        # Table rows also cite sections/appendices rather than theorem environments.
        for m in re.finditer(r'\\label\{([^}]+)\}', source):
            if m[1] not in result:
                begin = source.rfind('\n', 0, m.start()) + 1
                result[m[1]] = dict(file=filename, line=source.count('\n', 0, begin) + 1,
                                     text=source[begin:source.find('\n', m.end())], kind='locator')
    return result


def build_report(tex_directory: Path) -> dict:
    declarations = declaration_index()
    tex = tex_index(tex_directory)
    source_mode = 'current TeX source'
    if not tex:
        excerpts = HERE / 'checks' / 'tex_statements.json'
        if not excerpts.exists():
            raise FileNotFoundError('Provide --tex-dir containing the manuscript TeX files.')
        tex = json.loads(excerpts.read_text(encoding='utf-8'))
        source_mode = 'exported TeX excerpts; use --tex-dir to compare a new manuscript'
    supplement = (HERE / 'formalization_supplement.tex').read_text(encoding='utf-8')
    table = supplement.split('\\begin{longtable}', 1)[1].split('\\end{longtable}', 1)[0]
    rows = []
    errors = []
    for line in table.splitlines():
        if ' & ' not in line or '\\pref{' not in line:
            continue
        cells = line.split(' & ')
        label = re.search(r'\\pref\{([^}]+)\}', cells[0])[1]
        files = re.findall(r'\\lean\{([^}]+\.lean)\}', cells[-1])
        names = [s.replace(r'\_', '_').replace(r'\allowbreak', '')
                 for s in re.findall(r'\\lean\{([^}]+)\}', cells[1])]
        selected = []
        for name in names:
            # Plain manifest node names are locators, not Lean declarations.
            if name.startswith(('P_', 'L_')) or name == 'NodeData':
                continue
            candidates = [d for d in declarations if d['file'] in files and
                          (d['name'] == name or d['name'].split('.')[-1] == name.split('.')[-1])]
            if name in {'PricingScalarCertificates', 'NodeScalarCertificates',
                        'FamilyNumerics', 'FamilyIdentities'}:
                candidates = [d for d in declarations if d['name'] == name and d['kind'] == 'structure']
            if not candidates:
                errors.append(f'{label}: declaration {name} not found in {files}')
            selected.extend(candidates)
        if label not in tex:
            errors.append(f'Missing TeX label: {label}')
        # Expand Prop abbreviations: a short exported theorem can hide its hypotheses here.
        pending = set(re.findall(r'\b\w+Statement\b', '\n'.join(d['text'] for d in selected)))
        expanded = []
        while pending:
            name = pending.pop()
            matches = [d for d in declarations if d['name'] == name]
            for d in matches:
                if d not in expanded:
                    expanded.append(d)
                    pending.update(re.findall(r'\b\w+Statement\b', d['text']))
            pending.difference_update(d['name'] for d in expanded)
        rows.append(dict(label=label, tex=tex.get(label), scope_as_documented=cells[1],
                         declarations=selected, expanded_statements=expanded))
    nodes = tomllib.loads((HERE / 'factgraph.toml').read_text(encoding='utf-8'))['nodes']
    differences = []
    for key, node in nodes.items():
        statement = node['statement'].strip()
        if not statement.startswith(r'\begin{'):
            continue
        label = re.search(r'\\label\{([^}]+)\}', statement)
        if label and label[1] in tex and statement != tex[label[1]]['text'].strip():
            differences.append(dict(node=key, label=label[1],
                                    meaning='Stored historical TeX wording differs; no semantic verdict.'))
    return dict(scope='Source correspondence only; no automatic semantic-equivalence verdict.',
                source_mode=source_mode,
                rows=rows, source_errors=errors,
                historical_manifest_wording_differences=differences,
                semantic_review_required=['quantifiers', 'hypotheses', 'definitions',
                                          'equality cases', 'external-certificate assumptions'],
                declaration_count=sum(d['kind'] in {'theorem', 'lemma'} for d in declarations))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=HERE / 'checks' / 'statement_correspondence.json')
    parser.add_argument('--tex-dir', type=Path, default=HERE)
    args = parser.parse_args()
    current_tex = tex_index(args.tex_dir)
    report = build_report(args.tex_dir)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    if current_tex:
        (args.output.parent / 'tex_statements.json').write_text(
            json.dumps(current_tex, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
    args.output.write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
    md = ['# TeX / Lean source correspondence', '', report['scope'], '',
          'Source mode: ' + report['source_mode'] + '.', '',
          'Quantifiers, assumptions, definitions, equality cases and certificate hypotheses '
          'require semantic review. Source lookup success does not establish equivalence.', '',
          'The JSON companion contains the full excerpts, expanded statements and certificate structures.', '']
    for row in report['rows']:
        md += ['## ' + row['label'], '',
               'Printed source: ' + str(row['tex']['file']) + ':' + str(row['tex']['line']), '',
               '```tex', row['tex']['text'], '```', '']
        for d in row['declarations']:
            md += [f"[{d['name']}](../../lean/FixedPrice/{d['file']}#L{d['line']})", '',
                   '```lean', d['text'], '```', '']
    md += ['## Historical manifest wording', '',
           'These differences are source observations, not rejected theorems:', '']
    md += [f"- {x['node']} ({x['label']}): {x['meaning']}" for x in report['historical_manifest_wording_differences']]
    args.output.with_suffix('.md').write_text(
        '\n'.join(line.rstrip() for block in md for line in block.split('\n'))+'\n',
        encoding='utf-8')
    print(f"{len(report['rows'])} correspondence rows; {report['declaration_count']} theorem/lemma declarations")
    print(f"{len(report['source_errors'])} source-navigation errors; semantic equivalence is not certified")
    for error in report['source_errors']:
        print(error)
    # Source failures are ordinary tool errors; this does not issue a proof credential.
    raise SystemExit(bool(report['source_errors']))


if __name__ == '__main__':
    main()
