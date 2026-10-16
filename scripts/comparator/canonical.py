"""Structural declaration fingerprints for the pinned Lean NDJSON format.

IDs, allocation order, and binder spelling are ignored. Definition bodies,
types, universe expressions, constructor order and recursor rules are retained.
This is a comparison parser; nanoda separately checks the untouched export.
"""
import hashlib
import json
from pathlib import Path


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result: raise ValueError('duplicate JSON field: ' + key)
        result[key] = value
    return result


def exact_fields(value, expected):
    if not isinstance(value, dict) or set(value) != set(expected):
        raise ValueError('ambiguous or unknown export fields')


def digest(value):
    return hashlib.sha256(json.dumps(value, separators=(',', ':'), ensure_ascii=True).encode()).hexdigest()


def read_export(path, max_bytes=2_000_000_000, type_roots=(), bindings=None, protect_types=(), protect_declarations=(), implementation_declarations=()):
    if Path(path).stat().st_size > max_bytes:
        raise ValueError('proof export exceeds approved resource limit')
    names = {0: (digest(['anonymous']), '')}
    levels = {0: digest(['zero'])}
    expressions, declarations, references, constant_names = {}, {}, {}, {}
    applications, strings, declaration_exprs, declaration_names = {}, {}, {}, {}
    def name(idx):
        return names[idx][0]
    def expr(idx):
        return expressions[idx]
    def declare(kind, item):
        label = names[item['name']][1]
        if label in declarations:
            raise ValueError('duplicate exported declaration: ' + label)
        if item.get('isUnsafe', False) or item.get('safety', 'safe') != 'safe':
            raise ValueError('unsafe exported declaration: ' + label)
        normalized = {'kind': kind, 'name': name(item['name']), 'type': expr(item['type'])}
        declaration_exprs[label] = [item['type']]
        declaration_names[label] = []
        for key, val in item.items():
            if key in ('name', 'type', 'isUnsafe', 'safety'):
                continue
            if key in ('value',):
                normalized[key] = expr(val)
                declaration_exprs[label].append(val)
            elif key in ('levelParams', 'all', 'ctors'):
                normalized[key] = list(map(name, val))
                if key != 'levelParams': declaration_names[label].extend(names[x][1] for x in val)
            elif key == 'induct':
                normalized[key] = name(val)
                declaration_names[label].append(names[val][1])
            elif key == 'rules':
                normalized[key] = [{'ctor': name(x['ctor']), 'nfields': x['nfields'], 'rhs': expr(x['rhs'])} for x in val]
                declaration_exprs[label].extend(x['rhs'] for x in val)
                declaration_names[label].extend(names[x['ctor']][1] for x in val)
            elif key == 'hints':
                normalized[key] = 'regular' if isinstance(val, dict) and set(val) == {'regular'} else val
            elif key in ('cidx', 'numFields', 'numParams', 'numIndices', 'numMotives', 'numMinors',
                         'numNested', 'isRec', 'isReflexive', 'k', 'kind'):
                normalized[key] = val
            else:
                raise ValueError('unknown declaration field: ' + key)
        declarations[label] = {'kind': kind, 'type': expr(item['type']), 'body': digest(normalized),
                               '_type_index': item['type']}
    with Path(path).open() as stream:
        first = stream.readline(16777217)
        if len(first) > 16777216: raise ValueError('export metadata exceeds size bound')
        meta = json.loads(first, object_pairs_hook=unique_object)
        if meta.get('meta', {}).get('format', {}).get('version') != '3.1.0' or meta['meta']['lean']['version'] != '4.34.0':
            raise ValueError('unapproved Lean export format/toolchain')
        while True:
            line = stream.readline(16777217)
            if not line: break
            if len(line) > 16777216: raise ValueError('export record exceeds size bound')
            item = json.loads(line, object_pairs_hook=unique_object)
            if 'in' in item:
                if set(item) not in ({'in','str'}, {'in','num'}): raise ValueError('ambiguous name record')
                idx = item['in']
                if idx != len(names):
                    raise ValueError('invalid name numbering')
                kind = 'str' if 'str' in item else 'num'
                val = item[kind]
                exact_fields(val, ['pre', 'str' if kind == 'str' else 'i'])
                part = val['str'] if kind == 'str' else val['i']
                prefix = names[val['pre']]
                names[idx] = (digest([kind, prefix[0], part]), prefix[1] + ('.' if prefix[1] else '') + str(part))
            elif 'il' in item:
                if len(item) != 2: raise ValueError('ambiguous universe record')
                idx = item['il']
                if idx != len(levels):
                    raise ValueError('invalid universe numbering')
                kind, val = next((k,v) for k,v in item.items() if k != 'il')
                if kind == 'param': normalized = name(val)
                elif kind == 'succ': normalized = levels[val]
                elif kind in ('max', 'imax'): normalized = [levels[x] for x in val]
                else: raise ValueError('unknown universe form')
                levels[idx] = digest([kind, normalized])
            elif 'ie' in item:
                if len(item) != 2: raise ValueError('ambiguous expression record')
                idx = item['ie']
                if idx != len(expressions):
                    raise ValueError('invalid expression numbering')
                kind, val = next((k,v) for k,v in item.items() if k != 'ie')
                fields = {'const':['name','us'], 'app':['fn','arg'],
                          'lam':['binderInfo','name','type','body'], 'forallE':['binderInfo','name','type','body'],
                          'letE':['name','type','value','body','nondep'], 'proj':['typeName','idx','struct'],
                          'mdata':['expr']}
                if kind in fields: exact_fields(val, fields[kind])
                refs = []
                def use(x):
                    refs.append(x); return expr(x)
                if kind == 'sort': normalized = levels[val]
                elif kind == 'const':
                    normalized = [name(val['name']), [levels[x] for x in val['us']]]
                    constant_names[idx] = names[val['name']][1]
                elif kind in ('bvar', 'natVal', 'strVal'):
                    normalized = val
                    if kind == 'strVal': strings[idx] = val
                elif kind == 'app':
                    normalized = [use(val['fn']), use(val['arg'])]
                    applications[idx] = (val['fn'], val['arg'])
                elif kind in ('lam', 'forallE'): normalized = [val['binderInfo'], use(val['type']), use(val['body'])]
                elif kind == 'letE': normalized = [use(val['type']), use(val['value']), use(val['body']), val['nondep']]
                elif kind == 'proj':
                    normalized = [name(val['typeName']), val['idx'], use(val['struct'])]
                    constant_names[idx] = names[val['typeName']][1]
                elif kind == 'mdata':
                    expressions[idx] = use(val['expr']); references[idx] = refs; continue
                else: raise ValueError('unknown expression form: ' + kind)
                expressions[idx] = digest([kind, normalized]); references[idx] = refs
            elif set(item) == {'inductive'}:
                exact_fields(item['inductive'], ['types','ctors','recs'])
                for group, kind in [('types', 'inductive'), ('ctors', 'constructor'), ('recs', 'recursor')]:
                    for decl in item['inductive'][group]: declare(kind, decl)
            elif len(item) == 1 and next(iter(item)) in ('axiom','def','thm','opaque','quot'):
                kind = next(iter(item)); declare(kind, item[kind])
            else:
                raise ValueError('unknown export record')
    for label in type_roots:
        if label not in declarations:
            raise ValueError('missing artifact correctness theorem: ' + label)
        todo = [declarations[label]['_type_index']]
        seen, found = set(), set()
        while todo:
            node = todo.pop()
            if node in seen: continue
            seen.add(node)
            if node in constant_names: found.add(constant_names[node])
            todo.extend(references[node])
        declarations[label]['type_constants'] = sorted(found)
    for root, (byte_name, literal) in (bindings or {}).items():
        if root not in declarations or declarations[root]['kind'] != 'thm':
            raise ValueError('missing exact byte binding theorem')
        node = declarations[root]['_type_index']; args = []
        while node in applications:
            node, arg = applications[node]; args.append(arg)
        args.reverse()
        if len(args) != 3 or constant_names.get(node) != 'Eq' or constant_names.get(args[0]) != 'String' or constant_names.get(args[1]) != byte_name or strings.get(args[2]) != literal:
            raise ValueError('byte binding theorem has a different actual statement: ' + root)
    # Freeze every definition on which an approved statement depends. Following
    # only the statement's immediate constant names would allow Safe (or one of
    # its helpers) to be weakened while retaining an identical theorem type.
    todo_expr = [declarations[r]['_type_index'] for r in protect_types]
    todo_name = list(protect_declarations)
    seen_expr, frozen = set(), set()
    while todo_expr or todo_name:
        while todo_name:
            label = todo_name.pop()
            if label in frozen: continue
            if label not in declarations: raise ValueError('missing type dependency: ' + label)
            frozen.add(label)
            if label in implementation_declarations:
                if declarations[label]['kind'] != 'def':
                    raise ValueError('implementation hole must be a safe definition: ' + label)
                todo_expr.append(declarations[label]['_type_index'])
            else:
                todo_expr.extend(declaration_exprs[label])
            todo_name.extend(declaration_names[label])
        while todo_expr:
            node = todo_expr.pop()
            if node in seen_expr: continue
            seen_expr.add(node)
            todo_expr.extend(references[node])
            if node in constant_names: todo_name.append(constant_names[node])
    for label, value in declarations.items():
        value.pop('_type_index')
        value['protected'] = label in frozen
    return declarations


def compare(reference, candidate, roots, protected, implementation=()):
    checked = {}
    for name in roots:
        if name not in reference or name not in candidate:
            raise ValueError('missing required theorem: ' + name)
        a, b = reference[name], candidate[name]
        if a['kind'] != 'thm' or b['kind'] != 'thm' or a['type'] != b['type']:
            raise ValueError('theorem statement differs from approved reference: ' + name)
        checked[name] = b['type']
    for name in implementation:
        if name not in reference or name not in candidate or reference[name]['kind'] != 'def' or candidate[name]['kind'] != 'def' or reference[name]['type'] != candidate[name]['type']:
            raise ValueError('implementation declaration type/kind differs: ' + name)
    for name in protected:
        if name in implementation: continue
        if name not in reference or name not in candidate or reference[name]['body'] != candidate[name]['body']:
            raise ValueError('protected declaration differs from approved reference: ' + name)
    return checked


if __name__ == '__main__':
    import sys
    config = json.loads(Path(sys.argv[2]).read_text())
    roots = config.pop('audit_roots', None)
    declarations = read_export(sys.argv[1], **config)
    if roots is not None:
        sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
        from independent.replay import audit_export
        audit_export(sys.argv[1], roots)
    print(json.dumps(declarations))
