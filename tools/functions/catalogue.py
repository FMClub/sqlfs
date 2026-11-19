#!/usr/bin/env python3
"""Function catalogues of the engines, compared with the model (TODO 4.1-4.8).

For each engine, the names of the functions which its SQL layer registers are read from its source:

  PostgreSQL  src/include/catalog/pg_proc.dat
  MySQL       sql/item_create.cc (native functions) and sql/sql_yacc.yy (functions of the grammar)
  MariaDB     sql/item_create.cc and sql/sql_yacc.yy
  TiDB        pkg/parser/ast/functions.go
  OceanBase   src/sql/engine/expr/ob_expr_operator_factory.cpp (REG_OP: MySQL mode, REG_OP_ORCL: Oracle mode)
  SQLite      the amalgamation sqlite3.c (FUNCTION, AGGREGATE, WAGGREGATE, ... tables)

Each name is then either modelled (the dialect's tables have it: checked by Coq, see --coq), modelled by
syntax (a construct of the grammar of the model, listed in SYNTAX), excluded with a reason (the rules of
EXCLUDE), or not modelled. The report is written to docs/closeouts/<engine>.md.

Usage:
  catalogue.py extract ENGINE SRC > names.txt
  catalogue.py coq ENGINE names.txt > Catalogue.v      (a Coq file which prints the modelled names)
  catalogue.py report ENGINE SRC modelled.txt          (writes docs/closeouts/ENGINE.md)
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


# ---------------------------------------------------------------------------------------------------
# extraction

def pg_entries(src):
    t = (Path(src) / 'src/include/catalog/pg_proc.dat').read_text()
    t = re.sub(r'(?m)^\s*#.*$', '', t)
    out = []
    for chunk in re.split(r'\{\s*oid\s*=>', t)[1:]:
        def field(k, d=''):
            m = re.search(k + r"\s*=>\s*'((?:[^'\\]|\\.)*)'", chunk)
            return m.group(1) if m else d
        out.append({'name': field('proname'), 'kind': field('prokind', 'f'), 'ret': field('prorettype'),
                    'args': field('proargtypes').split(), 'descr': field('descr'),
                    'retset': field('proretset', 'f') == 't'})
    return out


GRAMMAR_RULES = ('function_call_keyword', 'function_call_keyword_timestamp', 'function_call_nonkeyword',
                 'function_call_conflict', 'sum_expr', 'window_func_call', 'window_func_expr')


def yacc_functions(path):
    """The tokens which start an alternative of the function rules of the grammar, followed by '('."""
    t = Path(path).read_text(errors='replace')
    names = set()
    for rule in GRAMMAR_RULES:
        m = re.search(r'(?m)^' + rule + r'\s*:(.*?)^\s*;', t, flags=re.S)
        if not m:
            continue
        body = re.sub(r'\{(?:[^{}]|\{(?:[^{}]|\{[^{}]*\})*\})*\}', ' ', m.group(1))
        for tok in re.findall(r"(?:^|\|)\s*([A-Z][A-Z0-9_]*)\s+'\('", body, flags=re.M):
            n = re.sub(r'_SYM$', '', tok).lower()
            n = {'substring': 'substring', 'char': 'char', 'utc_date': 'utc_date'}.get(n, n)
            names.add(n)
    return names


def item_create(path):
    t = Path(path).read_text(errors='replace')
    return {n.lower() for n in re.findall(r'STRING_WITH_LEN\("([A-Za-z0-9_]+)"\)', t)} | \
           {n.lower() for n in re.findall(r'^\s*\{"([A-Za-z0-9_]+)",\s*SQL_FN', t, flags=re.M)}


def tidb_names(src):
    t = (Path(src) / 'pkg/parser/ast/functions.go').read_text()
    return set(re.findall(r'^\s*[A-Z]\w*\s*=\s*"([a-z0-9_]+)"', t, flags=re.M))


def ob_names(src, oracle):
    base = Path(src) / 'src/sql/engine/expr'
    defs = {}
    for f in [Path(src) / 'deps/oblib/src/lib/ob_name_def.h']:
        for k, v in re.findall(r'#define\s+(N_\w+)\s+"([^"]*)"', f.read_text(errors='replace')):
            defs[k] = v.lower()
    cls_name = {}
    for f in base.glob('*.cpp'):
        t = f.read_text(errors='replace')
        for m in re.finditer(r'(ObExpr\w+)::\1\s*\([^)]*\)\s*:\s*\w+\s*\((.{0,400}?)\)', t, flags=re.S):
            n = re.search(r'\b(N_\w+)\b', m.group(2))
            if n and n.group(1) in defs:
                cls_name[m.group(1)] = defs[n.group(1)]
    t = (base / 'ob_expr_operator_factory.cpp').read_text(errors='replace')
    t = re.sub(r'(?m)^\s*//.*$', '', t)
    macro = 'REG_OP_ORCL' if oracle else 'REG_OP'
    names = set()
    for c in re.findall(r'\b' + macro + r'\s*\(\s*(ObExpr\w+)', t):
        if c in cls_name:
            names.add(cls_name[c])
    return {n for n in names if re.fullmatch(r'[a-z_][a-z0-9_$#]*', n)}


def sqlite_names(path):
    t = Path(path).read_text(errors='replace')
    names = set()
    for m in re.finditer(r'\b(?:[A-Z_]*FUNCTION[A-Z0-9_]*|[A-Z_]*AGGREGATE[A-Z0-9_]*|PURE_DATE|DFUNCTION|'
                         r'INLINE_FUNC|TEST_FUNC|MFUNCTION|JFUNCTION|WINDOWFUNC[A-Z]*)\s*\(\s*([a-z_][a-z0-9_]*)\s*,', t):
        names.add(m.group(1))
    return names


def extract(engine, src):
    if engine == 'PostgreSQL':
        return sorted({e['name'] for e in pg_entries(src)})
    if engine in ('MySQL', 'MariaDB'):
        return sorted(item_create(Path(src) / 'sql/item_create.cc') | yacc_functions(Path(src) / 'sql/sql_yacc.yy'))
    if engine == 'TiDB':
        return sorted(tidb_names(src))
    if engine == 'OceanBaseMySQL':
        return sorted(ob_names(src, False))
    if engine == 'OceanBaseOracle':
        return sorted(ob_names(src, True))
    if engine == 'SQLite':
        return sorted(sqlite_names(src))
    raise SystemExit('unknown engine ' + engine)


if __name__ == '__main__' and len(sys.argv) >= 4 and sys.argv[1] == 'extract':
    for n in extract(sys.argv[2], sys.argv[3]):
        print(n)


# ---------------------------------------------------------------------------------------------------
# the names which the model has: computed by Coq

VSEM = {'PostgreSQL': 'PostgreSQL', 'MySQL': 'MySQL', 'MariaDB': 'MariaDB', 'TiDB': 'TiDB',
        'OceanBaseMySQL': 'OceanBaseMySQL', 'OceanBaseOracle': 'OceanBaseOracle', 'SQLite': 'SQLite'}


def coq_file(engine, names):
    lits = ';\n  '.join('"%s"' % n for n in names)
    return '''Require Import List String.
Require Import SqlFull Values Dialects PostgreSQL MySQL SQLite OceanBase MariaDB TiDB.
Import ListNotations.
Open Scope string_scope.
Definition some {A} (o : option A) := match o with Some _ => true | None => false end.
Definition known (d : vsem) (n : string) : bool :=
  some (vs_symb d n) || some (vs_agg d n) || some (vs_pred d n) || some (vs_table_fun d n).
Definition names := [
  %s].
Eval vm_compute in (List.filter (known %s) names).
''' % (lits, VSEM[engine])


def parse_coq_output(text):
    return set(re.findall(r'"([^"]*)"', text))


if __name__ == '__main__' and len(sys.argv) >= 4 and sys.argv[1] == 'coq':
    print(coq_file(sys.argv[2], [l.strip() for l in open(sys.argv[3]) if l.strip()]))


# ---------------------------------------------------------------------------------------------------
# classification of the names which the model does not have

def refs(path, keys):
    t = Path(path).read_text(errors='replace')
    out = set()
    for k in keys:
        for v in re.findall(k + r"\s*=>\s*'([^'(]+)", t):
            out.add(v)
    return out


# the types of PostgreSQL which the model has (Values.v: integers, numeric, floats, text, booleans,
# temporal types, json, jsonb, arrays of these; the polymorphic types)
PG_TYPES = {'int2', 'int4', 'int8', 'numeric', 'float4', 'float8', 'text', 'varchar', 'bpchar', 'name', 'char',
            'bool', 'date', 'time', 'timetz', 'timestamp', 'timestamptz', 'interval', 'json', 'jsonb', 'unknown',
            'any', 'anyelement', 'anyarray', 'anynonarray', 'anycompatible', 'anycompatiblearray',
            'anycompatiblenonarray', 'record', 'void', 'bytea'}
PG_TYPES |= {'_' + t for t in list(PG_TYPES)}
PG_INTERNAL = {'internal', 'cstring', 'trigger', 'event_trigger', 'fdw_handler', 'index_am_handler',
               'table_am_handler', 'tsm_handler', 'language_handler'}
PG_TYPE_GROUPS = [
    ({'point', 'lseg', 'path', 'box', 'polygon', 'line', 'circle'}, 'geometric types'),
    ({'inet', 'cidr', 'macaddr', 'macaddr8'}, 'network address types'),
    ({'tsvector', 'tsquery', 'regconfig', 'regdictionary', 'gtsvector'}, 'full-text search'),
    ({'xml', '_xml'}, 'XML'),
    ({'money'}, 'money'),
    ({'anyrange', 'anymultirange', 'anycompatiblerange', 'anycompatiblemultirange', 'int4range', 'int8range',
      'numrange', 'daterange', 'tsrange', 'tstzrange', 'int4multirange', 'int8multirange', 'nummultirange',
      'datemultirange', 'tsmultirange', 'tstzmultirange'}, 'range and multirange types'),
    ({'bit', 'varbit'}, 'bit strings'),
    ({'uuid'}, 'uuid'),
    ({'jsonpath'}, 'SQL/JSON path language'),
    ({'tid', 'xid', 'xid8', 'cid', 'pg_lsn', 'pg_snapshot', 'txid_snapshot', 'oid', 'oid8', 'regclass', 'regproc',
      'regprocedure', 'regoper', 'regoperator', 'regtype', 'regrole', 'regnamespace', 'regcollation', 'aclitem',
      'int2vector', 'oidvector', 'pg_node_tree', 'pg_ndistinct', 'pg_dependencies', 'pg_mcv_list',
      'pg_brin_bloom_summary', 'pg_brin_minmax_multi_summary', '_aclitem', '_oid', 'refcursor', 'regdatabase'},
     'system types (identifiers, transactions, catalogs)'),
    ({'anyenum'}, 'enum types (user-defined types)'),
]
PG_SYSTEM_PREFIX = ('pg_', 'has_', 'binary_upgrade_', 'brin_', 'gin_', 'txid_', 'current_setting', 'set_config',
                    'obj_description', 'col_description', 'shobj_description', 'format_type', 'currval', 'nextval',
                    'setval', 'lastval', 'getdatabaseencoding', 'version', 'inet_client', 'inet_server',
                    'row_security_active', 'current_schemas', 'current_query', 'unicode_version', 'icu_unicode_version',
                    'mxid_age', 'age(xid)', 'satisfies_hash_partition', 'amvalidate', 'fmgr_', 'ts_debug',
                    'acl', 'makeaclitem', 'to_reg', 'parse_ident', 'quote_', 'get_current_ts_config', 'currtid',
                    'cursor_to_', 'database_to_', 'query_to_', 'schema_to_', 'table_to_', 'gist_', 'spg_',
                    'heap_', 'bt', 'hash', 'interval_hash', 'clock_', 'statement_', 'transaction_', 'timeofday',
                    'getpgusername', 'session_user', 'current_user', 'current_role', 'current_database',
                    'current_catalog', 'current_schema', 'user', 'system_user')
PG_NONDET = {'random', 'random_normal', 'setseed', 'gen_random_uuid', 'uuidv4', 'uuidv7', 'array_sample',
             'array_shuffle'}


def pg_classify(src, modelled):
    cat = Path(src) / 'src/include/catalog'
    oper = refs(cat / 'pg_operator.dat', ['oprcode'])
    restr = refs(cat / 'pg_operator.dat', ['oprrest', 'oprjoin'])
    casts = refs(cat / 'pg_cast.dat', ['castfunc'])
    aggsup = refs(cat / 'pg_aggregate.dat', ['aggtransfn', 'aggfinalfn', 'aggcombinefn', 'aggserialfn',
                                               'aggdeserialfn', 'aggmtransfn', 'aggminvtransfn', 'aggmfinalfn'])
    amproc = refs(cat / 'pg_amproc.dat', ['amproc'])
    typio = refs(cat / 'pg_type.dat', ['typinput', 'typoutput', 'typreceive', 'typsend', 'typmodin', 'typmodout',
                                       'typanalyze', 'typsubscript'])
    res = {}
    for e in pg_entries(src):
        n = e['name']
        if n in modelled:
            continue
        types = set(e['args'] + [e['ret']])
        if n in PG_NONDET:
            r = ('excluded', 'nondeterministic: the result is not a function of the database (TODO 3.10)')
        elif types & PG_INTERNAL or n in typio or n in restr:
            r = ('excluded', 'internal support function (type I/O, planner, index or language support): '
                             'it takes or returns internal values which no query handles')
        elif n in amproc:
            r = ('excluded', 'index support function (comparison or hash for an operator class): the comparison '
                             'is modelled by the operators')
        elif n in aggsup:
            r = ('excluded', 'state transition or final function of an aggregate: the aggregate is modelled whole')
        elif n.startswith(PG_SYSTEM_PREFIX):
            r = ('excluded', 'system administration, catalog or session information: depends on the server, '
                             'not on the database of the query')
        else:
            groups = [g for ts, g in PG_TYPE_GROUPS if types & ts]
            if groups:
                r = ('excluded', 'type not modelled: ' + groups[0])
            elif n in oper or e['descr'].startswith('implementation of'):
                r = ('operator', 'implementation of an operator: the operator is modelled under its symbol')
            elif n in casts or (n in PG_TYPES and len(e['args']) == 1):
                r = ('operator', 'conversion function: modelled by CAST (cast_int, cast_numeric, cast_text, ...)')
            elif not types <= PG_TYPES:
                r = ('excluded', 'type not modelled: ' + ', '.join(sorted(types - PG_TYPES)))
            else:
                r = ('planned', e['descr'] or 'function')
        prev = res.get(n)
        order = ['planned', 'excluded', 'operator']
        if prev is None or order.index(r[0]) < order.index(prev[0]):
            res[n] = r
    return res

# names which are constructs of the grammar of the model, not entries of the function tables
WINDOW_FUNS = {'row_number', 'rank', 'dense_rank', 'percent_rank', 'cume_dist', 'ntile', 'lag', 'lead',
               'first_value', 'last_value', 'nth_value'}
SYNTAX = {
    'PostgreSQL': dict({n: 'window function (SqlFull.v, swfun)' for n in WINDOW_FUNS},
                       notlike='the predicate NOT LIKE', int4inc='count(*) state function (internal)',
                       numeric_inc='internal increment of an aggregate state', int8_sum='internal state of sum',
                       similar_escape='SIMILAR TO pattern translation (pg_similar)',
                       similar_to_escape='SIMILAR TO pattern translation (pg_similar)',
                       generate_subscripts='planned with generate_series (table function)'),
}

# the reasons of the remaining names, by name pattern
REASONS = {
    'PostgreSQL': [
        (r'^(json|jsonb)_(populate_record|populate_recordset|to_record|to_recordset)|^jsonb_populate_record_valid$|'
         r'^row_to_json$|^array_to_json$', 'excluded', 'composite (row) types are not values of the model'),
        (r'^lo_|^loread$|^lowrite$', 'excluded', 'large objects: server storage'),
        (r'^ts_', 'excluded', 'type not modelled: full-text search'),
        (r'^xml_', 'excluded', 'type not modelled: XML'),
        (r'_subdiff$', 'excluded', 'type not modelled: range and multirange types'),
        (r'^(normalize|is_normalized|unicode_assigned|casefold|unistr)$', 'excluded',
         'needs the Unicode character database (normalization forms, case folding beyond ASCII): open issue 24'),
        (r'^(timezone|make_timestamptz|date_add|date_subtract)$', 'excluded',
         'needs the time zone database: the model has the UTC offset of the session only'),
        (r'^(convert|convert_from|convert_to|to_ascii|encode|decode|get_bit|get_byte|set_bit|set_byte|'
         r'sha224|sha256|sha384|sha512|crc32|crc32c|bit_count)$', 'excluded',
         'binary strings (bytea) and character encodings: the strings of the model are Unicode text'),
        (r'^(sind|cosd|tand|cotd|asind|acosd|atand|atan2d|asinh|acosh|atanh|erf|erfc|gamma|lgamma)$', 'planned',
         'double precision function: needs a correctly rounded implementation in IEEE.v (sind etc. are exact '
         'at multiples of 30 degrees in PostgreSQL)'),
        (r'_agg_(strict|unique)|_agg_unique_strict$|^(json_object|jsonb_object|jsonb_set_lax)$', 'planned',
         'variant of a modelled JSON function'),
        (r'^(array_fill|array_sort|regexp_match|regexp_matches|regexp_split_to_array)$', 'planned',
         'array function (arrays are modelled as JSON lists)'),
        (r'^(to_number|error_on_null)$', 'planned', 'formatting and assertion function'),
    ],
}


def classify(engine, src, modelled, names):
    res = {}
    if engine == 'PostgreSQL':
        res = pg_classify(src, modelled)
    else:
        res = {n: ('planned', '') for n in names if n not in modelled}
    syn = SYNTAX.get(engine, {})
    for n in list(res):
        if n in syn:
            res[n] = ('syntax', syn[n])
            continue
        if res[n][0] == 'planned':
            for pat, cat, why in REASONS.get(engine, []):
                if re.search(pat, n):
                    res[n] = (cat, why)
                    break
    return res


TITLES = {'syntax': 'Modelled by a construct of the grammar', 'operator': 'Modelled under an operator or CAST',
          'excluded': 'Excluded, with the reason', 'planned': 'Not modelled yet'}


def report(engine, src, modelled, names, source_desc):
    res = classify(engine, src, modelled, names)
    names = sorted(set(names))
    mod = [n for n in names if n in modelled]
    lines = ['# Function catalogue of %s (closeout)' % engine, '',
             'Generated by `tools/functions/catalogue.py` from %s. Each name which the engine registers is either' % source_desc,
             'modelled (an entry of the tables of the dialect, checked by Coq), modelled by a construct of the',
             'grammar or by an operator, excluded with a reason, or not modelled yet.', '',
             '| | names |', '|---|---|',
             '| Registered by the engine | %d |' % len(names),
             '| Modelled (tables of the dialect) | %d |' % len(mod)]
    for k in ('syntax', 'operator', 'excluded', 'planned'):
        lines.append('| %s | %d |' % (TITLES[k], sum(1 for v in res.values() if v[0] == k)))
    lines += ['', '## Modelled', '', ', '.join('`%s`' % n for n in mod), '']
    for k in ('syntax', 'operator', 'excluded', 'planned'):
        by = {}
        for n, (c, why) in sorted(res.items()):
            if c == k:
                by.setdefault(why, []).append(n)
        if not by:
            continue
        lines += ['## ' + TITLES[k], '', '| Reason | Names |', '|---|---|']
        for why in sorted(by, key=lambda w: -len(by[w])):
            ns = by[why]
            shown = ', '.join('`%s`' % n for n in ns[:60]) + (' and %d more' % (len(ns) - 60) if len(ns) > 60 else '')
            lines.append('| %s | %s |' % (why.replace('|', '\\|') or 'not modelled', shown))
        lines.append('')
    out = ROOT / 'docs/closeouts' / (engine + '.md')
    out.parent.mkdir(exist_ok=True)
    out.write_text('\n'.join(lines) + '\n')
    return res


if __name__ == '__main__' and len(sys.argv) >= 6 and sys.argv[1] == 'report':
    eng, src, names_f, out_f, desc = sys.argv[2:7]
    names = [l.strip() for l in open(names_f) if l.strip()]
    r = report(eng, src, parse_coq_output(open(out_f).read()), names, desc)
    import collections
    print(collections.Counter(v[0] for v in r.values()))
