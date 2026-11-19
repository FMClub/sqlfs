# Regular expressions (TODO 2.4)

Code: `src/data/dialects/Regex.v` (abstract syntax, parser, matcher, choice of the match, replacement)
and `src/data/dialects/RegexFuns.v` (the functions of each dialect). Tests: `src/testing/Test_Regex.v`.
The expected values come from PostgreSQL's `src/test/regress/expected/regex.out` and from the examples
in the manuals of MySQL, MariaDB and Oracle.

## The model

- **Syntax.** There is one abstract syntax for all the engines. It covers:
  - characters, `.` and bracket expressions, with ranges, negation and the POSIX classes `[:alpha:]` …;
  - the escapes `\d \w \s \D \W \S`;
  - groups, `(?:…)`, the lookaheads `(?=…)` and `(?!…)`, and the lookbehinds `(?<=…)` and `(?<!…)`;
  - alternation, and the quantifiers `* + ? {m} {m,} {m,n}` with lazy forms;
  - back references `\1`–`\9`;
  - the anchors `^ $ \A \z`, and the word boundaries `\b \B` (PostgreSQL: `\y \Y \m \M`).

  The flavours differ in a few points:
  - PostgreSQL: `\b` is a backspace.
  - TiDB (RE2): back references and lookaheads are syntax errors.
  - Oracle: lookaheads are syntax errors.
- **Matching.** A backtracking matcher returns the matches from a position in the order of preference:
  - a greedy repetition prefers one more iteration and a lazy one one less;
  - an iteration which matches the empty string ends the repetition, as in Perl and Spencer's engine (`()*\1` matches);
  - a back reference compares the text of the group.
- **The choice of the match.**
  - Leftmost-first is used by Perl-style engines: ICU (MySQL 8, OceanBase MySQL mode), PCRE (MariaDB), RE2 (TiDB) and Oracle. At the leftmost position where there is a match, it takes the first one in the order of preference.
  - PostgreSQL uses Advanced Regular Expressions. At the leftmost position, it takes the longest match if the expression is greedy and the shortest if not (manual, "Regular Expression Matching Rules"). Greediness follows these rules:
    - a branch has the greediness of its first quantified atom;
    - `{m}` keeps the greediness of its atom;
    - an alternation is greedy;
    - an expression with no greediness attribute is greedy.
- **Replacement.** A group is written `$n` in ICU and RE2, and `\n` in PostgreSQL, PCRE and Oracle. `\&` (PostgreSQL) is the whole match.

## Table

| Function | PostgreSQL | MySQL / TiDB / OceanBase | MariaDB | SQLite | Oracle |
|---|---|---|---|---|---|
| match predicate | `~ ~* !~ !~*` | `REGEXP`, `RLIKE`, `NOT REGEXP` | same | `REGEXP`: error (no `regexp()` function is defined) | `REGEXP_LIKE` (condition) |
| `regexp_like(s, p [, flags])` | M (boolean) | M (1/0) | M | — | M |
| `regexp_count(s, p [, start [, flags]])` | M | — | — | — | M |
| `regexp_instr(s, p [, pos [, occ [, end? [, flags [, group]]]]])` | M | M | M (two arguments) | — | M |
| `regexp_substr(s, p [, pos [, occ [, flags [, group]]]])` | M | M | M (two arguments) | — | M |
| `regexp_replace(s, p, r [, …])` | M (first match; all with `g`; PG 16 start/N forms) | M (all matches, or occurrence N) | M (all) | — | M (all, or occurrence N) |
| `substring(s from pattern)` | M (the first group, else the match) | — | — | — | — |
| `SIMILAR TO [ESCAPE]` | M (translated to an anchored ARE, as `similar_to_escape` does) | — | — | — | — |

**Flags:**
- All engines: `i`, `c` and `m`.
- MySQL and Oracle: `n` makes `.` match a line break.
- PostgreSQL:
  - `n` is newline-sensitive mode: `.` does not match a line break, and `^`/`$` match at the lines.
  - `s` is the default mode, which is not newline-sensitive.
  - `g` selects all the matches.
- Other flags are errors.

**Case sensitivity by default:**
- MySQL family: case-insensitive under a case-insensitive collation (the session collation, TODO 1.3), and case-sensitive under a binary one.
- PostgreSQL and Oracle: case-sensitive.

## Known differences and limits

- Case folding covers ASCII letters only (ledger row 24).
- PostgreSQL ARE: the groups of the chosen match are those of the first match in preference order that has the chosen length. Spencer's engine computes the groups by its own rules (`regexec.c` `cdissect`), and they can differ when several decompositions have the same overall length.
- Not modelled:
  - `regexp_match` and `regexp_matches` (they return arrays) and `regexp_split_to_table` (a table function): arrays and table functions are TODO 2.8 and 3.x;
  - the `x` flag (extended syntax);
  - Unicode property classes `\p{…}`;
  - possessive quantifiers, which are read as greedy ones.
- Validation: every query of the form `'s' ~ 'p'` and `substring('s' from 'p')` in PostgreSQL's `regex.out`
  that has a single-row result was replayed (49 cases, `src/testing/Test_Regex.v`). The one difference is
  `'a' ~ '$()|^\1'`, which PostgreSQL answers `f`. The test comment says it covers a former infinite loop
  of the back-reference search (`cfindloop`). Under the usual semantics `$()` matches at the end of `'a'`,
  and the model answers `t`.
- The model has no limit on time or backtracking. MySQL raises errors when `regexp_time_limit` or `regexp_stack_limit` is exceeded.
