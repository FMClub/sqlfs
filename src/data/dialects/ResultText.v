(** * The text of a result value, as each dialect's client prints it (TODO 7.2)

    The conformance harnesses compare the text that an engine's client printed with the value of the model:
    [result_text d v] is that text. The clients differ in the NULL ([psql], [sqlite3] and SQL*Plus print an
    empty cell, the [mysql] client and [mysqltest] print [NULL]) and in the booleans ([t]/[f] in [psql]; the
    MySQL family and SQLite have integers). The other values are printed by [text_of], which follows the
    output functions of the engines (the scale of a decimal, the shortest text of a double in the MySQL
    family, [%!.15g] in SQLite, ISO dates, the fewest fractional digits of a PostgreSQL timestamp). *)
Require Import List String.
Require Import Values Dialects ValueKit.
Open Scope string_scope.

Inductive client := Psql | Mysql | Sqlite3 | Sqlplus.

Definition client_of (d : vsem) : client :=
  if String.eqb (vs_name d) "PostgreSQL" then Psql
  else if String.eqb (vs_name d) "SQLite" then Sqlite3
  else if String.eqb (vs_name d) "OceanBase (Oracle mode)" then Sqlplus
  else Mysql.

Definition result_text (d : vsem) (v : NullValues.value) : string :=
  if NullValues.is_err v then "ERROR"
  else if NullValues.is_null v then (match client_of d with Mysql => "NULL" | _ => "" end)
  else match v, client_of d with
       | NullValues.Value_bool (Some b), Psql => if b then "t" else "f"
       | NullValues.Value_bool (Some b), _ => if b then "1" else "0"
       | _, _ => match text_of v with Some s => s | None => "?" end
       end.
