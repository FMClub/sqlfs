(************************************************************************************)
(**                                                                                 *)
(**                 The Extension of SQLFormalSemantics Library                     *)
(**                                                                                 *)
(**   System and information functions (TODO 2.9): their values come from the       *)
(**   environment of the evaluation, as the current time does ([statement_time]).   *)
(**                                                                                 *)
(************************************************************************************)

Require Import List String ZArith.

Require Import Values.

Import ListNotations.
Import NullValues.
Open Scope string_scope.

(** The environment of a query: the server, the session and the effects of the statements which came
    before it in the session. A query cannot change them; the default values below are those of a fresh
    session of user [root] on database [test]. *)
Record sys_env : Type := mk_sys_env
  { env_user : string;            (** the user name (without host) *)
    env_host : string;            (** the client host ([user@host] in MySQL) *)
    env_database : string;        (** the current database (PostgreSQL: [current_database]) *)
    env_schema : string;          (** the current schema (PostgreSQL [current_schema], Oracle) *)
    env_connection : Z;           (** [connection_id ()], [pg_backend_pid ()] *)
    env_last_insert_id : Z;       (** [last_insert_id ()], [last_insert_rowid ()] *)
    env_row_count : Z;            (** [row_count ()]: -1 after a statement which returned rows *)
    env_found_rows : Z;           (** [found_rows ()] *)
    env_changes : Z;              (** SQLite [changes ()], [total_changes ()] *)
    env_versions : string -> string }. (** the version string of an engine *)

Definition default_versions (engine : string) : string :=
  match engine with
  | "PostgreSQL" => "PostgreSQL 16.4 on x86_64-pc-linux-gnu, compiled by gcc, 64-bit"
  | "MySQL" => "8.0.36"
  | "Percona Server for MySQL" => "8.0.36-28"
  | "PolarDB for MySQL" => "8.0.18"
  | "MariaDB" => "11.4.2-MariaDB"
  | "TiDB" => "8.0.11-TiDB-v8.1.0"
  | "OceanBase (MySQL mode)" => "5.7.25-OceanBase-v4.2.1.0"
  | "OceanBase (Oracle mode)" => "OceanBase 4.2.1.0"
  | "SQLite" => "3.45.1"
  | _ => ""
  end.

Definition default_env : sys_env :=
  mk_sys_env "root" "localhost" "test" "public" 1%Z 0%Z (-1)%Z 0%Z 0%Z default_versions.

Definition str_v (s : string) : value := Value_string (Some s).

(** the functions of an engine; [none] are those which take no argument *)
Definition sys_table (env : sys_env) (engine : string) : list (string * (list value -> value)) :=
  let k (v : value) := fun (l : list value) => match l with nil => v | _ => Value_Err "wrong number of arguments" end in
  match engine with
  | "PostgreSQL" =>
       ("version", k (str_v (env_versions env engine)))
    :: ("current_user", k (str_v (env_user env))) :: ("session_user", k (str_v (env_user env)))
    :: ("user", k (str_v (env_user env))) :: ("current_role", k (str_v (env_user env)))
    :: ("current_database", k (str_v (env_database env))) :: ("current_catalog", k (str_v (env_database env)))
    :: ("current_schema", k (str_v (env_schema env)))
    :: ("pg_backend_pid", k (VInt 32 (env_connection env)))
    :: nil
  | "SQLite" =>
       ("sqlite_version", k (str_v (env_versions env engine)))
    :: ("last_insert_rowid", k (Value_Z (Some (env_last_insert_id env))))
    :: ("changes", k (Value_Z (Some (env_changes env)))) :: ("total_changes", k (Value_Z (Some (env_changes env))))
    :: nil
  | "OceanBase (Oracle mode)" =>
       ("user", k (str_v (env_user env))) :: ("uid", k (Value_Z (Some 0%Z)))
    :: ("sys_context", fun l => match l with
                                | Value_string (Some ns) :: Value_string (Some p) :: nil =>
                                  if String.eqb ns "USERENV" then
                                    match p with
                                    | "CURRENT_SCHEMA" | "CURRENT_USER" | "SESSION_USER" => str_v (env_user env)
                                    | "DB_NAME" => str_v (env_database env)
                                    | "SESSIONID" => Value_Z (Some (env_connection env))
                                    | _ => Value_string None
                                    end
                                  else Value_string None
                                | _ => Value_string None end)
    :: nil
  | _ => (* the MySQL family *)
       ("version", k (str_v (env_versions env engine)))
    :: ("database", k (str_v (env_database env))) :: ("schema", k (str_v (env_database env)))
    :: ("user", k (str_v (env_user env ++ "@" ++ env_host env))) :: ("current_user", k (str_v (env_user env ++ "@" ++ env_host env)))
    :: ("session_user", k (str_v (env_user env ++ "@" ++ env_host env))) :: ("system_user", k (str_v (env_user env ++ "@" ++ env_host env)))
    :: ("connection_id", k (Value_I (Some (env_connection env, 1%nat))))
    :: ("last_insert_id", fun l => match l with
                                   | nil => Value_I (Some (env_last_insert_id env, 1%nat))
                                   (* [LAST_INSERT_ID (expr)] returns [expr] (and sets the value for the next statements) *)
                                   | v :: nil => v
                                   | _ => Value_Err "wrong number of arguments" end)
    :: ("row_count", k (Value_Z (Some (env_row_count env))))
    :: ("found_rows", k (Value_I (Some (env_found_rows env, 1%nat))))
    :: nil
  end.
