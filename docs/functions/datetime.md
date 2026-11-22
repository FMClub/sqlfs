# Date and time functions (TODO 1.5 and 2.7)

Code:
- `src/data/proof_of_concept/Temporal.v`: calendar, texts, formats, intervals (TODO 1.5).
- `src/data/dialects/TemporalFuns.v`: the functions added by TODO 2.7.
- The temporal entries of each dialect's table.

Tests: `src/testing/Test_Date.v` (1.5) and `src/testing/Test_DateTime.v` (2.7). The expected values of
2.7 are the examples of the manuals. The current time is the fixed `statement_time`, 2026-01-01 12:00
UTC: a query is evaluated at one instant, and the session time zone is UTC.

| Function | PostgreSQL | MySQL family | SQLite | Oracle mode |
|---|---|---|---|---|
| arithmetic with intervals, `date_add`/`date_sub`/`adddate`/`subdate`, `INTERVAL n unit` | M | M | M (modifiers) | M (`date ± n`) |
| `extract`, `date_part` | M | M (`EXTRACT(unit FROM t)` with composite units) | — (`strftime`) | M |
| `date_trunc` | M | — | — | M (`TRUNC(d, fmt)`) |
| `date_format`, `to_char`, `strftime` | M (`to_char`; of a number: `PgNumFormat.v`, after `formatting.c`, in the C locale) | M | M | M (`TO_CHAR`) |
| `str_to_date`, `to_date`, `to_timestamp` | M (`to_date`, `to_timestamp(text, fmt)`, `to_timestamp(epoch)`) | M (`STR_TO_DATE`: `DATE`, `TIME` or `DATETIME` by the format) | — | M (`TO_DATE`) |
| `datediff`, `timestampdiff`, `months_between`, `age` | M (`age`, PostgreSQL's borrowing) | M | — (`julianday` differences) | M |
| `now`, `current_*`, `sysdate`, `utc_*`, `clock_timestamp`… | M (the statement time) | M | M | M |
| `make_date`, `make_time`, `make_timestamp`, `make_interval` | M | — (`MAKEDATE`, `MAKETIME` M) | — | — |
| `justify_days`, `justify_hours`, `justify_interval`, `date_bin`, `isfinite` | M | — | — | — |
| `last_day`, `add_months`, `next_day`, `ROUND(date)` | — | M (`LAST_DAY`) | — | M |
| `from_days`, `to_days`, `from_unixtime`, `unix_timestamp`, `sec_to_time`, `time_to_sec` | — | M | M (`unixepoch`) | — |
| `dayname`, `monthname`, `period_add`, `period_diff`, `timediff`, `addtime`, `subtime`, `time_format` | — | M | — | — |
| `julianday`, `unixepoch`, `date()`/`time()`/`datetime()` with modifiers | — | — | M | — |
| `timeofday()` | X (a text of the clock, nondeterministic) | — | — | — |

## Known differences

- Time zones other than UTC are not modelled (TODO 1.5).
- PostgreSQL's `DateStyle`: the dialect `PostgreSQL` writes the dates and timestamps in the ISO style (the default `ISO, MDY`); `PostgreSQL_regress` in the `Postgres, MDY` style of the regression database (`03-09-2010`, `Tue Mar 09 00:00:00 2010`), in its conversions to text (`::text`, `concat`, `concat_ws`, `||`, `format`) and in its client. The times, the intervals and the timestamps with a time zone are not converted.
- MySQL zero dates (`0000-00-00`, a month or a day of 0): the model has no such date. `STR_TO_DATE` of a format without a month or a day returns NULL, where MySQL returns a zero date.
- `TIME_FORMAT` with hours above 23 shows the hour modulo 24; MySQL shows the whole hour count.
- `justify_interval` does not make the signs of the fields agree. PostgreSQL makes `1 mon -1 hour` into `29 days 23:00:00`.
- The date text of Oracle mode inside `text` in the tests is the generic text: `NLS_DATE_FORMAT` applies to `TO_CHAR` and to the conversion to a string.
