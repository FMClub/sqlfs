# 待讨论的问题（Open issues）

本仓库没有开启 GitHub Issues，所以用这个文件记录**需要讨论的设计与方向性问题**。
实现层面的细节问题（聚合函数对 NULL 的处理、字符串比较、`SqlExt` 的 JOIN 顺序等）已经直接修复，
见 `docs/SQL_COVERAGE.md`，不在此列。

每一条给出：现状、为什么不能直接改、可选方案。

---

## I1. `Sql.v` 核心语义有两处与 SQL 不符，但修改会破坏与代数的等价性证明

**现状**（均由 `src/testing/Test_Audit.v` 中的 `old_aggregate_empty`、`old_row_not_in` 机器检验）：

- 没有 `GROUP BY` 的聚合查询在空表上返回 0 行；SQL 返回 1 行
  （`SELECT count(*) FROM empty` 应为 `0`）。原因是 `make_groups` 对输入行做划分，空输入没有分组。
- 多列 `(a, b) [NOT] IN (子查询)` 只要任一分量为 NULL 就判为 UNKNOWN；
  SQL 是逐分量比较，某一分量确定不等时整行比较为 FALSE。

**为什么没有直接改**：`eval_sql_query` 与 `eval_sql_formula` 的这两处定义被 `SqlAlgebra.v`
（约 3800 行，SQL 与扩展关系代数的等价性证明）直接依赖，改定义需要重做相关证明。

**可选方案**：
1. 修改 `Sql.v` / `Formula.v` 并重做 `SqlAlgebra.v` 中受影响的证明（工作量大，结论最强）。
2. 保持 `Sql.v` 不变，把它明确定位为“已证明的片段”，在文档中声明这两处偏差；完整语义以 `SqlFull.v` 为准。
3. 给等价性定理加前提（输入非空 / `IN` 为单列），在前提下保持证明。

## I2. `SqlFull.v` 与已有成果之间还没有定理联系

**现状**：`SqlFull.v` 是新的语法和可执行语义，正确性目前靠 130 多个可计算的例子（`Test_SqlFull.v`、`Test_Audit.v`）和
`SqlFullFacts.v` 里的若干性质保证。它与 `Sql.v` 的关系、与关系代数的关系都**没有证明**。

**需要决定的方向**：
- 是否证明嵌入定理：`Sql.v` 的查询翻译到 `SqlFull` 后语义一致（需排除 I1 的两处偏差，并处理
  bag 与 list、`N_join_bag` 与笛卡尔积的差别）。
- 是否把代数（`SqlAlgebra.v` / `SqlAlgebraExt.v`）扩展到外连接、DISTINCT、排序、窗口，并证明
  `SqlFull` 到代数的翻译正确。这是原论文主定理的自然延伸，但工作量很大，需要先确定覆盖哪些构造。
- `SqlExt.v`（合作者的 JOIN 扩展）与 `SqlFull.v` 功能重叠：合并、保留其一，还是让 `SqlExt` 成为
  `SqlFull` 的一个子集？

## I3. 运行时错误被建模为 NULL

**现状**：语义是全函数。除以零、非法类型转换、标量子查询返回多行，在 SQL 中是运行时错误，
这里统一返回 NULL。

**问题**：这与多数数据库不一致（会把“报错的查询”当成“有结果的查询”）。

**可选方案**：(a) 保持现状并在定理中说明；(b) 求值结果改为 `option` / 错误单子，所有定义和证明都要带上
错误传播；(c) 另外定义一个“不会出错”的静态/动态判定谓词，定理只对满足该谓词的查询成立。

## I4. 命名元组模型 vs. SQL 的位置语义

**现状**：元组是“属性名 → 值”的有限映射。因此：
- 集合运算要求两边属性名相同（SQL 按位置对应）；
- 结果中不能有重名列，自连接必须显式重命名；
- `FROM` 中同名属性会被静默合并（见 `SQL_COVERAGE.md` 的 A6）。

**需要决定**：是否引入位置化/带限定名的列模型（影响 `Tuple.Rcd` 及其上的全部证明），
还是保持命名模型，并写一个把真实 SQL 规范化为“属性互不相同”形式的前端及其正确性说明。

## I5. 没有静态类型与良构性检查

**现状**：查询没有类型系统。类型不匹配的比较结果是 UNKNOWN，对非数值做算术得到 NULL，
非法的分组引用（`SELECT` 中出现未分组的列）取分组中的第一行。NULL 带类型
（`Value_Z None` 与 `Value_string None` 是不同的值），目前在写入元组时按属性类型规范化。

**需要决定**：是否定义类型检查与良构性判定（类似 `WellFormed.v` 对旧语言所做的），
并把语义的正确性陈述限制在良构查询上。聚合函数“属于哪一层查询块”的判定目前是语法性的
（按列绑定在哪一层），与旧代码 `find_eval_env` 的判定方式不同，也应在良构性定义中统一。

## I6. 方言相关的选择是写死的

**现状**：以下行为在 SQL 标准中是实现定义的，目前固定为 PostgreSQL 的行为：
NULL 在排序中视为最大；整数除法向零截断；`avg` 返回精确有理数；`GREATEST`/`LEAST` 忽略 NULL；
无全序的 `LIMIT` 取确定的一种结果。

**需要决定**：是否把这些做成参数（“方言”记录），使同一套定理可对多个数据库实例化。

## I7. 尚未覆盖的 SQL 特性

按预计难度排序，需要决定优先级：
- 递归 CTE（`WITH RECURSIVE`）：不保证终止，需要燃料参数或不动点的存在性条件；
- `GROUPING SETS` / `ROLLUP` / `CUBE`；
- 带数值偏移的 `RANGE` 窗口帧、帧排除；
- 日期/时间、浮点数、字符排序规则；
- 有序集聚合（`percentile_cont` 等）、多参数聚合、`string_agg` 的 `ORDER BY`。

## I8. 构建与仓库维护

- 根目录 `Makefile` 执行 `cd src; make`，但 `src/Makefile` 被 `.gitignore` 忽略，新克隆的仓库不能直接
  `make`；提交的 `src/CoqMakeFile*` 是生成文件且含机器相关路径。
- `coq-sqlformalsemantics.opam` 要求 Coq 8.11.2，README 写的是 8.15.0（本次用 8.15.2 验证通过）。
- `src/data/proof_of_concept/FreshAttr.v` 含 `Admitted`，且不在 `_CoqProject` 中。
- 没有 CI；建议加一个编译全部文件（含测试）的工作流。
