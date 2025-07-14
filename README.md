# 2025 年四川大学几何与拓扑暑期学校笔记

这是本人参加[四川大学几何与拓扑暑期学校](https://math.scu.edu.cn/info/1247/4584.htm)的笔记，包含量子场论、代数曲线、非交换几何以及专题报告的课程笔记。

目前笔记的整体是利用 LaTeX 编写的，使用 `pdflatex` 编译。目前正在计划使用 `Typst` 完全重写。

## 推送规范

- 每个课程的笔记放在对应的目录下，
- 笔记节标题按照 `Day x: Title` 的格式命名，
- Commit 按照 `update for dayx number` 来命名，其中 `x` 是课程的天数，`number` 是当前推送时间与当日授课预期时间的大致比例。

## CI

- CI 会在每次推送到主分支时自动运行，使用 [ltex](https://valentjn.github.io/ltex/index.html) 检查 `.tex` 笔记的拼写与语法错误。在`.ltex_dict/`中添加新单词可以避免拼写错误。可以在正文使用注释 `% ltex: enabled=false` 来禁用某些部分的检查。使用[harper-cli](https://github.com/automattic/harper) 检查 `.typ` 笔记的拼写与语法错误。

## 编辑

- `Typst` 笔记请使用 `typst c ./qft/note.typ --input colored=true` 命令编译，将得到 `note.pdf` 文件，
- `LaTeX` 笔记使用标准流程即可。
