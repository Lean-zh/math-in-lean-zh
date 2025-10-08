# Lean 形式化数学

本教程基于 Lean 4，VS Code，和 Mathlib。[英文版](https://leanprover-community.github.io/mathematics_in_lean/)

在您的计算机上使用此存储库的副本。或者，你可以使用Github Codespaces或Gitpod在云上运行 Lean 和 VS Code。

本书介绍 [Lean 4](https://leanprover.github.io/) 和
[Mathlib](https://github.com/leanprover-community/mathlib4).
Lean 3 版 [https://github.com/leanprover-community/mathematics_in_lean3](https://github.com/leanprover-community/mathematics_in_lean3).


# 源文件在 master 目录下，项目文件在 gh-pages 目录下

# 源文件说明

本仓库用于生成 [Mathematics in Lean (Chinese Translation)](https://www.leanprover.cn/math-in-lean-zh/) 教材和用户仓库。



我们的构建流程会对事先标记过的 Lean 文件应用基础脚本以生成以下文件

- 教材源文件,
- Lean 习题文件,
- Lean 习题解答文件,

并将它们放到正确的位置。

我们使用 [Sphinx](https://www.sphinx-doc.org/en/master/)
 和 [Read the Docs theme](https://sphinx-rtd-theme.readthedocs.io/en/stable/)
 生成教材的 HTML 和 PDF版本。

最后，我们用另一个脚本将内容部署到
[用户仓库](https://github.com/leanprover-community/mathematics_in_lean).


环境配置
-----

编辑 Lean 文件需要安装 Lean、GitHub 及相关工具。具体请参考 [Lean 社区网页](https://leanprover-community.github.io/) 。
特别注意，拉取本仓库后请运行
```
lake exe cache get
```
以获取 Mathlib 的编译版本。

构建教材需要安装
[Sphinx 和 ReadTheDocs](https://sphinx-rtd-tutorial.readthedocs.io/en/latest/install.html)
，以及 Python 的 `regex` 包.
 理想情况下，运行 `pip install -r scripts/requirements.txt` 即可。


概览
--------

Lean 源文件位于 `MIL` 目录。每章一个文件夹，文件夹名以字母 `C` 和章节号开头。
脚本会对章节排序，并忽略不以 `C` 开头的文件夹。

每个文件夹应包含同名的 `.rst` 文件，作为 Sphinx 的章节头。
每个文件夹还包含每个小节的 Lean 源文件，文件名以 `S` 和小节号开头。
脚本会忽略不以 `S` 开头的 Lean 文件。
生成内容所用的标记方法见下文。

`sphinx_source` 文件夹包含的部分文件，将自动添加到生成的 `source` 文件夹，供 Sphinx 使用。
其中包括教材中用到的图片文件夹。

`user_repo_source` 文件夹包含的部分文件，将自动添加到生成的 `user_repo` 文件夹，供用户仓库使用。
其中包括该仓库的 `README` 文件。


构建
-----

运行 `scripts/mkall.py` 会执行以下操作：
- 创建并初始化供 Sphinx 使用的 `source` 目录。
- 创建并初始化 `user_repo` 目录，包含将要部署到用户仓库的文件。
- 更新 `MIL.lean` 文件以匹配 `MIL` 文件夹内容。

有了 `source` 目录后，可以用 `make html` 和 `make latexpdf` 分别构建教材的 HTML 和 PDF 版本，Sphinx 会将它们放到自动生成的 `build` 目录。

运行 `scripts/deploy.sh leanprover-community mathematics_in_lean` 会调用上述所有脚本，将 HTML 和 PDF 教材复制到 `user_repo`，并部署到 GitHub 仓库 `leanprover-community/mathematics_in_lean`。
你也可以部署到其他位置进行测试。

运行 `scripts/clean.py` 会删除 `source`、`user_repo` 和 `build` 目录。


标记符
------

`MIL` 文件夹中的 Lean 文件会生成三类文件：
- 教材 Sphinx 源文件
- 用户仓库的习题文件
- 用户仓库的解答文件

Lean 文件中的每一行文本会根据简单的标记指令，决定被发送到哪些目标文件。

当 `scripts/mkall.py` 开始处理文件时，默认会将输出发送到对应的习题文件和解答文件。例如，import 行就是如此。

以下符号只用于标记教材内容：
```
/- TEXT:
这里是教材内容。
TEXT. -/
```
注释之间的内容只会发送到 Sphinx 源文件。

`TEXT. -/` 行之后的内容，默认只发送到习题文件。
你可以用 `EXAMPLES: -/` 达到同样效果，`SOLUTIONS: -/` 只发送到解答文件，`BOTH: -/` 同时发送到习题和解答文件，`OMIT: -/` 不发送到任何文件。

你还可以用 `-- EXAMPLES:`、`-- SOLUTIONS:`、`-- BOTH:`、`-- OMIT:` 修改其后内容将发送到的对象。

处理 Lean 代码时，可以用如下方式将一段代码作为引用块添加到教材：
```
-- QUOTE:
example : 1 + 1 = 2 := by rfl
-- QUOTE.
```
注意用句点标记引用块结束。
不能引用只发送到解答文件的内容。
`QUOTE` 指令不受 `EXAMPLES`、`SOLUTIONS`、`BOTH`、`OMIT` 指令影响。
例如，你可以在引用块中间切换输出目标。

你还可以用 `/- EXAMPLES:`、`/- SOLUTIONS:`、`/- BOTH:`、`/- OMIT:` 在块注释中指定内容发送目标。
这有助于在习题文件中用 `sorry`，而在解答文件中给出完整解答。例如：
```
/- TEXT:
这里是 ``rintro`` 的用法示例：
TEXT. -/
-- QUOTE:
example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  rintro x ⟨xs, xt | xu⟩
  · left; exact ⟨xs, xt⟩
  · right; exact ⟨xs, xu⟩
-- QUOTE.

/- TEXT:
以证明另一部分的包含关系作为练习：
BOTH: -/
-- QUOTE:
theorem foo : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  rintro x (⟨xs, xt⟩ | ⟨xs, xu⟩)
  · use xs; left; exact xt
  · use xs; right; exact xu
-- QUOTE.
```
第二个文本块展示了习题的常见写法：教材说明后的 `theorem` 或 `example` 行将同时发送到习题和解答文件。
习题文件只包含 `sorry`，解答文件包含完整解答。Lean 会检查解答，但不会在引用块中展示。

需要空行时，建议在相关片段之后指定，这样下次启用输出时无需再加空行。
如上例，`-- QUOTE:` 前后没有空行，因为假定前面已插入空行，但 `-- QUOTE.` 后有空行。

习题和解答文件常用 section 声明变量，但引用块中通常省略 section 命令。例如：
```
/- TEXT:
这里是 ``rintro`` 的用法示例：
BOTH: -/
section
variable (s t u : Set α)

-- EXAMPLES:
-- QUOTE:
example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  rintro x ⟨xs, xt | xu⟩
  · left; exact ⟨xs, xt⟩
  · right; exact ⟨xs, xu⟩
-- QUOTE.
```
确保后续文件中有与 `section` 匹配的 `end` ，并在其后加空行。这些内容将同时发往习题文件和解答文件（BOTH）。

Lean 输入文件中的 `αα` 字符会被脚本删除。可以使用这个小技巧，让习题和解答文件使用同名标识符。例如：
```
/- TEXT:
以证明另一方向的包含关系作为练习：
EXAMPLES: -/
-- QUOTE:
theorem foo : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  sorry
-- QUOTE.

-- SOLUTIONS:
theorem fooαα : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  rintro x (⟨xs, xt⟩ | ⟨xs, xu⟩)
  · use xs; left; exact xt
  · use xs; right; exact xu

```
这样，习题和解答的定理都可以命名为 `foo`，且 Lean 不会因重复标识符报错。

最后，无论内容在 Lean 源文件中的何处，都可以用标签机制在教材中引用这些内容。例如：
```
theorem foo : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
-- TAG: my_tag
  rintro x (⟨xs, xt⟩ | ⟨xs, xu⟩)
  · use xs; left; exact xt
  · use xs; right; exact xu
-- TAG: end
```
第一个标签 `my_tag` 可自定义，第二个必须为 `end`。

在文本块中插入：
```
-- LITERALINCLUDE: my_tag
```
即可在教材中以引用块形式插入标记内容，使用 Sphinx 的专门指令。


测试
-------

运行 `scripts/mkall.py` 后，可以用 `lake build` 编译所有 Lean 源文件。
这会输出所有 `#check`、`#eval` 等命令的结果，以及每个 `sorry` 的警告等。通过扫描输出可以检测所有定义、定理和证明是否正确。
但这不能保证由 Lean 源文件生成的习题和解答文件也都正确。

测试习题文件可用 `scripts/examples_test.py` 。
它会像 `scripts/mkall.py` 一样编译所有 Lean 源文件，然后将 `user_repo` 中的 Lean 文件复制到 `MIL/Test` 文件夹，并构建 `MIL.lean` 以导入这些文件。
用 `lake build` 编译即可。

同理，测试解答文件可用 `scripts/solutions_test.py`，然后用 `lake build` 编译。

用 `scripts/clean_test.py` 删除 `MIL/Test` 目录，并恢复 `MIL.lean` 导入 Lean 源文件。


构建单个小节
----------------------

可以用 `scripts/mksection.py` 测试构建单个小节。例如：
```
  scripts/mksection.py C03_Logic S02_The_Existential_Quantifier
```
这会为指定小节生成习题文件、解答文件和 Sphinx 的 rst 文件。


教材勘误
-----------------

教材仍在完善中，欢迎反馈和修正。你可以提交 PR，或在 [Lean Zulip 频道](https://leanprover.zulipchat.com/) 找到我们，也欢迎通过邮件联系。

# 项目文件说明

## 在本地计算机上使用本仓库

请按如下步骤操作：

1. 按照 [Lean 4 和 VS Code 安装说明](https://leanprover-community.github.io/get_started.html) 安装 Lean 4 和 VS Code。

2. 确保已安装 [git](https://git-scm.com/)。

3. 按照 [项目协作说明](https://leanprover-community.github.io/install/project.html#working-on-an-existing-project) 拉取 `mathematics_in_lean` 仓库并在 VS Code 中打开。

4. 教材每节都有对应的 Lean 文件，包含例题和练习。可在 `MIL` 文件夹中按章节查找。
   强烈建议复制该文件夹，在副本中做练习和实验，这样可以保留原文件，也方便仓库更新（见下文）。
   副本可命名为 `my_files` 或其他名称，也可用来创建自己的 Lean 文件。

此时可在浏览器中打开 [教材](https://leanprover-community.github.io/mathematics_in_lean/) ，并在 VS Code 中做练习。

教材和本仓库仍在完善中。可通过 `git pull` 更新仓库，然后在 `mathematics_in_lean` 文件夹中运行 `lake exe cache get`。
（操作需要 `MIL` 文件夹内容未经修改，所以建议在副本中练习。）


## 使用 Github Codespaces

如果安装 Lean 有困难，可以直接在浏览器中用 Github Codespaces 运行 Lean。
需要 Github 账号，登录后点击：

<a href='https://codespaces.new/leanprover-community/mathematics_in_lean' target="_blank" rel="noreferrer noopener"><img src='https://github.com/codespaces/badge.svg' alt='Open in GitHub Codespaces' style='max-width: 100%;'></a>

确保机器类型为 `4-core`，然后点击 `Create codespace`（可能需要几分钟）。
这会在云端创建虚拟机并安装 Lean 和 Mathlib。

打开 MIL 文件夹下的任意 `.lean` 文件即可启动 Lean，可能需要等待一会。
建议按上述说明复制 `MIL` 文件夹。
可在浏览器终端中运行 `git pull` 和 `lake exe cache get` 更新仓库。

Codespaces 每月有一定免费时长。工作结束后，按 `Ctrl/Cmd+Shift+P`，输入 `stop current codespace`，选择 `Codespaces: Stop Current Codespace`。
如果忘记关闭，虚拟机会在一段时间无操作后自动关闭。

要重启之前的工作区，请访问 <https://github.com/codespaces>。


## 使用 Gitpod 仓库

Gitpod 是 Github Codespaces 的替代方案，但略不方便，需要验证手机号。
如有 Gitpod 账号或愿意注册，可访问
[https://gitpod.io/#/https://github.com/leanprover-community/mathematics_in_lean](https://gitpod.io/#/https://github.com/leanprover-community/mathematics_in_lean)。
这会在云端创建虚拟机并安装 Lean 和 Mathlib。
随后会在虚拟仓库中打开 VS Code 窗口。
建议按上述说明复制 `MIL` 文件夹。
可在浏览器终端中运行 `git pull` 和 `lake exe cache get` 更新仓库。

Gitpod 每月有 50 小时免费时长。
工作结束后，可在左侧菜单选择 `Stop workspace`。
工作区也会在最后一次操作后 30 分钟或关闭标签页后 3 分钟自动停止。

要重启之前的工作区，请访问 [https://gitpod.io/workspaces/](https://gitpod.io/workspaces/).
如果你更改筛选器从 Active 到 All，你会看到所有最近的工作区。
你可以固定一个工作区，以便将其保留在活动列表中。


## 如何参与

欢迎 PR，详情见置顶 issue。
