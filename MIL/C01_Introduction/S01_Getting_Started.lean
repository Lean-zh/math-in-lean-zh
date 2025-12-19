/- TEXT:

入门指南
---------------

本书教你使用 Lean 4 交互式证明助手来形式化数学。你需要一点儿数学知识，但并不需要太多。
我们将涵盖从数论到测度论和分析的基础方面，如果你对它们不熟悉，你可以在学习的过程中逐渐掌握。
我们也不预设任何对形式化方法的背景知识。
形式化可以被视为一种计算机编程：我们将用一种 Lean 可以理解的规范化的语言，类似于编程语言，来编写数学定义、定理和证明。
作为回报，Lean 提供反馈和信息，解析表达式并保证它们是形式良好的，并最终验证我们的证明的正确性。

你可以从 `Lean 项目页面 <https://leanprover.github.io>`_
和 `Lean 社区网页 <https://leanprover-community.github.io/>`_
了解更多关于 Lean 的信息。本教程基于 Lean 庞大且不断增长的库 **Mathlib** 。
我们也强烈建议加入 `Lean Zulip 在线聊天群 <https://leanprover.zulipchat.com/>`_，如果你还没有加入的话。
在那里你会发现一个活跃而友好的 Lean 爱好者社区，愿意回答问题并提供精神支持。

- 项目在Mathlib版本 15a391f3007c5c377ba21af3e0a1d53502310685 上测试通过（2024.10.16）。
  Mathlib 更新迅速，可能会遇到旧版代码在新版 Mathlib 下无法通过的问题。
  如果读者遇到了版本不兼容问题，请提交PR以使本项目跟进最新 Mathlib，或者提交issue或联系译者协助解决。

虽然你可以在线阅读本书的 pdf （注：中文版暂不支持 pdf） 或 html 版本，
但它设计为可以交互式阅读，在 VS Code 编辑器中运行 Lean 代码。开始学习吧：

（中文用户可以参考 `中文安装教程 <https://www.leanprover.cn/tutorial/install/>`_ ）

1. 按照这些 `安装说明 <https://leanprover-community.github.io/get_started.html>`_
   安装 Lean 4 和 VS Code.

2. 确保你已安装了 `git <https://git-scm.com/>`_.

3. 按照这些 `说明 <https://leanprover-community.github.io/install/project.html#working-on-an-existing-project>`_
   来获取 ``mathematics_in_lean`` 存储库并在 VS Code 中打开它。

4. 本书的每个部分都有一个与之相关联的 Lean 文件，其中包含示例和练习。你可以在名为 ``MIL`` 的文件夹中按章节组织的地方找到它们。
   我们强烈建议复制该文件夹，并在复制的文件夹中进行实验和练习。这样可以保持原始文件的完整性，并且在存储库改动时更容易同步（见下文）。
   你可以将复制的文件夹命名为 ``my_files`` 或其他任何你喜欢的名字，并在其中创建自己的 Lean 文件。

在这之后，你可以按照以下步骤在 VS Code 的侧边栏中打开教科书：

1. 输入 ``ctrl-shift-P`` （在 macOS 中为 ``command-shift-P`` ）。

2. 在出现的栏中输入 ``Lean 4: Docs: Show Documentation Resources``，然后按回车键。
   （一旦该选项在菜单中被高亮显示，你就可以按回车键选择它。）

3. 在打开的窗口中，点击 ``Mathematics in Lean``.

或者，你还可以在云中运行 Lean 和 VS Code，使用 `Gitpod <https://gitpod.io/>`_。
你可以在 Github 上的 Mathematics in Lean `项目官方页面 <https://github.com/leanprover-community/mathematics_in_lean>`_
或 `中文页面 <https://github.com/Lean-zh/math-in-lean-zh>`_ 找到如何操作的说明。
尽管如此，我们仍然建议按照上述方式在 ``MIL`` 文件夹的副本中进行操作。

这本教科书及其相关存储库仍在不断完善中。你可以通过在 ``mathematics_in_lean`` 文件夹内输入 ``git pull``,
接着输入 ``lake exe cache get`` 来更新存储库。（这假设你没有改变 ``MIL`` 文件夹的内容，这也是我们建议你制作副本的原因。）

我们希望你在阅读教科书的同时，在 ``MIL`` 文件夹中完成练习，该文件夹包含了解释、说明和提示。文本通常会包含示例，就像这个例子一样：
TEXT. -/
-- QUOTE:
#eval "Hello, World!"
-- QUOTE.

/- TEXT:
你应该能够在相关的 Lean 文件中找到相应的示例。如果你点击该行，VS Code 将在 ``Lean Goal`` 窗口中显示 Lean 的反馈，
如果你将光标悬停在 ``#eval`` 命令上，VS Code 将在弹出窗口中显示 Lean 对此命令的响应。我们鼓励你编辑文件并尝试自己的示例。

此外，本书还提供了许多具有挑战性的练习供你尝试。不要匆忙跳过这些练习！Lean 需要 **交互式地做** 数学，而不仅仅是阅读。
完成练习是学习的核心内容。你不必完成所有练习；当你觉得已经掌握了相关技能时，可以自由地继续前进。
你始终可以将你的解决方案与与每个部分相关的 ``solutions`` 文件夹中的解决方案进行比较。
TEXT. -/
