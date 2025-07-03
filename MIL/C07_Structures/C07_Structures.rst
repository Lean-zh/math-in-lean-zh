.. _structures:

结构体（Structures）
=========================

现代数学广泛使用了代数结构，这些代数结构封装了可在不同环境中实例化的模式，而且往往有多种方法来对它们进行定义和实例化。

因此，Lean 提供了相应的方法来形式化定义这些结构并对其进行操作。
此前你已经接触过一些代数结构的示例，比如在
:numref:`Chapter %s <basics>`
中的环（rings）和格（lattices）。
本章将解释之前出现过的方括号语法，比如 ``[Ring α]``、 ``[Lattice α]``，并介绍如何创建和使用自定义的代数结构。

如需了解更多技术细节，可以参考
`Theorem Proving in Lean <https://leanprover.github.io/theorem_proving_in_lean/>`_，
以及 Anne Baanen 的这篇论文 `Use and abuse of instance parameters in the Lean mathematical library <https://arxiv.org/abs/2202.01629>`_。
