.. _topology:

.. index:: topology

拓扑学
========

.. Topology
.. ========

.. Calculus is based on the concept of a function, which is used to model
.. quantities that depend on one another.
.. For example, it is common to study quantities that change over time.
.. The notion of a *limit* is also fundamental.
.. We may say that the limit of a function :math:`f(x)` is a value :math:`b`
.. as :math:`x` approaches a value :math:`a`,
.. or that :math:`f(x)` *converges to* :math:`b` as :math:`x` approaches :math:`a`.
.. Equivalently, we may say that a :math:`f(x)` approaches :math:`b` as :math:`x`
.. approaches a value :math:`a`, or that it *tends to* :math:`b`
.. as :math:`x` tends to :math:`a`.
.. We have already begun to consider such notions in :numref:`sequences_and_convergence`.

微积分建立在函数的概念之上，旨在对相互依赖的量进行建模。例如，研究随时间变化的量是一个常见的应用场景。
**极限**（limit）这一概念同样基础。我们可以说，当 :math:`x` 趋近于某个值 :math:`a` 时，函数 :math:`f(x)` 的极限是一个值 :math:`b` ，或者说 :math:`f(x)` 当 :math:`x` 趋近于 :math:`a` 时 **收敛于（converges to）** :math:`b` 。
等价地，我们可以说当 :math:`x` 趋近于某个值 :math:`a` 时，:math:`f(x)` 趋近于 :math:`b` ，或者说它当 :math:`x` 趋向于 :math:`a` 时 **趋向于（tends to）** :math:`b` 。我们在
:numref:`sequences_and_convergence`
中已开始考虑此类概念。

.. *Topology* is the abstract study of limits and continuity.
.. Having covered the essentials of formalization in Chapters :numref:`%s <basics>`
.. to :numref:`%s <structures>`,
.. in this chapter, we will explain how topological notions are formalized in Mathlib.
.. Not only do topological abstractions apply in much greater generality,
.. but that also, somewhat paradoxically, make it easier to reason about limits
.. and continuity in concrete instances.

**拓扑学**是对极限和连续性的抽象研究。
在第 :numref:`%s <basics>` 章到第 :numref:`%s <structures>` 章中，我们已经介绍了形式化的基础知识，在本章中，我们将解释在 Mathlib 中如何形式化拓扑概念。
拓扑抽象不仅适用范围更广，而且有些矛盾的是，这也使得在具体实例中推理极限和连续性变得更加容易。

.. Topological notions build on quite a few layers of mathematical structure.
.. The first layer is naive set theory,
.. as described in :numref:`Chapter %s <sets_and_functions>`.
.. The next layer is the theory of *filters*, which we will describe in :numref:`filters`.
.. On top of that, we layer
.. the theories of *topological spaces*, *metric spaces*, and a slightly more exotic
.. intermediate notion called a *uniform space*.

拓扑概念建立在多层数学结构之上。
第一层是朴素集合论，如第 :numref:`Chapter %s <sets_and_functions>` 所述。
接下来的一层是 **滤子** 理论，我们将在 :numref:`filters` 中进行描述。
在此之上，我们再叠加 **拓扑空间** 、 **度量空间** 以及一种稍显奇特的中间概念—— **一致空间** 的理论。

.. Whereas previous chapters relied on mathematical notions that were likely
.. familiar to you,
.. the notion of a filter less well known,
.. even to many working mathematicians.
.. The notion is essential, however, for formalizing mathematics effectively.
.. Let us explain why.
.. Let ``f : ℝ → ℝ`` be any function. We can consider
.. the limit of ``f x`` as ``x`` approaches some value ``x₀``,
.. but we can also consider the limit of ``f x`` as ``x`` approaches infinity
.. or negative infinity.
.. We can moreover consider the limit of ``f x`` as ``x`` approaches ``x₀`` from
.. the right, conventionally written ``x₀⁺``, or from the left,
.. written  ``x₀⁻``. There are variations where ``x`` approaches ``x₀`` or ``x₀⁺``
.. or ``x₀⁻`` but
.. is not allowed to take on the value ``x₀`` itself.
.. This results in at least eight ways that ``x`` can approach something.
.. We can also restrict to rational values of ``x``
.. or place other constraints on the domain, but let's stick to those 8 cases.

虽然前面的章节所依赖的数学概念您可能已经熟悉，但“滤子”这一概念对您来说可能不太熟悉，甚至对许多从事数学工作的人员来说也是如此。
然而，这一概念对于有效地形式化数学来说是必不可少的。让我们解释一下原因。
设 ``f : ℝ → ℝ`` 为任意函数。我们可以考虑当 ``x`` 趋近于某个值 ``x₀`` 时 ``f x`` 的极限，但也可以考虑当 ``x`` 趋近于正无穷或负无穷时 ``f x`` 的极限。此外，我们还可以考虑当 ``x`` 从右趋近于 ``x₀``（通常记为 ``x₀⁺``）或从左趋近于 ``x₀``（记为 ``x₀⁻``）时 ``f x`` 的极限。还有些变化情况是 ``x`` 趋近于 ``x₀`` 或 ``x₀⁺`` 或 ``x₀⁻``，但不允许取值为 ``x₀`` 本身。
这导致了至少八种 ``x`` 趋近于某个值的方式。我们还可以限制 ``x`` 为有理数，或者对定义域施加其他约束，但让我们先只考虑这八种情况。

.. We have a similar variety of options on the codomain:
.. we can specify that ``f x`` approaches a value from the left or right,
.. or that it approaches positive or negative infinity, and so on.
.. For example, we may wish to say that ``f x`` tends to ``+∞``
.. when ``x`` tends to ``x₀`` from the right without
.. being equal to ``x₀``.
.. This results in 64 different kinds of limit statements,
.. and we haven't even begun to deal with limits of sequences,
.. as we did in :numref:`sequences_and_convergence`.

在值域方面，我们也有类似的多种选择：
我们可以指定 ``f x`` 从左侧或右侧趋近某个值，或者趋近正无穷或负无穷等等。
例如，我们可能希望说当 ``x`` 从右侧趋近 ``x₀`` 但不等于 ``x₀`` 时，``f x`` 趋近于 ``+∞`` 。
这会产生 64 种不同的极限表述，而且我们甚至还没有开始处理序列的极限，就像我们在 :numref:`sequences_and_convergence` 中所做的那样。

.. The problem is compounded even further when it comes to the supporting lemmas.
.. For instance, limits compose: if
.. ``f x`` tends to ``y₀`` when ``x`` tends to ``x₀`` and
.. ``g y`` tends to ``z₀`` when ``y`` tends to ``y₀`` then
.. ``g ∘ f x`` tends to ``z₀`` when ``x`` tends to ``x₀``.
.. There are three notions of "tends to" at play here,
.. each of which can be instantiated in any of the eight ways described
.. in the previous paragraph.
.. This results in 512 lemmas, a lot to have to add to a library!
.. Informally, mathematicians generally prove two or three of these
.. and simply note that the rest can be proved "in the same way."
.. Formalizing mathematics requires making the relevant notion of "sameness"
.. fully explicit, and that is exactly what Bourbaki's theory of filters
.. manages to do.

当涉及到辅助引理时，问题变得更加复杂。
例如，极限的复合：如果当 ``x`` 趋近于 ``x₀`` 时， ``f x`` 趋近于 ``y₀``，且当 ``y`` 趋近于 ``y₀`` 时， ``g y`` 趋近于 ``z₀``，那么当 ``x`` 趋近于 ``x₀`` 时， ``g ∘ f x`` 趋近于 ``z₀``。
这里涉及三种“趋近于”的概念，每种概念都可以按照上一段描述的八种方式中的任何一种来实例化。
而这会产生 512 个引理，要添加到库中实在太多了！
非正式地说，数学家通常只证明其中两三个，然后简单地指出其余的可以“以相同方式”进行证明。
形式化数学需要明确相关“相同”的概念，而这正是布尔巴基（Bourbaki）的滤子理论所做到的。
