.. _groups_and_ring:


群与环
================

我们已经在 :numref:`proving_identities_in_algebraic_structures` 中学习过如何对群与环中的运算进行推理。在稍后的 :numref:`section_algebraic_structures` 也领略过定义抽象代数结构的方法。这类结构诸如群，或是像高斯整环这样的具体示例。:numref:`Chapter %s <hierarchies>` 中解释了 Mathlib 如何处理这些抽象结构的层级关系。

本章中，我们将更为详细地探讨群和环。由于 Mathlib 总在扩展中，我们没办法一应俱全，
但我们将为你给出使用相关库的切入点，并展示如何使用其中的核心概念。
这一章和
:numref:`Chapter %s <hierarchies>` 有些重复，但在这里我们会集中于如何使用 Mathlib，而非探究其背后的设计理念。
因此，要理解本章中的一些例子，你可能需要回顾
:numref:`Chapter %s <hierarchies>`。
