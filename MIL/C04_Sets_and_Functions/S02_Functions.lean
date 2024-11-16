-- BOTH:
import MIL.Common
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/- TEXT:
.. _functions:

函数
---------

若 ``f : α → β`` 是一个函数，而 ``p`` 是一个类型为 ``β`` 的元素的集合，则 Mathlib 库把 ``preimage f p`` (记为 ``f ⁻¹' p`` ) 定义为 ``{x | f x ∈ p}`` 。表达式 ``x ∈ f ⁻¹' p`` 简写为 ``f x ∈ p`` 。这经常很方便，就像在下面例子中看到的这样：
TEXT. -/
-- BOTH:
section

-- QUOTE:
variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

-- EXAMPLES:
example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl
-- QUOTE.

/- TEXT:
若 ``s`` 是类型为 ``α`` 的元素的集合，库也把 ``image f s`` (记为 ``f '' s`` ) 定义为 ``{y | ∃ x, x ∈ s ∧ f x = y}`` 。从而假设 ``y ∈ f '' s`` 分解为三元组 ``⟨x, xs, xeq⟩`` ，其中 ``x : α`` 满足假设 ``xs : x ∈ s`` 和 ``xeq : f x = y`` 。 ``rintro`` 策略中的 ``rfl`` 标签 (见 :numref:`the_existential_quantifier`) 在这类情况下被明确了。
TEXT. -/
-- QUOTE:
example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt
-- QUOTE.

/- TEXT:
``use`` 策略使用了 ``rfl`` 使得在可以做到时关闭目标。

另一个例子：
TEXT. -/
-- QUOTE:
example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs
-- QUOTE.

/- TEXT:
可以把 ``use x, xs`` 这一行换成 ``apply mem_image_of_mem f xs`` ，因为这个定理就是为此时设计，不过此处的证明可以提醒你它是用存在量词定义的。

下列等价关系是一个好练习题：
TEXT. -/
-- QUOTE:
example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  · intro h x xs
    have : f x ∈ f '' s := mem_image_of_mem _ xs
    exact h this
  intro h y ymem
  rcases ymem with ⟨x, xs, fxeq⟩
  rw [← fxeq]
  apply h xs

/- TEXT:
它表明 ``image f`` 和 ``preimage f`` 是 ``Set α`` 和 ``Set β`` 之间所谓 *伽罗瓦连接(Galois connection)* 的一个实例，每个实例都由子集关系作为偏序。在库中，这个等价关系被命名为 ``image_subset_iff`` 。在实践中，右边是更常用的表达方式，因为 ``y ∈ f ⁻¹' t`` 展开为 ``f y ∈ t`` ，而处理 ``x ∈ f '' s`` 则需要分解一个存在量词。

这里有一长串集合论定理供您消遣。你不必一次全部做完，只需做其中几个，其余的留待一个空闲的雨天再做。
TEXT. -/
-- QUOTE:
example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  sorry

example : f '' (f ⁻¹' u) ⊆ u := by
  sorry

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  sorry

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  sorry

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  sorry

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  sorry

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  sorry

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  sorry

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  sorry

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  sorry

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  sorry

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  sorry

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  sorry

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  rintro x ⟨y, ys, fxeq⟩
  rw [← h fxeq]
  exact ys

example : f '' (f ⁻¹' u) ⊆ u := by
  rintro y ⟨x, xmem, rfl⟩
  exact xmem

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  intro y yu
  rcases h y with ⟨x, fxeq⟩
  use x
  constructor
  · show f x ∈ u
    rw [fxeq]
    exact yu
  exact fxeq

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  rintro y ⟨x, xs, fxeq⟩
  use x, h xs

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  intro x; apply h

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  ext x; rfl

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  rintro y ⟨x, ⟨xs, xt⟩, rfl⟩
  constructor
  · use x, xs
  · use x, xt

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  rintro y ⟨⟨x₁, x₁s, rfl⟩, ⟨x₂, x₂t, fx₂eq⟩⟩
  use x₁
  constructor
  · use x₁s
    rw [← h fx₂eq]
    exact x₂t
  · rfl

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  rintro y ⟨⟨x₁, x₁s, rfl⟩, h⟩
  use x₁
  constructor
  · constructor
    · exact x₁s
    · intro h'
      apply h
      use x₁, h'
  · rfl

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) :=
  fun x ↦ id

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  ext y; constructor
  · rintro ⟨⟨x, xs, rfl⟩, fxv⟩
    use x, ⟨xs, fxv⟩
  rintro ⟨x, ⟨⟨xs, fxv⟩, rfl⟩⟩
  exact ⟨⟨x, xs, rfl⟩, fxv⟩

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  rintro y ⟨x, ⟨xs, fxu⟩, rfl⟩
  exact ⟨⟨x, xs, rfl⟩, fxu⟩

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  rintro x ⟨xs, fxu⟩
  exact ⟨⟨x, xs, rfl⟩, fxu⟩

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  rintro x (xs | fxu)
  · left
    exact ⟨x, xs, rfl⟩
  right; exact fxu

/- TEXT:
你还可以尝试下一组练习，这些练习描述了像和原像在带下标集合的并集和交集中的性质。在第三个练习中，参数 ``i : I`` 是必要的，因为要保证指标集非空。要证明其中任何一个，我们推荐使用 ``ext`` 或 ``intro`` 展开等式或集合之间的包含关系的定义，然后调用 ``simp`` 解包集合成员所需的条件。
BOTH: -/
-- QUOTE:
variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  ext y; simp
  constructor
  · rintro ⟨x, ⟨i, xAi⟩, fxeq⟩
    use i, x
  rintro ⟨i, x, xAi, fxeq⟩
  exact ⟨x, ⟨i, xAi⟩, fxeq⟩
-- BOTH:

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  intro y; simp
  intro x h fxeq i
  use x
  exact ⟨h i, fxeq⟩
-- BOTH:

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  intro y; simp
  intro h
  rcases h i with ⟨x, xAi, fxeq⟩
  use x; constructor
  · intro i'
    rcases h i' with ⟨x', x'Ai, fx'eq⟩
    have : f x = f x' := by rw [fxeq, fx'eq]
    have : x = x' := injf this
    rw [this]
    exact x'Ai
  exact fxeq
-- BOTH:

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  ext x
  simp
-- BOTH:

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  ext x
  simp
-- QUOTE.

-- OMIT:
/-
In type theory, a function ``f : α → β`` can be applied to any
element of the domain ``α``,
but we sometimes want to represent functions that are
meaningfully defined on only some of those elements.
For example, as a function of type ``ℝ → ℝ → ℝ``,
division is only meaningful when the second argument is nonzero.
In mathematics, when we write an expression of the form ``s / t``,
we should have implicitly or explicitly ruled out
the case that ``t`` is zero.

But since division has type ``ℝ → ℝ → ℝ`` in Lean,
it also has to return a value when the second argument is zero.
The strategy generally followed by the library is to assign such
functions convenient values outside their natural domain.
For example, defining ``x / 0`` to be ``0`` means that the
identity ``(x + y) / z = x / z + y / z`` holds for every
``x``, ``y``, and ``z``.

As a result, when we read an expression ``s / t`` in Lean,
we should not assume that ``t`` is a meaningful input value.
When we need to, we can restrict the statement of a theorem to
guarantee that it is.
For example, theorem ``div_mul_cancel`` asserts ``x ≠ 0 → x / y * y = x`` for
``x`` and ``y`` in suitable algebraic structures.

.. TODO: previous text (delete eventually)

.. The fact that in type theory a function is always totally
.. defined on its domain type
.. sometimes forces some difficult choices.
.. For example, if we want to define ``x / y`` and ``log x``
.. as functions on the reals,
.. we have to assign a value to the first when ``y`` is ``0``,
.. and a value to the second for ``x ≤ 0``.
.. The strategy generally followed by the Lean library
.. in these situations is to assign such functions somewhat arbitrary
.. but convenient values outside their natural domain.
.. For example, defining ``x / 0`` to be ``0`` means that the
.. identity ``(x + y) / z = x / z + y / z`` holds
.. for every ``x``, ``y``, and ``z``.
.. When you see a theorem in the library that uses the
.. division symbol,
.. you should be mindful that theorem depends on this
.. nonstandard definition,
.. but this generally does not cause problems in practice.
.. When we need to,
.. we can restrict the statement of a theorem so that
.. it does not rely on such values.
.. For example, if a theorem begins ``∀ x > 0, ...``,
.. dividing by ``x`` in the body of the statement is not problematic.
.. Limiting the scope of a quantifier in this way is known
.. as *relativization*.

.. TODO: comments from Patrick
.. This discussion is very important and we should really get it right. The natural tendency of mathematicians here is to think Lean does bullshit and will let them prove false things. So we should focus on why there is no issue, not on apologies or difficulties.

.. I think we could include a discussion of the fact that the meaning of f : α → β is actually more subtle that it seems. Saying f is a function from α to β is actually a slight oversimplification. The more nuanced meaning is that f is a function whose possible meaningful input values all have type α and whose output values have type β, but we should not assume that every term with type α is a meaningful input value.

.. Then we of course need to point out that defining terms of type α → β required to assign a value to every term of type α, and this can be irritating but this is balanced by the convenience of having a couple of unconditional lemma like the (x+y)/z thing.

.. Also, I feel it is very important to point out that real world math doesn't force you to (x+y)/⟨z, proof that z doesn't vanish⟩. So type theory is not different here.

.. TODO: deleted because we haven't discussed subtypes yet.
.. Be sure to do that eventually.
.. There are ways around this, but they are generally unpleasant.
.. For example, we can take ``log`` to be defined on
.. the subtype ``{ x // x > 0 }``,
.. but then we have to mediate between two different types,
.. the reals and that subtype.
-/

/- TEXT:
Mathlib 库定义了谓词 ``InjOn f s``, 表示 ``f`` 在 ``s`` 上是单射。定义如下：
TEXT. -/
-- QUOTE:

example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _
-- QUOTE.

-- BOTH:
end

/- TEXT:
可以证明语句 ``Injective f`` 等价于 ``InjOn f univ`` 。类似地，库中将 ``range f`` 定义为 ``{x | ∃y, f y = x}`` ，因此可以证明 ``range f`` 等于  ``f '' univ`` 。这是 Mathlib 中的一个常见主题：虽然函数的许多属性都是对于其完整域定义的，但通常也有相对化版本，将语句限制为域类型的子集。

下面是一些使用 ``InjOn`` 和 ``range`` 的例子：
BOTH: -/
section

-- QUOTE:
open Set Real

-- EXAMPLES:
example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  intro e
  -- log x = log y
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]


example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]
-- QUOTE.

/- TEXT:
证明这些：
EXAMPLES: -/
-- QUOTE:
example : InjOn sqrt { x | x ≥ 0 } := by
  sorry

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  sorry

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  sorry

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example : InjOn sqrt { x | x ≥ 0 } := by
  intro x xnonneg y ynonneg
  intro e
  calc
    x = sqrt x ^ 2 := by rw [sq_sqrt xnonneg]
    _ = sqrt y ^ 2 := by rw [e]
    _ = y := by rw [sq_sqrt ynonneg]


example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  intro x xnonneg y ynonneg
  intro e
  dsimp at *
  calc
    x = sqrt (x ^ 2) := by rw [sqrt_sq xnonneg]
    _ = sqrt (y ^ 2) := by rw [e]
    _ = y := by rw [sqrt_sq ynonneg]


example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  ext y; constructor
  · rintro ⟨x, ⟨xnonneg, rfl⟩⟩
    apply sqrt_nonneg
  intro ynonneg
  use y ^ 2
  dsimp at *
  constructor
  apply pow_nonneg ynonneg
  apply sqrt_sq
  assumption

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    dsimp at *
    apply pow_two_nonneg
  intro ynonneg
  use sqrt y
  exact sq_sqrt ynonneg

-- BOTH:
end

/- TEXT:
我们要使用两种新方法定义函数 ``f : α → β`` 的反函数。第一，我们需要小心 Lean 中任意类型可能为空。为了在没有 ``x`` 满足 ``f x = y`` 时定义 ``f`` 的逆在 ``y`` 处的取值，我们想要指定 ``α`` 中的缺省值。将注释 ``[Inhabited α]`` 添加为变量等于假设 ``α`` 有一个默认元素，即 ``default`` 。第二，当存在多于一个 ``x`` 满足 ``f x = y`` 时，反函数需要 *选择* 其中一个。这需要诉诸 *选择公理*。Lean 允许使用多种途径访问它：一种方便的途径是使用经典的 ``choose`` 操作符，如下所示。
TEXT. -/
-- BOTH:
section
-- QUOTE:
variable {α β : Type*} [Inhabited α]

-- EXAMPLES:
#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h
-- QUOTE.

/- TEXT:
给定 ``h : ∃ x, P x``, 则 ``Classical.choose h`` 的值是某个满足 ``P x`` 的 ``x`` 。定理 ``Classical.choose_spec h`` 表明 ``Classical.choose h`` 符合要求。

有了这些，我们就可以定义反函数如下：
BOTH: -/
-- QUOTE:
noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h
-- QUOTE.

/- TEXT:
之所以需要 ``noncomputable section`` 和 ``open Classical`` 这两行，是因为我们正在以一种重要的方式使用经典逻辑。在输入 ``y`` 时，函数 ``inverse f`` 返回某个满足 ``f x = y`` 的 ``x`` 值（如果有的话），否则返回一个缺省的 ``α`` 元素。这是一个 *dependent if* 结构的实例，因为在正例中，返回值 ``Classical.choose h`` 取决于假设 ``h`` 。给定 ``h : e`` 时，等式 ``dif_pos h`` 将 ``if h : e then a else b`` 改写为 ``a`` ，同样，给定 ``h : ¬ e`` ，``dif_neg h`` 将它改写为 ``b`` 。定理 ``inverse_spec`` 表明 ``inverse f`` 满足这一设定的第一部分。

如果你还不完全理解它们的工作原理，也不用担心。仅 ``inverse_spec`` 定理就足以说明，当且仅当 ``f`` 是单射时，``inverse f`` 是左逆，当且仅当 ``f`` 是满射时，``inverse f`` 是右逆。通过在 VS Code 双击或右键单击 ``LeftInverse`` 和 ``RightInverse`` ，或使用命令 ``#print LeftInverse`` 和 ``#print RightInverse`` ，可以查看它们的定义。然后尝试证明这两个定理。它们很棘手，你最好先打个自然语言草稿。每个定理都能用大约六行短代码证明。附加题：尝试将每个证明压缩成单行证明。
BOTH: -/
-- QUOTE:
variable (f : α → β)

open Function

-- EXAMPLES:
example : Injective f ↔ LeftInverse (inverse f) f :=
  sorry

example : Surjective f ↔ RightInverse (inverse f) f :=
  sorry
-- QUOTE.

-- SOLUTIONS:
example : Injective f ↔ LeftInverse (inverse f) f := by
  constructor
  · intro h y
    apply h
    apply inverse_spec
    use y
  intro h x1 x2 e
  rw [← h x1, ← h x2, e]

example : Injective f ↔ LeftInverse (inverse f) f :=
  ⟨fun h y ↦ h (inverse_spec _ ⟨y, rfl⟩), fun h x1 x2 e ↦ by rw [← h x1, ← h x2, e]⟩

example : Surjective f ↔ RightInverse (inverse f) f := by
  constructor
  · intro h y
    apply inverse_spec
    apply h
  intro h y
  use inverse f y
  apply h

example : Surjective f ↔ RightInverse (inverse f) f :=
  ⟨fun h y ↦ inverse_spec _ (h _), fun h y ↦ ⟨inverse f y, h _⟩⟩

-- BOTH:
end

-- OMIT:
/-
.. TODO: These comments after this paragraph are from Patrick.
.. We should decide whether we want to do this here.
.. Another possibility is to wait until later.
.. There may be good examples for the topology chapter,
.. at which point, the reader will be more of an expert.

.. This may be a good place to also introduce a discussion of the choose tactic, and explain why you choose (!) not to use it here.

.. Typically, you can include:

.. example {α β : Type*} {f : α → β} : surjective f ↔ ∃ g : β → α, ∀ b, f (g b) = b :=
.. begin
..   split,
..   { intro h,
..     dsimp [surjective] at h, -- this line is optional
..     choose g hg using h,
..     use g,
..     exact hg },
..   { rintro ⟨g, hg⟩,
..     intros b,
..     use g b,
..     exact hg b },
.. end
.. Then contrast this to a situation where we really want a def outputting an element or a function, maybe with a less artificial example than your inverse.

.. We should also tie this to the "function are global" discussion, and the whole thread of deferring proofs to lemmas instead of definitions. There is a lot going on here, and all of it is crucial for formalization.
-/
/- TEXT:
在本节的最后，我们将从类型论的角度来阐述康托尔的著名定理，即不存在从集合到其幂集的满射函数。看看你是否能理解这个证明，然后填上缺失的两行。
TEXT. -/
-- BOTH:
section
variable {α : Type*}
open Function

-- EXAMPLES:
-- QUOTE:
theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S
  sorry
  have h₃ : j ∉ S
  sorry
  contradiction
-- QUOTE.

-- COMMENTS: TODO: improve this
-- SOLUTIONS:
theorem Cantorαα : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S := h₁
  have h₃ : j ∉ S := by rwa [h] at h₁
  contradiction

-- BOTH:
end
