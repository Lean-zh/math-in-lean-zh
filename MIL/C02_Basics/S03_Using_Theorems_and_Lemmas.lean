-- BOTH:
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import MIL.Common

variable (a b c d e : ℝ)
open Real

/- TEXT:
.. _using_theorems_and_lemmas:

使用定理和引理
-------------------------

.. index:: inequalities

重写对于证明等式很有用，但是对于其他类型的定理呢？
例如，我们如何证明一个不等式，比如在 :math:`b \le c` 时 :math:`a + e^b \le a + e^c` ？
本节我们会着重使用 ``apply`` 和 ``exact`` 。

考虑库定理 ``le_refl`` 和 ``le_trans``：
TEXT. -/
-- QUOTE:
#check (le_refl : ∀ a : ℝ, a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
-- QUOTE.

/- TEXT:
``→`` 是右结合的，因此 ``le_trans`` 应该被解释为 ``a ≤ b → (b ≤ c → a ≤ c)`` 。
详细规则在 :numref:`implication_and_the_universal_quantifier` 一节中解释。
标准库设计者已经将 ``le_trans`` 中的 ``a`` , ``b`` 和 ``c`` 设置为隐式参数，也就是在使用时从语境中推断。
这样 Lean 就 **不会** 让你显式提供他们(强制显式参数将在后面讨论)。
例如，当假设 ``h : a ≤ b`` 和 ``h' : b ≤ c`` 在语境中时，以下所有语句都有效：
TEXT. -/
section
-- QUOTE:
variable (h : a ≤ b) (h' : b ≤ c)

#check (le_refl : ∀ a : Real, a ≤ a)
#check (le_refl a : a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (le_trans h : b ≤ c → a ≤ c)
#check (le_trans h h' : a ≤ c)
-- QUOTE.

end

/- TEXT:

.. index:: apply, tactics ; apply, exact, tactics ; exact

``apply`` 策略的作用规则是：
它把被 ``apply`` 的表达式的 **结论** 与当前的目标相匹配，
并将 **前提** （如果有的话）作为新目标。如果给定的证明与目标完全匹配（ **定义** 等价），
则可以使用 ``exact`` 策略代替 ``apply`` 。你可以考察下面的例子：
TEXT. -/
-- QUOTE:
example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans
  -- le_trans : a ≤ b → b ≤ c → a ≤ c, `a ≤ c` 匹配到了目标 `x ≤ z`
  -- 于是 `a` 被重命名（正式地：“实例化”）为 `x`，`c`被重命名为 `z`，
  -- `b` 尚未得到它的新名字，因此处在“元变量”（metavariable）状态，表示为 `?b`
  -- 接下来两个前提 `x ≤ ?b`，`?b ≤ z` 成为了新目标
  · apply h₀
  · apply h₁

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans h₀
  apply h₁

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z :=
  le_trans h₀ h₁

example (x : ℝ) : x ≤ x := by
  apply le_refl

example (x : ℝ) : x ≤ x :=
  le_refl x
-- QUOTE.

/- TEXT:
在第一个示例中， ``apply le_trans`` 创建两个目标，我们使用点 ``·``
（用 ``\.`` 或 ``\centerdot`` 键入，或者直接用英文句号 ``.`` 也可以）来指示对每个目标分别进行证明。
这些点并不是语法上必要的，但它们 **聚焦** 了目标增加了可读性：
在点引入的代码块中，只有一个目标可见，并且必须在代码块结束之前完成证明。
另外，点和策略之间其实也可以不用空格。
在第三个和最后一个示例中，我们直接构造了证明项 ``le_transle_trans h₀ h₁`` 和 ``le_refl x`` 。

另一些库定理：
TEXT. -/
-- QUOTE:
#check (le_refl : ∀ a, a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (lt_of_le_of_lt : a ≤ b → b < c → a < c)
#check (lt_of_lt_of_le : a < b → b ≤ c → a < c)
#check (lt_trans : a < b → b < c → a < c)
-- QUOTE.

/- TEXT:
利用这些定理和 ``apply`` 和 ``exact`` 策略来证明下面的问题：
TEXT. -/
-- Try this.
-- QUOTE:
example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  apply lt_of_le_of_lt h₀
  apply lt_trans h₁
  exact lt_of_le_of_lt h₂ h₃

/- TEXT:

.. index:: linarith, tactics ; linarith

实际上 Lean 有一个自动化策略来证明这类问题：
TEXT. -/
-- QUOTE:
example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  linarith
-- QUOTE.

/- TEXT:
``linarith`` 策略用于处理 **线性算术** ，也就是仅涉及加法和数乘的等式和不等式。
TEXT. -/
section

-- QUOTE:
example (h : 2 * a ≤ 3 * b) (h' : 1 ≤ a) (h'' : d = 2) : d + a ≤ 5 * b := by
  linarith
-- QUOTE.

end

/- TEXT:
除了语境中的等式和不等式之外，你还能把其他式子作为参数传给 ``linarith`` 。在下一个示例中， ``exp_le_exp.mpr h'`` 对应表达式 ``exp b ≤ exp c`` ，稍后解释原因。在 Lean 中，我们用 ``f x`` 来表示将函数 ``f`` 应用于参数 ``x`` ，类似地我们用 ``h x`` 来表示将事实或定理 ``h`` 应用到参数 ``x`` 。括号仅用于复合参数，如 ``f (x + y)`` 。 如果没有括号，``f x + y`` 将被解析为 ``(f x) + y`` 。
TEXT. -/
-- QUOTE:
example (h : 1 ≤ a) (h' : b ≤ c) : 2 + a + exp b ≤ 3 * a + exp c := by
  linarith [exp_le_exp.mpr h']
-- QUOTE.

/- TEXT:
.. index:: exponential, logarithm

这里列出更多库定理，可以用于实数上的不等式：
TEXT. -/
-- QUOTE:
#check (exp_le_exp : exp a ≤ exp b ↔ a ≤ b)
#check (exp_lt_exp : exp a < exp b ↔ a < b)
#check (log_le_log : 0 < a → a ≤ b → log a ≤ log b)
#check (log_lt_log : 0 < a → a < b → log a < log b)
#check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (add_le_add_right : a ≤ b → ∀ c, a + c ≤ b + c)
#check (add_lt_add_of_le_of_lt : a ≤ b → c < d → a + c < b + d)
#check (add_lt_add_of_lt_of_le : a < b → c ≤ d → a + c < b + d)
#check (add_lt_add_left : a < b → ∀ c, c + a < c + b)
#check (add_lt_add_right : a < b → ∀ c, a + c < b + c)
#check (add_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a + b)
#check (add_pos : 0 < a → 0 < b → 0 < a + b)
#check (add_pos_of_pos_of_nonneg : 0 < a → 0 ≤ b → 0 < a + b)
#check (exp_pos : ∀ a, 0 < exp a)
#check add_le_add_left
-- QUOTE.

/- TEXT:
``exp_le_exp`` 、 ``exp_lt_exp`` 和 ``log_le_log`` 等定理使用 **双向蕴含** ，表示“当且仅当”。(用 ``\lr`` 或者 ``\iff`` 输入)。我们将在下一章更详细地讨论这个连接词。 ``rw`` 也可以处理双向蕴含，就像等号一样，将目标中匹配到的表达式右侧重写成左侧。
TEXT. -/
-- QUOTE:
example (h : a ≤ b) : exp a ≤ exp b := by
  rw [exp_le_exp]
  exact h
-- QUOTE.

/- TEXT:
实际上，表达式 ``h : A ↔ B`` 是 ``A → B`` 和  ``B → A`` 的合取，我们可以用 ``h.mp`` “肯定前件式”（modus ponens）指代 ``A → B`` ，而 ``h.mpr`` “肯定前件式的反向”（modus ponens reverse）指代 ``B → A`` 。另外还可以用 ``h.1`` 表示 ``h.mp`` 和用 ``h.2`` 表示 ``h.mpr`` ，虽然这样或许会影响可读性。你可以考察下例；
TEXT. -/
-- QUOTE:
example (h₀ : a ≤ b) (h₁ : c < d) : a + exp c + e < b + exp d + e := by
  apply add_lt_add_of_lt_of_le
  · apply add_lt_add_of_le_of_lt h₀
    apply exp_lt_exp.mpr h₁
  apply le_refl
-- QUOTE.

/- TEXT:
第一行，``apply add_lt_add_of_lt_of_le`` 创建了两个目标，我们再次使用点将两个证明分开。

试试下面的例子。中间的例子展示了 ``norm_num`` 策略可用于解决具体数字的问题。
TEXT. -/
-- QUOTE:
example (h₀ : d ≤ e) : c + exp (a + d) ≤ c + exp (a + e) := by sorry

example : (0 : ℝ) < 1 := by norm_num

example (h : a ≤ b) : log (1 + exp a) ≤ log (1 + exp b) := by
  have h₀ : 0 < 1 + exp a := by sorry
  apply log_le_log h₀
  sorry
-- QUOTE.

-- SOLUTIONS:
example (h₀ : d ≤ e) : c + exp (a + d) ≤ c + exp (a + e) := by
  apply add_le_add_left
  rw [exp_le_exp]
  apply add_le_add_left h₀

-- 使用 `linarith`
example (h₀ : d ≤ e) : c + exp (a + d) ≤ c + exp (a + e) := by
  have : exp (a + d) ≤ exp (a + e) := by
    rw [exp_le_exp]
    linarith
  linarith [this]

example (h : a ≤ b) : log (1 + exp a) ≤ log (1 + exp b) := by
  have h₀ : 0 < 1 + exp a := by linarith [exp_pos a]
  apply log_le_log h₀
  apply add_le_add_left (exp_le_exp.mpr h)

-- SOLUTION.
/- TEXT:
你也许体会到了，寻找你想要的库定理是形式化的重要环节。有以下方式：

* 在 `GitHub 存储库 <https://github.com/leanprover-community/mathlib4>`_ 中浏览 Mathlib。

* 在 `Mathlib 网页 <https://leanprover-community.github.io/mathlib4_docs/>`_ 上查询 API 文档。

* 根据 Mathlib 命名惯例和编辑器智能代码提示功能来猜测定理名称（有时需要手动用 ``Ctrl-空格`` 或 Mac 键盘上的 ``Cmd-空格`` 来开启自动补全）。 Mathlib 的一种命名惯例是，定理 `A_of_B_of_C` 是以前提 B 和 C 推出 A，其中 A 、B 和 C 差不多是把表达式用人类语言朗读出来的样子（但经常会去掉变量名）。因此，形如 ``x + y ≤ ...`` 的定理可能会以 `add_le` 开头。键入 ``add_le`` 然后看看编辑器有没有好建议。请注意，按两次 ``Ctrl-空格`` 将显示更多可用的信息。（译注：快捷键可能无效，和 VS Code 设置有关，在弹出的提示菜单中可以看到右箭头，点击可展开完整信息。）

* VS Code 中，右键单击定理名称将显示一个菜单，其中包含“转到定义”，你可以在附近找到类似的定理。

* 你可以使用 ``apply?`` 策略，这是一个 Mathlib 自带的定理搜索工具，它会自己尝试在库中找到相关的定理。
TEXT. -/
-- QUOTE:
example : 0 ≤ a ^ 2 := by
  -- apply?
  exact sq_nonneg a
-- QUOTE.

/- TEXT:
``--`` 是注释行，你可以取消注释来试着用用 ``apply?`` ，然后你可以尝试用这个工具证明下面的例子：
TEXT. -/
-- QUOTE:
example (h : a ≤ b) : c - exp b ≤ c - exp a := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (h : a ≤ b) : c - exp b ≤ c - exp a := by
  apply sub_le_sub_left
  exact exp_le_exp.mpr h

-- 另一法：
example (h : a ≤ b) : c - exp b ≤ c - exp a := by
  linarith [exp_le_exp.mpr h]

/- TEXT:
你可以再试试用 ``linarith`` 而不是 ``apply?`` 来实现它。其他例子：
TEXT. -/
-- QUOTE:
example : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  have h : 0 ≤ a ^ 2 - 2 * a * b + b ^ 2
  calc
    a ^ 2 - 2 * a * b + b ^ 2 = (a - b) ^ 2 := by ring
    _ ≥ 0 := by apply pow_two_nonneg

  calc
    2 * a * b = 2 * a * b + 0 := by ring
    _ ≤ 2 * a * b + (a ^ 2 - 2 * a * b + b ^ 2) := add_le_add (le_refl _) h
    _ = a ^ 2 + b ^ 2 := by ring
-- QUOTE.

/- TEXT:
Mathlib 习惯于在二元运算符如 ``*`` 和 ``^`` 旁边加空格，不过我不会干扰你的审美喜好。

有几个值得注意的地方。首先，表达式 ``s ≥ t`` 和 ``t ≤ s`` 定义等价，对人类来说可以互换，但是 Lean 的某些功能不理解这种等价（so sad），因此在 Mathlib 中习惯于使用 ``≤`` 而不是 ``≥``。其次，``ring`` 策略真好用！最后，注意到在第二个 ``calc`` 证明的第二行中使用了证明项 ``add_le_add (le_refl _) h``，没必要写成 ``by exact add_le_add (le_refl _) h``。

事实上，上例中的唯一需要人类智慧的地方就是找出假设 ``h`` ，后面其实只涉及线性算术，都交给 ``linarith`` ：
TEXT. -/
-- QUOTE:
example : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  have h : 0 ≤ a ^ 2 - 2 * a * b + b ^ 2
  calc
    a ^ 2 - 2 * a * b + b ^ 2 = (a - b) ^ 2 := by ring
    _ ≥ 0 := by apply pow_two_nonneg
  linarith
-- QUOTE.

/- TEXT:
好极了！下面是对你的挑战。你可以使用定理 ``abs_le'.mpr`` 。
你大概还会用到 ``constructor`` 策略将一个合取分解为两个目标；参见 :numref:`conjunction_and_biimplication` 。
TEXT. -/
-- QUOTE:
example : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  sorry

#check abs_le'.mpr
-- QUOTE.

-- SOLUTIONS:
theorem fact1 : a * b * 2 ≤ a ^ 2 + b ^ 2 := by
  have h : 0 ≤ a ^ 2 - 2 * a * b + b ^ 2
  calc
    a ^ 2 - 2 * a * b + b ^ 2 = (a - b) ^ 2 := by ring
    _ ≥ 0 := by apply pow_two_nonneg
  linarith

theorem fact2 : -(a * b) * 2 ≤ a ^ 2 + b ^ 2 := by
  have h : 0 ≤ a ^ 2 + 2 * a * b + b ^ 2
  calc
    a ^ 2 + 2 * a * b + b ^ 2 = (a + b) ^ 2 := by ring
    _ ≥ 0 := by apply pow_two_nonneg
  linarith

example : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  have h : (0 : ℝ) < 2 := by norm_num
  apply abs_le'.mpr
  constructor
  · rw [le_div_iff₀ h]
    apply fact1
  rw [le_div_iff₀ h]
  apply fact2

/- TEXT:
如果你连这都解决了，说明你马上要成为形式化大师了！
TEXT. -/
