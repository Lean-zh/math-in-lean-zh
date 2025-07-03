-- BOTH:
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.GroupTheory.Perm.Subgroup
import Mathlib.GroupTheory.PresentedGroup

import MIL.Common

/- TEXT:
.. _groups:

幺半群与群
------------------

.. index:: monoid
.. index:: group (algebraic structure)

幺半群和同态
^^^^^^^^^^^^^^^^^^^^^^^^^^^

抽象代数课程通常从群开始，逐步深入到环、域直至向量空间。这种教学顺序常会导致讨论环上的乘法等非群结构运算时出现不必要的曲折：许多群定理证明的方法同样适用，但我们却要重新证明。
一般来说，当你用书本学习数学时，多数作者用一行 “以下留作习题” 化解此窘境。不过，在 Lean 中，我们有另一种虽然不那么方便，但更安全，更适于形式化的方法：引入幺半群 (monoid)。

类型 `M` 上的 **幺半群** 是一个内部具有结合律和单位元的复合法则 (composition law)。幺半群引入的初衷是同时描述群和环的乘法结构。一些自然的例子如：自然数与加法构成一个幺半群。

从实用的角度而言，你几乎可以忘记 Mathlib 中的幺半群。但了解其存在是有益的，否则在寻找那些实际上并不需要元素可逆的引理时，你可能忽略它们在幺半群而非群的文件中。

类型 ``M`` 上的幺半群被写作 ``Monoid M``.
函数 ``Monoid`` 是一个类型类，所以通常作为隐式实例参数而出现。（即在方括号中）
``Monoid`` 默认用乘号作运算符号。如需使用加号，可以使用 ``AddMonoid``。
若需满足交换律，可使用 ``CommMonoid``.
EXAMPLES: -/
-- QUOTE:
example {M : Type*} [Monoid M] (x : M) : x * 1 = x := mul_one x

example {M : Type*} [AddCommMonoid M] (x y : M) : x + y = y + x := add_comm x y
-- QUOTE.

/- TEXT:
注意：虽然库中确实定义了 ``AddMonoid``，但将加号用于非交换的运算可能会导致混淆。

幺半群 ``M`` 与 ``N`` 间的同态的类型称为 ``MonoidHom M N``，可写作 ``M →* N``. 在将一个同态作用于类型 ``M`` 的元素时，Lean 将视其为一个由 ``M`` 到 ``N`` 的函数。相应的加法版本被称为 ``AddMonoidHom``, 写作 ``M →+ N``.
``M →* N``.
EXAMPLES: -/
-- QUOTE:
example {M N : Type*} [Monoid M] [Monoid N] (x y : M) (f : M →* N) : f (x * y) = f x * f y :=
  f.map_mul x y

example {M N : Type*} [AddMonoid M] [AddMonoid N] (f : M →+ N) : f 0 = 0 :=
  f.map_zero
-- QUOTE.

/- TEXT:
同态其实是一系列映射, 即：同态映射本身和它的一些性质。
:numref:`section_hierarchies_morphisms` 中对这样的系列映射有解释。
现在，我们发现这也产生了些不妙的效果：我们无法使用常规的函数复合来复合两个映射。对此，有 ``MonoidHom.comp`` 和 ``AddMonoidHom.comp``.
EXAMPLES: -/
-- QUOTE:
example {M N P : Type*} [AddMonoid M] [AddMonoid N] [AddMonoid P]
    (f : M →+ N) (g : N →+ P) : M →+ P := g.comp f
-- QUOTE.

/- TEXT:
群和同态
^^^^^^^^^^^^^^^^^^^^^^^^^^

对于群，我们有更多可以探讨的。群，就是幺半群加上每一个元素都有逆元的性质。
EXAMPLES: -/
-- QUOTE:
example {G : Type*} [Group G] (x : G) : x * x⁻¹ = 1 := mul_inv_cancel x
-- QUOTE.

/- TEXT:

.. index:: group (tactic), tactics ; group

正如之前我们看到的 ``ring`` 策略，我们有 ``group`` 策略用来证明所有群所共同满足的恒等式。
(即自由群所满足的恒等式)

EXAMPLES: -/
-- QUOTE:
example {G : Type*} [Group G] (x y z : G) : x * (y * z) * (x * z)⁻¹ * (x * y * x⁻¹)⁻¹ = 1 := by
  group
-- QUOTE.

/- TEXT:
.. index:: abel, tactics ; abel

对满足交换律的群，还有 ``abel`` 策略.

EXAMPLES: -/
-- QUOTE:
example {G : Type*} [AddCommGroup G] (x y z : G) : z + x + (y - z - x) = y := by
  abel
-- QUOTE.

/- TEXT:
有趣的是，群同态所需满足的实际上与幺半群别无二致。所以我们之前的例子可以照搬过来。
EXAMPLES: -/
-- QUOTE:
example {G H : Type*} [Group G] [Group H] (x y : G) (f : G →* H) : f (x * y) = f x * f y :=
  f.map_mul x y
-- QUOTE.

/- TEXT:
当然也有点新性质：
EXAMPLES: -/
-- QUOTE:
example {G H : Type*} [Group G] [Group H] (x : G) (f : G →* H) : f (x⁻¹) = (f x)⁻¹ :=
  f.map_inv x
-- QUOTE.

/- TEXT:
你也许会担心构造一个群同态需要枉费些不必要的工夫：幺半群同态的定义需要映射保持幺元，可这是群的情况下由第一条保持运算的性质就能自动得到的。虽然在实际中多做这一步并不困难，但我们可以避免它。接下来的函数可以由保持运算的群间映射给出群同态.
EXAMPLES: -/
-- QUOTE:
example {G H : Type*} [Group G] [Group H] (f : G → H) (h : ∀ x y, f (x * y) = f x * f y) :
    G →* H :=
  MonoidHom.mk' f h
-- QUOTE.

/- TEXT:
同样对于群（幺半群）同构，我们有类型 ``MulEquiv`` , 记为 ``≃*`` (对应加号版本
``AddEquiv`` 记为 ``≃+``).
 ``f : G ≃* H`` 的逆是 ``MulEquiv.symm f : H ≃* G``,
 ``f`` 和 ``g`` 的复合是 ``MulEquiv.trans f g``, ``G`` 到自身的恒等同构 ``M̀ulEquiv.refl G``.
使用匿名投影子记号, 前两个可对应写作 ``f.symm`` 和
``f.trans g``.
这些类型的元素将在必要时自动转换为同态或函数.
EXAMPLES: -/
-- QUOTE:
example {G H : Type*} [Group G] [Group H] (f : G ≃* H) :
    f.trans f.symm = MulEquiv.refl G :=
  f.self_trans_symm
-- QUOTE.

/- TEXT:
你可以用 ``MulEquiv.ofBijective`` 从一个也是双射的同态构造同构.
同时这样做会使逆映射被标记为不可计算的 (noncomputable).
EXAMPLES: -/
-- QUOTE:
noncomputable example {G H : Type*} [Group G] [Group H]
    (f : G →* H) (h : Function.Bijective f) :
    G ≃* H :=
  MulEquiv.ofBijective f h
-- QUOTE.

/- TEXT:
子群
^^^^^^^^^

就像群同态是一系列映射一样，``G`` 的子群也是一个由类型 ``G`` 的集合和相应的封闭性质所共同构成结构。
EXAMPLES: -/
-- QUOTE:
example {G : Type*} [Group G] (H : Subgroup G) {x y : G} (hx : x ∈ H) (hy : y ∈ H) :
    x * y ∈ H :=
  H.mul_mem hx hy

example {G : Type*} [Group G] (H : Subgroup G) {x : G} (hx : x ∈ H) :
    x⁻¹ ∈ H :=
  H.inv_mem hx
-- QUOTE.

/- TEXT:
在以上的例子中, 重要的一点是要理解 ``Subgroup G`` 是 ``G`` 的子群的类型，而不是对一个 ``Set G`` 中元素 ``H`` 的附加的断言 ``IsSubgroup H``. ``Subgroup G`` 类型已经被赋予了到 ``Set G`` 的类型转换和一个与 ``G`` 间的包含关系的判断。
参见 :numref:`section_hierarchies_subobjects` 以了解这是为何要以及如何完成的。

当然，两个子群相同当且仅当它们包含的元素完全相同。这一事实被注册到了 ``ext`` 策略, 所以你可以像证明两个集合相等一样来证明两个子群相等。

当我们论证类似 ``ℤ`` 是 ``ℚ`` 的一个加性子群这样的命题时,
我们真正想要的其实相当于是构造一个 ``AddSubgroup ℚ`` 类型的项，该项到
``Set ℚ`` 的投影为 ``ℤ``，或者更精确的说，``ℤ`` 在 ``ℚ`` 中的像.
EXAMPLES: -/
-- QUOTE:
example : AddSubgroup ℚ where
  carrier := Set.range ((↑) : ℤ → ℚ)
  add_mem' := by
    rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
    use n + m
    simp
  zero_mem' := by
    use 0
    simp
  neg_mem' := by
    rintro _ ⟨n, rfl⟩
    use -n
    simp
-- QUOTE.

/- TEXT:
通过使用类型类，Mathlib 知道群的子群继承了群结构。
EXAMPLES: -/
-- QUOTE:
example {G : Type*} [Group G] (H : Subgroup G) : Group H := inferInstance
-- QUOTE.

/- TEXT:
这一个例子隐含了一些信息. 对象 ``H`` 并不是一个类型, 但 Lean  通过将其解释为 ``G`` 的子类型自动将其转换为了一个类型.
以上例子还可以用更清晰的方式来表述:
EXAMPLES: -/
-- QUOTE:
example {G : Type*} [Group G] (H : Subgroup G) : Group {x : G // x ∈ H} := inferInstance
-- QUOTE.

/- TEXT:
使用类型``Subgroup G`` 而不是断言
``IsSubgroup : Set G → Prop`` 的一个重要优势在于可以为 ``Subgroup G`` 轻松地赋予额外的结构.
重要的是, 它具有对于包含关系的完备格结构 (lattice structure). 例如, 相较于用额外的引理来说明两个 ``G`` 的子群的交仍然是一个子群, 我们可以使用格运算符 ``⊓`` 直接构造出这个交集构成的子群. 我们可以将有关格的任意引理应用到这样的构造上.

现在我们来检验, 两个子群的下确界导出的集合, 从定义上来说,
确实是它们的交集.
EXAMPLES: -/
-- QUOTE:
example {G : Type*} [Group G] (H H' : Subgroup G) :
    ((H ⊓ H' : Subgroup G) : Set G) = (H : Set G) ∩ (H' : Set G) := rfl
-- QUOTE.

/- TEXT:
为实际上给出了集合交集的运算使用另一个记号可能有些奇怪, 但要知道，这样的对应关系在上确界与并集运算之间不再成立. 因为一般来说, 子群的并不再构成一个子群.
我们需要的是这样的并生成的子群, 这可以使用 ``Subgroup.closure`` 来得到.
EXAMPLES: -/
-- QUOTE:
example {G : Type*} [Group G] (H H' : Subgroup G) :
    ((H ⊔ H' : Subgroup G) : Set G) = Subgroup.closure ((H : Set G) ∪ (H' : Set G)) := by
  rw [Subgroup.sup_eq_closure]
-- QUOTE.

/- TEXT:
另一个微妙的地方在于 ``G`` 本身并不具有类型 ``Subgroup G``,
所以我们需要一种方式来将 ``G`` 视作它自身的子群.
这同样由格结构来证明: 全集构成的子群是格中的最大元.
EXAMPLES: -/
-- QUOTE:
example {G : Type*} [Group G] (x : G) : x ∈ (⊤ : Subgroup G) := trivial
-- QUOTE.

/- TEXT:
类似的，格中的最小元是只包含有单位元的子群.
EXAMPLES: -/
-- QUOTE:
example {G : Type*} [Group G] (x : G) : x ∈ (⊥ : Subgroup G) ↔ x = 1 := Subgroup.mem_bot
-- QUOTE.

/- TEXT:
作为操作群与子群的练习，你可以定义一个子群与环境群中的元素得到的共轭子群.
BOTH: -/
-- QUOTE:
def conjugate {G : Type*} [Group G] (x : G) (H : Subgroup G) : Subgroup G where
  carrier := {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹}
  one_mem' := by
/- EXAMPLES:
    dsimp
    sorry
SOLUTIONS: -/
    dsimp
    use 1
    constructor
    exact H.one_mem
    group
-- BOTH:
  inv_mem' := by
/- EXAMPLES:
    dsimp
    sorry
SOLUTIONS: -/
    dsimp
    rintro - ⟨h, h_in, rfl⟩
    use h⁻¹, H.inv_mem h_in
    group
-- BOTH:
  mul_mem' := by
/- EXAMPLES:
    dsimp
    sorry
SOLUTIONS: -/
    dsimp
    rintro - - ⟨h, h_in, rfl⟩ ⟨k, k_in, rfl⟩
    use h*k, H.mul_mem h_in k_in
    group
-- BOTH:
-- QUOTE.

/- TEXT:
将前两个主题结合在一个, 我们就可以使用群同态来“前推” (push forward) 或“拉回” (pull back) 子群. Mathlib 中的命名习惯是将这两个操作称为 ``map``
和 ``comap``.
它们并不是常见的数学名词, 但它们的优势在于较 "pushforward" 和 "direct image" 更为简洁.
EXAMPLES: -/
-- QUOTE:
example {G H : Type*} [Group G] [Group H] (G' : Subgroup G) (f : G →* H) : Subgroup H :=
  Subgroup.map f G'

example {G H : Type*} [Group G] [Group H] (H' : Subgroup H) (f : G →* H) : Subgroup G :=
  Subgroup.comap f H'

#check Subgroup.mem_map
#check Subgroup.mem_comap
-- QUOTE.

/- TEXT:
特别的, 最小子群（即只含单位元的群）在同态 ``f`` 下的前像构成一个被称为同态
``f`` 的 **核** 的子群, 而 ``f`` 的值域同样也是一个子群.
EXAMPLES: -/
-- QUOTE:
example {G H : Type*} [Group G] [Group H] (f : G →* H) (g : G) :
    g ∈ MonoidHom.ker f ↔ f g = 1 :=
  f.mem_ker

example {G H : Type*} [Group G] [Group H] (f : G →* H) (h : H) :
    h ∈ MonoidHom.range f ↔ ∃ g : G, f g = h :=
  f.mem_range
-- QUOTE.

/- TEXT:
作为操作群同态和子群的练习, 我们来证明一些初等性质.
Mathlib 已经证明了它们, 所以如果你想真正锻炼自己，最好不要依赖于 ``exact?``。
BOTH: -/
-- QUOTE:
section exercises
variable {G H : Type*} [Group G] [Group H]

open Subgroup

example (φ : G →* H) (S T : Subgroup H) (hST : S ≤ T) : comap φ S ≤ comap φ T := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  intro x hx
  rw [mem_comap] at * -- Lean 实际上不需要这一行
  exact hST hx
-- BOTH:

example (φ : G →* H) (S T : Subgroup G) (hST : S ≤ T) : map φ S ≤ map φ T := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  intro x hx
  rw [mem_map] at * -- Lean 实际上不需要这一行
  rcases hx with ⟨y, hy, rfl⟩
  use y, hST hy
-- BOTH:

variable {K : Type*} [Group K]

-- 记得你可以用 `ext` 策略证明子群的相等性.
example (φ : G →* H) (ψ : H →* K) (U : Subgroup K) :
    comap (ψ.comp φ) U = comap φ (comap ψ U) := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  -- 完整的证明可以直接是 ``rfl``, 但我们稍微拆解一下.
  ext x
  simp only [mem_comap]
  rfl
-- BOTH:

-- 将一个子群先后通过两个群同态 “前推” 相当于通过这些同态的复合 “前推” .
example (φ : G →* H) (ψ : H →* K) (S : Subgroup G) :
    map (ψ.comp φ) S = map ψ (S.map φ) := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  ext x
  simp only [mem_map]
  constructor
  · rintro ⟨y, y_in, hy⟩
    exact ⟨φ y, ⟨y, y_in, rfl⟩, hy⟩
  · rintro ⟨y, ⟨z, z_in, hz⟩, hy⟩
    use z, z_in
    calc ψ.comp φ z = ψ (φ z) := rfl
    _               = ψ y := by congr
    _               = x := hy
-- BOTH:

end exercises
-- QUOTE.

/- TEXT:
让我们用两个非常经典的例子来结束对 Mathlib 中子群的介绍.
拉格朗日定理 (Lagrange theorem) 说明了有限群的子群的阶可以整除该群的阶. 西罗第一定理 (Sylow's first theorem)，是拉格朗日定理的一个著名部分逆定理.

虽然 Mathlib 的这一部分是部分为了允许计算而设置的，但我们可以通过以下的 open scoped 命令告诉 Lean 使用非构造性逻辑。
BOTH: -/
-- QUOTE:
open scoped Classical

-- EXAMPLES:

example {G : Type*} [Group G] (G' : Subgroup G) : Nat.card G' ∣ Nat.card G :=
  ⟨G'.index, mul_comm G'.index _ ▸ G'.index_mul_card.symm⟩

-- BOTH:
open Subgroup

-- EXAMPLES:
example {G : Type*} [Group G] [Finite G] (p : ℕ) {n : ℕ} [Fact p.Prime]
    (hdvd : p ^ n ∣ Nat.card G) : ∃ K : Subgroup G, Nat.card K = p ^ n :=
  Sylow.exists_subgroup_card_pow_prime p hdvd
-- QUOTE.

/- TEXT:
接下来的两个练习推导出拉格朗日引理的一个推论。（Mathlib 也已经有证明，所以也不要太快地使用 ``exact?``）
BOTH: -/
-- QUOTE:
lemma eq_bot_iff_card {G : Type*} [Group G] {H : Subgroup G} :
    H = ⊥ ↔ Nat.card H = 1 := by
  suffices (∀ x ∈ H, x = 1) ↔ ∃ x ∈ H, ∀ a ∈ H, a = x by
    simpa [eq_bot_iff_forall, Nat.card_eq_one_iff_exists]
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  constructor
  · intro h
    use 1, H.one_mem
  · rintro ⟨y, -, hy'⟩ x hx
    calc x = y := hy' x hx
    _      = 1 := (hy' 1 H.one_mem).symm
-- EXAMPLES:

#check card_dvd_of_le
-- BOTH:

lemma inf_bot_of_coprime {G : Type*} [Group G] (H K : Subgroup G)
    (h : (Nat.card H).Coprime (Nat.card K)) : H ⊓ K = ⊥ := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  have D₁ : Nat.card (H ⊓ K : Subgroup G) ∣ Nat.card H := card_dvd_of_le inf_le_left
  have D₂ : Nat.card (H ⊓ K : Subgroup G) ∣ Nat.card K := card_dvd_of_le inf_le_right
  exact eq_bot_iff_card.2 (Nat.eq_one_of_dvd_coprimes h D₁ D₂)
-- QUOTE.

/- TEXT:
具体群
^^^^^^^^^^^^^^^

在 Mathlib 中，也可以操作具体的群，尽管这通常比处理抽象理论更为复杂。
例如, 对任意一个类型 ``X``, ``X`` 的置换群为 ``Equiv.Perm X``.
特别的，对称群 :math:`\mathfrak{S}_n` 是 ``Equiv.Perm (Fin n)``.
你也可以论述关于这些群的抽象事实, 比如 ``Equiv.Perm X`` 在 ``X`` 有限时
是由轮换生成的.
EXAMPLES: -/
-- QUOTE:
open Equiv

example {X : Type*} [Finite X] : Subgroup.closure {σ : Perm X | Perm.IsCycle σ} = ⊤ :=
  Perm.closure_isCycle
-- QUOTE.

/- TEXT:
可以完全具体化并计算轮换的实际乘积. 下面使用 ``#simp`` 命令,
其调用 ``simp`` 策略作用于表达式. 记号 ``c[]`` 用于表示轮换表示下的置换. 本例中是 ``ℕ`` 上的置换.
也可以在第一个元素上用 ``(1 : Fin 5)`` 这样的类型标注使其在
``Perm (Fin 5)`` 上计算.
EXAMPLES: -/
-- QUOTE:
#simp [mul_assoc] c[1, 2, 3] * c[2, 3, 4]
-- QUOTE.

/- TEXT:
另一种处理具体群的方式是使用自由群及其相关表示.
类型 ``α`` 上的自由群是一个 ``FreeGroup α`` , 对应包含映射为
``FreeGroup.of : α → FreeGroup α``. 例如，可以定义类型 ``S`` ，其中有三个元素
``a``, ``b`` 和 ``c``, 这些元素可以构成自由群中的元素 ``ab⁻¹``.
EXAMPLES: -/
-- QUOTE:
section FreeGroup

inductive S | a | b | c

open S

def myElement : FreeGroup S := (.of a) * (.of b)⁻¹
-- QUOTE.

/- TEXT:
我们给出了预期的类型，所以 Lean 能推断出 ``.of`` 代表着
``FreeGroup.of``.

自由群的整体性质体现在等价性 ``FreeGroup.lift`` 中.
例如，可以定义 ``FreeGroup S`` 到 ``Perm (Fin 5)`` 的群同态:
映射 ``a`` 到 ``c[1, 2, 3]``, ``b`` 到 ``c[2, 3, 1]``, ``c`` 到 ``c[2, 3]``,
EXAMPLES: -/
-- QUOTE:
def myMorphism : FreeGroup S →* Perm (Fin 5) :=
  FreeGroup.lift fun | .a => c[1, 2, 3]
                     | .b => c[2, 3, 1]
                     | .c => c[2, 3]

-- QUOTE.

/- TEXT:
最后一个例子, 让我们通过定义一个元素立方为单位来生成一个群 (也即同构于 :math:`\mathbb{Z}/3`) 并构造从其到 ``Perm (Fin 5)`` 的态射.

``Unit`` 类型只有一个元素，表示为
``()``. 函数 ``PresentedGroup`` 接受一系列关系,
(即一系列某个自由群中的元素), 并将这个自由群模去由这些关系(元素)生成的正规子群, 返回得到的商群. (在 :numref:`quotient_groups` 中将展示如何处理更一般的商关系) 为简化定义, 我们使用 ``deriving Group`` to 直接生成 ``myGroup`` 上的群实例.
EXAMPLES: -/
-- QUOTE:
def myGroup := PresentedGroup {.of () ^ 3} deriving Group
-- QUOTE.

/- TEXT:
presented groups 的整体性质确保了可以由那些将关系元都映射到目标群的单位元的函数构造群同态.
我们只需要一个函数和其满足该性质的证明, 就能用
``PresentedGroup.toGroup`` 得到所需的群态射.
EXAMPLES: -/
-- QUOTE:
def myMap : Unit → Perm (Fin 5)
| () => c[1, 2, 3]

lemma compat_myMap :
    ∀ r ∈ ({.of () ^ 3} : Set (FreeGroup Unit)), FreeGroup.lift myMap r = 1 := by
  rintro _ rfl
  simp
  decide

def myNewMorphism : myGroup →* Perm (Fin 5) := PresentedGroup.toGroup compat_myMap

end FreeGroup
-- QUOTE.

/- TEXT:
群作用
^^^^^^^^^^^^^

群作用是群论与其它数学相作用的一项重要方式.
群 ``G`` 在某类型 ``X`` 上的一个作用也正是 ``G`` 到
``Equiv.Perm X`` 的一个态射. 所以某种意义上来说群作用已经为前文的讨论所涉及了.
不过我们并不想显式地给出这个态射; 它应该更多可能的由 Lean 自动推断得到. 对此, 我们有类型类 ``MulAction G X``.
这种方式的缺点是, 当我们有同一个群在同一类型上的多个群作用时, 会产生一些曲折, 比如将定义携带不同类型类实例的同义类型.

实例化类型类之后，我们可以使用 ``g • x`` 表示群中的 ``g`` 作用在
点 ``x`` 上.
BOTH: -/
-- QUOTE:
noncomputable section GroupActions

-- EXAMPLES:
example {G X : Type*} [Group G] [MulAction G X] (g g': G) (x : X) :
    g • (g' • x) = (g * g') • x :=
  (mul_smul g g' x).symm
-- QUOTE.

/- TEXT:
对应的加法版本为 ``AddAction``, 记号是
``+ᵥ``. 仿射空间的定义中会用到这个实例.
EXAMPLES: -/
-- QUOTE:
example {G X : Type*} [AddGroup G] [AddAction G X] (g g' : G) (x : X) :
    g +ᵥ (g' +ᵥ x) = (g + g') +ᵥ x :=
  (add_vadd g g' x).symm
-- QUOTE.

/- TEXT:
底层的群态射为 ``MulAction.toPermHom``.
EXAMPLES: -/
-- QUOTE:
open MulAction

example {G X : Type*} [Group G] [MulAction G X] : G →* Equiv.Perm X :=
  toPermHom G X
-- QUOTE.

/- TEXT:
为了说明这一点，让我们看看如何将任意群 ``G`` 的 Cayley 同构嵌入定义为一个置换群，即 ``Perm G``。
EXAMPLES: -/
-- QUOTE:
def CayleyIsoMorphism (G : Type*) [Group G] : G ≃* (toPermHom G G).range :=
  Equiv.Perm.subgroupOfMulAction G G
-- QUOTE.

/- TEXT:
以下是这段话的翻译：

请注意，在上述定义之前，并不需要一定是群，而是可以是幺半群或者任何具有乘法操作的类型。

群的条件真正开始发挥作用是在我们需要将 ``X`` 分成轨道（orbits）时。对应于 ``X`` 的等价关系被称为 ``MulAction.orbitRel``。
这个等价关系并没有被声明为一个全局实例。
EXAMPLES: -/
/- OMIT:
TODO: We need to explain `Setoid` somewhere.
EXAMPLES. -/
-- QUOTE:
example {G X : Type*} [Group G] [MulAction G X] : Setoid X := orbitRel G X
-- QUOTE.

/- TEXT:
利用这一点，我们可以说明在群 ``G`` 的作用下，集合 ``X`` 被划分为多个轨道 (orbits) 。

更具体地说，我们得到一个集合 ``X`` 与一个依赖乘积类型 (dependent product)
``(ω : orbitRel.Quotient G X) × (orbit G (Quotient.out' ω))``
之间的双射, 其中, ``Quotient.out' ω`` 简单地选择一个元素，该元素映射到 ``ω``。

请注意，该依赖积的元素是形如 ``⟨ω, x⟩`` 的对，其中 ``x`` 的类型 ``orbit G (Quotient.out' ω)`` 依赖于 ``ω``。

EXAMPLES: -/
-- QUOTE:
example {G X : Type*} [Group G] [MulAction G X] :
    X ≃ (ω : orbitRel.Quotient G X) × (orbit G (Quotient.out' ω)) :=
  MulAction.selfEquivSigmaOrbits G X
-- QUOTE.

/- TEXT:
特别是，当 X 是有限集时，可以结合 ``Fintype.card_congr`` 和 ``Fintype.card_sigma`` 推导出 ``X`` 的基数等于其轨道 (orbits) 基数之和。

此外，这些轨道与 ``G`` 在稳定子 (stabilizers) 的左平移作用下的商集 (quotient) 一一对应 (存在双射关系)。
这种通过子群的左平移作用定义的商集通常使用符号 `/` 来表示，因此可以用以下简洁的表述来说明。
EXAMPLES: -/
-- QUOTE:
example {G X : Type*} [Group G] [MulAction G X] (x : X) :
    orbit G x ≃ G ⧸ stabilizer G x :=
  MulAction.orbitEquivQuotientStabilizer G x
-- QUOTE.

/- TEXT:
将上述两个结果结合的一个重要特殊情况是当 ``X`` 是一个通过平移作用配备了一个子群 ``H`` 的群 ``G`` 。
在这种情况下，所有稳定子都是平凡的，因此每个轨道都与 ``H`` 一一对应，我们得到：
EXAMPLES: -/
-- QUOTE:
example {G : Type*} [Group G] (H : Subgroup G) : G ≃ (G ⧸ H) × H :=
  groupEquivQuotientProdSubgroup
-- QUOTE.

/- TEXT:
这是我们前面看到的拉格朗日定理版本的概念变体。
请注意，这个版本并不假设有限性。

作为本节的练习，让我们使用前面练习中的 ``conjugate`` 定义，构建一个群对其子群通过共轭作用的群作用。
BOTH: -/
-- QUOTE:
variable {G : Type*} [Group G]

lemma conjugate_one (H : Subgroup G) : conjugate 1 H = H := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  ext x
  simp [conjugate]
-- BOTH:

instance : MulAction G (Subgroup G) where
  smul := conjugate
  one_smul := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    exact conjugate_one
-- BOTH:
  mul_smul := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    intro x y H
    ext z
    constructor
    · rintro ⟨h, h_in, rfl⟩
      use y*h*y⁻¹
      constructor
      · use h
      · group
    · rintro ⟨-, ⟨h, h_in, rfl⟩, rfl⟩
      use h, h_in
      group
-- BOTH:

end GroupActions
-- QUOTE.

/- TEXT:
.. _quotient_groups:

商群
^^^^^^^^^^^^^^^

在上述关于子群作用于群的讨论中，我们看到了商 ``G ⧸ H`` 的出现。
一般来说，这只是一个类型。只有当 ``H`` 是正规子群时，它才能被赋予群结构，使得商映射是一个群态射（group morphism）（并且这种群结构是唯一的）。

正规性假设是一个类型类 ``Subgroup.Normal``，因此类型类推断可以使用它来导出商上的群结构。
BOTH: -/
-- QUOTE:
noncomputable section QuotientGroup

-- EXAMPLES:
example {G : Type*} [Group G] (H : Subgroup G) [H.Normal] : Group (G ⧸ H) := inferInstance

example {G : Type*} [Group G] (H : Subgroup G) [H.Normal] : G →* G ⧸ H :=
  QuotientGroup.mk' H
-- QUOTE.

/- TEXT:
通过 ``QuotientGroup.lift`` 可以使用商群的整体性质：
当且仅当群态射 ``φ`` 的核包含 ``N`` 时，``φ`` 可以下降为 ``G ⧸ N`` 上的态射。
EXAMPLES: -/
-- QUOTE:
example {G : Type*} [Group G] (N : Subgroup G) [N.Normal] {M : Type*}
    [Group M] (φ : G →* M) (h : N ≤ MonoidHom.ker φ) : G ⧸ N →* M :=
  QuotientGroup.lift N φ h
-- QUOTE.

/- TEXT:
目标群被称为 ``M`` 这一事实表明，``M`` 拥有幺半群结构就足够了。

一个重要的特殊情况是当 ``N = ker φ`` 时。在这种情况下，下降的态射是单射，并且我们得到一个从群到其像的群同构。这个结果通常被称为 **第一同构定理**。
EXAMPLES: -/
-- QUOTE:
example {G : Type*} [Group G] {M : Type*} [Group M] (φ : G →* M) :
    G ⧸ MonoidHom.ker φ →* MonoidHom.range φ :=
  QuotientGroup.quotientKerEquivRange φ
-- QUOTE.

/- TEXT:
将整体性质应用于一个态射 ``φ : G →* G'`` 与商群投影 ``Quotient.mk' N'`` 的组合时，我们也可以构造一个从 ``G ⧸ N`` 到 ``G' ⧸ N'`` 的态射。

对 ``φ`` 的条件通常表述为 “``φ`` 应该将 ``N`` 映射到 ``N'`` 内部。” 但这相当于要求 ``φ`` 应该将 ``N'`` 拉回到 ``N`` 上，而后者的条件更便于处理，因为拉回（pullback）的定义不涉及存在量词。
EXAMPLES: -/
-- QUOTE:
example {G G': Type*} [Group G] [Group G']
    {N : Subgroup G} [N.Normal] {N' : Subgroup G'} [N'.Normal]
    {φ : G →* G'} (h : N ≤ Subgroup.comap φ N') : G ⧸ N →* G' ⧸ N':=
  QuotientGroup.map N N' φ h
-- QUOTE.

/- TEXT:
需要注意的一个细微点是，类型 ``G ⧸ N`` 实际上依赖于 ``N``（在定义等同的范围内），因此证明两个正规子群 ``N`` 和 ``M`` 是相等的并不足以使相应的商群相等。然而，在这种情况下，整体性质确实给出了一个同构。
EXAMPLES: -/
-- QUOTE:
example {G : Type*} [Group G] {M N : Subgroup G} [M.Normal]
    [N.Normal] (h : M = N) : G ⧸ M ≃* G ⧸ N := QuotientGroup.quotientMulEquivOfEq h
-- QUOTE.

/- TEXT:
作为本节的最后一组练习，我们将证明：如果 ``H`` 和 ``K`` 是有限群 ``G`` 的不相交正规子群，且它们的基数的乘积等于 ``G`` 的基数，那么 ``G`` 同构于 ``H × K``。请记住，这里的 “不相交” 意味着 ``H ⊓ K = ⊥``。

我们从拉格朗日引理的一些操作开始，此时不假设子群是正规或不相交的。
BOTH: -/
-- QUOTE:
section
variable {G : Type*} [Group G] {H K : Subgroup G}

open MonoidHom

#check Nat.card_pos -- 参数将从子群条件中隐式推导出
#check Subgroup.index_eq_card
#check Subgroup.index_mul_card
#check Nat.eq_of_mul_eq_mul_right

lemma aux_card_eq [Finite G] (h' : Nat.card G = Nat.card H * Nat.card K) :
    Nat.card (G ⧸ H) = Nat.card K := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  have := calc
    Nat.card (G ⧸ H) * Nat.card H = Nat.card G := by rw [← H.index_eq_card, H.index_mul_card]
    _                             = Nat.card K * Nat.card H := by rw [h', mul_comm]

  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos this
-- QUOTE.

/- TEXT:
从现在开始，我们假设我们的子群是正规且不相交的，并假设基数条件。现在，我们构造所需同构的第一个部分。
BOTH: -/
-- QUOTE:
variable [H.Normal] [K.Normal] [Fintype G] (h : Disjoint H K)
  (h' : Nat.card G = Nat.card H * Nat.card K)

#check Nat.bijective_iff_injective_and_card
#check ker_eq_bot_iff
#check restrict
#check ker_restrict

def iso₁ [Fintype G] (h : Disjoint H K) (h' : Nat.card G = Nat.card H * Nat.card K) : K ≃* G ⧸ H := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  apply MulEquiv.ofBijective ((QuotientGroup.mk' H).restrict K)
  rw [Nat.bijective_iff_injective_and_card]
  constructor
  · rw [← ker_eq_bot_iff, (QuotientGroup.mk' H).ker_restrict K]
    simp [h]
  · symm
    exact aux_card_eq h'
-- QUOTE.

/- TEXT:
现在我们可以定义第二个部分。
我们将需要 ``MonoidHom.prod``，它可以根据从 ``G₀`` 到 ``G₁`` 和 ``G₂`` 的态射构建一个从 ``G₀`` 到 ``G₁ × G₂`` 的态射。
BOTH: -/
-- QUOTE:
def iso₂ : G ≃* (G ⧸ K) × (G ⧸ H) := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  apply MulEquiv.ofBijective <| (QuotientGroup.mk' K).prod (QuotientGroup.mk' H)
  rw [Nat.bijective_iff_injective_and_card]
  constructor
  · rw [← ker_eq_bot_iff, ker_prod]
    simp [h.symm.eq_bot]
  · rw [Nat.card_prod]
    rw [aux_card_eq h', aux_card_eq (mul_comm (Nat.card H) _▸ h'), h']
-- QUOTE.

/- TEXT:
再将这两部分结合起来.
EXAMPLES: -/
-- QUOTE:
#check MulEquiv.prodCongr

-- BOTH:
def finalIso : G ≃* H × K :=
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  (iso₂ h h').trans ((iso₁ h.symm (mul_comm (Nat.card H) _ ▸ h')).prodCongr (iso₁ h h')).symm

end
end QuotientGroup
-- QUOTE.
