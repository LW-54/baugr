/-
  Baugr.Law — Generalized Monoidal Promise Valency, Top-Completion `Cap R`,
  and Composable ScopeLaw Algebra
  Derived directly from Mark Burgess (2015, arXiv:1505.01716v1 §2.7 & §4.1).
-/

namespace Baugr

/-- Ordered Commutative Monoid for generalized Promise Valency (`+b#n`, capacities, budgets). -/
class ResourceMonoid (R : Type) where
  zero       : R
  add        : R → R → R
  le         : R → R → Prop
  le_refl    : ∀ x, le x x
  le_trans   : ∀ x y z, le x y → le y z → le x z
  add_zero   : ∀ x, add x zero = x
  zero_add   : ∀ x, add zero x = x
  add_comm   : ∀ x y, add x y = add y x
  add_assoc  : ∀ x y z, add (add x y) z = add x (add y z)
  zero_le    : ∀ x, le zero x
  add_le_add : ∀ a b c d, le a b → le c d → le (add a c) (add b d)

instance : ResourceMonoid Nat where
  zero       := 0
  add        := Nat.add
  le         := Nat.le
  le_refl    := Nat.le_refl
  le_trans   := fun _ _ _ => Nat.le_trans
  add_zero   := Nat.add_zero
  zero_add   := Nat.zero_add
  add_comm   := Nat.add_comm
  add_assoc  := Nat.add_assoc
  zero_le    := Nat.zero_le
  add_le_add := fun _ _ _ _ => Nat.add_le_add

/-- Top-completion `R⊤` adjoining an unbounded ceiling `∞` to any `ResourceMonoid R`.
    Unifies exclusive (`bounded 1`), finite (`bounded n`), and broadcast (`unbounded`)
    valencies inside a single heterogeneous Ordered Commutative Monoid. -/
inductive Cap (R : Type) where
  | bounded (val : R)
  | unbounded
  deriving DecidableEq, Repr

instance {R : Type} [ResourceMonoid R] : ResourceMonoid (Cap R) where
  zero := .bounded ResourceMonoid.zero
  add a b :=
    match a, b with
    | .bounded x, .bounded y => .bounded (ResourceMonoid.add x y)
    | _,          _          => .unbounded
  le a b :=
    match a, b with
    | _,          .unbounded => True
    | .unbounded, .bounded _ => False
    | .bounded x, .bounded y => ResourceMonoid.le x y
  le_refl x := by cases x with | bounded r => exact ResourceMonoid.le_refl r | unbounded => trivial
  le_trans a b c h1 h2 := by
    cases a <;> cases b <;> cases c <;> simp_all
    exact ResourceMonoid.le_trans _ _ _ h1 h2
  add_zero x := by
    cases x with
    | bounded r => exact congrArg Cap.bounded (ResourceMonoid.add_zero r)
    | unbounded => rfl
  zero_add x := by
    cases x with
    | bounded r => exact congrArg Cap.bounded (ResourceMonoid.zero_add r)
    | unbounded => rfl
  add_comm a b := by
    cases a <;> cases b <;> try rfl
    exact congrArg Cap.bounded (ResourceMonoid.add_comm _ _)
  add_assoc a b c := by
    cases a <;> cases b <;> cases c <;> try rfl
    exact congrArg Cap.bounded (ResourceMonoid.add_assoc _ _ _)
  zero_le x := by
    cases x with
    | bounded r => exact ResourceMonoid.zero_le r
    | unbounded => trivial
  add_le_add a b c d h1 h2 := by
    cases a <;> cases b <;> cases c <;> cases d <;> simp_all
    exact ResourceMonoid.add_le_add _ _ _ _ h1 h2

/-- Cartesian product of Ordered Commutative Monoids (multi-dimensional budgets). -/
instance {R₁ R₂ : Type} [ResourceMonoid R₁] [ResourceMonoid R₂] : ResourceMonoid (R₁ × R₂) where
  zero       := (ResourceMonoid.zero, ResourceMonoid.zero)
  add a b    := (ResourceMonoid.add a.1 b.1, ResourceMonoid.add a.2 b.2)
  le a b     := ResourceMonoid.le a.1 b.1 ∧ ResourceMonoid.le a.2 b.2
  le_refl x  := ⟨ResourceMonoid.le_refl x.1, ResourceMonoid.le_refl x.2⟩
  le_trans _ _ _ h1 h2 := ⟨ResourceMonoid.le_trans _ _ _ h1.1 h2.1, ResourceMonoid.le_trans _ _ _ h1.2 h2.2⟩
  add_zero x := Prod.ext (ResourceMonoid.add_zero x.1) (ResourceMonoid.add_zero x.2)
  zero_add x := Prod.ext (ResourceMonoid.zero_add x.1) (ResourceMonoid.zero_add x.2)
  add_comm x y := Prod.ext (ResourceMonoid.add_comm x.1 y.1) (ResourceMonoid.add_comm x.2 y.2)
  add_assoc x y z := Prod.ext (ResourceMonoid.add_assoc x.1 y.1 z.1) (ResourceMonoid.add_assoc x.2 y.2 z.2)
  zero_le x  := ⟨ResourceMonoid.zero_le x.1, ResourceMonoid.zero_le x.2⟩
  add_le_add _ _ _ _ h1 h2 := ⟨ResourceMonoid.add_le_add _ _ _ _ h1.1 h2.1, ResourceMonoid.add_le_add _ _ _ _ h1.2 h2.2⟩

/-- Monoidal sum of resource demands across a list of bindings. -/
def sumResource {α R : Type} [ResourceMonoid R] (weight : α → R) : List α → R
  | []      => ResourceMonoid.zero
  | x :: xs => ResourceMonoid.add (weight x) (sumResource weight xs)

/-- Open composable ScopeLaw over any resolved system view `V`. -/
abbrev ScopeLaw (V : Type) := V → Prop

def andLaw {V : Type} (L₁ L₂ : ScopeLaw V) : ScopeLaw V := fun v => L₁ v ∧ L₂ v
def allLaws {V : Type} (ls : List (ScopeLaw V)) : ScopeLaw V := fun v => ∀ L ∈ ls, L v

end Baugr
