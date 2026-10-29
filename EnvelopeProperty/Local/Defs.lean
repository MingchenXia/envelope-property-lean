/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.Basic

/-!
# Function classes on affine analytifications

Definitions from Fang–Han–Xia, *The envelope property for unibranch projective varieties*,
§5.1–5.3, specialised to an affine variety `Y = Spec A` over the trivially valued field `k`.

* `IsConvexPLOn U u` (Definition 5.1(1)): near every point of the open set `U`, `u` is a finite
  maximum of functions `∑ᵢ aᵢ log|fᵢ| + b` with `aᵢ, b ∈ ℚ` and `fᵢ` invertible near the point.
  On an affine variety, a regular function invertible on a Zariski open `V₀` is, near any point of
  `V₀`, a quotient `g/hⁿ` of elements of `A` that do not vanish there; so it is equivalent to ask
  that the `fᵢ ∈ A` do not vanish on the neighbourhood (with signed rational coefficients).
* `IsLocallyPSHOn U u` (Definition 5.1(3)): near every point, `u` is the limit of a decreasing
  sequence of convex PL functions.
* `FSData`, `IsFS` (Definition 5.7(1)): affine Fubini–Study functions
  `max{a₁ log|f₁| + b₁, …, a_r log|f_r| + b_r, b₀}` with `aᵢ ∈ ℚ_{>0}`, `bᵢ ∈ ℚ`, where the `fᵢ`
  include a set of generators of the `k`-algebra `A`.
* `HasLogGrowth u` (Definition 5.7(2)) and `IsRegularizable u` (Definition 5.7(3)).
* `hull K`, `IsRunge D`, `SatisfiesHullIneq u` (§5.3).

Functions are total maps `Berk k A → EReal`; statements "on `U`" only constrain values on `U`.
A decreasing limit is recorded as the infimum of an antitone sequence.
-/

open scoped NNReal ENNReal Topology

noncomputable section

namespace EnvelopeProperty

open Berk

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A]

/-! ### Convex PL and locally psh functions -/

/-- The real number `∑ᵢ aᵢ log|fᵢ|_y + b` attached to a coefficient vector `a`, a constant `b`
and functions `fᵢ` (only meaningful where all `fᵢ` are nonzero). -/
def tropAffine {n : ℕ} (f : Fin n → A) (p : (Fin n → ℚ) × ℚ) (y : Berk k A) : ℝ :=
  ∑ i, (p.1 i : ℝ) * Real.log (y.val (f i) : ℝ) + p.2

/-- **Convex PL functions** (Definition 5.1(1), affine form). Every point of `U` has an open
neighbourhood `W ⊆ U`, functions `f₁, …, f_n ∈ A` not vanishing on `W`, and a nonempty finite
family of pairs `(a, b) ∈ ℚⁿ × ℚ` such that `u = max_{(a,b)} (∑ᵢ aᵢ log|fᵢ| + b)` on `W`. -/
def IsConvexPLOn (U : Set (Berk k A)) (u : Berk k A → EReal) : Prop :=
  ∀ x ∈ U, ∃ W : Set (Berk k A), IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧
    ∃ (n : ℕ) (f : Fin n → A) (s : Finset ((Fin n → ℚ) × ℚ)) (hs : s.Nonempty),
      (∀ y ∈ W, ∀ i, y.val (f i) ≠ 0) ∧
      ∀ y ∈ W, u y = ((s.sup' hs fun p => tropAffine f p y : ℝ) : EReal)

/-- `u` is, on `U`, the pointwise limit of a decreasing sequence of convex PL functions on `U`. -/
def IsDecrConvexPLLimitOn (U : Set (Berk k A)) (u : Berk k A → EReal) : Prop :=
  ∃ v : ℕ → Berk k A → EReal, (∀ j, IsConvexPLOn U (v j)) ∧
    (∀ y ∈ U, Antitone fun j => v j y) ∧ ∀ y ∈ U, u y = ⨅ j, v j y

/-- **Locally psh functions** (Definition 5.1(3), affine form): every point of `U` has an open
neighbourhood `W ⊆ U` on which `u` is the limit of a decreasing sequence of convex PL functions. -/
def IsLocallyPSHOn (U : Set (Berk k A)) (u : Berk k A → EReal) : Prop :=
  ∀ x ∈ U, ∃ W : Set (Berk k A), IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧ IsDecrConvexPLLimitOn W u

/-! ### Affine Fubini–Study functions -/

/-- The value `a log|f|_x + b` of a term `(f, a, b)`. -/
def fsTerm (t : A × ℚ × ℚ) (x : Berk k A) : EReal :=
  ((t.2.1 : ℝ) : EReal) * logAbs t.1 x + ((t.2.2 : ℝ) : EReal)

variable (k A) in
/-- Data of an **affine Fubini–Study function** (Definition 5.7(1)):
`max{a₁ log|f₁| + b₁, …, a_r log|f_r| + b_r, b₀}` with `aᵢ ∈ ℚ_{>0}`, `bᵢ, b₀ ∈ ℚ`, where the
functions `fᵢ` include a set of generators of the `k`-algebra `A`. -/
structure FSData where
  /-- The terms `(fᵢ, aᵢ, bᵢ)`. -/
  terms : Finset (A × ℚ × ℚ)
  /-- The constant term `b₀`. -/
  const : ℚ
  /-- The coefficients `aᵢ` are positive. -/
  pos : ∀ t ∈ terms, 0 < t.2.1
  /-- The functions `fᵢ` generate `A` as a `k`-algebra. -/
  gen : Algebra.adjoin k (Prod.fst '' (terms : Set (A × ℚ × ℚ))) = ⊤

namespace FSData

/-- The function `max{a₁ log|f₁| + b₁, …, b₀}` defined by FS data. -/
def eval (g : FSData k A) (x : Berk k A) : EReal :=
  max ((g.const : ℝ) : EReal) (g.terms.sup fun t => fsTerm t x)

end FSData

/-- `u` is an affine Fubini–Study function, `u ∈ FS(Y)`. -/
def IsFS (u : Berk k A → EReal) : Prop :=
  ∃ g : FSData k A, ∀ x, u x = g.eval x

/-- **Logarithmic growth** (Definition 5.7(2)): `u ≤ g + C` for some `g ∈ FS(Y)`, `C ∈ ℝ`. -/
def HasLogGrowth (u : Berk k A → EReal) : Prop :=
  ∃ (g : FSData k A) (C : ℝ), ∀ x, u x ≤ g.eval x + (C : EReal)

/-- **Regularizable functions** `ℛ(Y)` (Definition 5.7(3)): functions not identically `-∞` that
are pointwise limits of decreasing sequences in `FS(Y)`. -/
def IsRegularizable (u : Berk k A → EReal) : Prop :=
  (∃ x, u x ≠ ⊥) ∧ ∃ g : ℕ → FSData k A,
    (∀ x, Antitone fun j => (g j).eval x) ∧ ∀ x, u x = ⨅ j, (g j).eval x

/-! ### Polynomial hulls -/

/-- The **polynomial hull** `K̂ = {y : |f(y)| ≤ sup_K |f| for all f ∈ A}` of a set `K`, written
with `log |f|` (equivalent, `log` being an order isomorphism `[0, ∞] ≃ [-∞, ∞]`). -/
def hull (K : Set (Berk k A)) : Set (Berk k A) :=
  {y | ∀ f : A, logAbs f y ≤ ⨆ x ∈ K, logAbs f x}

/-- `K` is **polynomially convex** if `K̂ = K`. -/
def IsPolyConvex (K : Set (Berk k A)) : Prop := hull K = K

/-- An open set `D` is **Runge** if `K̂ ⊆ D` for every compact `K ⊆ D`. -/
def IsRunge (D : Set (Berk k A)) : Prop :=
  ∀ K ⊆ D, IsCompact K → hull K ⊆ D

/-- The **hull inequality**: `u(y) ≤ sup_K u` for every compact `K` and every `y ∈ K̂`. -/
def SatisfiesHullIneq (u : Berk k A → EReal) : Prop :=
  ∀ K : Set (Berk k A), IsCompact K → ∀ y ∈ hull K, u y ≤ ⨆ x ∈ K, u x

end EnvelopeProperty
