/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib

/-!
# The Berkovich analytification of an affine scheme over a trivially valued field

Let `k` be a field, regarded as a non-Archimedean field with the trivial absolute value,
and let `A` be a commutative `k`-algebra. The Berkovich analytification `(Spec A)^an` is
the set of multiplicative seminorms `|·|_x : A → ℝ≥0` satisfying the ultrametric inequality
and restricting to the trivial absolute value on `k`. Such a seminorm is exactly a
valuation `A → ℝ≥0` in Mathlib's (multiplicative) sense that is trivial on `k`; its
support may be any prime ideal of `A`. The topology is the coarsest one for which all
evaluation maps `x ↦ |f|_x` are continuous.

In the additive notation of the source (Fang–Han–Xia, §2.1 and §5) a point is a
semivaluation `v` with `v(f) = -log |f|_x`; we use the multiplicative form throughout and
write `logAbs f x = log |f|_x ∈ [-∞, ∞)`.

## Main definitions

* `EnvelopeProperty.Berk k A`: the analytification of `Spec A`.
* `EnvelopeProperty.Berk.logAbs f`: the function `log |f|` with values in `EReal`.
* `EnvelopeProperty.Berk.comap φ`: the map on analytifications induced by a `k`-algebra map.
* `EnvelopeProperty.Berk.triv`: the trivial valuation (for a domain).
* The scaling action is defined in `EnvelopeProperty.Berkovich.Topology`.
-/

open scoped NNReal ENNReal Topology

noncomputable section

namespace EnvelopeProperty

/-- The Berkovich analytification of `Spec A` over the trivially valued field `k`: the
multiplicative ultrametric seminorms on `A` (Mathlib valuations with values in `ℝ≥0`)
that are trivial on the nonzero elements of `k`. -/
@[ext]
structure Berk (k : Type*) [Field k] (A : Type*) [CommRing A] [Algebra k A] where
  /-- The multiplicative seminorm `f ↦ |f|_x` attached to the point. -/
  val : Valuation A ℝ≥0
  /-- The seminorm restricts to the trivial absolute value on `k`. -/
  val_algebraMap : ∀ c : k, c ≠ 0 → val (algebraMap k A c) = 1

namespace Berk

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A]

/-- The value `|f|_x ∈ ℝ≥0`. -/
abbrev abs (f : A) (x : Berk k A) : ℝ≥0 := x.val f

/-- The embedding of the analytification into the space of all functions `A → ℝ≥0`. -/
def toFun (x : Berk k A) : A → ℝ≥0 := fun f => x.val f

theorem toFun_injective : Function.Injective (toFun : Berk k A → A → ℝ≥0) := by
  intro x y h
  exact Berk.ext (Valuation.ext fun f => congrFun h f)

instance : TopologicalSpace (Berk k A) :=
  TopologicalSpace.induced toFun inferInstance

theorem isInducing_toFun : Topology.IsInducing (toFun : Berk k A → A → ℝ≥0) := ⟨rfl⟩

theorem isEmbedding_toFun : Topology.IsEmbedding (toFun : Berk k A → A → ℝ≥0) :=
  ⟨isInducing_toFun, toFun_injective⟩

instance : T2Space (Berk k A) := isEmbedding_toFun.t2Space

@[fun_prop]
theorem continuous_toFun : Continuous (toFun : Berk k A → A → ℝ≥0) :=
  isInducing_toFun.continuous

@[fun_prop]
theorem continuous_abs (f : A) : Continuous (abs f : Berk k A → ℝ≥0) :=
  (continuous_apply f).comp continuous_toFun

/-- A map into the analytification is continuous iff all the evaluation maps are. -/
theorem continuous_iff {X : Type*} [TopologicalSpace X] {g : X → Berk k A} :
    Continuous g ↔ ∀ f : A, Continuous fun y => (g y).val f := by
  rw [isInducing_toFun.continuous_iff, continuous_pi_iff]
  rfl

theorem abs_algebraMap (x : Berk k A) {c : k} (hc : c ≠ 0) :
    x.val (algebraMap k A c) = 1 :=
  x.val_algebraMap c hc

theorem abs_algebraMap_le_one (x : Berk k A) (c : k) : x.val (algebraMap k A c) ≤ 1 := by
  by_cases hc : c = 0
  · simp [hc]
  · exact (x.val_algebraMap c hc).le

/-! ### The functions `log |f|` -/

/-- The function `log |f| : (Spec A)^an → [-∞, ∞)`, with values in `EReal`. -/
def logAbs (f : A) (x : Berk k A) : EReal := ENNReal.log (x.val f : ℝ≥0∞)

@[simp]
theorem logAbs_def (f : A) (x : Berk k A) : logAbs f x = ENNReal.log (x.val f : ℝ≥0∞) := rfl

@[fun_prop]
theorem continuous_logAbs (f : A) : Continuous (logAbs f : Berk k A → EReal) :=
  ENNReal.continuous_log.comp (ENNReal.continuous_coe.comp (continuous_abs f))

theorem logAbs_mul (f g : A) (x : Berk k A) :
    logAbs (f * g) x = logAbs f x + logAbs g x := by
  simp [logAbs, ENNReal.coe_mul, ENNReal.log_mul_add]

theorem logAbs_pow (f : A) (n : ℕ) (x : Berk k A) :
    logAbs (f ^ n) x = n * logAbs f x := by
  simp [logAbs, ENNReal.coe_pow, ENNReal.log_pow]

@[simp]
theorem logAbs_one (x : Berk k A) : logAbs (1 : A) x = 0 := by
  simp [logAbs]

@[simp]
theorem logAbs_zero (x : Berk k A) : logAbs (0 : A) x = ⊥ := by
  simp [logAbs]

theorem logAbs_algebraMap (x : Berk k A) {c : k} (hc : c ≠ 0) :
    logAbs (algebraMap k A c) x = 0 := by
  simp [logAbs, x.val_algebraMap c hc]

theorem logAbs_ne_top (f : A) (x : Berk k A) : logAbs f x ≠ ⊤ := by
  simp [logAbs, ENNReal.log_eq_top_iff]

theorem logAbs_lt_top (f : A) (x : Berk k A) : logAbs f x < ⊤ :=
  lt_top_iff_ne_top.2 (logAbs_ne_top f x)

theorem logAbs_eq_bot_iff (f : A) (x : Berk k A) : logAbs f x = ⊥ ↔ x.val f = 0 := by
  simp [logAbs, ENNReal.log_eq_bot_iff]

theorem logAbs_add_le (f g : A) (x : Berk k A) :
    logAbs (f + g) x ≤ max (logAbs f x) (logAbs g x) := by
  simp only [logAbs]
  rw [← ENNReal.log_monotone.map_max]
  apply ENNReal.log_monotone
  rw [← ENNReal.coe_max]
  exact ENNReal.coe_le_coe.2 (x.val.map_add f g)

theorem logAbs_le_logAbs_iff (f g : A) (x : Berk k A) :
    logAbs f x ≤ logAbs g x ↔ x.val f ≤ x.val g := by
  simp [logAbs, ENNReal.log_le_log_iff]

theorem logAbs_lt_logAbs_iff (f g : A) (x : Berk k A) :
    logAbs f x < logAbs g x ↔ x.val f < x.val g := by
  simp [logAbs, ENNReal.log_lt_log_iff]

theorem logAbs_algebraMap_le_zero (x : Berk k A) (c : k) :
    logAbs (algebraMap k A c) x ≤ 0 := by
  by_cases hc : c = 0
  · simp [hc]
  · exact (logAbs_algebraMap x hc).le

/-! ### Functoriality -/

section comap

variable {B : Type*} [CommRing B] [Algebra k B]

/-- The map `(Spec B)^an → (Spec A)^an` induced by a `k`-algebra map `A → B`. -/
def comap (φ : A →ₐ[k] B) (x : Berk k B) : Berk k A where
  val := x.val.comap φ.toRingHom
  val_algebraMap c hc := by
    simp [Valuation.comap_apply, x.val_algebraMap c hc]

@[simp]
theorem comap_id (x : Berk k A) : comap (AlgHom.id k A) x = x := rfl

@[simp]
theorem comap_val_apply (φ : A →ₐ[k] B) (x : Berk k B) (f : A) :
    (comap φ x).val f = x.val (φ f) := rfl

@[fun_prop]
theorem continuous_comap (φ : A →ₐ[k] B) : Continuous (comap (k := k) φ) := by
  rw [continuous_iff]
  intro f
  exact continuous_abs (φ f)

@[simp]
theorem logAbs_comap (φ : A →ₐ[k] B) (f : A) (x : Berk k B) :
    logAbs f (comap φ x) = logAbs (φ f) x := rfl

end comap

/-! ### The trivial valuation -/

section triv

variable [IsDomain A]

open Classical in
/-- The trivial valuation `v_triv`: `|f| = 1` for `f ≠ 0` (the zero additive valuation on
the function field). Defined when `A` is a domain. -/
def triv : Berk k A where
  val := 1
  val_algebraMap c hc := by
    have : algebraMap k A c ≠ 0 :=
      (map_ne_zero_iff _ (algebraMap k A).injective).2 hc
    simp [Valuation.one_apply_of_ne_zero this]

theorem triv_val_of_ne_zero {f : A} (hf : f ≠ 0) : (triv : Berk k A).val f = 1 := by
  classical
  exact Valuation.one_apply_of_ne_zero hf

theorem logAbs_triv_of_ne_zero {f : A} (hf : f ≠ 0) : logAbs f (triv : Berk k A) = 0 := by
  simp [logAbs, triv_val_of_ne_zero hf]

end triv

end Berk

end EnvelopeProperty
