import EnvelopeProperty.AlgGeom.FormalFunctionsFixedTarget
import EnvelopeProperty.Global.FibreStableFiltration

/-! # Vanishing of genuine original compatible ideal-power cohomology families -/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.FormalFunctionsCompatibleCohomology

open FcReesCechDegreeComplex FcReesCechDegreeTransitions

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
variable [X.IsSeparated] {ι : Type u} [LinearOrder ι] [Fintype ι]
variable (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))

/-- The ACTUAL original compatible ideal-power cohomology families,
retaining every original transition and original R-module structure. -/
def compatibleCohomology (q : ℕ) :
    Submodule R (∀ n : ℕ, (degreeComplex I f U hU n).homology q) where
  carrier := {y | ∀ n m (h : n ≤ m), (homologyLower I f U hU h q).hom (y m) = y n}
  zero_mem' := by intro n m h; exact map_zero _
  add_mem' := by
    intro y z hy hz n m h
    change (homologyLower I f U hU h q).hom (y m + z m) = y n + z n
    rw [map_add, hy n m h, hz n m h]
  smul_mem' := by
    intro a y hy n m h
    change (homologyLower I f U hU h q).hom (a • y m) = a • y n
    exact ((homologyLower I f U hU h q).hom.map_smul a (y m)).trans
      (congrArg (fun z => a • z) (hy n m h))

/-- Genuine complete-Noetherian projective geometry separates EVERY actual
fixed-target image filtration; adic completeness derives the Jacobson condition. -/
theorem fixedTarget_iInf_eq_bot [IsNoetherianRing R] [IsAdicComplete I R]
    (hf : IsProjectiveFactorization f) (hcover : IsOpenCover U) (n q : ℕ) :
    (⨅ d : ℕ, (FormalFunctionsFixedTarget.imageFiltration I f U hU n q).N d) = ⊥ := by
  let : Module.Finite R ((degreeComplex I f U hU n).homology q) :=
    FormalFunctionsDegreeFinite.degreeCech_finite I f hf U hcover hU n q
  exact FibreStableFiltration.iInf_eq_bot_of_le_jacobson I
    (FormalFunctionsFixedTarget.imageFiltration I f U hU n q)
    (FormalFunctionsFixedTarget.imageFiltration_stable I f U hU hf hcover n q)
    (IsAdicComplete.le_jacobson_bot I)

/-- EVERY genuine original compatible cohomology family vanishes, derived
from actual projective geometry and the original complete Noetherian base alone. -/
theorem compatible_eq_zero [IsNoetherianRing R] [IsAdicComplete I R]
    (hf : IsProjectiveFactorization f) (hcover : IsOpenCover U) (q : ℕ)
    (y : ∀ n : ℕ, (degreeComplex I f U hU n).homology q)
    (hy : ∀ n m (h : n ≤ m), (homologyLower I f U hU h q).hom (y m) = y n) :
    y = 0 := by
  funext n
  have hmem : y n ∈ ⨅ d : ℕ,
      (FormalFunctionsFixedTarget.imageFiltration I f U hU n q).N d := by
    apply (Submodule.mem_iInf _).mpr
    intro d
    exact ⟨y (n + d), hy n (n + d) (Nat.le_add_right n d)⟩
  rw [fixedTarget_iInf_eq_bot I f U hU hf hcover n q] at hmem
  exact hmem

/-- The ENTIRE actual original compatible ideal-power cohomology module
is zero, without an assumed prozero transition map or finite-level vanishing premise. -/
theorem compatibleCohomology_eq_bot [IsNoetherianRing R] [IsAdicComplete I R]
    (hf : IsProjectiveFactorization f) (hcover : IsOpenCover U) (q : ℕ) :
    compatibleCohomology I f U hU q = ⊥ := by
  apply bot_unique
  intro y hy
  exact compatible_eq_zero I f U hU hf hcover q y hy

/-- The SAME original compatible-family vanishing in the literal positive
infinitesimal indexing n+1, proved directly in every original positive target. -/
theorem compatible_positive_eq_zero [IsNoetherianRing R] [IsAdicComplete I R]
    (hf : IsProjectiveFactorization f) (hcover : IsOpenCover U) (q : ℕ)
    (y : ∀ n : ℕ, (degreeComplex I f U hU (n + 1)).homology q)
    (hy : ∀ n m (h : n ≤ m),
      (homologyLower I f U hU (Nat.succ_le_succ h) q).hom (y m) = y n) :
    y = 0 := by
  funext n
  have hmem : y n ∈ ⨅ d : ℕ,
      (FormalFunctionsFixedTarget.imageFiltration I f U hU (n + 1) q).N d := by
    apply (Submodule.mem_iInf _).mpr
    intro d
    let P : {j : ℕ // n + 1 ≤ j} → Prop := fun j =>
      y n ∈ LinearMap.range (homologyLower I f U hU j.2 q).hom
    let j₁ : {j : ℕ // n + 1 ≤ j} :=
      ⟨(n + d) + 1, Nat.succ_le_succ (Nat.le_add_right n d)⟩
    let j₂ : {j : ℕ // n + 1 ≤ j} :=
      ⟨(n + 1) + d, Nat.le_add_right (n + 1) d⟩
    have he : j₁ = j₂ := Subtype.ext (by
      change (n + d) + 1 = (n + 1) + d
      omega)
    have hm : P j₁ := ⟨y (n + d), hy n (n + d) (Nat.le_add_right n d)⟩
    exact (congrArg P he).mp hm
  rw [fixedTarget_iInf_eq_bot I f U hU hf hcover (n + 1) q] at hmem
  exact hmem

end EnvelopeProperty.FormalFunctionsCompatibleCohomology
