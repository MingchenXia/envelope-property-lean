import EnvelopeProperty.AlgGeom.ReesCechDegreeHomology
import EnvelopeProperty.AlgGeom.FormalFunctionsReesMultiplication

/-! # Original homogeneous multiplication on genuine ideal-power Cech cohomology -/

open CategoryTheory Limits AlgebraicGeometry
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.FcReesCechHomogeneousMultiplication

open FcReesCechDegreeComplex FcReesFormalRestriction

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

/-- Literal original homogeneous multiplication on an actual affine intersection. -/
def chartMultiply {V : X.Opens} (hV : IsAffineOpen V) {e : ℕ}
    (a : ↥(I ^ e)) (d : ℕ) :
    letI := chartAlgebra f hV
    ↥((I.map (chartCoefficient f hV)) ^ d) →ₗ[R]
      ↥((I.map (chartCoefficient f hV)) ^ (e + d)) := by
  letI := chartAlgebra f hV
  exact FormalFunctionsReesMultiplication.powerMultiply I a d

/-- The entire original ideal-power restriction square preserves the actual
homogeneous coefficient coming from the same original base element. -/
theorem chartMultiply_naturality {V W : X.Opens} (hVW : V ≤ W)
    (hV : IsAffineOpen V) (hW : IsAffineOpen W) {e : ℕ} (a : ↥(I ^ e)) (d : ℕ) :
    letI := chartAlgebra f hV
    letI := chartAlgebra f hW
    (FcReesPowerDecomposition.chartPowerRestriction I f hVW hV hW (e + d)).comp
        (chartMultiply I f hW a d) =
      (chartMultiply I f hV a d).comp
        (FcReesPowerDecomposition.chartPowerRestriction I f hVW hV hW d) := by
  let := chartAlgebra f hV
  let := chartAlgebra f hW
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  let ρ := (X.presheaf.map (homOfLE hVW).op).hom
  change ρ (chartCoefficient f hW a * (x : Γ(X, W))) =
    chartCoefficient f hV a * ρ (x : Γ(X, W))
  rw [map_mul]
  exact congrArg (fun b => b * ρ (x : Γ(X, W)))
    (DFunLike.congr_fun (FcReesFormalChartSheaf.chartCoefficient_naturality f hVW hV hW) (a : R))

section Cech

variable [X.IsSeparated] {ι : Type u} [LinearOrder ι] [Fintype ι]
variable (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))

/-- Multiply at EVERY actual original ordered affine intersection by the same
original homogeneous coefficient, in its original ideal-power degree. -/
def termMultiply {e : ℕ} (a : ↥(I ^ e)) (d n : ℕ) :
    degreeTerm I f U hU d n ⟶ degreeTerm I f U hU (e + d) n := by
  letI : ∀ i : OrderedCechIndex ι n,
      Algebra R Γ(X, ∏ᶜ fun j : Fin (n + 1) => U (i.1 j)) :=
    fun i => chartAlgebra f (IsAffineOpen.cechIntersection U hU n i.1)
  exact ModuleCat.ofHom {
    toFun := fun x i =>
      chartMultiply I f (IsAffineOpen.cechIntersection U hU n i.1) a d (x i)
    map_add' := by
      intro x y
      funext i
      exact (chartMultiply I f (IsAffineOpen.cechIntersection U hU n i.1) a d).map_add _ _
    map_smul' := by
      intro r x
      funext i
      exact (chartMultiply I f (IsAffineOpen.cechIntersection U hU n i.1) a d).map_smul r _ }

omit [Fintype ι] in
/-- Every WHOLE actual ordered coface commutes with original homogeneous
multiplication, retaining the original restriction and original coefficient. -/
theorem termMultiply_coface {e : ℕ} (a : ↥(I ^ e)) (d n : ℕ) (k : Fin (n + 2)) :
    termMultiply I f U hU a d n ≫ degreeCoface I f U hU (e + d) n k =
      degreeCoface I f U hU d n k ≫ termMultiply I f U hU a d (n + 1) := by
  let : ∀ i : OrderedCechIndex ι n,
      Algebra R Γ(X, ∏ᶜ fun j : Fin (n + 1) => U (i.1 j)) :=
    fun i => chartAlgebra f (IsAffineOpen.cechIntersection U hU n i.1)
  let : ∀ i : OrderedCechIndex ι (n + 1),
      Algebra R Γ(X, ∏ᶜ fun j : Fin (n + 2) => U (i.1 j)) :=
    fun i => chartAlgebra f (IsAffineOpen.cechIntersection U hU (n + 1) i.1)
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext i
  exact DFunLike.congr_fun
    (chartMultiply_naturality I f
      (leOfHom ((orderedCechFace U n k).φ i))
      (IsAffineOpen.cechIntersection U hU (n + 1) i.1)
      (IsAffineOpen.cechIntersection U hU n (i.delete k).1) a d) (x (i.delete k))

omit [Fintype ι] in
/-- The WHOLE original ideal-power alternating differential commutes with
literal original homogeneous multiplication. -/
theorem termMultiply_differential {e : ℕ} (a : ↥(I ^ e)) (d n : ℕ) :
    termMultiply I f U hU a d n ≫ degreeDifferential I f U hU (e + d) n =
      degreeDifferential I f U hU d n ≫ termMultiply I f U hU a d (n + 1) := by
  simp only [degreeDifferential, Preadditive.comp_sum, Preadditive.sum_comp,
    Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  apply Finset.sum_congr rfl
  intro k _
  exact congrArg (fun b => ((-1 : ℤ) ^ (k : ℕ)) • b)
    (termMultiply_coface I f U hU a d n k)

/-- Original homogeneous multiplication is an actual cochain map between
the genuine original ideal-power degree complexes. -/
def degreeMultiply {e : ℕ} (a : ↥(I ^ e)) (d : ℕ) :
    degreeComplex I f U hU d ⟶ degreeComplex I f U hU (e + d) where
  f n := termMultiply I f U hU a d n
  comm' n m hnm := by
    have hm : n + 1 = m := hnm
    subst m
    simp only [degreeComplex, CochainComplex.of_d]
    exact termMultiply_differential I f U hU a d n

/-- The resulting genuine original ideal-power cohomology multiplication,
constructed from the actual original cochain map. -/
def homologyMultiply {e : ℕ} (a : ↥(I ^ e)) (d n : ℕ) :
    (degreeComplex I f U hU d).homology n ⟶
      (degreeComplex I f U hU (e + d)).homology n :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) n).map
    (degreeMultiply I f U hU a d)

end Cech

end EnvelopeProperty.FcReesCechHomogeneousMultiplication
