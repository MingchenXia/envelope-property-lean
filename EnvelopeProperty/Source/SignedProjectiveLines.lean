import EnvelopeProperty.AlgGeom.FiniteOriginalProjectivePowerFrames
import EnvelopeProperty.AlgGeom.ProjectiveTwistTensorAddition
import EnvelopeProperty.AlgGeom.ProjectiveTwistCoordinateComparison
import EnvelopeProperty.AlgGeom.BundleTensorPowerTensor
import EnvelopeProperty.AlgGeom.NativeNumericalLineFamilyMaps
import EnvelopeProperty.AlgGeom.NativeNumericalGeneratedLineSums

/-! # Signed-degree lines of a projective presentation and their numerical classes

Let `X` be a scheme with finitely many morphisms `q c: X → ℙ^{d_c}`, `c ∈ Fin (r+1)` (a
*presentation* of `X`, FHX §2 and the blueprint chapter `source-presentation-models`).
For a multidegree `n ∈ ℤ^{r+1}` and a choice of coordinate hyperplanes `t c`, the line

  `L(n) = ⨂_c q_c^* 𝒪(n_c)`

is `signedProjectiveLine d q t n`. Here `𝒪(n_c)` is the integer twist
`coordinateHyperplaneTwist (t c) (n c)` of AINTLIB (`𝒪(1)` built from the hyperplane
`X_{t c} = 0`, `𝒪(-1)` its ideal sheaf). For `n ≥ 0` it is literally the line
`FiniteOriginalProjectivePowerFrames.projectiveLine` (`signedProjectiveLine_natCast`).

Main results (`lem:pm-line-class`):
* `lineClass_signedProjectiveLine`: the numerical class of `L(n)` is
  `∑_c n_c [q_c^* 𝒪(1)]`, i.e. `lineFamilyMap p (presentationFactorLine q) _ n`. The proof uses
  that `[A ⊗ B] = [A] + [B]`, that the twists add under tensor product
  (`ProjectiveTwistTensorAddition.tensorIso`), and that they do not depend on the hyperplane
  (`ProjectiveTwistCoordinateComparison.coordinateIso`).
* `signedProjectiveLinePowerIso`: `L(m • n) ≅ L(n)^{⊗ m}`.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory MvPolynomial
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.Variety
open FiniteOriginalProjectivePowerFrames CanonicalGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra
noncomputable local instance signedLinesMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X
noncomputable local instance signedLinesSymmetric (X : Scheme.{u}) : SymmetricCategory X.Modules :=
  Scheme.Modules.symmetricCategory X
noncomputable local instance signedLinesPullbackMonoidal {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (Scheme.Modules.pullback f).Monoidal := Scheme.Modules.pullbackMonoidal f

private theorem tensorInvertible {X : Scheme.{u}} {L M : X.Modules}
    (hL : IsInvertible L) (hM : IsInvertible M) : IsInvertible (L ⊗ M) :=
  (hL.tensorObj hM).of_iso (ModularCurves.monoidalTensorObjIso L M)

/-! ### The lines -/

section Lines

variable {k : Type u} [Field k] {X : Scheme.{u}} {r : ℕ} (d : Fin (r + 1) → ℕ)
  (q : ∀ c, X ⟶ Proj (homogeneousSubmodule (Fin (d c + 1)) k))

/-- The factor line `F_c = q_c^* 𝒪(1)` of a presentation (`def:pm-signed-line`); this is the
`factorLine` of a product embedding. -/
def presentationFactorLine (c : Fin (r + 1)) : X.Modules :=
  (pullback (q c)).obj (coordinateHyperplaneTwist (R := k) (0 : Fin (d c + 1)) 1)

theorem presentationFactorLine_isInvertible (c : Fin (r + 1)) :
    IsInvertible (presentationFactorLine d q c) :=
  (coordinateHyperplaneTwist_isInvertible (R := k) (0 : Fin (d c + 1)) 1).pullback (q c)

variable (t : ∀ c, Fin (d c + 1))

/-- The signed-degree line `L(n) = ⨂_c q_c^* 𝒪(n_c)` (`def:pm-signed-line`). -/
def signedProjectiveLine (n : Fin (r + 1) → ℤ) : X.Modules :=
  tensorLine (fun c => (pullback (q c)).obj (coordinateHyperplaneTwist (R := k) (t c) (n c)))

theorem signedProjectiveLine_isInvertible (n : Fin (r + 1) → ℤ) :
    IsInvertible (signedProjectiveLine d q t n) :=
  tensorLine_isInvertible _ (fun c =>
    (coordinateHyperplaneTwist_isInvertible (R := k) (t c) (n c)).pullback (q c))

/-- In nonnegative degrees the signed line is literally the tensor line. -/
theorem signedProjectiveLine_natCast (n : Fin (r + 1) → ℕ) :
    signedProjectiveLine d q t (fun c => (n c : ℤ)) = projectiveLine d q t n := rfl

end Lines

/-! ### Isomorphisms of tensor lines -/

/-- Factorwise isomorphisms give an isomorphism of tensor lines. -/
def tensorLineIso {X : Scheme.{u}} : {r : ℕ} → {M N : Fin (r + 1) → X.Modules} →
    (∀ c, M c ≅ N c) → (tensorLine M ≅ tensorLine N)
  | 0, _, _, e => e 0
  | _ + 1, _, _, e => e 0 ⊗ᵢ tensorLineIso (fun c => e c.succ)

/-- The tensor line of tensor powers is the tensor power of the tensor line. -/
def tensorLinePowerIso {X : Scheme.{u}} (m : ℕ) : {r : ℕ} → (M : Fin (r + 1) → X.Modules) →
    (tensorLine (fun c => bundleTensorPower (M c) m) ≅ bundleTensorPower (tensorLine M) m)
  | 0, _ => Iso.refl _
  | _ + 1, M =>
      (Iso.refl (bundleTensorPower (M 0) m) ⊗ᵢ tensorLinePowerIso m (fun c => M c.succ)) ≪≫
        (BundleTensorPowerTensor.powerTensorIso (M 0) (tensorLine (fun c => M c.succ)) m).symm

/-! ### Numerical classes -/

section Classes

variable {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProjective p]

open NativeRealNumericalClasses

/-- The class of a tensor line is the sum of the classes of its factors. -/
theorem lineClass_tensorLine : {r : ℕ} → (M : Fin (r + 1) → X.Modules) →
    (hM : ∀ c, IsInvertible (M c)) →
    lineClass p (tensorLine M) (tensorLine_isInvertible M hM) = ∑ c, lineClass p (M c) (hM c)
  | 0, M, hM => by
      rw [Fin.sum_univ_one]
      rfl
  | r + 1, M, hM => by
      rw [Fin.sum_univ_succ]
      have h := lineClass_tensor p (M 0) (tensorLine (fun c : Fin (r + 1) => M c.succ)) (hM 0)
        (tensorLine_isInvertible _ (fun c : Fin (r + 1) => hM c.succ))
      have ih := lineClass_tensorLine (fun c : Fin (r + 1) => M c.succ) (fun c => hM c.succ)
      exact h.trans (congrArg (fun z => lineClass p (M 0) (hM 0) + z) ih)

variable {m : ℕ} (f : X ⟶ Proj (homogeneousSubmodule (Fin (m + 1)) k))

/-- The class of `f^* 𝒪(a)` for the twist along the coordinate hyperplane `j`. -/
private def twistClass (j : Fin (m + 1)) (a : ℤ) : Space p :=
  lineClass p ((pullback f).obj (coordinateHyperplaneTwist (R := k) j a))
    ((coordinateHyperplaneTwist_isInvertible (R := k) j a).pullback f)

private theorem twistClass_add (j : Fin (m + 1)) (a b : ℤ) :
    twistClass p f j (a + b) = twistClass p f j a + twistClass p f j b := by
  let A := coordinateHyperplaneTwist (R := k) j a
  let B := coordinateHyperplaneTwist (R := k) j b
  have hA := (coordinateHyperplaneTwist_isInvertible (R := k) j a).pullback f
  have hB := (coordinateHyperplaneTwist_isInvertible (R := k) j b).pullback f
  let e : (pullback f).obj (coordinateHyperplaneTwist (R := k) j (a + b)) ≅
      (pullback f).obj A ⊗ (pullback f).obj B :=
    (pullback f).mapIso (ProjectiveTwistTensorAddition.tensorIso (R := k) j j j a b).symm ≪≫
      (Functor.Monoidal.μIso (pullback f) A B).symm
  exact (lineClass_eq_of_iso p _ (tensorInvertible hA hB) e).trans
    (lineClass_tensor p _ _ hA hB)

private theorem twistClass_coordinate (j l : Fin (m + 1)) (a : ℤ) :
    twistClass p f j a = twistClass p f l a :=
  lineClass_eq_of_iso p _ _
    ((pullback f).mapIso (ProjectiveTwistCoordinateComparison.coordinateIso (R := k) j l a))

private theorem twistClass_eq_zsmul (j : Fin (m + 1)) (a : ℤ) :
    twistClass p f j a = a • twistClass p f 0 1 := by
  let φ : ℤ →+ Space p := AddMonoidHom.mk' (twistClass p f j) (twistClass_add p f j)
  exact (AddMonoidHom.apply_int _ φ a).trans
    (congrArg (fun z => a • z) (twistClass_coordinate p f j 0 1))

variable {r : ℕ} {d : Fin (r + 1) → ℕ} (q : ∀ c, X ⟶ Proj (homogeneousSubmodule (Fin (d c + 1)) k))
  (t : ∀ c, Fin (d c + 1))

/-- **The class of a signed line** (`lem:pm-line-class`):
`[⨂_c q_c^* 𝒪(n_c)] = ∑_c n_c [q_c^* 𝒪(1)]` in `N¹(X)_ℝ`. -/
theorem lineClass_signedProjectiveLine (n : Fin (r + 1) → ℤ) :
    lineClass p (signedProjectiveLine d q t n) (signedProjectiveLine_isInvertible d q t n) =
      lineFamilyMap p (presentationFactorLine d q) (presentationFactorLine_isInvertible d q)
        (fun c => (n c : ℝ)) := by
  rw [lineFamilyMap_apply]
  refine (lineClass_tensorLine p _ (fun c =>
    (coordinateHyperplaneTwist_isInvertible (R := k) (t c) (n c)).pullback (q c))).trans ?_
  apply Finset.sum_congr rfl
  intro c _
  rw [Int.cast_smul_eq_zsmul ℝ (n c)]
  exact twistClass_eq_zsmul p (q c) (t c) (n c)

end Classes

/-! ### Powers -/

section Powers

variable {k : Type u} [Field k] {m : ℕ}

/-- `𝒪(e a) ≅ 𝒪(a)^{⊗ e}` on projective space, from tensor addition of twists. -/
def twistPowerIso (j : Fin (m + 1)) (a : ℤ) : (e : ℕ) →
    (coordinateHyperplaneTwist (R := k) j ((e : ℤ) * a) ≅
      bundleTensorPower (coordinateHyperplaneTwist (R := k) j a) e)
  | 0 => eqToIso (congrArg (coordinateHyperplaneTwist (R := k) j)
        (show ((0 : ℕ) : ℤ) * a = 0 by simp)) ≪≫
      ModularCurves.monoidalUnitObjIso (Proj (homogeneousSubmodule (Fin (m + 1)) k))
  | e + 1 =>
      eqToIso (congrArg (coordinateHyperplaneTwist (R := k) j)
          (show ((e + 1 : ℕ) : ℤ) * a = (e : ℤ) * a + a by push_cast; ring)) ≪≫
        (ProjectiveTwistTensorAddition.tensorIso (R := k) j j j ((e : ℤ) * a) a).symm ≪≫
        (twistPowerIso j a e ⊗ᵢ Iso.refl _) ≪≫
        ModularCurves.monoidalTensorObjIso
          (bundleTensorPower (coordinateHyperplaneTwist (R := k) j a) e)
          (coordinateHyperplaneTwist (R := k) j a)

variable {X : Scheme.{u}} {r : ℕ} (d : Fin (r + 1) → ℕ)
  (q : ∀ c, X ⟶ Proj (homogeneousSubmodule (Fin (d c + 1)) k)) (t : ∀ c, Fin (d c + 1))

/-- **Powers of signed lines** (`lem:pm-line-class`): `L(e • n) ≅ L(n)^{⊗ e}`. -/
def signedProjectiveLinePowerIso (n : Fin (r + 1) → ℤ) (e : ℕ) :
    signedProjectiveLine d q t (e • n) ≅ bundleTensorPower (signedProjectiveLine d q t n) e :=
  tensorLineIso (fun c =>
      (pullback (q c)).mapIso
          (eqToIso (congrArg (coordinateHyperplaneTwist (R := k) (t c))
            (show (e • n) c = (e : ℤ) * n c by simp)) ≪≫
            twistPowerIso (t c) (n c) e) ≪≫
        BundleTensorPowerPullback.pullbackIso (q c) _ e) ≪≫
    tensorLinePowerIso e _

end Powers

end EnvelopeProperty.Variety
