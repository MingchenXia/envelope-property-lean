import EnvelopeProperty.Vanishing.NadelBlowupCanonicalGluingChart

/-! # The actual whole native coordinate blowup canonical sheaf comparison -/

open AlgebraicGeometry CategoryTheory Opposite MvPolynomial
open Scheme.Modules

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.NadelBlowupCanonicalGluingWhole
open CoordinateSubspace CanonicalGeometry
open NadelBlowupCanonicalGluingChart NadelBlowupCanonicalGluingDescent

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual original model charts cover EVERY original blowup point,
with genuine original preimage points. -/
theorem modelChart_point_cover (A : Type u) [CommRing A] (n r : ℕ)
    (x : modelBlowUp A n r) :
    ∃ (i : {j : Fin n // j.val < r})
      (y : Spec (.of (MvPolynomial (Fin n) A))), modelChart A n r i.1 i.2 y = x := by
  have hx : x ∈ ⨆ (j : Fin n) (hj : j.val < r), (modelChart A n r j hj).opensRange := by
    rw [iSup_opensRange_modelChart]
    trivial
  obtain ⟨j, hjx⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  obtain ⟨hj, hy⟩ := TopologicalSpace.Opens.mem_iSup.mp hjx
  exact ⟨⟨j, hj⟩, hy⟩

/-- The SAME WHOLE native blowup along the actual coordinate centre of
positive codimension has its actual native canonical Cartier comparison.
Its ENTIRE original inclusion composite is the original native canonical
differential. Every chart factor, image, overlap and cover is produced
internally from the original field and m+1 <= n. -/
theorem exists_coordinate_blowup_canonical_ideal_iso (k : Type u) [Field k]
    (n m : ℕ) (hrn : m + 1 ≤ n) :
    let f := affineStructuralMap k (.of (MvPolynomial (Fin n) k))
    let π := affineBlowUp.π (centerIdeal k n (m + 1))
    let J := (affineBlowUp.exceptionalIdeal (centerIdeal k n (m + 1))) ^ m
    ∃ e : (pullback π).obj (canonicalLineSheaf f n) ≅
        tensorObj (canonicalLineSheaf (π ≫ f) n) J.toModules,
      e.hom ≫ SchemeTensorObjMorphisms.tensorObjIdealMap _ _ J.toModulesInclusion =
        exteriorCotangentSheafPullbackMap f π n := by
  let f := affineStructuralMap k (.of (MvPolynomial (Fin n) k))
  let π := affineBlowUp.π (centerIdeal k n (m + 1))
  let J := (affineBlowUp.exceptionalIdeal (centerIdeal k n (m + 1))) ^ m
  let N := canonicalLineSheaf (π ≫ f) n
  let : SmoothOfRelativeDimension n (π ≫ f) := smoothOfRelativeDimension_modelBlowUp k n (m + 1)
  let inc := SchemeTensorObjMorphisms.tensorObjIdealMap N J.toModules J.toModulesInclusion
  let : Mono inc := tensorIdealMap_mono N (canonicalLineSheaf_isInvertible (π ≫ f) n) J
  exact exists_iso_of_local_factors
    (fun _ : {j : Fin n // j.val < m + 1} => Spec (.of (MvPolynomial (Fin n) k)))
    (fun i => modelChart k n (m + 1) i.1 i.2) (modelChart_point_cover k n (m + 1))
    inc (exteriorCotangentSheafPullbackMap f π n)
    (fun i => exists_modelChart_factor_iso k n (m + 1) i.1 i.2 hrn)

open CategoryTheory.MonoidalCategory in
private def cancelActualIdeal {X : Scheme.{u}} (A B J : X.Modules)
    (hJ : IsInvertible J) (e : A ≅ Scheme.Modules.tensorObj B J) :
    B ≅ Scheme.Modules.tensorObj A (dualObj J) := by
  letI := Scheme.Modules.monoidalCategory X
  let D := dualObj J
  let e0 : A ≅ B ⊗ J := e ≪≫ (ModularCurves.monoidalTensorObjIso B J).symm
  exact (ρ_ B).symm ≪≫ whiskerLeftIso B hJ.monoidalEvaluationIso.symm ≪≫
    (α_ B J D).symm ≪≫ (e0.symm ⊗ᵢ Iso.refl D) ≪≫
      ModularCurves.monoidalTensorObjIso A D

/-- On the SAME whole original coordinate blowup, the actual target
canonical line is the actual pulled source canonical line times the
actual dual of the same exceptional-power ideal, namely O(mE). -/
def coordinateBlowupCanonicalDivisorIso (k : Type u) [Field k]
    (n m : ℕ) (hrn : m + 1 ≤ n) :
    let f := affineStructuralMap k (.of (MvPolynomial (Fin n) k))
    let π := affineBlowUp.π (centerIdeal k n (m + 1))
    let J := (affineBlowUp.exceptionalIdeal (centerIdeal k n (m + 1))) ^ m
    canonicalLineSheaf (π ≫ f) n ≅
      tensorObj ((pullback π).obj (canonicalLineSheaf f n)) (dualObj J.toModules) := by
  let J := (affineBlowUp.exceptionalIdeal (centerIdeal k n (m + 1))) ^ m
  have hJ : IsInvertible J.toModules :=
    (Scheme.IdealSheafData.isInvertible_pow
      (affineBlowUp.isInvertible_exceptionalIdeal (centerIdeal k n (m + 1))) m).isInvertibleModule_toModules
  exact cancelActualIdeal _ _ J.toModules hJ
    (Classical.choose (exists_coordinate_blowup_canonical_ideal_iso k n m hrn))

end EnvelopeProperty.Vanishing.NadelBlowupCanonicalGluingWhole
