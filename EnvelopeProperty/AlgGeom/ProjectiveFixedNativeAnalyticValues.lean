import EnvelopeProperty.AlgGeom.ProjectiveFixedNativeAnalyticCharts

/-! # Exact values of EVERY original native section under the SAME fixed analytic chart -/
open AlgebraicGeometry CategoryTheory TopologicalSpace
open Alterations
open scoped Classical NNReal Topology
noncomputable section
universe u
namespace EnvelopeProperty.ProjectiveFixedNativeAnalyticValues
open Berkovich ProjectiveChartFunctionFieldGeneration ProjectiveNativeModelChartAlgebra
open ProjectiveFixedNativeModelCharts ProjectiveFixedNativeAnalyticCharts
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem specIso_section {A B : Type u} [CommRing A] [CommRing B]
    (e : A ≃+* B) (s : A) :
    (Spec.map (CommRingCat.ofHom e.symm.toRingHom)).appTop ((Scheme.ΓSpecIso (.of B)).inv (e s)) =
      (Scheme.ΓSpecIso (.of A)).inv s := by
  have h := congrArg (fun q => q.hom (e s))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom e.symm.toRingHom))
  change (Scheme.ΓSpecIso (.of A)).inv (e.symm (e s)) =
    (Spec.map (CommRingCat.ofHom e.symm.toRingHom)).appTop
      ((Scheme.ΓSpecIso (.of B)).inv (e s)) at h
  rw [e.symm_apply_apply] at h
  exact h.symm

variable {k : Type u} [Field k] {m : ℕ} {X : Scheme.{u}} [IsIntegral X]
  (f : X ⟶ projectiveSpace k m) (i : Fin (m + 1)) [IsClosedImmersion f]
  [Nonempty (f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) i)]

/-- The whole original native affine chart scheme isomorphism pulls the section of
EVERY reconstructed coordinate-algebra element back to its exact original native section. -/
theorem nativeChartIso_section (s : Γ(X,f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) i)) :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    let := (f ≫ projectiveSpaceStructure k m).sectionsAlgebra (f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) i)
    (nativeChartIso f i).hom.appTop
      ((Scheme.ΓSpecIso (.of ((fullFieldModel f i).chartAlg (fun _ => i)))).inv
        (nativeSectionsEquivModelChart f i s)) =
      (f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) i).topIso.inv s := by
  change X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) k) at f
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  let := (f ≫ projectiveSpaceStructure k m).sectionsAlgebra (f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) i)
  let e := nativeSectionsEquivModelChart f i
  let hU := (MvPolynomial.coordinateOpen_isAffineOpen i).preimage f
  change hU.isoSpec.hom.appTop
    ((Spec.map (CommRingCat.ofHom e.symm.toRingHom)).appTop
      ((Scheme.ΓSpecIso (.of ((fullFieldModel f i).chartAlg (fun _ => i)))).inv (e s))) = _
  erw [specIso_section e.toRingEquiv s]
  rw [hU.isoSpec_hom_appTop, CommRingCat.comp_apply]
  apply congrArg (f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) i).topIso.inv
  exact congrArg (fun q => q s) (Scheme.ΓSpecIso Γ(X,f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) i)).inv_hom_id

variable (j : Fin (m + 1)) [Nonempty (f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) j)]

/-- Every actual section pullback is retained by the WHOLE chart scheme isomorphism
into ONE SAME fixed reconstructed original homogeneous model. -/
theorem nativeChartIsoAt_section (s : Γ(X,f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) j)) :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    let := (f ≫ projectiveSpaceStructure k m).sectionsAlgebra (f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) j)
    (nativeChartIsoAt f i j).hom.appTop
      ((Scheme.ΓSpecIso (.of ((fullFieldModel f i).chartAlg (fun _ => j)))).inv
        (nativeSectionsEquivModelChartAt f i j s)) =
      (f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) j).topIso.inv s := by
  change X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) k) at f
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  let := (f ≫ projectiveSpaceStructure k m).sectionsAlgebra (f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) j)
  let E := Subalgebra.equivOfEq ((fullFieldModel f j).chartAlg (fun _ => j))
    ((fullFieldModel f i).chartAlg (fun _ => j))
    ((modelChartAlg_eq_adjoin_coordinates f j).trans (modelChartAlgAt_eq_adjoin_coordinates f i j).symm)
  change (nativeChartIso f j).hom.appTop
    ((Spec.map (CommRingCat.ofHom E.symm.toRingHom)).appTop
      ((Scheme.ΓSpecIso (.of ((fullFieldModel f i).chartAlg (fun _ => j)))).inv
        (E (nativeSectionsEquivModelChart f j s)))) = _
  erw [specIso_section E.toRingEquiv]
  exact nativeChartIso_section f j s

/-- EVERY whole actual original native section has its SAME value under the complete
fixed-model native affine analytic chart homeomorphism, without a value-matching premise. -/
theorem nativeAffineChartHomeomorph_val
    (y : {y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) (f ≫ projectiveSpaceStructure k m) //
      y.1.point ∈ f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) j})
    (s : Γ(X,f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) j)) :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    let := (f ≫ projectiveSpaceStructure k m).sectionsAlgebra (f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) j)
    (nativeAffineChartHomeomorph f i j y).val (nativeSectionsEquivModelChartAt f i j s) =
      SchemeValuedPoint.eval y.1.1 (f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) j) y.2 s := by
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  let := (f ≫ projectiveSpaceStructure k m).sectionsAlgebra (f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) j)
  let U := f ⁻¹ᵁ MvPolynomial.coordinateOpen (R := k) j
  let R := RelativeSchemeValuedPoint.restrictionHomeomorph (v := (1 : _root_.Valuation k ℝ≥0))
    U (f ≫ projectiveSpaceStructure k m)
  obtain ⟨z,rfl⟩ := R.surjective y
  change (SchemeValuedPoint.spectrumHomeomorph
    (SchemeValuedPoint.map (nativeChartIsoAt f i j).hom (R.symm (R z)).1)).val
      (nativeSectionsEquivModelChartAt f i j s) = _
  rw [Homeomorph.symm_apply_apply, SchemeValuedPoint.spectrumHomeomorph_val_apply,
    SchemeValuedPoint.evalTop_map, nativeChartIsoAt_section]
  exact (SchemeValuedPoint.eval_map_ι_topIso U z.1 s).symm

end EnvelopeProperty.ProjectiveFixedNativeAnalyticValues
