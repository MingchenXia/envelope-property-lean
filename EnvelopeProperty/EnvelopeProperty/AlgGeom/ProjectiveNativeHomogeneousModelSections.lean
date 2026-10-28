import EnvelopeProperty.AlgGeom.ProjectiveNativeModelLineMetrics
import EnvelopeProperty.Projective.NativeHomogeneousSectionValues
import EnvelopeProperty.Projective.NativeQuotientAlgebra
import EnvelopeProperty.Global.NativeRankOneChartComparison
import EnvelopeProperty.Global.Sections

/-! # Original homogeneous forms are genuine sections of the SAME fixed native model -/
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open DeJongAlterations DeJongAlterations.Geometry.ProjectiveIdeal
open DeJongAlterations.Algebra.Segre
open scoped Classical NNReal Topology
noncomputable section
universe u
namespace EnvelopeProperty.ProjectiveNativeHomogeneousModelSections
open Berkovich ProjectiveChartFunctionFieldGeneration ProjectiveFixedNativeModelCharts
attribute [local instance] MvPolynomial.gradedAlgebra homogeneousChartAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {m : ℕ} {X : Scheme.{u}} [IsIntegral X]

private def nativeCoordinateSectionsAlg (j : Fin (m + 1)) :
    let q : Proj (homogeneousSubmodule (Fin (m + 1)) k) ⟶ Spec (.of k) := projectiveSpaceStructure k m
    let := q.sectionsAlgebra (coordinateOpen (R := k) j)
    CoordinateRing k j →ₐ[k] Γ(Proj (homogeneousSubmodule (Fin (m + 1)) k),coordinateOpen (R := k) j) := by
  let q : Proj (homogeneousSubmodule (Fin (m + 1)) k) ⟶ Spec (.of k) := projectiveSpaceStructure k m
  let := q.sectionsAlgebra (coordinateOpen (R := k) j)
  refine { (ProjBerk.nativeCoordinateSectionsIso (R := k) j).hom.hom with commutes' := ?_ }
  intro a
  change (ProjBerk.nativeCoordinateSectionsIso (R := k) j).hom.hom
    (algebraMap k (ProjBerk.CoordinateRing k j) a) = _
  rw [ProjBerk.nativeCoordinateSectionsIso_coefficients]
  rfl

/-- Every original whole homogeneous coefficient has exactly its actual original
native generic germ, evaluated at the SAME original true projective ratios. -/
theorem germ_homogeneousCoefficient_eq_aeval (f : X ⟶ projectiveSpace k m)
    (j : Fin (m + 1)) [Nonempty (f ⁻¹ᵁ coordinateOpen (R := k) j)]
    (d : ℕ) (F : MvPolynomial (Fin (m + 1)) k) (hF : F.IsHomogeneous d) :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    X.germToFunctionField (f ⁻¹ᵁ coordinateOpen (R := k) j)
      (f.app (coordinateOpen (R := k) j) (ProjectiveHomogeneousSections.coefficient j d F hF)) =
      MvPolynomial.aeval (coordinate f j) F := by
  change X ⟶ Proj (homogeneousSubmodule (Fin (m + 1)) k) at f
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  let q : Proj (homogeneousSubmodule (Fin (m + 1)) k) ⟶ Spec (.of k) := projectiveSpaceStructure k m
  let := q.sectionsAlgebra (coordinateOpen (R := k) j)
  let φ := ((SchemeFunctionFieldPullbackCoefficients.genericMap f q
    (coordinateOpen (R := k) j)).comp (nativeCoordinateSectionsAlg (k := k) j)).comp (coordinateDehom j)
  have he : φ = MvPolynomial.aeval (coordinate f j) := by
    apply MvPolynomial.algHom_ext
    intro a
    change X.germToFunctionField (f ⁻¹ᵁ coordinateOpen (R := k) j)
      (f.app (coordinateOpen (R := k) j)
        ((ProjBerk.nativeCoordinateSectionsIso (R := k) j).hom (coordinateDehom j (MvPolynomial.X a)))) = _
    erw [← ProjBerk.homogeneousSection_coefficient_eq_coordinate j 1 (MvPolynomial.X a)
      (MvPolynomial.isHomogeneous_X k a), MvPolynomial.aeval_X]
    rfl
  rw [ProjBerk.homogeneousSection_coefficient_eq_coordinate j d F hF]
  change φ F = _
  rw [he]

variable (f : X ⟶ projectiveSpace k m) (i : Fin (m + 1)) [IsClosedImmersion f]
  [Nonempty (f ⁻¹ᵁ coordinateOpen (R := k) i)]

/-- Actual polynomial substitution into the SAME original fixed homogeneous algebra. -/
def homogeneousImage (F : MvPolynomial (Fin (m + 1)) k) :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    (fullFieldModel f i).S := by
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  exact MvPolynomial.aeval (fun a => (fullFieldModel f i).coordElem ⟨0,a⟩) F

/-- The original homogeneous form evaluated at the actual original native pivot ratios. -/
def homogeneousCoefficient (F : MvPolynomial (Fin (m + 1)) k) : X.functionField := by
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  exact MvPolynomial.aeval (coordinate f i) F

/-- The actual homogeneous substitution has its exact original degree and actual
native function-field coefficient, with no piece/section comparison premise. -/
theorem homogeneousImage_eq_monomial (d : ℕ) (F : MvPolynomial (Fin (m + 1)) k)
    (hF : F.IsHomogeneous d) :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    (homogeneousImage f i F : MvPolynomial (Fin 1) X.functionField) =
      monomial (Finsupp.single 0 d) (homogeneousCoefficient f i F) := by
  change X ⟶ Proj (homogeneousSubmodule (Fin (m + 1)) k) at f
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  let P := fullFieldModel f i
  let ψ : MvPolynomial (Fin (m + 1)) k →ₐ[k] MvPolynomial (Fin 1) X.functionField :=
    P.S.val.comp (MvPolynomial.aeval (fun a : Fin (m + 1) => P.coordElem ⟨0,a⟩))
  have hψ : ψ = MvPolynomial.aeval (fun a => monomial (Finsupp.single (0 : Fin 1) 1) (coordinate f i a)) := by
    apply MvPolynomial.algHom_ext
    intro a
    simp only [ψ,AlgHom.comp_apply,MvPolynomial.aeval_X]
    exact P.coe_coordElem ⟨0,a⟩
  have hhom : (ψ F).IsHomogeneous d := by
    rw [hψ]
    simpa only [one_mul] using (hF.aeval (n := 1)
      (fun a => monomial (Finsupp.single (0 : Fin 1) 1) (coordinate f i a))
      (fun a => MvPolynomial.isHomogeneous_monomial _ (by simp)))
  have hm := MultiModel.rankOne_homogeneous_eq_monomial d (ψ F) hhom
  let ev : MvPolynomial (Fin 1) X.functionField →ₐ[k] X.functionField :=
    (MvPolynomial.aeval (fun _ : Fin 1 => (1 : X.functionField))).restrictScalars k
  have hev : ev.comp ψ = MvPolynomial.aeval (coordinate f i) := by
    apply MvPolynomial.algHom_ext
    intro a
    simp only [AlgHom.comp_apply,hψ,MvPolynomial.aeval_X]
    simp only [ev,AlgHom.restrictScalars_apply,MvPolynomial.aeval_monomial,
      Algebra.algebraMap_self,RingHom.id_apply,Finsupp.prod_single_index,one_pow,mul_one]
  have hc := congrArg ev hm
  rw [show ev (ψ F) = homogeneousCoefficient f i F from AlgHom.congr_fun hev F] at hc
  simp only [ev,AlgHom.restrictScalars_apply,MvPolynomial.aeval_monomial,
    Algebra.algebraMap_self,RingHom.id_apply,Finsupp.prod_single_index,one_pow,mul_one] at hc
  exact hm.trans (congrArg (monomial (Finsupp.single 0 d)) hc.symm)

/-- EVERY original form coefficient belongs to the genuine model graded piece. -/
theorem homogeneousCoefficient_mem_piece (d : ℕ) (F : MvPolynomial (Fin (m + 1)) k)
    (hF : F.IsHomogeneous d) :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    homogeneousCoefficient f i F ∈ (fullFieldModel f i).piece (Finsupp.single 0 d) := by
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  rw [MultiModel.mem_piece,← homogeneousImage_eq_monomial f i d F hF]
  exact (homogeneousImage f i F).property

/-- EVERY entire original chart coefficient is exactly the genuine model section
fraction of the SAME original homogeneous form in the SAME original function field. -/
theorem homogeneousCoefficient_chart_fraction (j : Fin (m + 1))
    [Nonempty (f ⁻¹ᵁ coordinateOpen (R := k) j)]
    (d : ℕ) (F : MvPolynomial (Fin (m + 1)) k) (hF : F.IsHomogeneous d) :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    let := (f ≫ projectiveSpaceStructure k m).sectionsAlgebra (f ⁻¹ᵁ coordinateOpen (R := k) j)
    (nativeSectionsEquivModelChartAt f i j
      (f.app (coordinateOpen (R := k) j) (ProjectiveHomogeneousSections.coefficient j d F hF)) : X.functionField) =
      homogeneousCoefficient f i F / (fullFieldModel f i).chartDen (fun _ => j) (Finsupp.single 0 d) := by
  change X ⟶ Proj (homogeneousSubmodule (Fin (m + 1)) k) at f
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  let := (f ≫ projectiveSpaceStructure k m).sectionsAlgebra (f ⁻¹ᵁ coordinateOpen (R := k) j)
  let P := fullFieldModel f i
  rw [nativeSectionsEquivModelChartAt_apply,germ_homogeneousCoefficient_eq_aeval]
  let ψ : MvPolynomial (Fin (m + 1)) k →ₐ[k] MvPolynomial (Fin 1) X.functionField :=
    P.S.val.comp (MvPolynomial.aeval (fun a : Fin (m + 1) => P.coordElem ⟨0,a⟩))
  have he : (P.dehom (fun _ => j)).comp ψ = MvPolynomial.aeval (coordinate f j) := by
    apply MvPolynomial.algHom_ext
    intro a
    simp only [AlgHom.comp_apply,ψ,MvPolynomial.aeval_X]
    change P.dehom (fun _ => j) (P.coordElem ⟨0,a⟩ : MvPolynomial (Fin 1) X.functionField) = _
    erw [P.coe_coordElem,P.dehom_monomial,P.chartDen_single]
    exact ProjectiveChartGenericTransitions.coordinate_div f i j a
  have hv := AlgHom.congr_fun he F
  change P.dehom (fun _ => j) (homogeneousImage f i F : MvPolynomial (Fin 1) X.functionField) = _ at hv
  rw [homogeneousImage_eq_monomial f i d F hF,P.dehom_monomial] at hv
  exact hv.symm

end EnvelopeProperty.ProjectiveNativeHomogeneousModelSections
