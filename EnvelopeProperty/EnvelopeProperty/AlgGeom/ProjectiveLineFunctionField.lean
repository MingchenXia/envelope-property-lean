import DeJongAlterations.Geometry.SegreChart
import DeJongAlterations.Geometry.ProjIntegral
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.FieldTheory.RatFunc.Basic
import EnvelopeProperty.AlgGeom.SchemeFunctionFieldSubalgebras

/-! # The actual native projective line and its genuine original rational function field -/

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Polynomial
noncomputable section
namespace EnvelopeProperty.ProjectiveLineFunctionField
open DeJongAlterations DeJongAlterations.Geometry
universe u

private theorem range_appLE_isIso {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] :
    IsIso (f.appLE f.opensRange ⊤ (by intro x _; exact ⟨x, rfl⟩)) := by
  let : IsIso (f.app f.opensRange) := f.isIso_app _ le_rfl
  let h : (⊤ : X.Opens) ≤ f ⁻¹ᵁ f.opensRange := by intro x _; exact ⟨x, rfl⟩
  have he : homOfLE h = eqToHom (Scheme.Hom.preimage_opensRange f).symm :=
    Subsingleton.elim _ _
  let : IsIso (homOfLE h) := by rw [he]; infer_instance
  change IsIso (f.app f.opensRange ≫ X.presheaf.map (homOfLE h).op)
  infer_instance

private def opensRangeSectionsEquiv {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] : Γ(X, ⊤) ≃+* Γ(Y, f.opensRange) := by
  let h : (⊤ : X.Opens) ≤ f ⁻¹ᵁ f.opensRange := by intro x _; exact ⟨x, rfl⟩
  let : IsIso (f.appLE f.opensRange ⊤ h) := range_appLE_isIso f
  exact (asIso (f.appLE f.opensRange ⊤ h)).commRingCatIsoToRingEquiv.symm

private theorem opensRangeSectionsEquiv_symm_apply {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] (s : Γ(Y, f.opensRange)) :
    (opensRangeSectionsEquiv f).symm s =
      f.appLE f.opensRange ⊤ (by intro x _; exact ⟨x, rfl⟩) s := by
  rfl

private theorem opensRangeSectionsEquiv_coefficient {X Y : Scheme.{u}}
    {R : Type u} [CommRing R] (f : X ⟶ Y) [IsOpenImmersion f]
    (p : Y ⟶ Spec (.of R)) (c : R) :
    letI := p.sectionsAlgebra f.opensRange
    (opensRangeSectionsEquiv f).symm (algebraMap R Γ(Y, f.opensRange) c) =
      ((Scheme.ΓSpecIso (.of R)).inv ≫ (f ≫ p).appLE ⊤ ⊤ le_top) c := by
  let := p.sectionsAlgebra f.opensRange
  rw [opensRangeSectionsEquiv_symm_apply, Scheme.Hom.algebraMap_sectionsAlgebra]
  change ((Scheme.ΓSpecIso (.of R)).inv ≫ p.appLE ⊤ f.opensRange le_top ≫
    f.appLE f.opensRange ⊤ _) c = _
  exact congrArg (fun q : Γ(Spec (.of R), ⊤) ⟶ Γ(X, ⊤) =>
    ((Scheme.ΓSpecIso (.of R)).inv ≫ q) c)
      (Scheme.Hom.appLE_comp_appLE f p ⊤ f.opensRange ⊤ le_top _)

variable (k : Type u) [Field k]

attribute [local instance] MvPolynomial.gradedAlgebra

private def chartCoordinateEquiv : MvPolynomial (Fin 1) k ≃ₐ[k]
    ProjectiveIdeal.CoordinateRing k (0 : Fin 2) :=
  MvPolynomial.renameEquiv k (finSuccAboveEquiv (0 : Fin 2))

/-- The SAME native projective line over the original field is genuinely integral. -/
instance projectiveLine_isIntegral : IsIntegral (projectiveSpace k 1) := by
  apply ProjIntegral.isIntegral_proj
  intro h
  have hx := HomogeneousIdeal.mem_irrelevant_of_mem (projectiveSpaceGrading k 1)
    (by decide : 0 < (1 : ℕ)) (MvPolynomial.isHomogeneous_X k (0 : Fin 2))
  rw [h] at hx
  exact MvPolynomial.X_ne_zero (0 : Fin 2) hx

/-- The actual original standard coordinate chart is genuinely nonempty. -/
instance chartRange_nonempty : Nonempty (Segre.coordinateChartInclusion (R := k) (0 : Fin 2)).opensRange := by
  let x := genericPoint (Spec (.of (ProjectiveIdeal.CoordinateRing k (0 : Fin 2))))
  exact ⟨⟨Segre.coordinateChartInclusion (R := k) (0 : Fin 2) x, ⟨x, rfl⟩⟩⟩

/-- The original entire standard affine-chart ring of the SAME native projective
line is the genuine original one-variable polynomial ring. -/
def chartRingEquiv :
    Γ(projectiveSpace k 1, (Segre.coordinateChartInclusion (R := k) (0 : Fin 2)).opensRange) ≃+* k[X] :=
  (opensRangeSectionsEquiv (Segre.coordinateChartInclusion (R := k) (0 : Fin 2))).symm.trans
    ((Scheme.ΓSpecIso (.of (ProjectiveIdeal.CoordinateRing k (0 : Fin 2)))).commRingCatIsoToRingEquiv.trans
      ((chartCoordinateEquiv k).symm.toRingEquiv.trans
        (MvPolynomial.uniqueAlgEquiv k (Fin 1)).toRingEquiv))

/-- The whole original chart-ring equivalence retains the ACTUAL structure-map coefficient action. -/
theorem chartRingEquiv_algebraMap (c : k) :
    letI := (projectiveSpaceStructure k 1).sectionsAlgebra
      (Segre.coordinateChartInclusion (R := k) (0 : Fin 2)).opensRange
    chartRingEquiv k (algebraMap k Γ(projectiveSpace k 1,
      (Segre.coordinateChartInclusion (R := k) (0 : Fin 2)).opensRange) c) = Polynomial.C c := by
  let f := Segre.coordinateChartInclusion (R := k) (0 : Fin 2)
  let p := projectiveSpaceStructure k 1
  let := p.sectionsAlgebra f.opensRange
  have hcoef : (Scheme.ΓSpecIso (.of (ProjectiveIdeal.CoordinateRing k (0 : Fin 2)))).hom
      ((opensRangeSectionsEquiv f).symm
        (algebraMap k Γ(projectiveSpace k 1, f.opensRange) c)) =
      algebraMap k (ProjectiveIdeal.CoordinateRing k (0 : Fin 2)) c := by
    rw [opensRangeSectionsEquiv_coefficient]
    rw [show f ≫ p = Spec.map (CommRingCat.ofHom
      (algebraMap k (ProjectiveIdeal.CoordinateRing k (0 : Fin 2)))) from
        Segre.coordinateChartInclusion_structure _]
    change ((Scheme.ΓSpecIso (.of k)).inv ≫
      (Spec.map (CommRingCat.ofHom (algebraMap k
        (ProjectiveIdeal.CoordinateRing k (0 : Fin 2))))).appTop ≫
          (Scheme.ΓSpecIso (.of (ProjectiveIdeal.CoordinateRing k (0 : Fin 2)))).hom) c = _
    rw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl
  change (MvPolynomial.uniqueAlgEquiv k (Fin 1))
    ((chartCoordinateEquiv k).symm ((Scheme.ΓSpecIso
      (.of (ProjectiveIdeal.CoordinateRing k (0 : Fin 2)))).hom
        ((opensRangeSectionsEquiv f).symm (algebraMap k Γ(projectiveSpace k 1, f.opensRange) c)))) = _
  rw [hcoef, (chartCoordinateEquiv k).symm.commutes]
  exact (MvPolynomial.uniqueAlgEquiv k (Fin 1)).commutes c

/-- The actual native projective line has its SAME genuine original rational function field. -/
def functionFieldEquiv : (projectiveSpace k 1).functionField ≃+* RatFunc k := by
  let f := Segre.coordinateChartInclusion (R := k) (0 : Fin 2)
  let U := f.opensRange
  let := projectiveLine_isIntegral k
  have hU : IsAffineOpen U := isAffineOpen_opensRange f
  have := functionField_isFractionRing_of_isAffineOpen (projectiveSpace k 1) U hU
  exact IsFractionRing.ringEquivOfRingEquiv
    (K := (projectiveSpace k 1).functionField) (L := RatFunc k) (chartRingEquiv k)

/-- EVERY actual original polynomial generic germ becomes the SAME original rational function. -/
theorem functionFieldEquiv_polynomial (p : k[X]) :
    functionFieldEquiv k ((projectiveSpace k 1).germToFunctionField
      (Segre.coordinateChartInclusion (R := k) (0 : Fin 2)).opensRange
        ((chartRingEquiv k).symm p)) = algebraMap k[X] (RatFunc k) p := by
  let U := (Segre.coordinateChartInclusion (R := k) (0 : Fin 2)).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange _
  have := functionField_isFractionRing_of_isAffineOpen (projectiveSpace k 1) U hU
  change IsFractionRing.ringEquivOfRingEquiv (K := (projectiveSpace k 1).functionField)
    (L := RatFunc k) (chartRingEquiv k)
      (algebraMap Γ(projectiveSpace k 1, U) (projectiveSpace k 1).functionField
        ((chartRingEquiv k).symm p)) = _
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap, RingEquiv.apply_symm_apply]

/-- The genuine projective-line rational function-field equivalence is over the
ACTUAL original structure-map field algebra, not a newly chosen coefficient action. -/
def functionFieldAlgEquiv :
    letI := (projectiveSpaceStructure k 1).stalkAlgebra (genericPoint (projectiveSpace k 1))
    (projectiveSpace k 1).functionField ≃ₐ[k] RatFunc k := by
  let p := projectiveSpaceStructure k 1
  let U := (Segre.coordinateChartInclusion (R := k) (0 : Fin 2)).opensRange
  let := p.stalkAlgebra (genericPoint (projectiveSpace k 1))
  let := p.sectionsAlgebra U
  refine { functionFieldEquiv k with commutes' := ?_ }
  intro c
  have hc : (chartRingEquiv k).symm (Polynomial.C c) = algebraMap k Γ(projectiveSpace k 1, U) c :=
    (chartRingEquiv k).symm_apply_eq.mpr (chartRingEquiv_algebraMap k c).symm
  rw [← (p.sectionsFunctionFieldAlgHom U).commutes c]
  change functionFieldEquiv k ((projectiveSpace k 1).germToFunctionField U
    (algebraMap k Γ(projectiveSpace k 1, U) c)) = _
  rw [← hc, functionFieldEquiv_polynomial]
  exact (IsScalarTower.algebraMap_apply k k[X] (RatFunc k) c).symm

end EnvelopeProperty.ProjectiveLineFunctionField
