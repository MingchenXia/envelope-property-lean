import EnvelopeProperty.AlgGeom.SchemeAffineCoefficientEquivalences
import EnvelopeProperty.AlgGeom.GenericCoefficientMultiModel
import EnvelopeProperty.AlgGeom.ProjectiveChartSectionRatios
import EnvelopeProperty.AlgGeom.ProjectiveFactorizationRingIso
import EnvelopeProperty.AlgGeom.ProjectiveBlowupSequence

/-! # Actual original projective ratios generate the ENTIRE same native function field -/

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization TopologicalSpace
open DeJongAlterations DeJongAlterations.Geometry.ProjectiveIdeal
open DeJongAlterations.Geometry.Segre DeJongAlterations.Algebra.Segre
noncomputable section
universe u
namespace EnvelopeProperty.ProjectiveChartFunctionFieldGeneration
attribute [local instance] MvPolynomial.gradedAlgebra homogeneousChartAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {m : ℕ}

/-- The whole original polynomial chart retains its literal original coefficient projection. -/
theorem chart_structure (i : Fin (m + 1)) :
    (coordinateOpen (R := k) i).ι ≫ projectiveSpaceStructure k m =
      (coordinateChartIso (R := k) i).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (CoordinateRing k i))) := by
  apply (cancel_epi (coordinateChartIso (R := k) i).inv).mp
  rw [Iso.inv_hom_id_assoc]
  exact coordinateChartInclusion_structure i

private theorem exists_isoSections {Y : Scheme.{u}} (A : Type u) [CommRing A] [Algebra k A]
    (p : Y ⟶ Spec (.of k)) (e : Y ≅ Spec (.of A))
    (hp : p = e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k A))) :
    letI := p.sectionsAlgebra ⊤
    ∃ E : A ≃ₐ[k] Γ(Y, ⊤), ∀ a,
      E a = e.hom.appTop.hom ((Scheme.ΓSpecIso (.of A)).inv.hom a) := by
  subst p
  exact ⟨SchemeAffineCoefficientEquivalences.isoSections A e, fun _ => rfl⟩

private def chartNativeIso (i : Fin (m + 1)) :
    letI := ((coordinateOpen (R := k) i).ι ≫ projectiveSpaceStructure k m).sectionsAlgebra ⊤
    CoordinateRing k i ≃ₐ[k] Γ((coordinateOpen (R := k) i).toScheme, ⊤) :=
  (exists_isoSections (CoordinateRing k i) _ (coordinateChartIso i) (chart_structure i)).choose

private theorem chartNativeIso_apply (i : Fin (m + 1)) (a : CoordinateRing k i) :
    letI := ((coordinateOpen (R := k) i).ι ≫ projectiveSpaceStructure k m).sectionsAlgebra ⊤
    chartNativeIso i a = (coordinateChartIso (R := k) i).hom.appTop.hom
      ((Scheme.ΓSpecIso (.of (CoordinateRing k i))).inv.hom a) :=
  (exists_isoSections (CoordinateRing k i) _ (coordinateChartIso i) (chart_structure i)).choose_spec a

/-- The SAME original chart polynomial algebra, with the actual original projective k action. -/
def sectionsEquiv (i : Fin (m + 1)) :
    letI := (projectiveSpaceStructure k m).sectionsAlgebra (coordinateOpen (R := k) i)
    CoordinateRing k i ≃ₐ[k] Γ(projectiveSpace k m, coordinateOpen (R := k) i) := by
  let U := coordinateOpen (R := k) i
  letI := ((U.ι ≫ projectiveSpaceStructure k m)).sectionsAlgebra ⊤
  letI := (projectiveSpaceStructure k m).sectionsAlgebra U
  exact (chartNativeIso (k := k) i).trans
    (SchemeAffineCoefficientEquivalences.openSections (projectiveSpaceStructure k m) U)

private def chartRingIso (i : Fin (m + 1)) :
    CommRingCat.of (CoordinateRing k i) ≅ Γ(projectiveSpace k m, coordinateOpen (R := k) i) :=
  (homogeneousChartEquiv (R := k) i).toRingEquiv.toCommRingCatIso.symm ≪≫
    Proj.basicOpenIsoAway (projectiveSpaceGrading k m) (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X k i) (by decide : 0 < (1 : ℕ))

private theorem homogeneousSectionsMap_eq {B τ : Type u} [CommRing B]
    [SetLike τ B] [AddSubgroupClass τ B] (ℬ : ℕ → τ) [GradedRing ℬ]
    (a : B) {d : ℕ} (ha : a ∈ ℬ d) (hd : 0 < d) :
    (Proj.basicOpenIsoAway ℬ a ha hd).hom =
      (Scheme.ΓSpecIso (.of (HomogeneousLocalization.Away ℬ a))).inv ≫
        (Proj.basicOpenIsoSpec ℬ a ha hd).hom.appTop ≫ (Proj.basicOpen ℬ a).topIso.hom := by
  rw [Proj.basicOpenIsoSpec_hom]
  simp only [Scheme.Hom.appTop]
  rw [Proj.basicOpenToSpec_app_top]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

private theorem chartRingIso_eq (i : Fin (m + 1)) :
    chartRingIso (k := k) i = (Scheme.ΓSpecIso (.of (CoordinateRing k i))).symm ≪≫
      Scheme.Γ.mapIso (coordinateChartIso (R := k) i).op ≪≫ (coordinateOpen (R := k) i).topIso := by
  apply Iso.ext
  change _ = (Scheme.ΓSpecIso (.of (CoordinateRing k i))).inv ≫
    (Spec.map (CommRingCat.ofHom (homogeneousChartEquiv (R := k) i).symm.toRingHom)).appTop ≫
      (Proj.basicOpenIsoSpec (projectiveSpaceGrading k m) (MvPolynomial.X i)
        (MvPolynomial.isHomogeneous_X k i) (by decide : 0 < (1 : ℕ))).hom.appTop ≫
          (coordinateOpen (R := k) i).topIso.hom
  erw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  rw [Category.assoc, ← homogeneousSectionsMap_eq]
  rfl

private theorem sectionsEquiv_apply (i : Fin (m + 1)) (a : CoordinateRing k i) :
    letI := (projectiveSpaceStructure k m).sectionsAlgebra (coordinateOpen (R := k) i)
    sectionsEquiv i a = (chartRingIso (k := k) i).hom.hom a := by
  change (coordinateOpen (R := k) i).topIso.hom.hom (chartNativeIso i a) = _
  rw [chartNativeIso_apply, chartRingIso_eq]
  rfl

/-- The native k-algebra isomorphism retains EVERY original coordinate ratio, including the pivot. -/
theorem sectionsEquiv_coordinate (i j : Fin (m + 1)) :
    letI := (projectiveSpaceStructure k m).sectionsAlgebra (coordinateOpen (R := k) i)
    sectionsEquiv i (coordinateDehomCoord i j) =
      ProjectiveHomogeneousSections.coefficient i 1 (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X k j) := by
  rw [sectionsEquiv_apply]
  change (Proj.awayToSection (projectiveSpaceGrading k m) (MvPolynomial.X i)).hom
    (homogeneousChartRatioHom i (coordinateDehomCoord i j)) = _
  rw [DeJongAlterations.Algebra.Segre.homogeneousChartRatioHom_coordinate]
  rfl

variable {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ projectiveSpace k m)
  (i : Fin (m + 1)) [Nonempty (f ⁻¹ᵁ coordinateOpen (R := k) i)]

/-- The TRUE original pulled X_j/X_i, taken to the SAME actual native function field K(X). -/
def coordinate (j : Fin (m + 1)) : X.functionField :=
  X.germToFunctionField (f ⁻¹ᵁ coordinateOpen (R := k) i)
    (f.app (coordinateOpen (R := k) i)
      (ProjectiveHomogeneousSections.coefficient i 1 (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X k j)))

/-- The genuine SAME original pivot is one in the ENTIRE actual original K(X). -/
theorem coordinate_self : coordinate f i i = 1 := by
  rw [coordinate, ProjectiveHomogeneousSections.coefficient_X,
    coordinateHyperplaneLocalEquation_self, map_one, map_one]

/-- Actual original closed immersion DERIVES generation of ALL native K(X) by the SAME
original projective coordinate ratios, without any function-field comparison premise. -/
theorem adjoin_coordinates_eq_top [IsClosedImmersion f] :
    letI := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    IntermediateField.adjoin k (Set.range (coordinate f i)) = ⊤ := by
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  let := (projectiveSpaceStructure k m).sectionsAlgebra (coordinateOpen (R := k) i)
  let F := IntermediateField.adjoin k (Set.range (coordinate f i))
  let φ := (SchemeFunctionFieldPullbackCoefficients.genericMap f (projectiveSpaceStructure k m)
    (coordinateOpen (R := k) i)).comp (sectionsEquiv (k := k) i).toAlgHom
  have hφ (j : ChartIndex i) : φ (MvPolynomial.X j) = coordinate f i j.val := by
    have hc := sectionsEquiv_coordinate (k := k) i j.val
    have he : coordinateDehomCoord (R := k) i j.val = MvPolynomial.X j := by
      simp only [coordinateDehomCoord, dif_neg j.property]
    rw [he] at hc
    change SchemeFunctionFieldPullbackCoefficients.genericMap f (projectiveSpaceStructure k m)
      (coordinateOpen (R := k) i) (sectionsEquiv i (MvPolynomial.X j)) = _
    rw [hc]
    rfl
  have hall (a : Γ(projectiveSpace k m, coordinateOpen (R := k) i)) :
      X.germToFunctionField (f ⁻¹ᵁ coordinateOpen (R := k) i)
        (f.app (coordinateOpen (R := k) i) a) ∈ F := by
    obtain ⟨b, rfl⟩ := (sectionsEquiv (k := k) i).surjective a
    change φ b ∈ F
    induction b using MvPolynomial.induction_on with
    | C a =>
      rw [show MvPolynomial.C a = algebraMap k (CoordinateRing k i) a from rfl, φ.commutes]
      exact F.algebraMap_mem a
    | add a b ha hb => rw [map_add]; exact F.add_mem ha hb
    | mul_X a j ha =>
      rw [map_mul, hφ]
      exact F.mul_mem ha (IntermediateField.subset_adjoin k _ ⟨j.val, rfl⟩)
  apply top_unique
  rw [← AffineFunctionFieldGeneration.closedImmersion_adjoin_eq_top
    (f ≫ projectiveSpaceStructure k m) f (coordinateOpen (R := k) i) (coordinateOpen_isAffineOpen i),
      IntermediateField.adjoin_le_iff]
  rintro _ ⟨a, rfl⟩
  exact hall a

/-- The homogeneous model is INTERNALLY reconstructed over the ENTIRE SAME native K(X),
from the SAME original projective embedding and all literal original coordinate ratios. -/
def fullFieldModel [IsClosedImmersion f] :
    letI := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    MultiModel k X.functionField 1 := by
  letI := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  let z (j : MultiModel.QuotVar (fun _ : Fin 1 => m)) : MvPolynomial (Fin 1) X.functionField :=
    monomial (Finsupp.single j.1 1) (coordinate f i j.2)
  refine {
    S := Algebra.adjoin k (Set.range z)
    isGraded := fun _ hp a => monomial_coeff_mem_adjoin (fun q hq => by
      obtain ⟨j, rfl⟩ := hq; exact ⟨_, _, rfl⟩) hp a
    fg := ⟨(Set.finite_range z).toFinset, by rw [Set.Finite.coe_toFinset]⟩
    M := fun _ => m
    coord := fun _ j => coordinate f i j
    coord_mem := fun c j => Algebra.subset_adjoin ⟨⟨c, j⟩, rfl⟩
    exists_coord_ne_zero := fun _ => ⟨i, by rw [coordinate_self]; exact one_ne_zero⟩
    isIntegral := fun p hp => isIntegral_algebraMap
      (R := Algebra.adjoin k (Set.range z)) (x := ⟨p, hp⟩)
    generates := ?_ }
  let s := {x : X.functionField | ∃ (a : Fin 1 →₀ ℕ) (b c : X.functionField),
    monomial a b ∈ Algebra.adjoin k (Set.range z) ∧
      monomial a c ∈ Algebra.adjoin k (Set.range z) ∧ c ≠ 0 ∧ x = b / c}
  have hgen (j : Fin (m + 1)) : coordinate f i j ∈ s := by
    refine ⟨Finsupp.single (0 : Fin 1) 1, coordinate f i j, coordinate f i i,
      Algebra.subset_adjoin ⟨⟨0, j⟩, rfl⟩, Algebra.subset_adjoin ⟨⟨0, i⟩, rfl⟩, ?_, ?_⟩
    · rw [coordinate_self]; exact one_ne_zero
    · rw [coordinate_self, div_one]
  have hle : IntermediateField.adjoin k (Set.range (coordinate f i)) ≤ IntermediateField.adjoin k s := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨j, rfl⟩
    exact IntermediateField.subset_adjoin k s (hgen j)
  rw [adjoin_coordinates_eq_top f i] at hle
  exact top_unique hle

/-- Native projectivity INTERNALLY constructs the actual original closed embedding and
nonempty chart which generate ALL of the SAME original native K(X), with its original p scalars. -/
theorem exists_native_field_coordinates {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (.of k)) [IsProjective p] :
    letI := p.stalkAlgebra (genericPoint X)
    ∃ m : ℕ, ∃ f : X ⟶ projectiveSpace k m,
      IsClosedImmersion f ∧ f ≫ projectiveSpaceStructure k m = p ∧
        ∃ i : Fin (m + 1), ∃ h : Nonempty (f ⁻¹ᵁ coordinateOpen (R := k) i),
          letI := h
          IntermediateField.adjoin k (Set.range (coordinate f i)) = ⊤ ∧ coordinate f i i = 1 := by
  obtain ⟨m, f, hf, hfp⟩ := (ProjectiveBlowupSequence.isProjectiveOver_iff p).mpr
    (ProjectiveFactorizationRingIso.of_isProjective p)
  subst p
  let : IsClosedImmersion f := hf
  have hcover : f (genericPoint X) ∈ ⨆ j : Fin (m + 1), coordinateOpen (R := k) j := by
    rw [iSup_coordinateOpen_eq_top]
    trivial
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hcover
  let h : Nonempty (f ⁻¹ᵁ coordinateOpen (R := k) j) := ⟨⟨genericPoint X, hj⟩⟩
  let := h
  exact ⟨m, f, hf, rfl, j, h, adjoin_coordinates_eq_top f j, coordinate_self f j⟩

end EnvelopeProperty.ProjectiveChartFunctionFieldGeneration
