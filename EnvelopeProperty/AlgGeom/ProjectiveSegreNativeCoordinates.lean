import EnvelopeProperty.AlgGeom.ProjectiveSegrePullbackSections
import EnvelopeProperty.AlgGeom.ProjectiveChartFunctionFieldGeneration
import Mathlib.AlgebraicGeometry.Stalk

/-! # Actual Segre generic coordinates in the SAME original whole function field -/
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial TopologicalSpace
open scoped TensorProduct
open Alterations Alterations.Geometry.ProjectiveIdeal Alterations.Geometry.Segre Alterations.Algebra.Segre
noncomputable section
universe u
namespace EnvelopeProperty.ProjectiveSegreNativeCoordinates
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra homogeneousChartAlgebra
variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] {m n : ℕ}

private theorem openStalk_coefficient {Y : Scheme.{u}} (U : Y.Opens) (x : Y)
    (hx : x ∈ U) (c : Γ(Y,U)) :
    (Scheme.ΓSpecIso (Y.presheaf.stalk x)).hom.hom
      ((U.fromSpecStalkOfMem x hx).appTop.hom (U.topIso.inv.hom c)) =
        Y.presheaf.germ U x hx c := by
  have h := congrArg (fun q => pullRingHom q c) (U.fromSpecStalkOfMem_toSpecΓ x hx)
  simp only [pullRingHom,Scheme.Hom.comp_appTop,Scheme.Opens.toSpecΓ_appTop,
    Category.assoc, Iso.inv_hom_id_assoc, CommRingCat.hom_comp, RingHom.comp_apply] at h
  have h' := congrArg (Scheme.ΓSpecIso (Y.presheaf.stalk x)).hom.hom h
  have he : ((Scheme.ΓSpecIso Γ(Y,U)).inv ≫
      (Spec.map (Y.presheaf.germ U x hx)).appTop) ≫
        (Scheme.ΓSpecIso (Y.presheaf.stalk x)).hom = Y.presheaf.germ U x hx := by
    rw [← Scheme.ΓSpecIso_inv_naturality,Category.assoc,Iso.inv_hom_id,Category.comp_id]
  simpa only [← CommRingCat.comp_apply,he] using h'

variable (f : X ⟶ projectiveSpace k m) (i : Fin (m+1))
  [Nonempty (f ⁻¹ᵁ coordinateOpen (R := k) i)]

private theorem generic_mem : f (genericPoint X) ∈ coordinateOpen (R := k) i :=
  ((genericPoint_spec X).mem_open_set_iff (f ⁻¹ᵁ coordinateOpen (R := k) i).isOpen).mpr
    (by simpa using (inferInstance : Nonempty (f ⁻¹ᵁ coordinateOpen (R := k) i)))

/-- The canonical original generic-stalk map into the actual original polynomial chart. -/
def nativeChart : Spec X.functionField ⟶ Spec (.of (CoordinateRing k i)) :=
  Spec.map (f.stalkMap (genericPoint X)) ≫
    (coordinateOpen (R := k) i).fromSpecStalkOfMem (f (genericPoint X)) (generic_mem f i) ≫
      (coordinateChartIso (R := k) i).hom

/-- The entire actual generic chart triangle is the SAME original generic map followed by f. -/
theorem nativeChart_fac : nativeChart f i ≫ coordinateChartInclusion i =
    X.fromSpecStalk (genericPoint X) ≫ f := by
  simp only [nativeChart,coordinateChartInclusion,Category.assoc,Iso.hom_inv_id_assoc,
    Scheme.Opens.fromSpecStalkOfMem_ι]
  exact Scheme.SpecMap_stalkMap_fromSpecStalk f

/-- EVERY original generic projective coordinate retains its SAME native function-field value. -/
theorem nativeChart_coordinate (a : Fin (m+1)) :
    (Scheme.ΓSpecIso X.functionField).hom.hom
      (pullRingHom (nativeChart f i) (coordinateDehomCoord i a)) =
        ProjectiveChartFunctionFieldGeneration.coordinate f i a := by
  rw [← ProjectiveChartSectionRatios.coefficient_pullback]
  have he : ProjectiveChartSectionRatios.chartFactor i (nativeChart f i) =
      Spec.map (f.stalkMap (genericPoint X)) ≫
        (coordinateOpen (R := k) i).fromSpecStalkOfMem (f (genericPoint X)) (generic_mem f i) := by
    simp only [ProjectiveChartSectionRatios.chartFactor,nativeChart,Category.assoc,Iso.hom_inv_id,
      Category.comp_id]
  rw [he,Scheme.Hom.comp_appTop]
  have heq : (Spec.map (f.stalkMap (genericPoint X))).appTop ≫
      (Scheme.ΓSpecIso X.functionField).hom =
        (Scheme.ΓSpecIso ((projectiveSpace k m).presheaf.stalk (f (genericPoint X)))).hom ≫
          f.stalkMap (genericPoint X) := by
    rw [← Iso.inv_comp_eq,← Category.assoc,← Scheme.ΓSpecIso_inv_naturality,
      Category.assoc,Iso.inv_hom_id,Category.comp_id]
  change (((coordinateOpen (R := k) i).topIso.inv ≫
    ((coordinateOpen (R := k) i).fromSpecStalkOfMem _ _).appTop) ≫
      (Spec.map (f.stalkMap (genericPoint X))).appTop ≫
        (Scheme.ΓSpecIso X.functionField).hom).hom _ = _
  rw [heq]
  change f.stalkMap (genericPoint X)
    ((Scheme.ΓSpecIso ((projectiveSpace k m).presheaf.stalk (f (genericPoint X)))).hom.hom
      (((coordinateOpen (R := k) i).fromSpecStalkOfMem _ _).appTop.hom
        ((coordinateOpen (R := k) i).topIso.inv.hom _))) = _
  exact (congrArg (fun r => f.stalkMap (genericPoint X) r)
    (openStalk_coefficient (Y := projectiveSpace k m) (coordinateOpen (R := k) i)
      (f (genericPoint X)) (generic_mem f i) _)).trans
        (f.germ_stalkMap_apply (coordinateOpen (R := k) i) (genericPoint X) (generic_mem f i) _)

variable (g : X ⟶ projectiveSpace k n)
  (hfg : f ≫ projectiveSpaceStructure k m = g ≫ projectiveSpaceStructure k n)
  (j : Fin (n+1)) [Nonempty (g ⁻¹ᵁ coordinateOpen (R := k) j)]

include hfg in
private theorem nativeChart_base :
    nativeChart f i ≫ (coordinateChartInclusion i ≫ projectiveSpaceStructure k m) =
      nativeChart g j ≫ (coordinateChartInclusion j ≫ projectiveSpaceStructure k n) := by
  rw [← Category.assoc,nativeChart_fac,Category.assoc,hfg]
  symm
  rw [← Category.assoc,nativeChart_fac,Category.assoc]

/-- The actual original generic pair into the genuine tensor-chart spectrum. -/
def nativeProductChart :
    Spec X.functionField ⟶ Spec (.of (CoordinateRing k i ⊗[k] CoordinateRing k j)) :=
  (productChart_isPullback (R := k) i j).lift
    (nativeChart f i) (nativeChart g j) (nativeChart_base f i g hfg j)

private theorem nativeProductChart_left :
    nativeProductChart f i g hfg j ≫ tensorChartLeft i j = nativeChart f i :=
  (productChart_isPullback (R := k) i j).lift_fst _ _ _

private theorem nativeProductChart_right :
    nativeProductChart f i g hfg j ≫ tensorChartRight i j = nativeChart g j :=
  (productChart_isPullback (R := k) i j).lift_snd _ _ _

/-- The whole generic pair map is the SAME original generic map followed by the original pair. -/
theorem nativeProductChart_fac : nativeProductChart f i g hfg j ≫ productChartInclusion i j =
    X.fromSpecStalk (genericPoint X) ≫ ProjectiveSegrePullbackSections.pair f g hfg := by
  apply pullback.hom_ext
  · rw [Category.assoc,productChartInclusion_fst,← Category.assoc]
    change (nativeProductChart f i g hfg j ≫ tensorChartLeft i j) ≫ _ = _
    rw [nativeProductChart_left,nativeChart_fac,Category.assoc,
      ProjectiveSegrePullbackSections.pair,pullback.lift_fst]
  · rw [Category.assoc,productChartInclusion_snd,← Category.assoc]
    change (nativeProductChart f i g hfg j ≫ tensorChartRight i j) ≫ _ = _
    rw [nativeProductChart_right,nativeChart_fac,Category.assoc,
      ProjectiveSegrePullbackSections.pair,pullback.lift_snd]

private theorem nativeSegreChart_fac :
    (nativeProductChart f i g hfg j ≫ affineChartMap i j) ≫
      coordinateChartInclusion (indexEquiv m n (i,j)) =
        X.fromSpecStalk (genericPoint X) ≫ ProjectiveSegrePullbackSections.morphism f g hfg := by
  rw [Category.assoc]
  change nativeProductChart f i g hfg j ≫ chartToProjective i j = _
  rw [← productChartInclusion_segre,← Category.assoc,nativeProductChart_fac,Category.assoc]
  rfl

/-- The SAME original generic point lies in the actual Segre product-pivot chart. -/
theorem segre_chart_nonempty :
    Nonempty (ProjectiveSegrePullbackSections.morphism f g hfg ⁻¹ᵁ
      coordinateOpen (R := k) (indexEquiv m n (i,j))) := by
  have heq := congrArg (fun q => q (IsLocalRing.closedPoint X.functionField))
    (nativeSegreChart_fac f i g hfg j)
  simp only [Scheme.Hom.comp_apply,Scheme.fromSpecStalk_closedPoint] at heq
  refine ⟨⟨genericPoint X, ?_⟩⟩
  have hh : coordinateChartInclusion (R := k) (indexEquiv m n (i,j))
      ((nativeProductChart f i g hfg j ≫ affineChartMap i j) (IsLocalRing.closedPoint X.functionField)) ∈
        (coordinateChartInclusion (R := k) (indexEquiv m n (i,j))).opensRange := ⟨_,rfl⟩
  rw [coordinateChartInclusion_opensRange] at hh
  exact (congrArg (fun x : projectiveSpace k (dimension m n) =>
    x ∈ coordinateOpen (R := k) (indexEquiv m n (i,j))) heq).mp hh

/-- EVERY actual Segre generic coordinate is the product of the SAME actual original factor ratios. -/
theorem coordinate_product (a : Fin (m+1)) (b : Fin (n+1)) :
    let := segre_chart_nonempty f i g hfg j
    ProjectiveChartFunctionFieldGeneration.coordinate (ProjectiveSegrePullbackSections.morphism f g hfg)
      (indexEquiv m n (i,j)) (indexEquiv m n (a,b)) =
        ProjectiveChartFunctionFieldGeneration.coordinate f i a *
          ProjectiveChartFunctionFieldGeneration.coordinate g j b := by
  let := segre_chart_nonempty f i g hfg j
  have heq : nativeProductChart f i g hfg j ≫ affineChartMap i j =
      nativeChart (ProjectiveSegrePullbackSections.morphism f g hfg) (indexEquiv m n (i,j)) := by
    apply (cancel_mono (coordinateChartInclusion (R := k) (indexEquiv m n (i,j)))).mp
    rw [nativeSegreChart_fac,nativeChart_fac]
  have h := congrArg (Scheme.ΓSpecIso X.functionField).hom.hom
    (pullRingHom_affineChartMap_coordinate i a j b (nativeProductChart f i g hfg j))
  rw [heq,map_mul,nativeProductChart_left,nativeProductChart_right,
    nativeChart_coordinate,nativeChart_coordinate,nativeChart_coordinate] at h
  exact h

/-- One original closed projective factor DERIVES generation of the ENTIRE same original K(X) by the actual Segre ratios. -/
theorem adjoin_coordinates_eq_top [IsClosedImmersion f] :
    letI := segre_chart_nonempty f i g hfg j
    letI := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    IntermediateField.adjoin k (Set.range
      (ProjectiveChartFunctionFieldGeneration.coordinate (ProjectiveSegrePullbackSections.morphism f g hfg)
        (indexEquiv m n (i,j)))) = ⊤ := by
  let := segre_chart_nonempty f i g hfg j
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  let F := IntermediateField.adjoin k (Set.range
    (ProjectiveChartFunctionFieldGeneration.coordinate (ProjectiveSegrePullbackSections.morphism f g hfg)
      (indexEquiv m n (i,j))))
  have hc (a : Fin (m+1)) : ProjectiveChartFunctionFieldGeneration.coordinate f i a ∈ F := by
    have he := coordinate_product f i g hfg j a j
    rw [ProjectiveChartFunctionFieldGeneration.coordinate_self,mul_one] at he
    exact IntermediateField.subset_adjoin k _ ⟨indexEquiv m n (a,j),he⟩
  have hle : IntermediateField.adjoin k
      (Set.range (ProjectiveChartFunctionFieldGeneration.coordinate f i)) ≤ F := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨a,rfl⟩
    exact hc a
  rw [ProjectiveChartFunctionFieldGeneration.adjoin_coordinates_eq_top f i] at hle
  exact top_unique hle

omit [IsIntegral X] in
/-- Appending ANY actual same-base projective map to one genuine original closed embedding gives a genuine original Segre closed embedding. -/
theorem morphism_isClosedImmersion [IsClosedImmersion f] :
    IsClosedImmersion (ProjectiveSegrePullbackSections.morphism f g hfg) := by
  let δ := ProjectiveSegrePullbackSections.pair f g hfg
  let q := pullback.fst (projectiveSpaceStructure k m) (projectiveSpaceStructure k n)
  have : IsSeparated q := inferInstance
  have : IsClosedImmersion (δ ≫ q) := by
    change IsClosedImmersion (pullback.lift f g hfg ≫ q)
    rw [pullback.lift_fst]
    infer_instance
  let : IsClosedImmersion δ := IsClosedImmersion.of_comp δ q
  exact IsClosedImmersion.comp δ (segre k m n)

end EnvelopeProperty.ProjectiveSegreNativeCoordinates
