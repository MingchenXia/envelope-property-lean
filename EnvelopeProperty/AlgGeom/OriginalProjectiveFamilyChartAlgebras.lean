import EnvelopeProperty.AlgGeom.OriginalProjectiveDiagonalNativeComparison
import EnvelopeProperty.AlgGeom.ProjectiveFixedNativeModelCharts
import EnvelopeProperty.Global.SmoothModelEP

/-! # ENTIRE actual original simultaneous chart algebras in the SAME native function field -/
open AlgebraicGeometry CategoryTheory MvPolynomial TopologicalSpace
open Alterations Alterations.Geometry.ProjectiveIdeal
open scoped Classical NNReal Topology
noncomputable section
universe u
namespace EnvelopeProperty.OriginalProjectiveFamilyChartAlgebras
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k K : Type u} [Field k] [Field K] [Algebra k K]

private theorem homLocAlg_eq_of_S (Y Z : MultiModel k K 1) (h : Y.S = Z.S) (g : K) (a : Fin 1 →₀ ℕ) :
    Y.homLocAlg g a = Z.homLocAlg g a := by
  cases Y
  cases Z
  cases h
  rfl


private theorem binary_preimage {X : Scheme.{u}} {m n : ℕ}
    (f : X ⟶ projectiveSpace k m) (g : X ⟶ projectiveSpace k n)
    (hfg : f ≫ projectiveSpaceStructure k m = g ≫ projectiveSpaceStructure k n)
    (i : Fin (m+1)) (j : Fin (n+1)) :
    ProjectiveSegrePullbackSections.morphism f g hfg ⁻¹ᵁ
      coordinateOpen (R := k) (Alterations.Algebra.Segre.indexEquiv m n (i,j)) =
      (f ⁻¹ᵁ coordinateOpen (R := k) i) ⊓ (g ⁻¹ᵁ coordinateOpen (R := k) j) := by
  change (ProjectiveSegrePullbackSections.pair f g hfg ≫ Alterations.Geometry.Segre.segre k m n) ⁻¹ᵁ
    Proj.basicOpen (Alterations.projectiveSpaceGrading k _)
      (MvPolynomial.X (Alterations.Algebra.Segre.indexEquiv m n (i,j))) = _
  rw [Scheme.Hom.comp_preimage,Alterations.Geometry.Segre.segre_preimage_coordinate,
    Alterations.Geometry.Segre.productCoordinateOpen,Scheme.Hom.preimage_inf,
    ← Scheme.Hom.comp_preimage,← Scheme.Hom.comp_preimage]
  simp only [ProjectiveSegrePullbackSections.pair,Limits.pullback.lift_fst,Limits.pullback.lift_snd]

/-- The SAME finite original Segre coordinate chart is EXACTLY the simultaneous original factor chart. -/
theorem morphism_preimage_coordinateOpen {X : Scheme.{u}} {r : ℕ} (d : Fin (r+1) → ℕ)
    (q : ∀ c,X ⟶ projectiveSpace k (d c)) (p : X ⟶ Spec (.of k))
    (hp : ∀ c,q c ≫ projectiveSpaceStructure k (d c) = p) (j : ∀ c,Fin (d c+1)) :
    FiniteSegreOriginalProjectiveMaps.morphism d q p hp ⁻¹ᵁ
      coordinateOpen (R := k) (FiniteSegreOriginalProjectiveMaps.index d j) =
      ⨅ c,q c ⁻¹ᵁ coordinateOpen (R := k) (j c) := by
  induction r with
  | zero =>
    change (q 0 ⁻¹ᵁ coordinateOpen (R := k) (j 0)) = _
    apply le_antisymm
    · apply le_iInf
      intro c
      have hc : c = 0 := Fin.fin_one_eq_zero c
      subst c
      exact le_rfl
    · exact iInf_le _ 0
  | succ r ih =>
    change ProjectiveSegrePullbackSections.morphism (q 0)
      (FiniteSegreOriginalProjectiveMaps.morphism (fun c : Fin (r+1) => d c.succ)
        (fun c => q c.succ) p (fun c => hp c.succ)) _ ⁻¹ᵁ
      coordinateOpen (R := k) (Alterations.Algebra.Segre.indexEquiv _ _
        (j 0,FiniteSegreOriginalProjectiveMaps.index (fun c : Fin (r+1) => d c.succ) (fun c => j c.succ))) = _
    rw [binary_preimage,ih]
    apply SetLike.coe_injective
    rw [Opens.coe_inf,Opens.coe_iInf,Opens.coe_iInf]
    ext x
    simp only [Set.mem_inter_iff,Set.mem_iInter,Fin.forall_fin_succ]

variable {X : Scheme.{u}} [IsIntegral X] {r : ℕ} {d : Fin (r+1) → ℕ}
  (q : ∀ c,X ⟶ projectiveSpace k (d c)) (p : X ⟶ Spec (.of k))
  (hp : ∀ c,q c ≫ projectiveSpaceStructure k (d c) = p) [IsClosedImmersion (q 0)]

/-- The ENTIRE actual finite Segre chart algebra equals the corresponding ENTIRE original family chart algebra in SAME K(X). -/
theorem actualChartAlgebra_eq (j : ∀ c,Fin (d c+1))
    (hJ : ∀ c,Nonempty (q c ⁻¹ᵁ coordinateOpen (R := k) (j c))) :
    let f := FiniteSegreOriginalProjectiveMaps.morphism d q p hp
    let b := f ≫ projectiveSpaceStructure k (FiniteSegreOriginalProjectiveMaps.dimension d)
    let hb := fun c => (hp c).trans (FiniteSegreOriginalProjectiveMaps.morphism_structure d q p hp).symm
    let pivot := FiniteProjectiveNativeFieldModels.pivot q
    let hU := fun c => (FiniteProjectiveNativeFieldModels.chartSite (q c)).property
    letI := FiniteSegreNativeCoordinateAlgebra.chart_nonempty d q p hp pivot hU
    letI := FiniteSegreOriginalProjectiveMaps.morphism_isClosedImmersion d q p hp
    letI := b.stalkAlgebra (genericPoint X)
    (ProjectiveChartFunctionFieldGeneration.fullFieldModel f
      (FiniteSegreOriginalProjectiveMaps.index d pivot)).chartAlg
        (fun _ => FiniteSegreOriginalProjectiveMaps.index d j) =
      (FiniteProjectiveNativeFieldModels.model q b hb).chartAlg j := by
  let f := FiniteSegreOriginalProjectiveMaps.morphism d q p hp
  let b := f ≫ projectiveSpaceStructure k (FiniteSegreOriginalProjectiveMaps.dimension d)
  let hb := fun c => (hp c).trans (FiniteSegreOriginalProjectiveMaps.morphism_structure d q p hp).symm
  let pivot := FiniteProjectiveNativeFieldModels.pivot q
  let hU := fun c => (FiniteProjectiveNativeFieldModels.chartSite (q c)).property
  let := FiniteSegreNativeCoordinateAlgebra.chart_nonempty d q p hp pivot hU
  let := FiniteSegreOriginalProjectiveMaps.morphism_isClosedImmersion d q p hp
  let := b.stalkAlgebra (genericPoint X)
  let Y := FiniteProjectiveNativeFieldModels.model q b hb
  let Z := ProjectiveChartFunctionFieldGeneration.fullFieldModel f
    (FiniteSegreOriginalProjectiveMaps.index d pivot)
  let a := OriginalProjectivePositiveDiagonalAlgebra.oneDegree (r+1)
  have ha := OriginalProjectiveDiagonalNativeComparison.oneDegree_pos r
  have hy : ∀ c,Y.coord c (j c) ≠ 0 := by
    intro c
    let : Nonempty (q c ⁻¹ᵁ coordinateOpen (R := k) (pivot c)) := hU c
    let : Nonempty (q c ⁻¹ᵁ coordinateOpen (R := k) (j c)) := hJ c
    exact ProjectiveChartGenericTransitions.coordinate_pivot_ne_zero (q c) (pivot c) (j c)
  have hz : Z.coord 0 (FiniteSegreOriginalProjectiveMaps.index d j) = ∏ c,Y.coord c (j c) :=
    FiniteSegreNativeCoordinateAlgebra.coordinate_product d q p hp pivot hU j
  have hzn : ∀ c,Z.coord c ((fun _ => FiniteSegreOriginalProjectiveMaps.index d j) c) ≠ 0 := by
    intro c
    have hc : c = 0 := Subsingleton.elim _ _
    subst c
    rw [hz]
    exact Finset.prod_ne_zero_iff.mpr (fun c _ => hy c)
  have hden : Z.chartDen (fun _ => FiniteSegreOriginalProjectiveMaps.index d j) (Finsupp.single 0 1) =
      Y.chartDen j a := by
    rw [MultiModel.chartDen,Fin.prod_univ_one]
    simp only [Finsupp.single_eq_same,pow_one]
    rw [hz,MultiModel.chartDen]
    apply Finset.prod_congr rfl
    intro c _
    change Y.coord c (j c) = Y.coord c (j c) ^ 1
    rw [pow_one]
  have hs : (Y.veronese ha).S = Z.S :=
    OriginalProjectivePositiveDiagonalAlgebra.model_positiveDiagonal_eq_actualSegreAlgebra q p hp
  change Z.chartAlg (fun _ => FiniteSegreOriginalProjectiveMaps.index d j) = Y.chartAlg j
  rw [Z.chartAlg_eq_homLocAlg hzn (a := Finsupp.single 0 1) (by intro c; have hc : c = 0 := Subsingleton.elim _ _; subst c; simp),
    hden,← homLocAlg_eq_of_S (Y.veronese ha) Z hs,MultiModel.homLocAlg_veronese,
    ← Y.chartAlg_eq_homLocAlg hy ha]

/-- The ENTIRE actual original simultaneous chart ring is the WHOLE original multigraded chart algebra. -/
def wholeChartSectionsEquiv (j : ∀ c,Fin (d c+1))
    (hJ : ∀ c,Nonempty (q c ⁻¹ᵁ coordinateOpen (R := k) (j c))) :
    let f := FiniteSegreOriginalProjectiveMaps.morphism d q p hp
    let b := f ≫ projectiveSpaceStructure k (FiniteSegreOriginalProjectiveMaps.dimension d)
    let hb := fun c => (hp c).trans (FiniteSegreOriginalProjectiveMaps.morphism_structure d q p hp).symm
    let pivot := FiniteProjectiveNativeFieldModels.pivot q
    let hU := fun c => (FiniteProjectiveNativeFieldModels.chartSite (q c)).property
    letI := FiniteSegreNativeCoordinateAlgebra.chart_nonempty d q p hp pivot hU
    letI := FiniteSegreNativeCoordinateAlgebra.chart_nonempty d q p hp j hJ
    letI := FiniteSegreOriginalProjectiveMaps.morphism_isClosedImmersion d q p hp
    letI := b.stalkAlgebra (genericPoint X)
    letI := b.sectionsAlgebra (f ⁻¹ᵁ coordinateOpen (R := k) (FiniteSegreOriginalProjectiveMaps.index d j))
    Γ(X,f ⁻¹ᵁ coordinateOpen (R := k) (FiniteSegreOriginalProjectiveMaps.index d j)) ≃ₐ[k]
      (FiniteProjectiveNativeFieldModels.model q b hb).chartAlg j := by
  let f := FiniteSegreOriginalProjectiveMaps.morphism d q p hp
  let b := f ≫ projectiveSpaceStructure k (FiniteSegreOriginalProjectiveMaps.dimension d)
  let hb := fun c => (hp c).trans (FiniteSegreOriginalProjectiveMaps.morphism_structure d q p hp).symm
  let pivot := FiniteProjectiveNativeFieldModels.pivot q
  let hU := fun c => (FiniteProjectiveNativeFieldModels.chartSite (q c)).property
  let := FiniteSegreNativeCoordinateAlgebra.chart_nonempty d q p hp pivot hU
  let := FiniteSegreNativeCoordinateAlgebra.chart_nonempty d q p hp j hJ
  let := FiniteSegreOriginalProjectiveMaps.morphism_isClosedImmersion d q p hp
  let := b.stalkAlgebra (genericPoint X)
  let := b.sectionsAlgebra (f ⁻¹ᵁ coordinateOpen (R := k) (FiniteSegreOriginalProjectiveMaps.index d j))
  exact (ProjectiveFixedNativeModelCharts.nativeSectionsEquivModelChartAt f
    (FiniteSegreOriginalProjectiveMaps.index d pivot) (FiniteSegreOriginalProjectiveMaps.index d j)).trans
      (Subalgebra.equivOfEq _ _ (actualChartAlgebra_eq q p hp j hJ))

/-- EVERY actual regular original chart function keeps its literal original generic germ in the SAME entire K(X). -/
theorem wholeChartSectionsEquiv_apply (j : ∀ c,Fin (d c+1))
    (hJ : ∀ c,Nonempty (q c ⁻¹ᵁ coordinateOpen (R := k) (j c)))
    (s : Γ(X,FiniteSegreOriginalProjectiveMaps.morphism d q p hp ⁻¹ᵁ
      coordinateOpen (R := k) (FiniteSegreOriginalProjectiveMaps.index d j))) :
    let f := FiniteSegreOriginalProjectiveMaps.morphism d q p hp
    let b := f ≫ projectiveSpaceStructure k (FiniteSegreOriginalProjectiveMaps.dimension d)
    let hb := fun c => (hp c).trans (FiniteSegreOriginalProjectiveMaps.morphism_structure d q p hp).symm
    let pivot := FiniteProjectiveNativeFieldModels.pivot q
    let hU := fun c => (FiniteProjectiveNativeFieldModels.chartSite (q c)).property
    letI := FiniteSegreNativeCoordinateAlgebra.chart_nonempty d q p hp pivot hU
    letI := FiniteSegreNativeCoordinateAlgebra.chart_nonempty d q p hp j hJ
    letI := FiniteSegreOriginalProjectiveMaps.morphism_isClosedImmersion d q p hp
    letI := b.stalkAlgebra (genericPoint X)
    letI := b.sectionsAlgebra (f ⁻¹ᵁ coordinateOpen (R := k) (FiniteSegreOriginalProjectiveMaps.index d j))
    ((wholeChartSectionsEquiv q p hp j hJ s :
      (FiniteProjectiveNativeFieldModels.model q b hb).chartAlg j) : X.functionField) =
      X.germToFunctionField (f ⁻¹ᵁ coordinateOpen (R := k) (FiniteSegreOriginalProjectiveMaps.index d j)) s := by
  let f := FiniteSegreOriginalProjectiveMaps.morphism d q p hp
  let b := f ≫ projectiveSpaceStructure k (FiniteSegreOriginalProjectiveMaps.dimension d)
  let hb := fun c => (hp c).trans (FiniteSegreOriginalProjectiveMaps.morphism_structure d q p hp).symm
  let pivot := FiniteProjectiveNativeFieldModels.pivot q
  let hU := fun c => (FiniteProjectiveNativeFieldModels.chartSite (q c)).property
  let := FiniteSegreNativeCoordinateAlgebra.chart_nonempty d q p hp pivot hU
  let := FiniteSegreNativeCoordinateAlgebra.chart_nonempty d q p hp j hJ
  let := FiniteSegreOriginalProjectiveMaps.morphism_isClosedImmersion d q p hp
  let := b.stalkAlgebra (genericPoint X)
  let := b.sectionsAlgebra (f ⁻¹ᵁ coordinateOpen (R := k) (FiniteSegreOriginalProjectiveMaps.index d j))
  rfl

end EnvelopeProperty.OriginalProjectiveFamilyChartAlgebras
