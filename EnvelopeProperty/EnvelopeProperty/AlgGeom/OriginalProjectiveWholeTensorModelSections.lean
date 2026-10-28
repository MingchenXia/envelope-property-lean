import EnvelopeProperty.AlgGeom.OriginalProjectiveTensorPivotCoefficients
import EnvelopeProperty.AlgGeom.OriginalProjectiveFamilyChartAlgebras
import EnvelopeProperty.AlgGeom.ModelSectionsFromChartFractions

/-! # Actual whole original finite tensor-line sections in the SAME simultaneous model -/
open AlgebraicGeometry CategoryTheory MvPolynomial TopologicalSpace Opposite
open Scheme.Modules DeJongAlterations
open scoped Classical
noncomputable section
universe u
namespace EnvelopeProperty.OriginalProjectiveWholeTensorModelSections
open FiniteOriginalProjectivePowerFrames CanonicalGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] {r : ℕ}
    (d : Fin (r+1) → ℕ) (q : ∀ j,X ⟶ Proj (homogeneousSubmodule (Fin (d j+1)) k))
    (p : X ⟶ Spec (.of k)) (hp : ∀ j,q j ≫ projectiveSpaceStructure k (d j) = p)
    [IsClosedImmersion (q 0)]
    (t : ∀ j,Fin (d j+1)) (n : Fin (r+1) → ℕ)

private def jointOpen (j : ∀ c,Fin (d c+1)) : X.Opens :=
  FiniteSegreOriginalProjectiveMaps.morphism d q p hp ⁻¹ᵁ
    coordinateOpen (R := k) (FiniteSegreOriginalProjectiveMaps.index d j)

omit [IsIntegral X] [IsClosedImmersion (q 0)] in
private theorem jointOpen_le (j : ∀ c,Fin (d c+1)) (c : Fin (r+1)) :
    jointOpen d q p hp j ≤ q c ⁻¹ᵁ coordinateOpen (R := k) (j c) := by
  change FiniteSegreOriginalProjectiveMaps.morphism d q p hp ⁻¹ᵁ coordinateOpen (R := k) _ ≤ _
  rw [OriginalProjectiveFamilyChartAlgebras.morphism_preimage_coordinateOpen]
  exact iInf_le _ c

omit [IsIntegral X] in
private theorem jointOpen_affine (j : ∀ c,Fin (d c+1)) :
    IsAffineOpen (jointOpen d q p hp j) := by
  let := FiniteSegreOriginalProjectiveMaps.morphism_isClosedImmersion d q p hp
  exact (coordinateOpen_isAffineOpen (FiniteSegreOriginalProjectiveMaps.index d j)).preimage
    (FiniteSegreOriginalProjectiveMaps.morphism d q p hp)

private abbrev chart (j : ∀ c,Fin (d c+1)) : X.affineOpens :=
  ⟨jointOpen d q p hp j,jointOpen_affine d q p hp j⟩

omit [IsClosedImmersion (q 0)] in
private theorem jointOpen_nonempty (j : ∀ c,Fin (d c+1))
    (hj : ∀ c,Nonempty (q c ⁻¹ᵁ coordinateOpen (R := k) (j c))) :
    Nonempty (jointOpen d q p hp j) :=
  FiniteSegreNativeCoordinateAlgebra.chart_nonempty d q p hp j hj

private def frame (j : ∀ c,Fin (d c+1)) :
    (projectiveLine d q t n).restrict (jointOpen d q p hp j).ι ≅
      unitObj (jointOpen d q p hp j).toScheme :=
  OriginalProjectiveTensorPivotCoefficients.chartFrame d q t n j
    (chart d q p hp j) (jointOpen_le d q p hp j)

private def chartCoefficient (j : ∀ c,Fin (d c+1)) (s : Γ(projectiveLine d q t n,⊤)) :
    Γ(X,jointOpen d q p hp j) :=
  OriginalProjectiveTensorPivotCoefficients.coefficient d q t n j
    (chart d q p hp j) (jointOpen_le d q p hp j) s

/-- The ACTUAL original whole pivot tensor section, internally supplied by original factor geometry. -/
def normalizer : Γ(projectiveLine d q t n,⊤) :=
  OriginalProjectiveTensorPivotCoefficients.pivotSection d q t n (FiniteProjectiveNativeFieldModels.pivot q)

omit [IsClosedImmersion (q 0)] in
/-- Nonvanishing of the SAME original pivot tensor is DERIVED from the actual original charts. -/
theorem normalizer_ne_zero : normalizer d q t n ≠ 0 :=
  OriginalProjectiveTensorPivotCoefficients.pivotSection_ne_zero d q t n
    (FiniteProjectiveNativeFieldModels.pivot q) (fun c => (FiniteProjectiveNativeFieldModels.chartSite (q c)).property)

/-- The literal native original coefficient of EVERY actual original whole tensor-line section. -/
def coefficient (s : Γ(projectiveLine d q t n,⊤)) : X.functionField :=
  sectionRatio (projectiveLine d q t n) (projectiveLine_isInvertible d q t n)
    (normalizer d q t n) (normalizer_ne_zero d q t n) ⊤ s

private theorem coordinates_ne_zero (j : ∀ c,Fin (d c+1))
    (hj : ∀ c,Nonempty (q c ⁻¹ᵁ coordinateOpen (R := k) (j c))) :
    letI := p.stalkAlgebra (genericPoint X)
    ∀ c,(FiniteProjectiveNativeFieldModels.model q p hp).coord c (j c) ≠ 0 := by
  let := p.stalkAlgebra (genericPoint X)
  intro c
  let : Nonempty (q c ⁻¹ᵁ coordinateOpen (R := k) (FiniteProjectiveNativeFieldModels.pivot q c)) :=
    (FiniteProjectiveNativeFieldModels.chartSite (q c)).property
  let := hj c
  exact ProjectiveChartGenericTransitions.coordinate_pivot_ne_zero (q c)
    (FiniteProjectiveNativeFieldModels.pivot q c) (j c)

private theorem normalizer_chart_coefficient (j : ∀ c,Fin (d c+1))
    (hj : ∀ c,Nonempty (q c ⁻¹ᵁ coordinateOpen (R := k) (j c))) :
    letI := jointOpen_nonempty d q p hp j hj
    letI := p.stalkAlgebra (genericPoint X)
    X.germToFunctionField (jointOpen d q p hp j)
      (chartCoefficient d q p hp t n j (normalizer d q t n)) =
      ((FiniteProjectiveNativeFieldModels.model q p hp).chartDenZ j (fun c => (n c : ℤ)))⁻¹ := by
  let : Nonempty (jointOpen d q p hp j) := jointOpen_nonempty d q p hp j hj
  let : Nonempty (chart d q p hp j).1 := jointOpen_nonempty d q p hp j hj
  let := p.stalkAlgebra (genericPoint X)
  have hg := OriginalProjectiveTensorPivotCoefficients.germ_coefficient_pivotSection d q t n j
    (chart d q p hp j) (jointOpen_le d q p hp j) (FiniteProjectiveNativeFieldModels.pivot q)
  refine hg.trans ?_
  change (∏ c,letI := hj c
    ProjectiveChartFunctionFieldGeneration.coordinate (q c) (j c) (FiniteProjectiveNativeFieldModels.pivot q c) ^ n c) =
      (∏ c,FiniteProjectiveNativeFieldModels.coordinate q c (j c) ^ (n c : ℤ))⁻¹
  rw [← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro c _
  let : Nonempty (q c ⁻¹ᵁ coordinateOpen (R := k) (FiniteProjectiveNativeFieldModels.pivot q c)) :=
    (FiniteProjectiveNativeFieldModels.chartSite (q c)).property
  let := hj c
  change ProjectiveChartFunctionFieldGeneration.coordinate (q c) (j c)
    (FiniteProjectiveNativeFieldModels.pivot q c) ^ n c =
      (ProjectiveChartFunctionFieldGeneration.coordinate (q c)
        (FiniteProjectiveNativeFieldModels.pivot q c) (j c) ^ (n c : ℤ))⁻¹
  rw [zpow_natCast]
  have hinv : ProjectiveChartFunctionFieldGeneration.coordinate (q c) (j c)
      (FiniteProjectiveNativeFieldModels.pivot q c) =
      (ProjectiveChartFunctionFieldGeneration.coordinate (q c) (FiniteProjectiveNativeFieldModels.pivot q c) (j c))⁻¹ := by
    rw [← ProjectiveChartGenericTransitions.coordinate_div (q c) (FiniteProjectiveNativeFieldModels.pivot q c)
      (j c) (FiniteProjectiveNativeFieldModels.pivot q c),ProjectiveChartFunctionFieldGeneration.coordinate_self,one_div]
  rw [hinv,inv_pow]

/-- EVERY actual whole original section has its exact SAME original joint-chart model fraction. -/
theorem coefficient_chart_fraction (j : ∀ c,Fin (d c+1))
    (hj : ∀ c,Nonempty (q c ⁻¹ᵁ coordinateOpen (R := k) (j c)))
    (s : Γ(projectiveLine d q t n,⊤)) :
    letI := jointOpen_nonempty d q p hp j hj
    letI := p.stalkAlgebra (genericPoint X)
    coefficient d q t n s / (FiniteProjectiveNativeFieldModels.model q p hp).chartDenZ j (fun c => (n c : ℤ)) =
      X.germToFunctionField (jointOpen d q p hp j) (chartCoefficient d q p hp t n j s) := by
  let : Nonempty (jointOpen d q p hp j) := jointOpen_nonempty d q p hp j hj
  let : Nonempty (chart d q p hp j).1 := jointOpen_nonempty d q p hp j hj
  let := p.stalkAlgebra (genericPoint X)
  have h := sectionRatio_localTrivializationCoefficient (projectiveLine d q t n)
    (projectiveLine_isInvertible d q t n) (normalizer d q t n) (normalizer_ne_zero d q t n)
    (chart d q p hp j) (frame d q p hp t n j) s
  change coefficient d q t n s = X.germToFunctionField (jointOpen d q p hp j)
    (chartCoefficient d q p hp t n j s) / X.germToFunctionField (jointOpen d q p hp j)
      (chartCoefficient d q p hp t n j (normalizer d q t n)) at h
  rw [normalizer_chart_coefficient d q p hp t n j hj,div_inv_eq_mul] at h
  have hden : (FiniteProjectiveNativeFieldModels.model q p hp).chartDenZ j (fun c => (n c : ℤ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun c _ => zpow_ne_zero _ (coordinates_ne_zero d q p hp j hj c))
  rw [h,mul_div_cancel_right₀ _ hden]


private def chartBaseEquiv (b : X ⟶ Spec (.of k))
    (hb : ∀ c,q c ≫ projectiveSpaceStructure k (d c) = b) (h : b = p)
    (j : ∀ c,Fin (d c+1)) :
    (letI := b.stalkAlgebra (genericPoint X); (FiniteProjectiveNativeFieldModels.model q b hb).chartAlg j) ≃+*
      (letI := p.stalkAlgebra (genericPoint X); (FiniteProjectiveNativeFieldModels.model q p hp).chartAlg j) := by
  cases h
  exact RingEquiv.refl _

private theorem chartBaseEquiv_coe (b : X ⟶ Spec (.of k))
    (hb : ∀ c,q c ≫ projectiveSpaceStructure k (d c) = b) (h : b = p)
    (j : ∀ c,Fin (d c+1))
    (x : (letI := b.stalkAlgebra (genericPoint X); (FiniteProjectiveNativeFieldModels.model q b hb).chartAlg j)) :
    ((chartBaseEquiv d q p hp b hb h j x :
      (letI := p.stalkAlgebra (genericPoint X); (FiniteProjectiveNativeFieldModels.model q p hp).chartAlg j)) : X.functionField) =
        (x : X.functionField) := by
  cases h
  rfl

private def chartSectionsEquiv (j : ∀ c,Fin (d c+1))
    (hj : ∀ c,Nonempty (q c ⁻¹ᵁ coordinateOpen (R := k) (j c))) :
    letI := p.stalkAlgebra (genericPoint X)
    Γ(X,jointOpen d q p hp j) ≃+* (FiniteProjectiveNativeFieldModels.model q p hp).chartAlg j := by
  let f := FiniteSegreOriginalProjectiveMaps.morphism d q p hp
  let base := f ≫ projectiveSpaceStructure k (FiniteSegreOriginalProjectiveMaps.dimension d)
  let := base.stalkAlgebra (genericPoint X)
  let := base.sectionsAlgebra (f ⁻¹ᵁ coordinateOpen (R := k) (FiniteSegreOriginalProjectiveMaps.index d j))
  exact (OriginalProjectiveFamilyChartAlgebras.wholeChartSectionsEquiv q p hp j hj).toRingEquiv.trans
    (chartBaseEquiv d q p hp _ _ (FiniteSegreOriginalProjectiveMaps.morphism_structure d q p hp) j)

private theorem chartSectionsEquiv_apply (j : ∀ c,Fin (d c+1))
    (hj : ∀ c,Nonempty (q c ⁻¹ᵁ coordinateOpen (R := k) (j c))) (b : Γ(X,jointOpen d q p hp j)) :
    letI := jointOpen_nonempty d q p hp j hj
    letI := p.stalkAlgebra (genericPoint X)
    ((chartSectionsEquiv d q p hp j hj b : (FiniteProjectiveNativeFieldModels.model q p hp).chartAlg j) : X.functionField) =
      X.germToFunctionField (jointOpen d q p hp j) b := by
  let := jointOpen_nonempty d q p hp j hj
  let f := FiniteSegreOriginalProjectiveMaps.morphism d q p hp
  let base := f ≫ projectiveSpaceStructure k (FiniteSegreOriginalProjectiveMaps.dimension d)
  let := base.stalkAlgebra (genericPoint X)
  let := base.sectionsAlgebra (f ⁻¹ᵁ coordinateOpen (R := k) (FiniteSegreOriginalProjectiveMaps.index d j))
  exact (chartBaseEquiv_coe d q p hp _ _
    (FiniteSegreOriginalProjectiveMaps.morphism_structure d q p hp) j _).trans
      (OriginalProjectiveFamilyChartAlgebras.wholeChartSectionsEquiv_apply q p hp j hj b)

private theorem factor_charts_nonempty (j : ∀ c,Fin (d c+1)) :
    letI := p.stalkAlgebra (genericPoint X)
    (∀ c,(FiniteProjectiveNativeFieldModels.model q p hp).coord c (j c) ≠ 0) →
      ∀ c,Nonempty (q c ⁻¹ᵁ coordinateOpen (R := k) (j c)) := by
  let := p.stalkAlgebra (genericPoint X)
  intro hj c
  let : Nonempty (q c ⁻¹ᵁ coordinateOpen (R := k) (FiniteProjectiveNativeFieldModels.pivot q c)) :=
    (FiniteProjectiveNativeFieldModels.chartSite (q c)).property
  exact (ProjectiveNativeCoordinateChartSupport.coordinate_ne_zero_iff_nonempty (q c)
    (FiniteProjectiveNativeFieldModels.pivot q c) (j c)).mp (hj c)

/-- EVERY whole original section belongs to the true SAME original simultaneous model section space. -/
theorem coefficient_mem_sections (s : Γ(projectiveLine d q t n,⊤)) :
    letI := p.stalkAlgebra (genericPoint X)
    coefficient d q t n s ∈ (FiniteProjectiveNativeFieldModels.model q p hp).sections (fun c => (n c : ℤ)) := by
  let := p.stalkAlgebra (genericPoint X)
  let P := FiniteProjectiveNativeFieldModels.model q p hp
  apply (P.mem_sections_iff_chart_fractions _ _).mpr
  intro j hj
  have hJ := factor_charts_nonempty d q p hp j hj
  let := jointOpen_nonempty d q p hp j hJ
  rw [coefficient_chart_fraction d q p hp t n j hJ s]
  have h := (chartSectionsEquiv d q p hp j hJ (chartCoefficient d q p hp t n j s)).property
  rwa [chartSectionsEquiv_apply d q p hp j hJ] at h

omit [IsClosedImmersion (q 0)] in
/-- The SAME genuine original coefficient is faithful on the ENTIRE original whole tensor-line section space. -/
theorem coefficient_injective : Function.Injective (coefficient d q t n) :=
  sectionRatio_injective (projectiveLine d q t n) (projectiveLine_isInvertible d q t n)
    (normalizer d q t n) (normalizer_ne_zero d q t n) ⊤

/-- EVERY genuine simultaneous model section is an ACTUAL whole original tensor-line section, by true original chart inversion and sheaf gluing. -/
theorem coefficient_surjective :
    letI := p.stalkAlgebra (genericPoint X)
    ∀ g : (FiniteProjectiveNativeFieldModels.model q p hp).sections (fun c => (n c : ℤ)),
      ∃ s : Γ(projectiveLine d q t n,⊤),coefficient d q t n s = (g : X.functionField) := by
  let := p.stalkAlgebra (genericPoint X)
  let P := FiniteProjectiveNativeFieldModels.model q p hp
  let L := projectiveLine d q t n
  let hL := projectiveLine_isInvertible d q t n
  let D := normalizer d q t n
  let hD := normalizer_ne_zero d q t n
  let J := {j : (∀ c,Fin (d c+1)) // ∀ c,Nonempty (q c ⁻¹ᵁ coordinateOpen (R := k) (j c))}
  let U (j : J) := jointOpen d q p hp j.val
  let E (j : J) : Γ(X,U j) ≃+* P.chartAlg j.val := chartSectionsEquiv d q p hp j.val j.property
  intro g
  let G (j : J) : P.chartAlg j.val :=
    ⟨(g : X.functionField) / P.chartDenZ j.val (fun c => (n c : ℤ)),
      P.div_chartDenZ_mem_chartAlg (coordinates_ne_zero d q p hp j.val j.property) g.property⟩
  let c (j : J) : Γ(X,U j) := (E j).symm (G j)
  let S (j : J) : Γ(L,U j) :=
    (nativeLocalFrameCoefficient L (U j) (frame d q p hp t n j.val)).symm (c j)
  have hcoeff (j : J) :
      letI := jointOpen_nonempty d q p hp j.val j.property
      X.germToFunctionField (U j) (c j) =
        (g : X.functionField) / P.chartDenZ j.val (fun c => (n c : ℤ)) := by
    let := jointOpen_nonempty d q p hp j.val j.property
    have he : chartSectionsEquiv d q p hp j.val j.property (c j) = G j :=
      (E j).apply_symm_apply (G j)
    exact (chartSectionsEquiv_apply d q p hp j.val j.property (c j)).symm.trans
      (congrArg Subtype.val he)
  have hratio (j : J) :
      letI := jointOpen_nonempty d q p hp j.val j.property
      sectionRatio L hL D hD (U j) (S j) = (g : X.functionField) := by
    let := jointOpen_nonempty d q p hp j.val j.property
    let : Nonempty (chart d q p hp j.val).1 := jointOpen_nonempty d q p hp j.val j.property
    rw [sectionRatio_nativeFrame_formula L hL D hD (U j) (frame d q p hp t n j.val) (S j)]
    have hn : nativeLocalFrameCoefficient L (U j) (frame d q p hp t n j.val) (S j) = c j :=
      (nativeLocalFrameCoefficient L (U j) (frame d q p hp t n j.val)).apply_symm_apply (c j)
    rw [hn,nativeLocalFrameCoefficient_global L (chart d q p hp j.val) (frame d q p hp t n j.val) D,hcoeff]
    change ((g : X.functionField) / P.chartDenZ j.val (fun c => (n c : ℤ))) /
      X.germToFunctionField (U j) (chartCoefficient d q p hp t n j.val D) = _
    rw [normalizer_chart_coefficient d q p hp t n j.val j.property,div_inv_eq_mul]
    have hden : P.chartDenZ j.val (fun c => (n c : ℤ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun c _ => zpow_ne_zero _ (coordinates_ne_zero d q p hp j.val j.property c))
    exact div_mul_cancel₀ _ hden
  have hcover : (⊤ : X.Opens) ≤ iSup U := by
    intro x _
    let f := FiniteSegreOriginalProjectiveMaps.morphism d q p hp
    have hx : f x ∈ ⨆ a : Fin (FiniteSegreOriginalProjectiveMaps.dimension d+1),coordinateOpen (R := k) a := by
      rw [iSup_coordinateOpen_eq_top]
      trivial
    obtain ⟨a,ha⟩ := Opens.mem_iSup.mp hx
    obtain ⟨j,hj⟩ := (FiniteSegreOriginalProjectiveMaps.index_bijective d).surjective a
    have hxj : x ∈ jointOpen d q p hp j := by
      change f x ∈ coordinateOpen (R := k) (FiniteSegreOriginalProjectiveMaps.index d j)
      rwa [hj]
    have hJ : ∀ c,Nonempty (q c ⁻¹ᵁ coordinateOpen (R := k) (j c)) :=
      fun c => ⟨⟨x,jointOpen_le d q p hp j c hxj⟩⟩
    exact Opens.mem_iSup.mpr ⟨⟨j,hJ⟩,hxj⟩
  have hcompat (j l : J) : L.presheaf.map (Opens.infLELeft (U j) (U l)).op (S j) =
      L.presheaf.map (Opens.infLERight (U j) (U l)).op (S l) := by
    let : Nonempty (U j) := jointOpen_nonempty d q p hp j.val j.property
    let : Nonempty (U l) := jointOpen_nonempty d q p hp l.val l.property
    have hj : genericPoint X ∈ U j := genericPoint_mem_nonempty_open _
    have hl : genericPoint X ∈ U l := genericPoint_mem_nonempty_open _
    let : Nonempty (U j ⊓ U l : X.Opens) := ⟨⟨genericPoint X,⟨hj,hl⟩⟩⟩
    apply sectionRatio_injective L hL D hD (U j ⊓ U l)
    exact (sectionRatio_restrict L hL D hD
      (show U j ⊓ U l ≤ U j from inf_le_left) (S j)).trans
      ((hratio j).trans ((hratio l).symm.trans
        (sectionRatio_restrict L hL D hD
          (show U j ⊓ U l ≤ U l from inf_le_right) (S l)).symm))
  obtain ⟨s,hs,_⟩ := TopCat.Sheaf.existsUnique_gluing' ⟨L.presheaf,L.isSheaf⟩ U ⊤
    (fun _ => homOfLE le_top) hcover S hcompat
  refine ⟨s,?_⟩
  let z : J := ⟨FiniteProjectiveNativeFieldModels.pivot q,
    fun c => (FiniteProjectiveNativeFieldModels.chartSite (q c)).property⟩
  let : Nonempty (U z) := jointOpen_nonempty d q p hp z.val z.property
  have hh := sectionRatio_restrict L hL D hD (le_top : U z ≤ ⊤) s
  rw [hs z] at hh
  exact hh.symm.trans (hratio z)

/-- The ENTIRE original whole tensor-line section space is equivalent to the ENTIRE genuine simultaneous model section space via its SAME original coefficient. -/
def wholeSectionsEquiv :
    letI := p.stalkAlgebra (genericPoint X)
    Γ(projectiveLine d q t n,⊤) ≃ (FiniteProjectiveNativeFieldModels.model q p hp).sections (fun c => (n c : ℤ)) := by
  let := p.stalkAlgebra (genericPoint X)
  refine Equiv.ofBijective (fun s => ⟨coefficient d q t n s,coefficient_mem_sections d q p hp t n s⟩) ⟨?_,?_⟩
  · intro s v h
    exact coefficient_injective d q t n (congrArg Subtype.val h)
  · intro g
    obtain ⟨s,hs⟩ := coefficient_surjective d q p hp t n g
    exact ⟨s,Subtype.ext hs⟩

/-- The SAME entire section equivalence retains the literal original normalized function-field coefficient. -/
theorem wholeSectionsEquiv_apply (s : Γ(projectiveLine d q t n,⊤)) :
    letI := p.stalkAlgebra (genericPoint X)
    ((wholeSectionsEquiv d q p hp t n s :
      (FiniteProjectiveNativeFieldModels.model q p hp).sections (fun c => (n c : ℤ))) : X.functionField) =
        coefficient d q t n s := rfl

/-- EVERY inverse-realized actual original whole section has its literal prescribed model coefficient. -/
theorem coefficient_wholeSectionsEquiv_symm :
    letI := p.stalkAlgebra (genericPoint X)
    ∀ g : (FiniteProjectiveNativeFieldModels.model q p hp).sections (fun c => (n c : ℤ)),
      coefficient d q t n ((wholeSectionsEquiv d q p hp t n).symm g) = (g : X.functionField) := by
  let := p.stalkAlgebra (genericPoint X)
  intro g
  exact congrArg Subtype.val ((wholeSectionsEquiv d q p hp t n).apply_symm_apply g)

end EnvelopeProperty.OriginalProjectiveWholeTensorModelSections
