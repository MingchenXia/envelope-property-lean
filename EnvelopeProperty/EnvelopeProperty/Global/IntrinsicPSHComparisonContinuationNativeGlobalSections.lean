import EnvelopeProperty.Global.IntrinsicPSHComparisonContinuationNativeCoordinateCoefficients

/-!
# Original full saturated sections are actual native global line sections

Actual inverse frames produce the local sections. Genuine rational-section
injectivity proves compatibility; actual sheaf gluing produces H0. The full
mathematical route is the owned audit `native-global-sections-route.tex`.
-/

open scoped Classical
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace ModularCurves
open EnvelopeProperty.CanonicalGeometry
noncomputable section
universe u
namespace EnvelopeProperty.MultiModel
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  (X : MultiModel k K 1)

private theorem originalDegreeOneCoefficient_mem (i : X.ChartIndex)
    (hi : ∀ c, X.coord c (i c) ≠ 0) (f : X.sections (1 : Fin 1 → ℤ)) :
    (f : K) / X.coord 0 (i 0) ∈ X.chartAlg i := by
  simpa only [chartDenZ, Fin.prod_univ_one, Pi.one_apply, zpow_one] using
    X.div_chartDenZ_mem_chartAlg hi f.property

/-- An ORIGINAL fully saturated coefficient gives an actual local line
section through the true inverse coordinate frame. -/
def nativeRankOneLocalSectionOfOriginal (i : X.ChartIndex)
    (hi : ∀ c, X.coord c (i c) ≠ 0) (j : Fin (X.M 0 + 1)) (hj : X.coord 0 j ≠ 0)
    (f : X.sections (1 : Fin 1 → ℤ)) :
    Γ(X.nativeRankOneCoordinateLine j, X.nativeRankOneCoordinateOpen (i 0)) :=
  (localFrameCoefficients (X.nativeRankOneCoordinateLineOverFrame i hi j hj)).symm
    ((X.nativeRankOneOriginalSectionsIso i hi).hom
      ⟨(f : K) / X.coord 0 (i 0), originalDegreeOneCoefficient_mem X i hi f⟩)

/-- Its actual whole local frame coefficient is the literal original f/c_i. -/
theorem nativeRankOneLocalSectionOfOriginal_coefficient (i : X.ChartIndex)
    (hi : ∀ c, X.coord c (i c) ≠ 0) (j : Fin (X.M 0 + 1)) (hj : X.coord 0 j ≠ 0)
    (f : X.sections (1 : Fin 1 → ℤ)) :
    localFrameCoefficients (X.nativeRankOneCoordinateLineOverFrame i hi j hj)
      (X.nativeRankOneLocalSectionOfOriginal i hi j hj f) =
      (X.nativeRankOneOriginalSectionsIso i hi).hom
        ⟨(f : K) / X.coord 0 (i 0), originalDegreeOneCoefficient_mem X i hi f⟩ :=
  (localFrameCoefficients (X.nativeRankOneCoordinateLineOverFrame i hi j hj)).apply_symm_apply _

/-- Every such actual local section has the SAME true intrinsic rational
coefficient e(f/c_j), independently of the original nonzero chart. -/
theorem nativeRankOneLocalSectionOfOriginal_ratio (i : X.ChartIndex)
    (hi : ∀ c, X.coord c (i c) ≠ 0) (j : Fin (X.M 0 + 1)) (hj : X.coord 0 j ≠ 0)
    (f : X.sections (1 : Fin 1 → ℤ)) :
    letI := X.nativeRankOneCoordinateOpen_nonempty i hi
    sectionRatio (X.nativeRankOneCoordinateLine j) (X.nativeRankOneCoordinateLine_isInvertible j hj)
      (X.nativeRankOneCoordinatePoleSection j) (X.nativeRankOneCoordinatePoleSection_ne_zero j hj)
      (X.nativeRankOneCoordinateOpen (i 0))
      (X.nativeRankOneLocalSectionOfOriginal i hi j hj f) =
      X.nativeRankOneFunctionFieldEquiv i hi ((f : K) / X.coord 0 j) := by
  have := X.nativeRankOneCoordinateOpen_nonempty i hi
  rw [X.nativeRankOneCoordinateSectionRatio_formula i hi j hj _,
    X.nativeRankOneLocalSectionOfOriginal_coefficient i hi j hj f,
    ← X.nativeRankOneFunctionFieldEquiv_coefficient i hi _, ← map_div₀]
  congr 1
  field_simp [hj, hi 0]

private theorem originalNonzeroCoordinateCover :
    (⊤ : X.nativeRankOneScheme.Opens) ≤
      ⨆ i : {i : X.ChartIndex // ∀ c, X.coord c (i c) ≠ 0},
        X.nativeRankOneCoordinateOpen (i.val 0) := by
  intro y _
  have hy : y ∈ ⨆ t : Fin (X.M 0 + 1), X.nativeRankOneCoordinateOpen t := by
    rw [X.nativeRankOne_iSup_coordinateOpen]
    trivial
  obtain ⟨t, ht⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
  have ht0 : X.coord 0 t ≠ 0 := by
    intro hz
    have he : X.coordElem ⟨0, t⟩ = 0 := Subtype.ext (by simp [hz])
    change X.coordElem ⟨0, t⟩ ∉ y.asHomogeneousIdeal at ht
    exact ht (he ▸ zero_mem y.asHomogeneousIdeal.toIdeal)
  let i : X.ChartIndex := fun c => (Subsingleton.elim (0 : Fin 1) c) ▸ t
  have hi : ∀ c, X.coord c (i c) ≠ 0 := by
    intro c
    have hc : c = 0 := Subsingleton.elim _ _
    subst c
    exact ht0
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i, hi⟩, ht⟩

/-- Actual sheaf gluing produces a genuine native GLOBAL section from every
ORIGINAL fully saturated degree-one coefficient, with every exact original
coordinate restriction. No gluing/matching premise is supplied. -/
theorem nativeRankOne_existsGlobalSectionOfOriginal (j : Fin (X.M 0 + 1))
    (hj : X.coord 0 j ≠ 0) (f : X.sections (1 : Fin 1 → ℤ)) :
    ∃ s : Γ(X.nativeRankOneCoordinateLine j, ⊤), ∀ (i : X.ChartIndex)
      (hi : ∀ c, X.coord c (i c) ≠ 0),
      (X.nativeRankOneCoordinateLine j).presheaf.map
        (homOfLE (le_top : X.nativeRankOneCoordinateOpen (i 0) ≤ ⊤)).op s =
        X.nativeRankOneLocalSectionOfOriginal i hi j hj f := by
  let M := X.nativeRankOneCoordinateLine j
  let V := {i : X.ChartIndex // ∀ c, X.coord c (i c) ≠ 0}
  let U : V → X.nativeRankOneScheme.Opens := fun i => X.nativeRankOneCoordinateOpen (i.val 0)
  let s (i : V) := X.nativeRankOneLocalSectionOfOriginal i.val i.property j hj f
  have hcpt : ∀ i l : V,
      M.presheaf.map (TopologicalSpace.Opens.infLELeft (U i) (U l)).op (s i) =
        M.presheaf.map (TopologicalSpace.Opens.infLERight (U i) (U l)).op (s l) := by
    intro i l
    have : Nonempty (U i) := X.nativeRankOneCoordinateOpen_nonempty i.val i.property
    have : Nonempty (U l) := X.nativeRankOneCoordinateOpen_nonempty l.val l.property
    have : Nonempty (U i ⊓ U l : X.nativeRankOneScheme.Opens) := ⟨⟨genericPoint X.nativeRankOneScheme,
      X.nativeRankOneGenericPoint_mem_coordinateOpen i.val i.property,
      X.nativeRankOneGenericPoint_mem_coordinateOpen l.val l.property⟩⟩
    apply sectionRatio_injective M (X.nativeRankOneCoordinateLine_isInvertible j hj)
      (X.nativeRankOneCoordinatePoleSection j) (X.nativeRankOneCoordinatePoleSection_ne_zero j hj)
      (U i ⊓ U l)
    have hleft : TopologicalSpace.Opens.infLELeft (U i) (U l) =
        homOfLE (inf_le_left : U i ⊓ U l ≤ U i) := Subsingleton.elim _ _
    have hright : TopologicalSpace.Opens.infLERight (U i) (U l) =
        homOfLE (inf_le_right : U i ⊓ U l ≤ U l) := Subsingleton.elim _ _
    rw [hleft, hright, sectionRatio_restrict, sectionRatio_restrict,
      X.nativeRankOneLocalSectionOfOriginal_ratio i.val i.property j hj f,
      X.nativeRankOneLocalSectionOfOriginal_ratio l.val l.property j hj f,
      X.nativeRankOneFunctionFieldEquiv_independent i.val l.val i.property l.property]
  obtain ⟨t, ht, _⟩ := TopCat.Sheaf.existsUnique_gluing' ⟨M.presheaf, M.isSheaf⟩ U ⊤
    (fun _ => homOfLE le_top) (originalNonzeroCoordinateCover X) s hcpt
  exact ⟨t, fun i hi => ht ⟨i, hi⟩⟩

/-- The genuine native global section constructed by actual sheaf gluing. -/
def nativeRankOneGlobalSectionOfOriginal (j : Fin (X.M 0 + 1))
    (hj : X.coord 0 j ≠ 0) (f : X.sections (1 : Fin 1 → ℤ)) :
    Γ(X.nativeRankOneCoordinateLine j, ⊤) :=
  (X.nativeRankOne_existsGlobalSectionOfOriginal j hj f).choose

/-- Every whole original coordinate restriction of the actual glued section
is precisely the actual inverse-frame section of f/c_i. -/
theorem nativeRankOneGlobalSectionOfOriginal_restrict (i : X.ChartIndex)
    (hi : ∀ c, X.coord c (i c) ≠ 0) (j : Fin (X.M 0 + 1)) (hj : X.coord 0 j ≠ 0)
    (f : X.sections (1 : Fin 1 → ℤ)) :
    (X.nativeRankOneCoordinateLine j).presheaf.map
      (homOfLE (le_top : X.nativeRankOneCoordinateOpen (i 0) ≤ ⊤)).op
      (X.nativeRankOneGlobalSectionOfOriginal j hj f) =
      X.nativeRankOneLocalSectionOfOriginal i hi j hj f :=
  (X.nativeRankOne_existsGlobalSectionOfOriginal j hj f).choose_spec i hi

/-- The true global coefficient of the actual glued native section is the
SAME ORIGINAL saturated coefficient. -/
theorem nativeRankOneGlobalSectionOfOriginal_coefficient (i : X.ChartIndex)
    (hi : ∀ c, X.coord c (i c) ≠ 0) (j : Fin (X.M 0 + 1)) (hj : X.coord 0 j ≠ 0)
    (f : X.sections (1 : Fin 1 → ℤ)) :
    X.nativeRankOneGlobalSectionCoefficient i hi j hj
      (X.nativeRankOneGlobalSectionOfOriginal j hj f) = (f : K) := by
  have := X.nativeRankOneCoordinateOpen_nonempty i hi
  have hq := sectionRatio_restrict (X.nativeRankOneCoordinateLine j)
    (X.nativeRankOneCoordinateLine_isInvertible j hj)
    (X.nativeRankOneCoordinatePoleSection j) (X.nativeRankOneCoordinatePoleSection_ne_zero j hj)
    (le_top : X.nativeRankOneCoordinateOpen (i 0) ≤ ⊤)
    (X.nativeRankOneGlobalSectionOfOriginal j hj f)
  rw [X.nativeRankOneGlobalSectionOfOriginal_restrict i hi j hj f,
    X.nativeRankOneLocalSectionOfOriginal_ratio i hi j hj f] at hq
  unfold nativeRankOneGlobalSectionCoefficient
  rw [← hq, RingEquiv.symm_apply_apply]
  exact (mul_comm _ _).trans (div_mul_cancel₀ _ hj)

/-- Actual native H0 is bijective with the ORIGINAL full saturated degree-one
section space. Its inverse is produced by actual sheaf gluing. -/
def nativeRankOneH0OriginalSectionsEquiv (i : X.ChartIndex)
    (hi : ∀ c, X.coord c (i c) ≠ 0) (j : Fin (X.M 0 + 1)) (hj : X.coord 0 j ≠ 0) :
    Γ(X.nativeRankOneCoordinateLine j, ⊤) ≃ X.sections (1 : Fin 1 → ℤ) :=
  Equiv.ofBijective
    (fun s => ⟨X.nativeRankOneGlobalSectionCoefficient i hi j hj s,
      X.nativeRankOneGlobalSectionCoefficient_mem_sections i hi j hj s⟩)
    ⟨fun _ _ h => X.nativeRankOneGlobalSectionCoefficient_injective i hi j hj
      (congrArg Subtype.val h), fun f =>
      ⟨X.nativeRankOneGlobalSectionOfOriginal j hj f,
        Subtype.ext (X.nativeRankOneGlobalSectionOfOriginal_coefficient i hi j hj f)⟩⟩

/-- The bijection's forward map is the literal original rational coefficient. -/
theorem nativeRankOneH0OriginalSectionsEquiv_apply (i : X.ChartIndex)
    (hi : ∀ c, X.coord c (i c) ≠ 0) (j : Fin (X.M 0 + 1)) (hj : X.coord 0 j ≠ 0)
    (s : Γ(X.nativeRankOneCoordinateLine j, ⊤)) :
    (X.nativeRankOneH0OriginalSectionsEquiv i hi j hj s : K) =
      X.nativeRankOneGlobalSectionCoefficient i hi j hj s := rfl

/-- Its actual inverse is exactly the section obtained by genuine sheaf gluing. -/
theorem nativeRankOneH0OriginalSectionsEquiv_symm (i : X.ChartIndex)
    (hi : ∀ c, X.coord c (i c) ≠ 0) (j : Fin (X.M 0 + 1)) (hj : X.coord 0 j ≠ 0)
    (f : X.sections (1 : Fin 1 → ℤ)) :
    (X.nativeRankOneH0OriginalSectionsEquiv i hi j hj).symm f =
      X.nativeRankOneGlobalSectionOfOriginal j hj f := by
  apply (X.nativeRankOneH0OriginalSectionsEquiv i hi j hj).injective
  apply Subtype.ext
  exact (congrArg Subtype.val ((X.nativeRankOneH0OriginalSectionsEquiv i hi j hj).apply_symm_apply f)).trans
    (X.nativeRankOneGlobalSectionOfOriginal_coefficient i hi j hj f).symm

end EnvelopeProperty.MultiModel

#check @EnvelopeProperty.MultiModel.nativeRankOneLocalSectionOfOriginal
#print axioms EnvelopeProperty.MultiModel.nativeRankOneLocalSectionOfOriginal
#check @EnvelopeProperty.MultiModel.nativeRankOneLocalSectionOfOriginal_coefficient
#print axioms EnvelopeProperty.MultiModel.nativeRankOneLocalSectionOfOriginal_coefficient
#check @EnvelopeProperty.MultiModel.nativeRankOneLocalSectionOfOriginal_ratio
#print axioms EnvelopeProperty.MultiModel.nativeRankOneLocalSectionOfOriginal_ratio
#check @EnvelopeProperty.MultiModel.nativeRankOne_existsGlobalSectionOfOriginal
#print axioms EnvelopeProperty.MultiModel.nativeRankOne_existsGlobalSectionOfOriginal
#check @EnvelopeProperty.MultiModel.nativeRankOneGlobalSectionOfOriginal
#print axioms EnvelopeProperty.MultiModel.nativeRankOneGlobalSectionOfOriginal
#check @EnvelopeProperty.MultiModel.nativeRankOneGlobalSectionOfOriginal_restrict
#print axioms EnvelopeProperty.MultiModel.nativeRankOneGlobalSectionOfOriginal_restrict
#check @EnvelopeProperty.MultiModel.nativeRankOneGlobalSectionOfOriginal_coefficient
#print axioms EnvelopeProperty.MultiModel.nativeRankOneGlobalSectionOfOriginal_coefficient
#check @EnvelopeProperty.MultiModel.nativeRankOneH0OriginalSectionsEquiv
#print axioms EnvelopeProperty.MultiModel.nativeRankOneH0OriginalSectionsEquiv
#check @EnvelopeProperty.MultiModel.nativeRankOneH0OriginalSectionsEquiv_apply
#print axioms EnvelopeProperty.MultiModel.nativeRankOneH0OriginalSectionsEquiv_apply
#check @EnvelopeProperty.MultiModel.nativeRankOneH0OriginalSectionsEquiv_symm
#print axioms EnvelopeProperty.MultiModel.nativeRankOneH0OriginalSectionsEquiv_symm
