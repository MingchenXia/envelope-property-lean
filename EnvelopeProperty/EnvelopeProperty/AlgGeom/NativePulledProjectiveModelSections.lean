import EnvelopeProperty.AlgGeom.NativePulledProjectiveLineFrames
import EnvelopeProperty.AlgGeom.ModelSectionsFromChartFractions

/-! # ALL actual original global pulled-line sections are the WHOLE genuine model section space -/
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial Opposite
open DeJongAlterations Scheme.Modules
open scoped Classical NNReal Topology
noncomputable section
universe u
namespace EnvelopeProperty.NativePulledProjectiveModelSections
open Berkovich CanonicalGeometry NativePulledProjectiveLineFrames
open ProjectiveChartFunctionFieldGeneration ProjectiveFixedNativeModelCharts
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {m : ℕ} {X : Scheme.{u}} [IsIntegral X]
  (f : X ⟶ projectiveSpace k m) (i t : Fin (m + 1)) (d : ℕ)
  [IsClosedImmersion f] [Nonempty (f ⁻¹ᵁ coordinateOpen (R := k) i)]

/-- The literal native generic coefficient of EVERY actual original global section,
in the actual original pivot frame of the SAME whole original pulled line. -/
def coefficient (s : Γ(line f t d,⊤)) : X.functionField :=
  X.germToFunctionField (f ⁻¹ᵁ coordinateOpen (R := k) i) (chartCoefficient f t d i s)

/-- The actual original frame coefficient is exactly its genuine canonical native
section ratio, with the actual original pivot-power normalizer derived internally. -/
theorem coefficient_eq_sectionRatio (s : Γ(line f t d,⊤)) :
    coefficient f i t d s = sectionRatio (line f t d) (line_isInvertible f t d)
      (coordinatePowerSection f t d i) (coordinatePowerSection_ne_zero f t d i) ⊤ s := by
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  let U : X.affineOpens := ⟨f ⁻¹ᵁ coordinateOpen (R := k) i,(coordinateOpen_isAffineOpen i).preimage f⟩
  have h := sectionRatio_localTrivializationCoefficient (line f t d) (line_isInvertible f t d)
    (coordinatePowerSection f t d i) (coordinatePowerSection_ne_zero f t d i)
    U (chartFrame f t d i) s
  change sectionRatio (line f t d) (line_isInvertible f t d)
    (coordinatePowerSection f t d i) (coordinatePowerSection_ne_zero f t d i) ⊤ s =
      coefficient f i t d s / X.germToFunctionField U.1
        (chartCoefficient f t d i (coordinatePowerSection f t d i)) at h
  have hden := germ_chartCoefficient_coordinatePowerSection f t d i i
  change X.germToFunctionField U.1 (chartCoefficient f t d i (coordinatePowerSection f t d i)) =
    (coordinate f i i) ^ d at hden
  rw [coordinate_self,one_pow] at hden
  rw [hden,div_one] at h
  exact h.symm

/-- EVERY original regular chart coefficient is exactly the original normalized
function-field coefficient divided by its actual SAME original chart denominator. -/
theorem coefficient_chart_fraction (j : Fin (m + 1))
    [Nonempty (f ⁻¹ᵁ coordinateOpen (R := k) j)] (s : Γ(line f t d,⊤)) :
    coefficient f i t d s / coordinate f i j ^ d =
      X.germToFunctionField (f ⁻¹ᵁ coordinateOpen (R := k) j) (chartCoefficient f t d j s) := by
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  let U : X.affineOpens := ⟨f ⁻¹ᵁ coordinateOpen (R := k) j,(coordinateOpen_isAffineOpen j).preimage f⟩
  have h := sectionRatio_localTrivializationCoefficient (line f t d) (line_isInvertible f t d)
    (coordinatePowerSection f t d i) (coordinatePowerSection_ne_zero f t d i)
    U (chartFrame f t d j) s
  rw [← coefficient_eq_sectionRatio f i t d s] at h
  change coefficient f i t d s = X.germToFunctionField U.1 (chartCoefficient f t d j s) /
    X.germToFunctionField U.1 (chartCoefficient f t d j (coordinatePowerSection f t d i)) at h
  have hden := germ_chartCoefficient_coordinatePowerSection f t d j i
  change X.germToFunctionField U.1 (chartCoefficient f t d j (coordinatePowerSection f t d i)) =
    (coordinate f j i) ^ d at hden
  have hinv : coordinate f j i = (coordinate f i j)⁻¹ := by
    rw [← ProjectiveChartGenericTransitions.coordinate_div f i j i,coordinate_self,one_div]
  rw [hden,hinv,inv_pow,div_inv_eq_mul] at h
  rw [h,mul_div_cancel_right₀ _ (pow_ne_zero d (ProjectiveChartGenericTransitions.coordinate_pivot_ne_zero f i j))]

private theorem chartDenZ_const (j : Fin (m + 1)) :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    (fullFieldModel f i).chartDenZ (fun _ => j) (fun _ => (d : ℤ)) = coordinate f i j ^ d := by
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  rw [MultiModel.chartDenZ,Fin.prod_univ_one]
  exact zpow_natCast _ _

/-- EVERY whole actual original global section gives a genuine model section;
no ambient homogeneous form or desired section-realization premise is required. -/
theorem coefficient_mem_sections (s : Γ(line f t d,⊤)) :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    coefficient f i t d s ∈ (fullFieldModel f i).sections (fun _ => (d : ℤ)) := by
  change X ⟶ Proj (homogeneousSubmodule (Fin (m + 1)) k) at f
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  let P := fullFieldModel f i
  apply (P.mem_sections_iff_chart_fractions _ _).mpr
  intro a ha
  let j := a 0
  let : Nonempty (f ⁻¹ᵁ coordinateOpen (R := k) j) :=
    (ProjectiveNativeCoordinateChartSupport.coordinate_ne_zero_iff_nonempty f i j).mp (ha 0)
  let := (f ≫ projectiveSpaceStructure k m).sectionsAlgebra (f ⁻¹ᵁ coordinateOpen (R := k) j)
  have he : a = fun _ => j := by
    funext c
    have hc : c = 0 := Subsingleton.elim c 0
    subst c
    rfl
  rw [he,chartDenZ_const f i d j,coefficient_chart_fraction f i t d j s]
  have h := (nativeSectionsEquivModelChartAt f i j (chartCoefficient f t d j s)).property
  rwa [nativeSectionsEquivModelChartAt_apply] at h

/-- The SAME original coefficient map is faithful on the WHOLE original global section space. -/
theorem coefficient_injective : Function.Injective (coefficient f i t d) := by
  intro s v h
  apply sectionRatio_injective (line f t d) (line_isInvertible f t d)
    (coordinatePowerSection f t d i) (coordinatePowerSection_ne_zero f t d i) ⊤
  rw [← coefficient_eq_sectionRatio f i t d s,← coefficient_eq_sectionRatio f i t d v]
  exact h

/-- EVERY genuine model section is realized by an ACTUAL whole original global
section, obtained by original inverse chart algebras, original line frames and actual sheaf gluing. -/
theorem coefficient_surjective :
    let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
    ∀ g : (fullFieldModel f i).sections (fun _ => (d : ℤ)),
      ∃ s : Γ(line f t d,⊤), coefficient f i t d s = (g : X.functionField) := by
  change X ⟶ Proj (homogeneousSubmodule (Fin (m + 1)) k) at f
  let := (f ≫ projectiveSpaceStructure k m).stalkAlgebra (genericPoint X)
  let P := fullFieldModel f i
  let L := line f t d
  let hL := line_isInvertible f t d
  let D := coordinatePowerSection f t d i
  let hD := coordinatePowerSection_ne_zero f t d i
  let J := {j : Fin (m + 1) // Nonempty (f ⁻¹ᵁ coordinateOpen (R := k) j)}
  let U (j : J) : X.Opens := f ⁻¹ᵁ coordinateOpen (R := k) j.val
  let E (j : J) : Γ(X,U j) ≃+* P.chartAlg (fun _ => j.val) := by
    let := j.property
    let := (f ≫ projectiveSpaceStructure k m).sectionsAlgebra (U j)
    exact (nativeSectionsEquivModelChartAt f i j.val).toRingEquiv
  change ∀ g : P.sections (fun _ => (d : ℤ)),
    ∃ s : Γ(line f t d,⊤), coefficient f i t d s = (g : X.functionField)
  intro g
  let G (j : J) : P.chartAlg (fun _ => j.val) := by
    let := j.property
    exact ⟨(g : X.functionField) / P.chartDenZ (fun _ => j.val) (fun _ => (d : ℤ)),
      P.div_chartDenZ_mem_chartAlg
        (fun _ => ProjectiveChartGenericTransitions.coordinate_pivot_ne_zero f i j.val) g.property⟩
  let c (j : J) : Γ(X,U j) := (E j).symm (G j)
  let S (j : J) : Γ(L,U j) :=
    (nativeLocalFrameCoefficient L (U j) (chartFrame f t d j.val)).symm (c j)
  have hcoeff (j : J) :
      letI := j.property
      X.germToFunctionField (U j) (c j) =
      (g : X.functionField) / P.chartDenZ (fun _ => j.val) (fun _ => (d : ℤ)) := by
    let := j.property
    let := (f ≫ projectiveSpaceStructure k m).sectionsAlgebra (U j)
    have he : nativeSectionsEquivModelChartAt f i j.val (c j) = G j :=
      (E j).apply_symm_apply (G j)
    exact (nativeSectionsEquivModelChartAt_apply f i j.val (c j)).symm.trans
      (congrArg Subtype.val he)
  have hratio (j : J) :
      letI := j.property
      sectionRatio L hL D hD (U j) (S j) = (g : X.functionField) := by
    let := j.property
    rw [sectionRatio_nativeFrame_formula L hL D hD (U j) (chartFrame f t d j.val) (S j)]
    have hn : nativeLocalFrameCoefficient L (U j) (chartFrame f t d j.val) (S j) = c j :=
      (nativeLocalFrameCoefficient L (U j) (chartFrame f t d j.val)).apply_symm_apply (c j)
    rw [hn,nativeLocalFrameCoefficient_global L
      ⟨U j,(coordinateOpen_isAffineOpen j.val).preimage f⟩ (chartFrame f t d j.val) D,hcoeff]
    have hden := germ_chartCoefficient_coordinatePowerSection f t d j.val i
    change X.germToFunctionField (U j) (chartCoefficient f t d j.val D) =
      coordinate f j.val i ^ d at hden
    change ((g : X.functionField) / P.chartDenZ (fun _ => j.val) (fun _ => (d : ℤ))) /
      X.germToFunctionField (U j) (chartCoefficient f t d j.val D) = _
    rw [hden,chartDenZ_const f i d j.val]
    have hinv : coordinate f j.val i = (coordinate f i j.val)⁻¹ := by
      rw [← ProjectiveChartGenericTransitions.coordinate_div f i j.val i,coordinate_self,one_div]
    rw [hinv,inv_pow,div_inv_eq_mul,
      div_mul_cancel₀ _ (pow_ne_zero d (ProjectiveChartGenericTransitions.coordinate_pivot_ne_zero f i j.val))]
  have hcover : (⊤ : X.Opens) ≤ iSup U := by
    intro x _
    have hx : f x ∈ ⨆ j : Fin (m + 1),coordinateOpen (R := k) j := by
      rw [iSup_coordinateOpen_eq_top]
      trivial
    obtain ⟨j,hj⟩ := Opens.mem_iSup.mp hx
    exact Opens.mem_iSup.mpr ⟨⟨j,⟨⟨x,hj⟩⟩⟩,hj⟩
  have hcompat (j l : J) : L.presheaf.map (Opens.infLELeft (U j) (U l)).op (S j) =
      L.presheaf.map (Opens.infLERight (U j) (U l)).op (S l) := by
    let := j.property
    let := l.property
    have hj : genericPoint X ∈ U j :=
      ((genericPoint_spec X).mem_open_set_iff (U j).isOpen).mpr (by simpa [U] using j.property)
    have hl : genericPoint X ∈ U l :=
      ((genericPoint_spec X).mem_open_set_iff (U l).isOpen).mpr (by simpa [U] using l.property)
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
  rw [coefficient_eq_sectionRatio f i t d s]
  let z : J := ⟨i,inferInstance⟩
  let := z.property
  have hh := sectionRatio_restrict L hL D hD (le_top : U z ≤ ⊤) s
  rw [hs z] at hh
  exact hh.symm.trans (hratio z)

end EnvelopeProperty.NativePulledProjectiveModelSections
