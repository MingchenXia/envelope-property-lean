import EnvelopeProperty.AlgGeom.SeshadriAmplenessCriterionSectionIntersections
import EnvelopeProperty.AlgGeom.NativeNumericalNefCone

/-! # Mixed intersections of a nef line with ample lines are nonnegative

Let `p : X ⟶ Spec k` be projective with `dim X ≤ d + 1`, let `N` be an invertible module whose
numerical class is nef (nonnegative degree on every closed integral curve), let `A` be ample
and let `F` be coherent. We prove `Δ_N Δ_A^d χ(X, F) ≥ 0`
(`mixedEulerDifference_nef_ample_nonneg`), i.e. `N · A^d · F ≥ 0`, with no reducedness or
irreducibility assumption on `X`.

The proof is by induction on `d`, together with the integral case with an invertible
coefficient. A coherent prime filtration reduces to integral closed subschemes; on an
integral curve the value is the degree of `N`; in higher dimension a nonzero section of a
positive power of `A` cuts down the dimension.

We also show that nefness is preserved by restriction to closed subschemes
(`lineClass_pullback_mem_nefCone_of_closed`). This is the mixed nonnegativity input of the
proof of Kleiman's theorem (Lazarsfeld, *Positivity I*, Theorem 1.4.9).

Blueprint: `seshadri-ampleness-criterion-nef-ample-mixed-intersections.tex`.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Scheme.Modules TopologicalSpace
universe u
namespace EnvelopeProperty.SeshadriAmplenessCriterionNefAmpleMixedIntersections
open SeshadriAmplenessCriterion NativeClosedCurveDegrees CurveLineDegrees
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

private theorem projective_closed_comp {Z Y W : Scheme.{u}}
    (i : Z ⟶ Y) [IsClosedImmersion i] (p : Y ⟶ W) [IsProjective p] :
    IsProjective (i ≫ p) := by
  constructor
  obtain ⟨E, hE, hEF, j, hj, hjp⟩ := IsProjective.exists_isClosedImmersion (f := p)
  let : IsClosedImmersion j := hj
  exact ⟨E, hE, hEF, i ≫ j, inferInstance,
    (Category.assoc i j E.projectiveBundleπ).trans
      (congrArg (fun q => i ≫ q) hjp)⟩

/-- Nefness restricts along closed immersions: a closed integral curve of `Y` is a closed
integral curve of `X`, and the pullback-composition isomorphism identifies the degrees. -/
theorem lineClass_pullback_mem_nefCone_of_closed
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsProjective p]
    (N : X.Modules) (hN : IsInvertible N)
    (hnef : NativeRealNumericalClasses.lineClass p N hN ∈
      NativeRealNumericalClasses.nefCone p)
    (i : Y ⟶ X) [IsClosedImmersion i] [IsProjective (i ≫ p)] :
    NativeRealNumericalClasses.lineClass (i ≫ p) ((Scheme.Modules.pullback i).obj N)
      (hN.pullback i) ∈ NativeRealNumericalClasses.nefCone (i ≫ p) := by
  apply (NativeRealNumericalClasses.lineClass_mem_nefCone_iff
    (i ≫ p) ((Scheme.Modules.pullback i).obj N) (hN.pullback i)).mpr
  intro C
  let : IsIntegral C.carrier := C.integral
  let : IsClosedImmersion C.inclusion := C.closed
  let C' : ClosedIntegralCurve X :=
    ⟨C.carrier, C.integral, C.inclusion ≫ i, inferInstance, C.dimension⟩
  let : IsProper (C.structureMorphism (i ≫ p)) := (C.projectiveFactorization (i ≫ p)).isProper
  let : CompactSpace C.carrier :=
    QuasiCompact.compactSpace_of_compactSpace (C.structureMorphism (i ≫ p))
  have h := (NativeRealNumericalClasses.lineClass_mem_nefCone_iff p N hN).mp hnef C'
  change (0 : ℝ) ≤ (degree ((C.inclusion ≫ i) ≫ p)
    ((Scheme.Modules.pullback (C.inclusion ≫ i)).obj N) : ℝ) at h
  rw [Category.assoc, degree_eq_of_iso _ ((pullbackComp C.inclusion i).app N).symm] at h
  exact h

/-- The empty closed subset of a nonempty (here: integral) scheme is proper. -/
theorem closeds_bot_ne_top_of_isIntegral (Z : Scheme.{u}) [IsIntegral Z] :
    (⊥ : Closeds Z) ≠ ⊤ := by
  intro heq
  have hx : genericPoint Z ∈ ((⊥ : Closeds Z) : Set Z) := by
    rw [heq, TopologicalSpace.Closeds.coe_top]
    exact Set.mem_univ _
  simp at hx

private theorem unit_finiteType (X : Scheme.{u}) : (unitObj X).IsFiniteType := by
  let : (unitObj X).IsFinitePresentation := isInvertible_unit.isFinitePresentation
  exact SheafOfModules.instIsFiniteTypeOfIsFinitePresentation (R := X.ringCatSheaf) (unitObj X)

private theorem integral_curve_nef_nonneg
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    [CompactSpace X] [X.IsSeparated]
    (p : X ⟶ Spec (.of k)) [IsProjective p]
    (hdim : topologicalKrullDim X ≤ (1 : ℕ)) (N : X.Modules) (hN : IsInvertible N)
    (hnef : NativeRealNumericalClasses.lineClass p N hN ∈
      NativeRealNumericalClasses.nefCone p)
    (T : X.Modules) (hT : IsInvertible T) :
    0 ≤ mixedEulerDifference p [N] T := by
  have hls : ∀ L ∈ [N], IsInvertible L := by simpa using hN
  rw [mixedEulerDifference_eq_unit_of_dimension_le p 1 hdim [N] (by simp) hls T hT]
  let : (unitObj X).IsQuasicoherent := isInvertible_unit.isQuasicoherent
  let : (unitObj X).IsFiniteType := unit_finiteType X
  by_cases hzero : topologicalKrullDim X ≤ (0 : ℕ)
  · exact (mixedEulerDifference_eq_zero_of_dimension_le 0 p hzero [N] (by simp) hls
      (unitObj X)).ge
  · have hdimOne : topologicalKrullDim X = 1 := by
      apply le_antisymm (hdim.trans_eq Nat.cast_one)
      apply le_of_not_gt
      intro hlt
      apply hzero
      exact ENat.WithBot.lt_add_one_iff.mp (by simpa only [Nat.cast_zero, zero_add] using hlt)
    let C : ClosedIntegralCurve X := ⟨X, inferInstance, 𝟙 X, inferInstance, hdimOne⟩
    have h := (NativeRealNumericalClasses.lineClass_mem_nefCone_iff p N hN).mp hnef C
    change (0 : ℝ) ≤ (degree (𝟙 X ≫ p) ((Scheme.Modules.pullback (𝟙 X)).obj N) : ℝ) at h
    rw [Category.id_comp, degree_eq_of_iso p ((pullbackId X).app N)] at h
    rw [mixedEulerDifference_singleton_eq_degree]
    exact_mod_cast h

private theorem coherent_of_integral_nonneg
    {k : Type u} [Field k] (d : ℕ)
    (H : ∀ {Z : Scheme.{u}} [IsIntegral Z] [CompactSpace Z] [Z.IsSeparated]
      (q : Z ⟶ Spec (.of k)) [IsProjective q] (_ : topologicalKrullDim Z ≤ (d + 1 : ℕ))
      (M : Z.Modules) (hM : IsInvertible M)
      (_ : NativeRealNumericalClasses.lineClass q M hM ∈ NativeRealNumericalClasses.nefCone q)
      (B : Z.Modules) (_ : SchemeLineAmpleness.IsAmple q B)
      (T : Z.Modules) (_ : IsInvertible T),
        0 ≤ mixedEulerDifference q (M :: List.replicate d B) T)
    {X : Scheme.{u}} [CompactSpace X] [X.IsSeparated]
    (p : X ⟶ Spec (.of k)) [IsProjective p]
    (hdim : topologicalKrullDim X ≤ (d + 1 : ℕ)) (N : X.Modules) (hN : IsInvertible N)
    (hnef : NativeRealNumericalClasses.lineClass p N hN ∈
      NativeRealNumericalClasses.nefCone p)
    (A : X.Modules) (hA : SchemeLineAmpleness.IsAmple p A)
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    0 ≤ mixedEulerDifference p (N :: List.replicate d A) F := by
  have hls : ∀ L ∈ N :: List.replicate d A, IsInvertible L := by
    intro L hL
    rcases List.mem_cons.mp hL with rfl | hL
    · exact hN
    · obtain ⟨_, rfl⟩ := List.mem_replicate.mp hL
      exact hA.isInvertible
  obtain ⟨n, hfil⟩ := exists_finite_coherent_primeFiltration p F
  induction hfil with
  | zero M hM => exact (mixedEulerDifference_eq_zero_of_isZero p _ hls M hM).ge
  | iso e _ ih => exact le_of_le_of_eq ih (mixedEulerDifference_eq_of_iso p _ e)
  | extension S hS hQ₁ hQ₂ hQ₃ hF₁ hF₂ hF₃ eta T hT e _ ih =>
    let : S.X₁.IsQuasicoherent := hQ₁
    let : S.X₂.IsQuasicoherent := hQ₂
    let : S.X₃.IsQuasicoherent := hQ₃
    let : S.X₁.IsFiniteType := hF₁
    let : S.X₂.IsFiniteType := hF₂
    let : S.X₃.IsFiniteType := hF₃
    let I := Scheme.IdealSheafData.vanishingIdeal
      (⟨closure ({eta} : Set X), isClosed_closure⟩ : Closeds X)
    let Z := I.subscheme
    let i : Z ⟶ X := I.subschemeι
    let : IsIntegral Z := SchemePointClosureIntegral.isIntegral_pointClosure eta
    let : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace i
    let : Z.IsSeparated := ⟨by
      have hsep : IsSeparated (i ≫ terminal.from X) := inferInstance
      simpa only [terminal.comp_from] using hsep⟩
    let : IsProjective (i ≫ p) := projective_closed_comp i p
    let Ni := (Scheme.Modules.pullback i).obj N
    let Ai := (Scheme.Modules.pullback i).obj A
    have hNi : IsInvertible Ni := hN.pullback i
    have hnefi := lineClass_pullback_mem_nefCone_of_closed p N hN hnef i
    have hAi : SchemeLineAmpleness.IsAmple (i ≫ p) Ai := isAmple_closedPullback i p A hA
    have hdimZ := IntegralSchemeDimension.topologicalKrullDim_le_of_isIntegralHom i (d + 1) hdim
    have hZ := H (i ≫ p) hdimZ Ni hNi hnefi Ai hAi T hT
    let : T.IsQuasicoherent := hT.isQuasicoherent
    have hpush := mixedEulerDifference_pushforward p i (N :: List.replicate d A) hls T
    simp only [List.map_cons, List.map_replicate] at hpush
    have hquotient : 0 ≤ mixedEulerDifference p (N :: List.replicate d A) S.X₃ := by
      rw [mixedEulerDifference_eq_of_iso p _ e, hpush]
      exact hZ
    rw [mixedEulerDifference_add p _ hls S hS]
    exact add_nonneg ih hquotient

/-- The cutting step: on an integral scheme of dimension at most `d + 2`, the nonnegativity
of `Δ_K Δ_C^{d+1} χ(Z, T)` follows from the statement with `d` ample entries on the zero
scheme of a section of a power of `C`. -/
private theorem integral_cut_nef_nonneg
    {k : Type u} [Field k] (d : ℕ)
    (ih : ∀ {Y : Scheme.{u}} [CompactSpace Y] [Y.IsSeparated]
      (q : Y ⟶ Spec (.of k)) [IsProjective q] (_ : topologicalKrullDim Y ≤ (d + 1 : ℕ))
      (M : Y.Modules) (hM : IsInvertible M)
      (_ : NativeRealNumericalClasses.lineClass q M hM ∈ NativeRealNumericalClasses.nefCone q)
      (B : Y.Modules) (_ : SchemeLineAmpleness.IsAmple q B)
      (G : Y.Modules) [G.IsQuasicoherent] [G.IsFiniteType],
        0 ≤ mixedEulerDifference q (M :: List.replicate d B) G)
    {Z : Scheme.{u}} [IsIntegral Z] [CompactSpace Z] [Z.IsSeparated]
    (r : Z ⟶ Spec (.of k)) [IsProjective r]
    (hdimZ : topologicalKrullDim Z ≤ (d + 1 + 1 : ℕ))
    (K : Z.Modules) (hK : IsInvertible K)
    (hnefK : NativeRealNumericalClasses.lineClass r K hK ∈
      NativeRealNumericalClasses.nefCone r)
    (C : Z.Modules) (hC : SchemeLineAmpleness.IsAmple r C)
    (T : Z.Modules) (hT : IsInvertible T) :
    0 ≤ mixedEulerDifference r (K :: List.replicate (d + 1) C) T := by
  have hls : ∀ L ∈ K :: List.replicate d C, IsInvertible L := by
    intro L hL
    rcases List.mem_cons.mp hL with rfl | hL
    · exact hK
    · obtain ⟨_, rfl⟩ := List.mem_replicate.mp hL
      exact hC.1
  let : T.IsQuasicoherent := hT.isQuasicoherent
  let : T.IsFinitePresentation := hT.isFinitePresentation
  let : T.IsFiniteType :=
    SheafOfModules.instIsFiniteTypeOfIsFinitePresentation (R := Z.ringCatSheaf) T
  obtain ⟨s, hs, a, ha, _⟩ :=
    ProjectiveAmpleSectionContainingClosedSubset.exists_nonzero_power_section_containing_closed
      r ⊥ (closeds_bot_ne_top_of_isIntegral Z) C hC
  let P := CanonicalGeometry.bundleTensorPower C s
  let hP : IsInvertible P := TensorPowerBaseIdealGrading.tensorPower_isInvertible hC.1 s
  let D := LineSectionZeroIdeal.zeroIdeal P hP a
  let i := D.subschemeι
  let : CompactSpace D.subscheme := QuasiCompact.compactSpace_of_compactSpace i
  let : D.subscheme.IsSeparated := ⟨by
    have hsep : IsSeparated (i ≫ terminal.from Z) := inferInstance
    simpa only [terminal.comp_from] using hsep⟩
  let : IsProjective (i ≫ r) := projective_closed_comp i r
  let Ki := (Scheme.Modules.pullback i).obj K
  let Ci := (Scheme.Modules.pullback i).obj C
  let Ti := (Scheme.Modules.pullback i).obj (T ⊗ P)
  have hKi : IsInvertible Ki := hK.pullback i
  have hnefi := lineClass_pullback_mem_nefCone_of_closed r K hK hnefK i
  have hCi : SchemeLineAmpleness.IsAmple (i ≫ r) Ci := isAmple_closedPullback i r C hC
  have hTP : IsInvertible (T ⊗ P) :=
    (hT.tensorObj hP).of_iso (ModularCurves.monoidalTensorObjIso T P)
  have hTi : IsInvertible Ti := hTP.pullback i
  let : Ti.IsQuasicoherent := hTi.isQuasicoherent
  let : Ti.IsFinitePresentation := hTi.isFinitePresentation
  let : Ti.IsFiniteType :=
    SheafOfModules.instIsFiniteTypeOfIsFinitePresentation (R := D.subscheme.ringCatSheaf) Ti
  have hdimD : topologicalKrullDim D.subscheme ≤ (d + 1 : ℕ) :=
    sectionZero_dimension_drop (d + 1) hdimZ P hP a ha
  have hD := ih (i ≫ r) hdimD Ki hKi hnefi Ci hCi Ti
  have hcut := mixedEulerDifference_sectionDifference r P hP a ha
    (K :: List.replicate d C) hls T hT
  simp only [List.map_cons, List.map_replicate] at hcut
  rw [mixedEulerDifference_tensorPower_cons r (d + 1 + 1) hdimZ C hC.1
    (K :: List.replicate d C) (by simp) hls T s,
    mixedEulerDifference_swap r C K (List.replicate d C) T] at hcut
  have hmul : 0 ≤ (s : ℤ) * mixedEulerDifference r
      (K :: C :: List.replicate d C) T := by
    rw [hcut]
    exact hD
  have hsZ : (0 : ℤ) < s := by exact_mod_cast hs
  simpa only [List.replicate_succ] using (mul_nonneg_iff_of_pos_left hsZ).mp hmul

/-- **Nef times ample powers is nonnegative.** On a projective scheme of dimension at most
`d + 1`, a nef invertible `N`, an ample `A` and a coherent `F` satisfy
`Δ_N Δ_A^d χ(X, F) ≥ 0`. The scheme may be reducible, nonreduced or empty. -/
theorem mixedEulerDifference_nef_ample_nonneg
    {k : Type u} [Field k] (d : ℕ)
    {X : Scheme.{u}} [CompactSpace X] [X.IsSeparated]
    (p : X ⟶ Spec (.of k)) [IsProjective p]
    (hdim : topologicalKrullDim X ≤ (d + 1 : ℕ)) (N : X.Modules) (hN : IsInvertible N)
    (hnef : NativeRealNumericalClasses.lineClass p N hN ∈
      NativeRealNumericalClasses.nefCone p)
    (A : X.Modules) (hA : SchemeLineAmpleness.IsAmple p A)
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    0 ≤ mixedEulerDifference p (N :: List.replicate d A) F := by
  have all : ∀ d : ℕ, ∀ {Y : Scheme.{u}} [CompactSpace Y] [Y.IsSeparated]
      (q : Y ⟶ Spec (.of k)) [IsProjective q] (_ : topologicalKrullDim Y ≤ (d + 1 : ℕ))
      (M : Y.Modules) (hM : IsInvertible M)
      (_ : NativeRealNumericalClasses.lineClass q M hM ∈ NativeRealNumericalClasses.nefCone q)
      (B : Y.Modules) (_ : SchemeLineAmpleness.IsAmple q B)
      (G : Y.Modules) [G.IsQuasicoherent] [G.IsFiniteType],
        0 ≤ mixedEulerDifference q (M :: List.replicate d B) G := by
    intro d
    induction d with
    | zero =>
      intro Y _ _ q _ hdimY M hM hnefM B hB G _ _
      apply coherent_of_integral_nonneg 0 ?_ q hdimY M hM hnefM B hB G
      intro Z _ _ _ r _ hdimZ K hK hnefK _C _hC T hT
      exact integral_curve_nef_nonneg r hdimZ K hK hnefK T hT
    | succ d ih =>
      intro Y _ _ q _ hdimY M hM hnefM B hB G _ _
      apply coherent_of_integral_nonneg (d + 1) ?_ q hdimY M hM hnefM B hB G
      intro Z _ _ _ r _ hdimZ K hK hnefK C hC T hT
      exact integral_cut_nef_nonneg d ih r hdimZ K hK hnefK C hC T hT
  exact all d p hdim N hN hnef A hA F

end EnvelopeProperty.SeshadriAmplenessCriterionNefAmpleMixedIntersections
