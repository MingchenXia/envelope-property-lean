import EnvelopeProperty.AlgGeom.SeshadriAmplenessCriterionIntegralAmplenessStep
import EnvelopeProperty.AlgGeom.SeshadriAmplenessCriterionClosedMapDimension
import EnvelopeProperty.AlgGeom.SeshadriAmplenessCriterionDimensionZeroAmpleness
import EnvelopeProperty.AlgGeom.NativeProjectiveDimensionBounds
import EnvelopeProperty.AlgGeom.SeshadriAmplenessCriterionStrataAmpleness
import EnvelopeProperty.AlgGeom.IntegralSchemeDimension

/-!
# Seshadri Ampleness Criterion Nakai

The numerical ampleness criterion for the SAME original invertible module.
All proper-subscheme ampleness induction conclusions and geometric sections,
generators and embeddings are constructed internally from actual closed tests. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace
open Scheme.Modules
universe u
namespace EnvelopeProperty.SeshadriAmplenessCriterion
attribute [local instance] Scheme.Modules.monoidalCategory

/-- Original whole line isomorphisms preserve the actual repeated Euler
difference with every original coefficient module, including degree zero. -/
theorem mixedEulerDifference_replicate_eq_of_iso {k : Type u} [Field k]
    {X : Scheme.{u}} [CompactSpace X] (p : X ⟶ Spec (.of k))
    (d : ℕ) {L M : X.Modules} (e : L ≅ M) (F : X.Modules) :
    mixedEulerDifference p (List.replicate d L) F =
      mixedEulerDifference p (List.replicate d M) F := by
  induction d generalizing F with
  | zero => rfl
  | succ d ih =>
      simp only [List.replicate_succ, mixedEulerDifference]
      rw [ih (F ⊗ L), ih F,
        mixedEulerDifference_eq_of_iso p (List.replicate d M) (Iso.refl F ⊗ᵢ e)]

private theorem positive_closed_tests_pullback {k : Type u} [Field k]
    {X Y : Scheme.{u}} (p : X ⟶ Spec (.of k)) (L : X.Modules)
    (j : Y ⟶ X) [IsClosedImmersion j]
    (hnum : ∀ (Z : Scheme.{u}) [IsIntegral Z] [CompactSpace Z] (i : Z ⟶ X),
      IsClosedImmersion i → ∀ e : ℕ, 0 < e → topologicalKrullDim Z = e →
        0 < mixedEulerDifference (i ≫ p)
          (List.replicate e ((Scheme.Modules.pullback i).obj L)) (unitObj Z)) :
    ∀ (Z : Scheme.{u}) [IsIntegral Z] [CompactSpace Z] (i : Z ⟶ Y),
      IsClosedImmersion i → ∀ e : ℕ, 0 < e → topologicalKrullDim Z = e →
        0 < mixedEulerDifference (i ≫ (j ≫ p))
          (List.replicate e ((Scheme.Modules.pullback i).obj ((Scheme.Modules.pullback j).obj L)))
          (unitObj Z) := by
  intro Z _ _ i hi e he hdim
  let : IsClosedImmersion i := hi
  have h := hnum Z (i ≫ j) inferInstance e he hdim
  rw [Category.assoc] at h
  let c : (Scheme.Modules.pullback i).obj ((Scheme.Modules.pullback j).obj L) ≅
      (Scheme.Modules.pullback (i ≫ j)).obj L := (pullbackComp i j).app L
  rw [mixedEulerDifference_replicate_eq_of_iso (i ≫ (j ≫ p)) e c (unitObj Z)]
  exact h

private theorem isProjective_closed_comp {k : Type u} [Field k]
    {X Y : Scheme.{u}} (j : Y ⟶ X) [IsClosedImmersion j]
    (p : X ⟶ Spec (.of k)) [IsProjective p] : IsProjective (j ≫ p) := by
  obtain ⟨V, hV, hVt, i, hi, hbase⟩ :=
    (inferInstance : IsProjective p).exists_isClosedImmersion
  let : IsClosedImmersion i := hi
  exact ⟨⟨V, hV, hVt, j ≫ i, inferInstance,
    (Category.assoc j i _).trans (congrArg (fun q => j ≫ q) hbase)⟩⟩

/-- Actual positivity on every closed integral test internally supplies all
proper ampleness induction conclusions. This is a total numerical theorem,
with no incoming Nakai/Serre/embedding or induction certificate. -/
theorem isAmple_of_positive_integral_closed_intersections_of_dimension_le
    {k : Type u} [Field k] :
    ∀ (d : ℕ) {X : Scheme.{u}} [IsIntegral X]
      (p : X ⟶ Spec (.of k)) [IsProjective p] (L : X.Modules) (_hL : IsInvertible L),
      topologicalKrullDim X ≤ d →
      (∀ (Y : Scheme.{u}) [IsIntegral Y] [CompactSpace Y] (j : Y ⟶ X),
        IsClosedImmersion j → ∀ e : ℕ, 0 < e → topologicalKrullDim Y = e →
          0 < mixedEulerDifference (j ≫ p)
            (List.replicate e ((Scheme.Modules.pullback j).obj L)) (unitObj Y)) →
      SchemeLineAmpleness.IsAmple p L := by
  intro d
  induction d with
  | zero =>
      intro X _ p _ L hL hdim _hnum
      exact SeshadriAmplenessCriterionDimensionZeroAmpleness.isAmple_of_dimension_le_zero
        p (by simpa only [Nat.cast_zero] using hdim) L hL
  | succ d ih =>
      intro X _ p _ L hL hdim hnum
      let hp := ProjectiveFactorizationRingIso.of_isProjective p
      let : IsProper p := hp.isProper
      let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
      let : X.IsSeparated := ⟨by
        have hsep : IsSeparated (p ≫ Limits.terminal.from (Spec (.of k))) := inferInstance
        simpa only [Limits.terminal.comp_from] using hsep⟩
      by_cases hlow : topologicalKrullDim X ≤ (d : ℕ)
      · exact ih p L hL hlow hnum
      have hdimExact : topologicalKrullDim X = (d + 1 : ℕ) := by
        apply le_antisymm hdim
        apply le_of_not_gt
        intro hlt
        apply hlow
        apply ENat.WithBot.lt_add_one_iff.mp
        simpa only [Nat.cast_add, Nat.cast_one] using hlt
      have hpos := hnum X (𝟙 X) inferInstance (d + 1) (Nat.zero_lt_succ d) hdimExact
      rw [Category.id_comp, mixedEulerDifference_replicate_eq_of_iso p (d + 1)
        ((pullbackId X).app L) (unitObj X)] at hpos
      apply isAmple_of_positive_diagonal_and_properIntegralClosedAmple
        p (d + 1) (Nat.zero_lt_succ d) hdim L hL hpos
      intro Y _ j hj hnonsurj
      let : IsClosedImmersion j := hj
      let : IsProjective (j ≫ p) := isProjective_closed_comp j p
      have hdimY := SeshadriAmplenessCriterionClosedMapDimension.closedImmersion_dimension_drop
        j hnonsurj d hdim
      exact ih (j ≫ p) ((Scheme.Modules.pullback j).obj L) (hL.pullback j) hdimY
        (positive_closed_tests_pullback p L j hnum)

/-- Numerical strict positivity on actual positive-dimensional closed integral
subschemes implies native ampleness of SAME L on ANY projective ambient scheme,
including reducible, nonreduced and empty schemes. -/
theorem isAmple_of_positive_integral_closed_intersections
    {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsProjective p] (L : X.Modules) (hL : IsInvertible L)
    (hnum : ∀ (Y : Scheme.{u}) [IsIntegral Y] [CompactSpace Y] (j : Y ⟶ X),
      IsClosedImmersion j → ∀ e : ℕ, 0 < e → topologicalKrullDim Y = e →
        0 < mixedEulerDifference (j ≫ p)
          (List.replicate e ((Scheme.Modules.pullback j).obj L)) (unitObj Y)) :
    SchemeLineAmpleness.IsAmple p L := by
  obtain ⟨d, hdim⟩ := NativeProjectiveDimensionBounds.exists_dimension_le_of_isProjective p
  apply SeshadriAmplenessCriterionStrataAmpleness.isAmple_of_strataAmple p L hL
  intro eta
  let I := Scheme.IdealSheafData.vanishingIdeal
    (⟨closure ({eta} : Set X), isClosed_closure⟩ : Closeds X)
  let : IsIntegral I.subscheme := SchemePointClosureIntegral.isIntegral_pointClosure eta
  let : IsProjective (I.subschemeι ≫ p) := isProjective_closed_comp I.subschemeι p
  have hdimI := IntegralSchemeDimension.topologicalKrullDim_le_of_isIntegralHom
    I.subschemeι d hdim
  exact isAmple_of_positive_integral_closed_intersections_of_dimension_le d
    (I.subschemeι ≫ p) ((Scheme.Modules.pullback I.subschemeι).obj L)
    (hL.pullback I.subschemeι) hdimI (positive_closed_tests_pullback p L I.subschemeι hnum)

#check @mixedEulerDifference_replicate_eq_of_iso
#print axioms mixedEulerDifference_replicate_eq_of_iso
#print axioms positive_closed_tests_pullback
#print axioms isProjective_closed_comp
#check @isAmple_of_positive_integral_closed_intersections_of_dimension_le
#print axioms isAmple_of_positive_integral_closed_intersections_of_dimension_le
#check @isAmple_of_positive_integral_closed_intersections
#print axioms isAmple_of_positive_integral_closed_intersections
end EnvelopeProperty.SeshadriAmplenessCriterion
