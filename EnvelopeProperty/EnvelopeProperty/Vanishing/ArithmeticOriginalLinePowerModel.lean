import EnvelopeProperty.Vanishing.ArithmeticOriginalLinePowerIso
import EnvelopeProperty.Vanishing.ArithmeticOriginalLineFamily
import EnvelopeProperty.Vanishing.AmpleScalarBaseChange

/-! # The actual original ample line has an ample arithmetic model

The final producer takes the original geometric ample datum. The original
positive-power embedding, original line model, original field comparison,
actual finite-stage power isomorphism and model ampleness are all produced.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open Scheme.Modules
universe u

namespace EnvelopeProperty.Vanishing.ArithmeticOriginalLinePowerModel
open CanonicalGeometry ProjBerk ArithmeticOriginalLinePowerIso ArithmeticOriginalLineFamily
open ArithmeticProjectiveOriginalFamily ArithmeticSmoothProjectiveOriginalFamily
open ArithmeticOriginalSmooth DeJongAlterations.StableModification.Limits

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual whole line isomorphisms transport the same positive-power ample criterion. -/
theorem ample_of_iso {R : Type u} [CommRing R] {Y : Scheme.{u}}
    {p : Y ⟶ Spec (.of R)} {L M : Y.Modules}
    (hL : SchemeLineAmpleness.IsAmple p L) (e : L ≅ M) : SchemeLineAmpleness.IsAmple p M := by
  refine ⟨hL.isInvertible.of_iso e.symm, ?_⟩
  obtain ⟨r, hr, hV⟩ := hL.2
  exact ⟨r, hr, SchemeAmpleClosedRestriction.veryAmple_of_iso hV
    (BundleTensorPowerPullback.powerIso e r)⟩

/-- The original field power comparison constructs actual ampleness on a
produced finite coefficient stage. No model power isomorphism is supplied. -/
theorem exists_ample_scalar_stage {R k : Type u} [CommRing R] [Field k] [Algebra R k]
    {Y : Scheme.{u}} (p : Y ⟶ Spec (.of R)) [Flat p] [IsProper p]
    (hi : Function.Injective (algebraMap R k)) (M : Y.Modules) (hM : IsInvertible M)
    (B : Y.Modules) (hB : SchemeLineAmpleness.IsVeryAmple p B) (r : ℕ) (hr : 0 < r)
    (e : (Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := k) p)).obj
        (bundleTensorPower M r) ≅
      (Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := k) p)).obj B) :
    ∃ C : FGSubalgebra R (⊤ : Subalgebra R k),
      SchemeLineAmpleness.IsAmple (FlatGlobalSections.structureMap (S := C.1) p)
        ((Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := C.1) p)).obj M) := by
  obtain ⟨C, eC, _, _⟩ := exists_iso_stage_of_proper p (bundleTensorPower M r)
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible hM r) B hB.isInvertible hi e
  have hVC := AmpleScalarBaseChange.isVeryAmple p (algebraMap R C.1) B hB
  have hVP := SchemeAmpleClosedRestriction.veryAmple_of_iso hVC
    (eC.symm ≪≫ BundleTensorPowerPullback.pullbackIso
      (FlatGlobalSections.firstProjection (S := C.1) p) M r)
  exact ⟨C, hM.pullback _, r, hr, hVP⟩

section FixedOriginalEmbedding
variable {k : Type u} [Field k] {d : ℕ} {X : Scheme.{u}}
  (j : X ⟶ NativeProjectiveScheme k d) [IsClosedImmersion j] (extra : Finset k)
  (p : X ⟶ Spec (.of k)) (hjp : j ≫ nativeStructureMap = p)

/-- For the same original positive-power embedding, the original line's
genuine canonical arithmetic model can be chosen ample, retaining all
previous coefficients and the actual original relative dimension. -/
theorem exists_ample_canonical_family (L : X.Modules) (hL : IsInvertible L)
    (r : ℕ) (hr : 0 < r)
    (ePower : (Scheme.Modules.pullback j).obj
      (coordinateHyperplaneTwist (R := k) (0 : Fin (d + 1)) 1) ≅ bundleTensorPower L r)
    (S : Subalgebra ℤ k) (hRS : coefficientBase j extra ≤ S) (hFT : Algebra.FiniteType ℤ S)
    (n : ℕ) (hn : SmoothOfRelativeDimension n (scalarProjection j extra S hRS)) :
    ∃ (U : Subalgebra ℤ k) (hSU : S ≤ U)
      (M : (scalarFamily j extra U (hRS.trans hSU)).Modules),
      Algebra.FiniteType ℤ U ∧ SmoothOfRelativeDimension n (scalarProjection j extra U (hRS.trans hSU)) ∧
      SchemeLineAmpleness.IsAmple (scalarProjection j extra U (hRS.trans hSU)) M ∧
      Nonempty ((Scheme.Modules.pullback
        (scalarOriginalMap j extra U (hRS.trans hSU) p hjp)).obj M ≅ L) := by
  obtain ⟨T, hST, M, hFTT, hnT, hM, ⟨eM⟩⟩ :=
    exists_original_line_model_relativeDimension j extra p hjp S hRS hFT n hn L hL
  let hRT := hRS.trans hST
  let q := scalarProjection j extra T hRT
  let B := scalarTwist j extra T hRT 1
  let : SmoothOfRelativeDimension n q := hnT
  let : Smooth q := SmoothOfRelativeDimension.smooth n q
  let : Flat q := inferInstance
  let : IsProper q := (scalarProjection_isProjectiveFactorization j extra T hRT).isProper
  let e := originalPowerComparisonOnLiteralFibre j extra p hjp T hRT M L r eM ePower
  obtain ⟨C, hAmpC⟩ := exists_ample_scalar_stage q Subtype.val_injective M hM B
    (scalarTwist_one_isVeryAmple j extra T hRT) r hr e
  let U := C.1.restrictScalars ℤ
  have hTU : T ≤ U := by
    intro x hx
    exact C.1.algebraMap_mem (⟨x, hx⟩ : T)
  let : Algebra.FiniteType ℤ T := hFTT
  let : Algebra.FiniteType T C.1 := (Subalgebra.fg_iff_finiteType _).mp C.2.1
  have hFTU : Algebra.FiniteType ℤ U := by
    change Algebra.FiniteType ℤ C.1
    exact Algebra.FiniteType.trans (S := T) inferInstance inferInstance
  let H := isPullback_scalarTransition j extra T U hRT hTU
  have HC : IsPullback (scalarTransition j extra T U hRT hTU)
      (scalarProjection j extra U (hRT.trans hTU)) q
      (Spec.map (CommRingCat.ofHom (algebraMap T C.1))) := H
  let E := HC.isoPullback
  let MC := (Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := C.1) q)).obj M
  let MU := (Scheme.Modules.pullback (scalarTransition j extra T U hRT hTU)).obj M
  have hAmpE : SchemeLineAmpleness.IsAmple (scalarProjection j extra U (hRT.trans hTU))
      ((Scheme.Modules.pullback E.hom).obj MC) := by
    have h := SchemeAmpleClosedRestriction.ample_pullback hAmpC E.hom
    have hq : E.hom ≫ FlatGlobalSections.structureMap (S := C.1) q =
        scalarProjection j extra U (hRT.trans hTU) := HC.isoPullback_hom_snd
    rw [hq] at h
    exact h
  let eU : (Scheme.Modules.pullback E.hom).obj MC ≅ MU :=
    (Scheme.Modules.pullbackComp E.hom (FlatGlobalSections.firstProjection (S := C.1) q)).app M ≪≫
      (Scheme.Modules.pullbackCongr HC.isoPullback_hom_fst).app M
  have hAmpU : SchemeLineAmpleness.IsAmple (scalarProjection j extra U (hRT.trans hTU)) MU :=
    ample_of_iso hAmpE eU
  exact ⟨U, hST.trans hTU, MU, hFTU,
    relativeDimension_scalarProjection j extra T U hRT hTU n hnT, hAmpU,
    ⟨originalPullbackTransitionIso j extra p hjp T U hRT hTU M ≪≫ eM⟩⟩

end FixedOriginalEmbedding

/-- The original geometric ample datum itself constructs an ample model of
the SAME original line on the SAME actual canonical arithmetic family.
The original positive-power embedding is selected internally. No model line,
model power comparison, or model ampleness certificate is a supplied input. -/
theorem exists_original_ample_model {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n p]
    (L : X.Modules) (hL : SchemeLineAmpleness.IsAmple p L) (extra : Finset k) :
    ∃ (d : ℕ) (j : X ⟶ NativeProjectiveScheme k d) (hj : IsClosedImmersion j),
      let : IsClosedImmersion j := hj
      ∃ (hjp : j ≫ nativeStructureMap = p) (S : Subalgebra ℤ k)
        (hRS : coefficientBase j extra ≤ S) (M : (scalarFamily j extra S hRS).Modules),
        Algebra.FiniteType ℤ S ∧ SmoothOfRelativeDimension n (scalarProjection j extra S hRS) ∧
        SchemeLineAmpleness.IsAmple (scalarProjection j extra S hRS) M ∧
        Nonempty ((Scheme.Modules.pullback (scalarOriginalMap j extra S hRS p hjp)).obj M ≅ L) := by
  obtain ⟨r, hr, d, j, hj, hjp, ⟨ePower⟩⟩ := hL.2
  let : IsClosedImmersion j := hj
  obtain ⟨S, hRS, hFT, hn, _, _⟩ := exists_relativeDimension_integer_stage j extra p hjp n
  obtain ⟨U, hSU, M, hFTU, hnU, hAmpU, eM⟩ := exists_ample_canonical_family
    j extra p hjp L hL.isInvertible r hr ePower S hRS hFT n hn
  exact ⟨d, j, hj, hjp, U, hRS.trans hSU, M, hFTU, hnU, hAmpU, eM⟩

end EnvelopeProperty.Vanishing.ArithmeticOriginalLinePowerModel
