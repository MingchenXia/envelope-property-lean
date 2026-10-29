import EnvelopeProperty.Vanishing.RelativeArithmeticOriginalAmpleModel
import EnvelopeProperty.Vanishing.RelativeArithmeticWittComparison

/-! # Smooth arithmetic coefficients for the original relative ample line

Only the produced coefficient domain is localized.  The distinct relative
affine algebra, original total space, dimension, relative ampleness, and
whole original-line pullback are retained under the actual scalar transition.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u

namespace EnvelopeProperty.Vanishing.RelativeArithmeticSmoothAmpleModel
open Alterations.StableModification.Limits

/-- The SAME original relatively ample line has a smooth arithmetic
coefficient-domain model.  The original affine base remains a separate
arbitrary finite-type algebra; no domain assumption is imposed on it. -/
theorem exists_original_smooth_ample_model
    {k R : Type u} [Field k] [CharZero k] [CommRing R]
    [Algebra k R] [Algebra.FiniteType k R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsSeparated f]
    (g : X ⟶ Spec (.of R))
    (hg : g ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) = f)
    (n : ℕ) [SmoothOfRelativeDimension n f]
    (L : X.Modules) (hL : SchemeLineAmpleness.IsAmple g L) :
    ∃ (A : Subalgebra ℤ k), Algebra.Smooth ℤ A ∧ Algebra.FiniteType ℤ A ∧
      ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B),
        Algebra.FinitePresentation A B ∧ Nonempty (k ⊗[A] B ≃ₐ[k] R) ∧
        ∃ (Y : Scheme.{u}) (a : X ⟶ Y) (p : Y ⟶ Spec (.of A))
          (q : Y ⟶ Spec (.of B)) (M : Y.Modules),
          IsPullback a f p (Spec.map (CommRingCat.ofHom (algebraMap A k))) ∧
          SmoothOfRelativeDimension n p ∧ IsSeparated p ∧ QuasiCompact p ∧
          q ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) = p ∧
          SchemeLineAmpleness.IsAmple q M ∧
          Nonempty ((Scheme.Modules.pullback a).obj M ≅ L) := by
  obtain ⟨A, hFTA, B, hB, hAB, hFPB, ⟨eB⟩, Y, a, p, q, M,
      H, hn, hsep, hqc, hqp, hM, ⟨eM⟩⟩ :=
    RelativeArithmeticOriginalAmpleModel.exists_original_ample_model f g hg n L hL
  let : CommRing B := hB
  let : Algebra A B := hAB
  let : Algebra.FinitePresentation A B := hFPB
  let : Algebra.FiniteType ℤ A := hFTA
  let : SmoothOfRelativeDimension n p := hn
  let : IsSeparated p := hsep
  let : QuasiCompact p := hqc
  obtain ⟨s, hs, _, hSmooth, hFTU, _, _, _, hAU⟩ :=
    ArithmeticSmoothCoefficientBase.exists_smooth_localizedCoefficientRing A
  let U := ArithmeticSmoothCoefficientBase.localizedCoefficientRing A s hs
  let U₀ : Subalgebra A k :=
    { U.toSubsemiring with algebraMap_mem' := fun x => hAU x.property }
  let : Algebra.FiniteType ℤ U₀ := hFTU
  let : Algebra.FiniteType A U₀ :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℤ A U₀
  let C : FGSubalgebra A (⊤ : Subalgebra A k) :=
    ⟨U₀, (Subalgebra.fg_iff_finiteType _).mpr inferInstance, le_top⟩
  let S := C.1.restrictScalars ℤ
  have hSU : S = U := by ext x; rfl
  have hSmoothS : Algebra.Smooth ℤ S := hSU.symm ▸ hSmooth
  have hFTS : Algebra.FiniteType ℤ S := hSU.symm ▸ hFTU
  let D := C.1 ⊗[A] B
  let : Algebra (C.1.restrictScalars ℤ) (C.1 ⊗[A] B) := by
    change Algebra C.1 (C.1 ⊗[A] B)
    infer_instance
  let YS := pullback p (Spec.map (CommRingCat.ofHom (algebraMap A C.1)))
  let pS := pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap A C.1)))
  let t := pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap A C.1)))
  let aS := ArithmeticOriginalLineDescent.originalBaseChangeMap a f p H C
  let qS := RelativeArithmeticScalarTransition.relativeMap (S := C.1) p q hqp
  let MS := (Scheme.Modules.pullback t).obj M
  have hFPD : Algebra.FinitePresentation S D :=
    Algebra.FinitePresentation.baseChange (R := A) (A := B) C.1
  let eD : k ⊗[S] D ≃ₐ[k] R :=
    (Algebra.TensorProduct.cancelBaseChange A C.1 k k B).trans eB
  have hnS : SmoothOfRelativeDimension n pS :=
    @MorphismProperty.IsStableUnderBaseChange.of_isPullback
      Scheme.{u} inferInstance (@SmoothOfRelativeDimension.{u} n)
      (smoothOfRelativeDimension_isStableUnderBaseChange n)
      _ _ _ _ _ _ _ _
      (IsPullback.of_hasPullback p
        (Spec.map (CommRingCat.ofHom (algebraMap A C.1)))) hn
  have hsepS : IsSeparated pS := by
    dsimp only [pS]
    infer_instance
  have hqcS : QuasiCompact pS := by
    dsimp only [pS]
    infer_instance
  exact ⟨S, hSmoothS, hFTS, D, inferInstance, inferInstance, hFPD, ⟨eD⟩,
    YS, aS, pS, qS, MS,
    RelativeArithmeticScalarTransition.original_isPullback p a f H C,
    hnS, hsepS, hqcS,
    RelativeArithmeticScalarTransition.relativeMap_coefficient (S := C.1) p q hqp,
    RelativeArithmeticScalarTransition.isAmple (S := C.1) p q hqp M hM,
    ⟨RelativeArithmeticScalarTransition.originalPullbackIso p a f H C M ≪≫ eM⟩⟩

end EnvelopeProperty.Vanishing.RelativeArithmeticSmoothAmpleModel
