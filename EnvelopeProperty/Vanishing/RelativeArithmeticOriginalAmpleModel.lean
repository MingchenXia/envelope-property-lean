import EnvelopeProperty.Vanishing.RelativeArithmeticOriginalLineModel
import EnvelopeProperty.Vanishing.ArithmeticOriginalLinePowerIso

/-! # The same original relatively ample line has a produced ample arithmetic model

The original positive-power embedding, whole line model, and actual model
power isomorphism are produced internally.  Isomorphism descent uses the
already proved nonproper compact/separated producer.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u

namespace EnvelopeProperty.Vanishing.RelativeArithmeticOriginalAmpleModel
open ProjBerk CanonicalGeometry Alterations.StableModification.Limits

private def originalToLiteralIso
    {A k : Type u} [CommRing A] [Field k] [Algebra A k]
    {X Y : Scheme.{u}} (a : X ⟶ Y) (f : X ⟶ Spec (.of k)) (p : Y ⟶ Spec (.of A))
    (H : IsPullback a f p (Spec.map (CommRingCat.ofHom (algebraMap A k))))
    (M : Y.Modules) :
    (Scheme.Modules.pullback H.isoPullback.inv).obj
      ((Scheme.Modules.pullback a).obj M) ≅
        (Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := k) p)).obj M :=
  (Scheme.Modules.pullbackComp H.isoPullback.inv a).app M ≪≫
    (Scheme.Modules.pullbackCongr H.isoPullback_inv_fst).app M

/-- Actual original relative ampleness constructs an ample arithmetic model
of the SAME whole original line over a distinct finite-presentation affine
algebra.  No properness over the original field and no domain hypothesis on
its original finite-type affine base is supplied. -/
theorem exists_original_ample_model
    {k R : Type u} [Field k] [CharZero k] [CommRing R]
    [Algebra k R] [Algebra.FiniteType k R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsSeparated f]
    (g : X ⟶ Spec (.of R))
    (hg : g ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) = f)
    (n : ℕ) [SmoothOfRelativeDimension n f]
    (L : X.Modules) (hL : SchemeLineAmpleness.IsAmple g L) :
    ∃ (A : Subalgebra ℤ k), Algebra.FiniteType ℤ A ∧
      ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B),
        Algebra.FinitePresentation A B ∧ Nonempty (k ⊗[A] B ≃ₐ[k] R) ∧
        ∃ (Y : Scheme.{u}) (a : X ⟶ Y) (p : Y ⟶ Spec (.of A))
          (q : Y ⟶ Spec (.of B)) (M : Y.Modules),
          IsPullback a f p (Spec.map (CommRingCat.ofHom (algebraMap A k))) ∧
          SmoothOfRelativeDimension n p ∧ IsSeparated p ∧ QuasiCompact p ∧
          q ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) = p ∧
          SchemeLineAmpleness.IsAmple q M ∧
          Nonempty ((Scheme.Modules.pullback a).obj M ≅ L) := by
  obtain ⟨r, hr, d, j, hj, hjg, ⟨ePower⟩⟩ := hL.2
  let jN : X ⟶ NativeProjectiveScheme R d := j
  let : IsClosedImmersion jN := hj
  obtain ⟨A, hFTA, B, hB, hAB, hFPB, ⟨eB⟩, Y, a, p, q, M, T,
      H, hn, hsep, hqc, hqp, hM, hVT, ⟨eM⟩, ⟨eT⟩⟩ :=
    RelativeArithmeticOriginalLineModel.exists_original_line_model
      f g hg n d jN hjg L hL.isInvertible
  let : CommRing B := hB
  let : Algebra A B := hAB
  let : Algebra.FinitePresentation A B := hFPB
  let : Algebra.FiniteType ℤ A := hFTA
  let : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℤ A
  let : SmoothOfRelativeDimension n p := hn
  let : Smooth p := SmoothOfRelativeDimension.smooth n p
  let : Flat p := inferInstance
  let : IsSeparated p := hsep
  let : QuasiCompact p := hqc
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace p
  let : Y.IsSeparated := ⟨by rw [← terminal.comp_from p]; infer_instance⟩
  let eOriginal : (Scheme.Modules.pullback a).obj (bundleTensorPower M r) ≅
      (Scheme.Modules.pullback a).obj T :=
    BundleTensorPowerPullback.pullbackIso a M r ≪≫
      BundleTensorPowerPullback.powerIso eM r ≪≫ ePower.symm ≪≫ eT.symm
  let eLiteral :
      (Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := k) p)).obj
        (bundleTensorPower M r) ≅
      (Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := k) p)).obj T :=
    (originalToLiteralIso a f p H (bundleTensorPower M r)).symm ≪≫
      (Scheme.Modules.pullback H.isoPullback.inv).mapIso eOriginal ≪≫
      originalToLiteralIso a f p H T
  obtain ⟨C, eC, _, _⟩ := ArithmeticOriginalLinePowerIso.exists_iso_stage
    p (bundleTensorPower M r) (TensorPowerBaseIdealGrading.tensorPower_isInvertible hM r)
    T hVT.isInvertible Subtype.val_injective eLiteral
  let S := C.1.restrictScalars ℤ
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
  have hVMS : SchemeLineAmpleness.IsVeryAmple qS (bundleTensorPower MS r) :=
    SchemeAmpleClosedRestriction.veryAmple_of_iso
      (RelativeArithmeticScalarTransition.isVeryAmple (S := C.1) p q hqp T hVT)
      (eC.symm ≪≫ BundleTensorPowerPullback.pullbackIso t M r)
  have hAmp : SchemeLineAmpleness.IsAmple qS MS := ⟨hM.pullback t, r, hr, hVMS⟩
  let : Algebra.FiniteType A C.1 := (Subalgebra.fg_iff_finiteType _).mp C.2.1
  have hFTS₀ : Algebra.FiniteType ℤ C.1 :=
    Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  have hFTS : Algebra.FiniteType ℤ S := hFTS₀
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
  exact ⟨S, hFTS, D, inferInstance, inferInstance, hFPD, ⟨eD⟩,
    YS, aS, pS, qS, MS,
    RelativeArithmeticScalarTransition.original_isPullback p a f H C,
    hnS, hsepS, hqcS,
    RelativeArithmeticScalarTransition.relativeMap_coefficient (S := C.1) p q hqp,
    hAmp, ⟨RelativeArithmeticScalarTransition.originalPullbackIso p a f H C M ≪≫ eM⟩⟩

end EnvelopeProperty.Vanishing.RelativeArithmeticOriginalAmpleModel
