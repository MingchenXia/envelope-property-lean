import EnvelopeProperty.Vanishing.RelativeArithmeticGeometricModel
import EnvelopeProperty.Vanishing.RelativeArithmeticLineExpression
import EnvelopeProperty.Vanishing.RelativeArithmeticScalarTransition
import EnvelopeProperty.AlgGeom.PositivePowerProjectiveGeneration
import ModularCurves.Picard.DualPullback.Iso

/-! # An arithmetic model of the same original line in the relative family

The original finite generators yield a projective map over the field.  It
descends on the actual smooth relative projective family using only its
quasi-compactness and separatedness.  The same original line is recovered
as an actual whole module, without replacing it by a positive power.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory MvPolynomial
open Scheme.Modules
open scoped TensorProduct
universe u

namespace EnvelopeProperty.Vanishing.RelativeArithmeticOriginalLineModel
open ProjBerk CanonicalGeometry DeJongAlterations.StableModification.Limits
attribute [local instance] Scheme.Modules.monoidalCategory MvPolynomial.gradedAlgebra

private def original_twist_power_iso
    {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (a : X ⟶ Y) (T : Y.Modules) {d : ℕ} (j : X ⟶ NativeProjectiveScheme R d)
    (eT : (Scheme.Modules.pullback a).obj T ≅ (Scheme.Modules.pullback j).obj
      (coordinateHyperplaneTwist (R := R) (0 : Fin (d + 1)) 1)) (N : ℕ) :
    (Scheme.Modules.pullback a).obj (bundleTensorPower T N) ≅
      (Scheme.Modules.pullback j).obj
        (coordinateHyperplaneTwist (R := R) (0 : Fin (d + 1)) (N : ℤ)) :=
  BundleTensorPowerPullback.pullbackIso a T N ≪≫
    BundleTensorPowerPullback.powerIso eT N ≪≫
    (BundleTensorPowerPullback.pullbackIso j
      (coordinateHyperplaneTwist (R := R) (0 : Fin (d + 1)) 1) N).symm ≪≫
    (Scheme.Modules.pullback j).mapIso
      (PositivePowerProjectiveGeneration.twistPowerIso (0 : Fin (d + 1)) N)

/-- The original invertible line itself has a constructed arithmetic model
in the original relative projective family.  The same relative very ample
embedding line and all total-space geometric hypotheses are retained. -/
theorem exists_original_line_model
    {k R : Type u} [Field k] [CharZero k] [CommRing R]
    [Algebra k R] [Algebra.FiniteType k R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsSeparated f]
    (g : X ⟶ Spec (.of R))
    (hg : g ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) = f)
    (n : ℕ) [SmoothOfRelativeDimension n f]
    (d : ℕ) (j : X ⟶ NativeProjectiveScheme R d) [hjClosed : IsClosedImmersion j]
    (hj : j ≫ nativeStructureMap = g) (L : X.Modules) (hL : IsInvertible L) :
    ∃ (A : Subalgebra ℤ k), Algebra.FiniteType ℤ A ∧
      ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B),
        Algebra.FinitePresentation A B ∧ Nonempty (k ⊗[A] B ≃ₐ[k] R) ∧
        ∃ (Y : Scheme.{u}) (a : X ⟶ Y) (p : Y ⟶ Spec (.of A))
          (q : Y ⟶ Spec (.of B)) (M T : Y.Modules),
          IsPullback a f p (Spec.map (CommRingCat.ofHom (algebraMap A k))) ∧
          SmoothOfRelativeDimension n p ∧ IsSeparated p ∧ QuasiCompact p ∧
          q ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) = p ∧
          IsInvertible M ∧ SchemeLineAmpleness.IsVeryAmple q T ∧
          Nonempty ((Scheme.Modules.pullback a).obj M ≅ L) ∧
          Nonempty ((Scheme.Modules.pullback a).obj T ≅
            (Scheme.Modules.pullback j).obj
              (coordinateHyperplaneTwist (R := R) (0 : Fin (d + 1)) 1)) := by
  obtain ⟨N, b, h, _, eL, hh⟩ :=
    RelativeArithmeticLineExpression.exists_original_line_expression
      (hj := hjClosed) f j L hL
  obtain ⟨A, hFTA, B, hB, hAB, hFPB, ⟨eB⟩, Y, a, p, q, T,
      H, hn, hsep, hqc, hqp, hVT, ⟨eT⟩⟩ :=
    RelativeArithmeticGeometricModel.exists_original_geometric_model f g hg n d j hj
  let : CommRing B := hB
  let : Algebra A B := hAB
  let : Algebra.FinitePresentation A B := hFPB
  let : Algebra.FiniteType ℤ A := hFTA
  let : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℤ A
  let : SmoothOfRelativeDimension n p := hn
  let : IsSeparated p := hsep
  let : QuasiCompact p := hqc
  obtain ⟨C, hC, _, hCoriginal⟩ :=
    ArithmeticOriginalLineDescent.exists_projective_morphism_baseChange a f p H
      Subtype.val_injective b h hh
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
  let TS := (Scheme.Modules.pullback t).obj T
  let V := (Scheme.Modules.pullback hC).obj
    (coordinateHyperplaneTwist (R := C.1) (0 : Fin (b + 1)) 1)
  let W := bundleTensorPower TS N
  let M := V ⊗ dualObj W
  have hTS : IsInvertible TS := hVT.isInvertible.pullback t
  have hV : IsInvertible V :=
    (coordinateHyperplaneTwist_isInvertible (0 : Fin (b + 1)) 1).pullback hC
  have hW : IsInvertible W := TensorPowerBaseIdealGrading.tensorPower_isInvertible hTS N
  have hM : IsInvertible M :=
    (hV.tensorObj hW.dual).of_iso (ModularCurves.monoidalTensorObjIso V (dualObj W))
  let eV : (Scheme.Modules.pullback aS).obj V ≅
      (Scheme.Modules.pullback h).obj
        (coordinateHyperplaneTwist (R := k) (0 : Fin (b + 1)) 1) :=
    (Scheme.Modules.pullbackComp aS hC).app _ ≪≫
      (Scheme.Modules.pullbackCongr hCoriginal).app _ ≪≫
      ((Scheme.Modules.pullbackComp h (nativeCoefficientMap (algebraMap C.1 k))).app _).symm ≪≫
      (Scheme.Modules.pullback h).mapIso
        (ProjectiveTwistCoefficientPullback.coordinatePolePowerPullbackIso
          (algebraMap C.1 k) (0 : Fin (b + 1)) 1)
  let eTS : (Scheme.Modules.pullback aS).obj TS ≅
      (Scheme.Modules.pullback j).obj
        (coordinateHyperplaneTwist (R := R) (0 : Fin (d + 1)) 1) :=
    RelativeArithmeticScalarTransition.originalPullbackIso p a f H C T ≪≫ eT
  let eW : (Scheme.Modules.pullback aS).obj W ≅
      (Scheme.Modules.pullback j).obj
        (coordinateHyperplaneTwist (R := R) (0 : Fin (d + 1)) (N : ℤ)) :=
    original_twist_power_iso aS TS j eTS N
  let : (Scheme.Modules.pullback aS).Monoidal := pullbackMonoidal aS
  let eM : (Scheme.Modules.pullback aS).obj M ≅ L :=
    (Functor.Monoidal.μIso (Scheme.Modules.pullback aS) V (dualObj W)).symm ≪≫
      (eV ⊗ᵢ (dualPullbackIsoOfIsInvertible aS W hW ≪≫ (dualIsoObj eW).symm)) ≪≫ eL
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
    YS, aS, pS, qS, M, TS,
    RelativeArithmeticScalarTransition.original_isPullback p a f H C,
    hnS, hsepS, hqcS,
    RelativeArithmeticScalarTransition.relativeMap_coefficient (S := C.1) p q hqp,
    hM, RelativeArithmeticScalarTransition.isVeryAmple (S := C.1) p q hqp T hVT,
    ⟨eM⟩, ⟨eTS⟩⟩

end EnvelopeProperty.Vanishing.RelativeArithmeticOriginalLineModel
