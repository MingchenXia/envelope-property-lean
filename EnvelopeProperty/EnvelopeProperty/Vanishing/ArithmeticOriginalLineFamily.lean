import EnvelopeProperty.Vanishing.ArithmeticOriginalLineExpression
import EnvelopeProperty.Vanishing.ArithmeticOriginalLineDescent
import EnvelopeProperty.Vanishing.ArithmeticOriginalSmoothFamily
import EnvelopeProperty.AlgGeom.BundleTensorPowerPullback
import EnvelopeProperty.FlatGlobalSections
import ModularCurves.Picard.DualPullback.Iso

/-! # A genuine arithmetic model for the actual original line

The original line, its generated projective morphism, and its actual whole
pullback comparison are constructed on a canonical later coefficient family.
Relative ampleness is a separate obligation, not a consequence asserted here.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite MvPolynomial
open Scheme.Modules
universe u

namespace EnvelopeProperty.Vanishing.ArithmeticOriginalLineFamily
open ProjBerk ArithmeticProjectiveOriginalFamily ArithmeticSmoothProjectiveOriginalFamily
open ArithmeticOriginalSmooth DeJongAlterations.StableModification.Limits

attribute [local instance] Scheme.Modules.monoidalCategory MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] {d : ℕ} {X : Scheme.{u}}
  (j : X ⟶ NativeProjectiveScheme k d) [IsClosedImmersion j] (extra : Finset k)
  (p : X ⟶ Spec (.of k)) (hjp : j ≫ nativeStructureMap = p)

/-- Further canonical coefficient enlargement retains the same whole
original map, rather than merely an abstract isomorphic generic fibre. -/
theorem scalarOriginalMap_transition (S T : Subalgebra ℤ k)
    (hRS : coefficientBase j extra ≤ S) (hST : S ≤ T) :
    scalarOriginalMap j extra T (hRS.trans hST) p hjp ≫ scalarTransition j extra S T hRS hST =
      scalarOriginalMap j extra S hRS p hjp := by
  apply pullback.hom_ext
  · rw [Category.assoc, scalarTransition_fst, scalarOriginalMap_fst, scalarOriginalMap_fst]
  · change (scalarOriginalMap j extra T (hRS.trans hST) p hjp ≫
      scalarTransition j extra S T hRS hST) ≫ scalarProjection j extra S hRS =
      scalarOriginalMap j extra S hRS p hjp ≫ scalarProjection j extra S hRS
    rw [Category.assoc, scalarTransition_projection, ← Category.assoc,
      scalarOriginalMap_projection, Category.assoc, ← Spec.map_comp]
    exact (scalarOriginalMap_projection j extra S hRS p hjp).symm

/-- The actual original pullback of every line or module on an earlier
coefficient family is preserved under its genuine canonical later transition. -/
def originalPullbackTransitionIso (S T : Subalgebra ℤ k)
    (hRS : coefficientBase j extra ≤ S) (hST : S ≤ T)
    (M : (scalarFamily j extra S hRS).Modules) :
    (Scheme.Modules.pullback (scalarOriginalMap j extra T (hRS.trans hST) p hjp)).obj
      ((Scheme.Modules.pullback (scalarTransition j extra S T hRS hST)).obj M) ≅
      (Scheme.Modules.pullback (scalarOriginalMap j extra S hRS p hjp)).obj M :=
  (Scheme.Modules.pullbackComp (scalarOriginalMap j extra T (hRS.trans hST) p hjp)
    (scalarTransition j extra S T hRS hST)).app M ≪≫
      (Scheme.Modules.pullbackCongr (scalarOriginalMap_transition j extra p hjp S T hRS hST)).app M

/-- A morphism on the original scheme is genuinely descended onto a later
canonical scalar family, containing every originally chosen coefficient. -/
theorem exists_scalar_projective_morphism (S : Subalgebra ℤ k)
    (hRS : coefficientBase j extra ≤ S) (hFT : Algebra.FiniteType ℤ S)
    (b : ℕ) (g : X ⟶ NativeProjectiveScheme k b) (hg : g ≫ nativeStructureMap = p) :
    ∃ (T : Subalgebra ℤ k) (hST : S ≤ T)
      (gT : scalarFamily j extra T (hRS.trans hST) ⟶ NativeProjectiveScheme T b),
      Algebra.FiniteType ℤ T ∧ gT ≫ nativeStructureMap = scalarProjection j extra T (hRS.trans hST) ∧
      scalarOriginalMap j extra T (hRS.trans hST) p hjp ≫ gT =
        g ≫ nativeCoefficientMap (algebraMap T k) := by
  let : Algebra.FiniteType ℤ S := hFT
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing ℤ _
  let q := scalarProjection j extra S hRS
  let a := scalarOriginalMap j extra S hRS p hjp
  let H := isPullback_scalarOriginalMap j extra S hRS p hjp
  let : IsProper q := (scalarProjection_isProjectiveFactorization j extra S hRS).isProper
  obtain ⟨B, gB, hgB, hgBOriginal⟩ :=
    ArithmeticOriginalLineDescent.exists_projective_morphism_baseChange a p q H
      Subtype.val_injective b g hg
  let T := B.1.restrictScalars ℤ
  have hST : S ≤ T := by
    intro x hx
    exact B.1.algebraMap_mem (⟨x, hx⟩ : S)
  let Htrans := isPullback_scalarTransition j extra S T hRS hST
  have HtransB : IsPullback (scalarTransition j extra S T hRS hST)
      (scalarProjection j extra T (hRS.trans hST)) q
      (Spec.map (CommRingCat.ofHom (algebraMap S B.1))) := Htrans
  let E := HtransB.isoPullback
  let gT := E.hom ≫ gB
  have hOriginal : scalarOriginalMap j extra T (hRS.trans hST) p hjp ≫ E.hom =
      ArithmeticOriginalLineDescent.originalBaseChangeMap a p q H B := by
    apply pullback.hom_ext
    · rw [Category.assoc, IsPullback.isoPullback_hom_fst]
      rw [ArithmeticOriginalLineDescent.originalBaseChangeMap, pullback.lift_fst]
      exact scalarOriginalMap_transition j extra p hjp S T hRS hST
    · rw [Category.assoc, IsPullback.isoPullback_hom_snd]
      rw [ArithmeticOriginalLineDescent.originalBaseChangeMap, pullback.lift_snd]
      exact scalarOriginalMap_projection j extra T (hRS.trans hST) p hjp
  let : Algebra.FiniteType S B.1 := (Subalgebra.fg_iff_finiteType _).mp B.2.1
  have hFTT : Algebra.FiniteType ℤ T := by
    change Algebra.FiniteType ℤ B.1
    exact Algebra.FiniteType.trans (S := S) inferInstance inferInstance
  refine ⟨T, hST, gT, hFTT, ?_, ?_⟩
  · dsimp only [gT]
    rw [Category.assoc, hgB]
    exact HtransB.isoPullback_hom_snd
  · dsimp only [gT]
    rw [← Category.assoc, hOriginal]
    exact hgBOriginal

/-- The actual two-twist line on the actual later canonical scalar family. -/
def modelLine (T : Subalgebra ℤ k) (hRT : coefficientBase j extra ≤ T) (N b : ℕ)
    (gT : scalarFamily j extra T hRT ⟶ NativeProjectiveScheme T b) :
    (scalarFamily j extra T hRT).Modules :=
  (Scheme.Modules.pullback gT).obj
    (coordinateHyperplaneTwist (R := T) (0 : Fin (b + 1)) 1) ⊗
      dualObj (scalarTwist j extra T hRT N)

/-- Local invertibility is derived for this constructed model line. -/
theorem modelLine_isInvertible (T : Subalgebra ℤ k) (hRT : coefficientBase j extra ≤ T) (N b : ℕ)
    (gT : scalarFamily j extra T hRT ⟶ NativeProjectiveScheme T b) :
    IsInvertible (modelLine j extra T hRT N b gT) := by
  let A := (Scheme.Modules.pullback gT).obj
    (coordinateHyperplaneTwist (R := T) (0 : Fin (b + 1)) 1)
  let B := scalarTwist j extra T hRT N
  have hA : IsInvertible A := (coordinateHyperplaneTwist_isInvertible (0 : Fin (b + 1)) 1).pullback gT
  have hB : IsInvertible B :=
    (coordinateHyperplaneTwist_isInvertible (0 : Fin (d + 1)) (N : ℤ)).pullback
      (scalarEmbedding j extra T hRT)
  exact (hA.tensorObj hB.dual).of_iso (ModularCurves.monoidalTensorObjIso A (dualObj B))

private def projectiveLinePullbackIso (T : Subalgebra ℤ k) (hRT : coefficientBase j extra ≤ T)
    (b : ℕ) (g : X ⟶ NativeProjectiveScheme k b)
    (gT : scalarFamily j extra T hRT ⟶ NativeProjectiveScheme T b)
    (hgT : scalarOriginalMap j extra T hRT p hjp ≫ gT = g ≫ nativeCoefficientMap (algebraMap T k)) :
    (Scheme.Modules.pullback (scalarOriginalMap j extra T hRT p hjp)).obj
      ((Scheme.Modules.pullback gT).obj (coordinateHyperplaneTwist (R := T) (0 : Fin (b + 1)) 1)) ≅
      (Scheme.Modules.pullback g).obj (coordinateHyperplaneTwist (R := k) (0 : Fin (b + 1)) 1) :=
  (Scheme.Modules.pullbackComp (scalarOriginalMap j extra T hRT p hjp) gT).app _ ≪≫
    (Scheme.Modules.pullbackCongr hgT).app _ ≪≫
    ((Scheme.Modules.pullbackComp g (nativeCoefficientMap (algebraMap T k))).app _).symm ≪≫
    (Scheme.Modules.pullback g).mapIso
      (ProjectiveTwistCoefficientPullback.coordinatePolePowerPullbackIso
        (algebraMap T k) (0 : Fin (b + 1)) 1)

private def modelLinePullbackIso (T : Subalgebra ℤ k) (hRT : coefficientBase j extra ≤ T)
    (N b : ℕ) (g : X ⟶ NativeProjectiveScheme k b)
    (gT : scalarFamily j extra T hRT ⟶ NativeProjectiveScheme T b)
    (hgT : scalarOriginalMap j extra T hRT p hjp ≫ gT = g ≫ nativeCoefficientMap (algebraMap T k)) :
    (Scheme.Modules.pullback (scalarOriginalMap j extra T hRT p hjp)).obj
      (modelLine j extra T hRT N b gT) ≅
      (Scheme.Modules.pullback g).obj (coordinateHyperplaneTwist (R := k) (0 : Fin (b + 1)) 1) ⊗
        dualObj ((Scheme.Modules.pullback j).obj
          (coordinateHyperplaneTwist (R := k) (0 : Fin (d + 1)) (N : ℤ))) := by
  let a := scalarOriginalMap j extra T hRT p hjp
  let A := (Scheme.Modules.pullback gT).obj (coordinateHyperplaneTwist (R := T) (0 : Fin (b + 1)) 1)
  let B := scalarTwist j extra T hRT N
  have hB : IsInvertible B :=
    (coordinateHyperplaneTwist_isInvertible (0 : Fin (d + 1)) (N : ℤ)).pullback
      (scalarEmbedding j extra T hRT)
  let : (Scheme.Modules.pullback a).Monoidal := pullbackMonoidal a
  exact (Functor.Monoidal.μIso (Scheme.Modules.pullback a) A (dualObj B)).symm ≪≫
    (projectiveLinePullbackIso j extra p hjp T hRT b g gT hgT ⊗ᵢ
      (dualPullbackIsoOfIsInvertible a B hB ≪≫
        (dualIsoObj (scalarTwistPullbackIso j extra T hRT p hjp N)).symm))

/-- The original invertible line itself has an internally constructed model
on a canonical later coefficient family, with its actual original pullback.
No finite model, line isomorphism, or ampleness certificate is an input. -/
theorem exists_original_line_model (S : Subalgebra ℤ k)
    (hRS : coefficientBase j extra ≤ S) (hFT : Algebra.FiniteType ℤ S)
    (L : X.Modules) (hL : IsInvertible L) :
    ∃ (T : Subalgebra ℤ k) (hST : S ≤ T)
      (M : (scalarFamily j extra T (hRS.trans hST)).Modules),
      Algebra.FiniteType ℤ T ∧ IsInvertible M ∧
      Nonempty ((Scheme.Modules.pullback
        (scalarOriginalMap j extra T (hRS.trans hST) p hjp)).obj M ≅ L) := by
  obtain ⟨N, b, g, _, eL, hg⟩ :=
    ArithmeticOriginalLineExpression.exists_original_line_expression p j L hL
  obtain ⟨T, hST, gT, hFTT, _, hgT⟩ := exists_scalar_projective_morphism
    j extra p hjp S hRS hFT b g hg
  exact ⟨T, hST, modelLine j extra T (hRS.trans hST) N b gT, hFTT,
    modelLine_isInvertible j extra T (hRS.trans hST) N b gT,
    ⟨modelLinePullbackIso j extra p hjp T (hRS.trans hST) N b g gT hgT ≪≫ eL⟩⟩

/-- The constructed original-line model retains the original family's already
proved relative dimension after its additional coefficients are adjoined. -/
theorem exists_original_line_model_relativeDimension (S : Subalgebra ℤ k)
    (hRS : coefficientBase j extra ≤ S) (hFT : Algebra.FiniteType ℤ S)
    (n : ℕ) (hn : SmoothOfRelativeDimension n (scalarProjection j extra S hRS))
    (L : X.Modules) (hL : IsInvertible L) :
    ∃ (T : Subalgebra ℤ k) (hST : S ≤ T)
      (M : (scalarFamily j extra T (hRS.trans hST)).Modules),
      Algebra.FiniteType ℤ T ∧
      SmoothOfRelativeDimension n (scalarProjection j extra T (hRS.trans hST)) ∧ IsInvertible M ∧
      Nonempty ((Scheme.Modules.pullback
        (scalarOriginalMap j extra T (hRS.trans hST) p hjp)).obj M ≅ L) := by
  obtain ⟨T, hST, M, hFTT, hM, e⟩ := exists_original_line_model j extra p hjp S hRS hFT L hL
  exact ⟨T, hST, M, hFTT, relativeDimension_scalarProjection j extra S T hRS hST n hn, hM, e⟩

/-- The original ample positive-power comparison is retained on the actual
original field fibre of the constructed model.  This is an ORIGINAL-FIBRE
comparison, not a claim that the comparison already descends to the model. -/
def originalPowerComparison (T : Subalgebra ℤ k) (hRT : coefficientBase j extra ≤ T)
    (M : (scalarFamily j extra T hRT).Modules) (L : X.Modules) (r : ℕ)
    (eM : (Scheme.Modules.pullback (scalarOriginalMap j extra T hRT p hjp)).obj M ≅ L)
    (ePower : (Scheme.Modules.pullback j).obj
      (coordinateHyperplaneTwist (R := k) (0 : Fin (d + 1)) 1) ≅
        CanonicalGeometry.bundleTensorPower L r) :
    (Scheme.Modules.pullback (scalarOriginalMap j extra T hRT p hjp)).obj
      (CanonicalGeometry.bundleTensorPower M r) ≅
      (Scheme.Modules.pullback (scalarOriginalMap j extra T hRT p hjp)).obj
        (scalarTwist j extra T hRT 1) :=
  BundleTensorPowerPullback.pullbackIso (scalarOriginalMap j extra T hRT p hjp) M r ≪≫
    BundleTensorPowerPullback.powerIso eM r ≪≫ ePower.symm ≪≫
      (scalarTwistPullbackIso j extra T hRT p hjp 1).symm

private def originalToLiteralModuleIso (T : Subalgebra ℤ k) (hRT : coefficientBase j extra ≤ T)
    (M : (scalarFamily j extra T hRT).Modules) :
    (Scheme.Modules.pullback
      (isPullback_scalarOriginalMap j extra T hRT p hjp).isoPullback.inv).obj
        ((Scheme.Modules.pullback (scalarOriginalMap j extra T hRT p hjp)).obj M) ≅
      (Scheme.Modules.pullback
        (FlatGlobalSections.firstProjection (S := k) (scalarProjection j extra T hRT))).obj M :=
  (Scheme.Modules.pullbackComp
    (isPullback_scalarOriginalMap j extra T hRT p hjp).isoPullback.inv
    (scalarOriginalMap j extra T hRT p hjp)).app M ≪≫
    (Scheme.Modules.pullbackCongr
      (isPullback_scalarOriginalMap j extra T hRT p hjp).isoPullback_inv_fst).app M

/-- The retained original positive-power comparison on the literal native
geometric fibre. The actual original cartesian square constructs the transport;
no comparison between the original X and the literal fibre is a premise. -/
def originalPowerComparisonOnLiteralFibre (T : Subalgebra ℤ k)
    (hRT : coefficientBase j extra ≤ T) (M : (scalarFamily j extra T hRT).Modules)
    (L : X.Modules) (r : ℕ)
    (eM : (Scheme.Modules.pullback (scalarOriginalMap j extra T hRT p hjp)).obj M ≅ L)
    (ePower : (Scheme.Modules.pullback j).obj
      (coordinateHyperplaneTwist (R := k) (0 : Fin (d + 1)) 1) ≅
        CanonicalGeometry.bundleTensorPower L r) :
    (Scheme.Modules.pullback
      (FlatGlobalSections.firstProjection (S := k) (scalarProjection j extra T hRT))).obj
        (CanonicalGeometry.bundleTensorPower M r) ≅
      (Scheme.Modules.pullback
        (FlatGlobalSections.firstProjection (S := k) (scalarProjection j extra T hRT))).obj
          (scalarTwist j extra T hRT 1) :=
  (originalToLiteralModuleIso j extra p hjp T hRT (CanonicalGeometry.bundleTensorPower M r)).symm ≪≫
    (Scheme.Modules.pullback
      (isPullback_scalarOriginalMap j extra T hRT p hjp).isoPullback.inv).mapIso
        (originalPowerComparison j extra p hjp T hRT M L r eM ePower) ≪≫
      originalToLiteralModuleIso j extra p hjp T hRT (scalarTwist j extra T hRT 1)

end EnvelopeProperty.Vanishing.ArithmeticOriginalLineFamily
