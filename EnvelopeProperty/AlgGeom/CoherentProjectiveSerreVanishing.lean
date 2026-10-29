/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import EnvelopeProperty.AlgGeom.CoherentProjectiveGlobalGeneration
import EnvelopeProperty.AlgGeom.SchemeInvertibleTensorQuasicoherent
import ModularCurves.EllipticCurve.ProjectiveSpaceTwistCechFinite
import ModularCurves.ForMathlib.SheafCechRestrictionAcyclicComparison
import ModularCurves.ForMathlib.SchemeModuleOrderedBaseCechHomotopyEquiv

/-! # Genuine uniform Serre vanishing for the original projective module

The elementary finite-coproduct cohomology comparison follows the actual
finite-biproduct argument in native ProjectiveSpaceTwistCechFinite.
-/
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules MvPolynomial TopologicalSpace
noncomputable section
universe u
namespace EnvelopeProperty.CoherentProjectiveSerreVanishing
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] Scheme.Modules.monoidalCategory
variable {R : Type u} [CommRing R] {σ : Type}

private theorem homology_X3_isZero {A : Type u} [CommRing A]
    {S : ShortComplex (CochainComplex (ModuleCat.{u} A) ℕ)} (hS : S.ShortExact)
    (q : ℕ) (hQ : IsZero (S.X₂.homology q)) (hK : IsZero (S.X₁.homology (q+1))) :
    IsZero (S.X₃.homology q) :=
  (hS.homology_exact₃ q (q+1) (by simp [ComplexShape.up_Rel])).isZero_of_both_isZero hQ hK

private theorem coproduct_homology_isZero {X Y : Scheme.{u}}
    (π : X ⟶ Y) {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    {I : Type} [Finite I] (M : I → X.Modules) (q : ℕ)
    (hM : ∀ i, IsZero ((orderedBaseCechComplex π (M i) U).homology q)) :
    IsZero ((orderedBaseCechComplex π (∐ M) U).homology q) := by
  classical
  let := Fintype.ofFinite I
  let : HasFiniteBiproducts X.Modules := HasFiniteBiproducts.of_hasFiniteProducts
  let A := Γ(Y, (⊤ : Y.Opens))
  let : HasFiniteBiproducts (ModuleCat.{u} A) := HasFiniteBiproducts.of_hasFiniteProducts
  let F := orderedBaseCechComplexFunctor π U ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (ComplexShape.up ℕ) q
  let : F.Additive := by dsimp only [F]; infer_instance
  let : PreservesFiniteBiproducts F := Functor.preservesFiniteBiproductsOfAdditive F
  let (i : I) : Subsingleton (F.obj (M i)) := ModuleCat.subsingleton_of_isZero (hM i)
  let : Subsingleton (∀ i : I, F.obj (M i)) := inferInstance
  let e₀ : F.obj (∐ M) ≅ F.obj (⨁ M) := F.mapIso (biproduct.isoCoproduct M).symm
  let e₁ : F.obj (⨁ M) ≅ ⨁ (F.obj ∘ M) := F.mapBiproduct M
  let e₂ : (⨁ (F.obj ∘ M)) ≅ ∏ᶜ (F.obj ∘ M) := biproduct.isoProduct (F.obj ∘ M)
  let e₃ : (∏ᶜ (F.obj ∘ M)) ≅ ModuleCat.of A (∀ i : I, F.obj (M i)) :=
    ModuleCat.piIsoPi (F.obj ∘ M)
  exact IsZero.of_iso (ModuleCat.isZero_of_subsingleton _) (e₀ ≪≫ e₁ ≪≫ e₂ ≪≫ e₃)

private theorem homology_isZero_of_card_le [Fintype σ] [LinearOrder σ]
    (M : (Proj (homogeneousSubmodule σ R)).Modules) (q : ℕ)
    (hq : Fintype.card (ULift.{u} σ) ≤ q) :
    IsZero ((orderedBaseCechComplex (homogeneousProjπ (R := R) (σ := σ)) M
      (coordinateOpenCover (R := R) (σ := σ))).homology q) := by
  let C := orderedBaseCechComplex (homogeneousProjπ (R := R) (σ := σ)) M
    (coordinateOpenCover (R := R) (σ := σ))
  have hX : IsZero (C.X q) := orderedBaseCechObject_isZero_of_card_le
    (homogeneousProjπ (R := R) (σ := σ)) M
    (coordinateOpenCover (R := R) (σ := σ)) q hq
  exact ShortComplex.isZero_homology_of_isZero_X₂ (C.sc q) hX

private theorem negative_twist_eq_idealPower (j : σ) (n : ℕ) :
    coordinateHyperplaneTwist (R := R) j (-(n : ℤ)) =
      coordinateHyperplaneIdealModulePower (R := R) j n := by
  cases n with
  | zero => rfl
  | succ n => rfl

private def negativeTensorIso (i j k : σ) (n d : ℕ) (h : n ≤ d) :
    coordinateHyperplaneIdealModulePower (R := R) i n ⊗
        coordinateHyperplaneTwist (R := R) j (d : ℤ) ≅
      coordinateHyperplaneTwist (R := R) k ((d-n : ℕ) : ℤ) :=
  ((eqToIso (negative_twist_eq_idealPower (R := R) i n).symm ⊗ᵢ Iso.refl _) ≪≫
    ProjectiveTwistTensorAddition.tensorIso i j k (-(n : ℤ)) (d : ℤ)) ≪≫
    eqToIso (congrArg (coordinateHyperplaneTwist (R := R) k) (by omega))

private def tensorCoproductIso {X : Scheme.{u}} {I : Type} (M : I → X.Modules)
    (L : X.Modules) (hL : IsInvertible L) : (∐ M) ⊗ L ≅ ∐ fun i => M i ⊗ L := by
  let : (tensorRight L).IsEquivalence :=
    SchemeInvertibleTensorEquivalence.tensorRight_isEquivalence L hL
  exact PreservesCoproduct.iso (tensorRight L) M

/-- Every finite original negative-twist source has one internally derived
bound making its actual original tensor with EVERY larger twist acyclic in
ALL positive original standard-cover cohomology degrees simultaneously. -/
theorem exists_negativeSource_bound [Fintype σ] [LinearOrder σ]
    {r : ℕ} (jj : Fin r → σ) (nn : Fin r → ℕ) (j : σ) :
    ∃ N : ℕ, ∀ d : ℕ, N ≤ d → ∀ q : ℕ,
      IsZero ((orderedBaseCechComplex (homogeneousProjπ (R := R) (σ := σ))
        ((∐ fun i : Fin r => coordinateHyperplaneIdealModulePower (R := R) (jj i) (nn i)) ⊗
          coordinateHyperplaneTwist (R := R) j (d : ℤ))
        (coordinateOpenCover (R := R) (σ := σ))).homology (q+1)) := by
  classical
  refine ⟨Finset.univ.sup nn, ?_⟩
  intro d hd q
  have hn (i : Fin r) : nn i ≤ d :=
    (Finset.le_sup (f := nn) (Finset.mem_univ i)).trans hd
  let Q : Fin r → (Proj (homogeneousSubmodule σ R)).Modules :=
    fun i => coordinateHyperplaneIdealModulePower (R := R) (jj i) (nn i)
  let L := coordinateHyperplaneTwist (R := R) j (d : ℤ)
  let P : Fin r → (Proj (homogeneousSubmodule σ R)).Modules :=
    fun i => coordinateHyperplaneTwist (R := R) j ((d-nn i : ℕ) : ℤ)
  let e : (∐ Q) ⊗ L ≅ ∐ P :=
    tensorCoproductIso Q L (coordinateHyperplaneTwist_isInvertible j (d : ℤ)) ≪≫
      Sigma.mapIso (fun i => negativeTensorIso (jj i) j j (nn i) d (hn i))
  have hP (i : Fin r) : IsZero ((orderedBaseCechComplex
      (homogeneousProjπ (R := R) (σ := σ)) (P i)
      (coordinateOpenCover (R := R) (σ := σ))).homology (q+1)) :=
    (coordinateHyperplaneTwist_orderedBaseCechComplex_exactAt_succ
      (R := R) j ((d-nn i : ℕ) : ℤ) (by omega) q).isZero_homology
  have hsum := coproduct_homology_isZero (homogeneousProjπ (R := R) (σ := σ))
    (coordinateOpenCover (R := R) (σ := σ)) P (q+1) hP
  exact IsZero.of_iso hsum (HomologicalComplex.homologyMapIso
    ((orderedBaseCechComplexFunctor (homogeneousProjπ (R := R) (σ := σ))
      (coordinateOpenCover (R := R) (σ := σ))).mapIso e) (q+1))

private theorem negativeSource_isQuasicoherent {r : ℕ} (jj : Fin r → σ) (nn : Fin r → ℕ) :
    (∐ fun i : Fin r => coordinateHyperplaneIdealModulePower (R := R) (jj i) (nn i)).IsQuasicoherent := by
  apply isQuasicoherent_coproduct
  intro i
  exact IsInvertible.isQuasicoherent (coordinateHyperplaneIdealModulePower_isInvertible (jj i) (nn i))

private theorem negativeSource_isFiniteType {r : ℕ} (jj : Fin r → σ) (nn : Fin r → ℕ) :
    (∐ fun i : Fin r => coordinateHyperplaneIdealModulePower (R := R) (jj i) (nn i)).IsFiniteType := by
  apply isFiniteType_fin_coproduct
  · intro i
    exact IsInvertible.isQuasicoherent (coordinateHyperplaneIdealModulePower_isInvertible (jj i) (nn i))
  · intro i
    let L := coordinateHyperplaneIdealModulePower (R := R) (jj i) (nn i)
    let : L.IsFinitePresentation := IsInvertible.isFinitePresentation
      (coordinateHyperplaneIdealModulePower_isInvertible (jj i) (nn i))
    refine { exists_localGeneratorsData := ?_ }
    obtain ⟨p, hp⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData L
    refine ⟨p.localGeneratorsData, ?_⟩
    constructor
    intro k
    exact (hp.isFinite_presentation k).isFiniteType_generators

private theorem exists_bound_of_card_le_add [Fintype σ] [LinearOrder σ] [IsNoetherianRing R]
    (s : ℕ) (M : (Proj (homogeneousSubmodule σ R)).Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] (j : σ) :
    ∃ N : ℕ, ∀ d : ℕ, N ≤ d → ∀ q : ℕ,
      Fintype.card (ULift.{u} σ) ≤ (q+1)+s →
      IsZero ((orderedBaseCechComplex (homogeneousProjπ (R := R) (σ := σ))
        (M ⊗ coordinateHyperplaneTwist (R := R) j (d : ℤ))
        (coordinateOpenCover (R := R) (σ := σ))).homology (q+1)) := by
  induction s generalizing M with
  | zero =>
    refine ⟨0, ?_⟩
    intro d _hd q hcard
    exact homology_isZero_of_card_le _ (q+1) (by simpa using hcard)
  | succ s ih =>
    obtain ⟨r, jj, nn, f, hf⟩ := exists_fin_coordinateNegativeTwist_quotient M
    let Q := ∐ fun i : Fin r => coordinateHyperplaneIdealModulePower (R := R) (jj i) (nn i)
    let : Q.IsQuasicoherent := negativeSource_isQuasicoherent jj nn
    let : Q.IsFiniteType := negativeSource_isFiniteType jj nn
    let : Epi f := hf
    let : LocallyOfFiniteType (homogeneousProjπ (R := R) (σ := σ)) :=
      homogeneousProjπ_locallyOfFiniteType (R := R) (σ := σ)
    let : IsLocallyNoetherian (Proj (homogeneousSubmodule σ R)) :=
      LocallyOfFiniteType.isLocallyNoetherian (homogeneousProjπ (R := R) (σ := σ))
    let : (kernel f).IsQuasicoherent := isQuasicoherent_kernel f
    let : (kernel f).IsFiniteType := isFiniteType_kernel f
    obtain ⟨NK, hK⟩ := ih (kernel f)
    obtain ⟨NQ, hQ⟩ := exists_negativeSource_bound (R := R) jj nn j
    refine ⟨max NK NQ, ?_⟩
    intro d hd q hcard
    have hdK : NK ≤ d := le_trans (le_max_left NK NQ) hd
    have hdQ : NQ ≤ d := le_trans (le_max_right NK NQ) hd
    let T := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
    have hT : T.ShortExact := { exact := ShortComplex.exact_kernel f }
    let L := coordinateHyperplaneTwist (R := R) j (d : ℤ)
    let hL : IsInvertible L := coordinateHyperplaneTwist_isInvertible j (d : ℤ)
    let F := tensorRight L
    let : F.IsEquivalence := SchemeInvertibleTensorEquivalence.tensorRight_isEquivalence L hL
    have hTd : (T.map F).ShortExact :=
      SchemeInvertibleTensorEquivalence.tensorRight_shortExact L hL T hT
    let : (T.map F).X₁.IsQuasicoherent :=
      SchemeInvertibleTensorQuasicoherent.isQuasicoherent_tensorRight (kernel f) L hL
    let : (T.map F).X₂.IsQuasicoherent :=
      SchemeInvertibleTensorQuasicoherent.isQuasicoherent_tensorRight Q L hL
    let : (T.map F).X₃.IsQuasicoherent :=
      SchemeInvertibleTensorQuasicoherent.isQuasicoherent_tensorRight M L hL
    have hTC := hTd.map_orderedBaseCechComplexFunctor_of_affine_openCover
      (homogeneousProjπ (R := R) (σ := σ)) (coordinateOpenCover (R := R) (σ := σ))
      (coordinateOpenCover_isAffineOpen (R := R))
    exact homology_X3_isZero hTC (q+1) (hQ d hdQ q)
      (hK d hdK (q+1) (by omega))

/-- The ACTUAL original finite-type quasicoherent module on genuine polynomial
projective space over a Noetherian ring has one DERIVED bound making EVERY
larger twist vanish in ALL positive standard-cover cohomology degrees at once.
No vanishing bound, resolution, kernel finiteness or cohomological certificate is assumed. -/
theorem exists_orderedCech_bound [Fintype σ] [LinearOrder σ] [IsNoetherianRing R]
    (M : (Proj (homogeneousSubmodule σ R)).Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] (j : σ) :
    ∃ N : ℕ, ∀ d : ℕ, N ≤ d → ∀ q : ℕ,
      IsZero ((orderedBaseCechComplex (homogeneousProjπ (R := R) (σ := σ))
        (M ⊗ coordinateHyperplaneTwist (R := R) j (d : ℤ))
        (coordinateOpenCover (R := R) (σ := σ))).homology (q+1)) := by
  obtain ⟨N, hN⟩ := exists_bound_of_card_le_add (Fintype.card (ULift.{u} σ)) M j
  exact ⟨N, fun d hd q => hN d hd q (by omega)⟩

private theorem sheaf_H_subsingleton_of_ordered_isZero [Fintype σ] [LinearOrder σ]
    (M : (Proj (homogeneousSubmodule σ R)).Modules) [M.IsQuasicoherent] (q : ℕ)
    (hM : IsZero ((orderedBaseCechComplex (homogeneousProjπ (R := R) (σ := σ)) M
      (coordinateOpenCover (R := R) (σ := σ))).homology (q+1))) :
    Subsingleton (CategoryTheory.Sheaf.H M.sheaf (q+1)) := by
  let π := homogeneousProjπ (R := R) (σ := σ)
  let U := coordinateOpenCover (R := R) (σ := σ)
  have hbase : IsZero ((baseCechComplex π M U).homology (q+1)) :=
    IsZero.of_iso hM (baseCechOrderedHomologyIso π M U (q+1))
  have hcech := (baseCechComplex_exactAt_iff π M U (q+1)).mp
    ((HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr hbase)
  exact (TopCat.Sheaf.cechComplex_exactAt_succ_iff_subsingleton_H_of_subsingleton_restrict_H
    U M.sheaf (iSup_coordinateOpenCover_eq_top (R := R))
    (fun p i r => cechIntersection_subsingleton_H M U
      (coordinateOpenCover_isAffineOpen (R := R)) p i r) q).mp hcech

/-- Genuine ordinary Serre vanishing: the SAME original coherent module on
actual polynomial projective space has a DERIVED bound annihilating its WHOLE
original positive SHEAF cohomology after EVERY larger original twist. The
finite order, cover, all kernel finiteness and all vanishing are internally
produced; no additional cohomological or comparison premise is assumed. -/
theorem exists_sheafCohomology_bound [Fintype σ] [IsNoetherianRing R]
    (M : (Proj (homogeneousSubmodule σ R)).Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] (j : σ) :
    ∃ N : ℕ, ∀ d : ℕ, N ≤ d → ∀ q : ℕ,
      Subsingleton (CategoryTheory.Sheaf.H
        (M ⊗ coordinateHyperplaneTwist (R := R) j (d : ℤ) :
          (Proj (homogeneousSubmodule σ R)).Modules).sheaf (q+1)) := by
  classical
  let : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  obtain ⟨N, hN⟩ := exists_orderedCech_bound M j
  refine ⟨N, ?_⟩
  intro d hd q
  let L := coordinateHyperplaneTwist (R := R) j (d : ℤ)
  let : (M ⊗ L).IsQuasicoherent :=
    SchemeInvertibleTensorQuasicoherent.isQuasicoherent_tensorRight M L
      (coordinateHyperplaneTwist_isInvertible j (d : ℤ))
  exact sheaf_H_subsingleton_of_ordered_isZero (M ⊗ L) q (hN d hd q)

end EnvelopeProperty.CoherentProjectiveSerreVanishing
