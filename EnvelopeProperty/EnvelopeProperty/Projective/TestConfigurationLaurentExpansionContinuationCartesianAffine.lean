import EnvelopeProperty.Projective.TestConfigurationLaurentExpansionContinuationLocalAffineMap
import EnvelopeProperty.Projective.TestConfigurationLaurentExpansionContinuationAffine

/-! # Actual Cartesian affine original-base maps and original open Laurent coefficients

The genuine geometric Cartesian square derives the original ring pushout.
Its affine module map extends the frozen chosen-product producer, and the
actual canonical local diagram gives original affine-open bijectivity.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct ChangeOfRings LaurentPolynomial
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
open Scheme.Modules

section Cartesian
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
  (q : Y ⟶ Spec (CommRingCat.of S)) (g : Y ⟶ X)
  (H : IsPullback g q f (Spec.map (CommRingCat.ofHom (algebraMap R S))))
  [Module.Flat R S] [QuasiCompact f] [QuasiSeparated f]

include H

/-- The actual original Cartesian square DERIVES its original coefficient
ring pushout, with no ring-square or section comparison supplied. -/
theorem originalCartesianSectionSquare :
    IsPushout (CommRingCat.ofHom (ProperBirationalSections.coefficientMap f))
      (CommRingCat.ofHom (algebraMap R S)) g.appTop
      (CommRingCat.ofHom (ProperBirationalSections.coefficientMap q)) := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap R S))
  let : Flat b := Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have hc : IsCompact (X := X) (⊤ : X.Opens) := by
    simpa using f.isCompact_preimage (isAffineOpen_top (Spec (CommRingCat.of R))).isCompact
  have hq : IsQuasiSeparated (α := X) (⊤ : X.Opens) := by
    simpa using f.isQuasiSeparated_preimage
      (isAffineOpen_top (Spec (CommRingCat.of R))).isQuasiSeparated
  have hi := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right
    H (US := ⊤) (UT := ⊤) (UX := ⊤) (UY := ⊤)
    (by simp) (by simp) (by simp) (isAffineOpen_top _) (isAffineOpen_top _) hc hq
  have hp := (isIso_pushoutSection_iff H
    (US := ⊤) (UT := ⊤) (UX := ⊤) (UY := ⊤) (by simp) (by simp) (by simp)).mp hi
  have hn : IsPushout f.appTop b.appTop g.appTop q.appTop := by
    simpa [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE] using hp
  apply hn.of_iso
    (Scheme.ΓSpecIso (CommRingCat.of R)) (Iso.refl _)
    (Scheme.ΓSpecIso (CommRingCat.of S)) (Iso.refl _)
  · simp [ProperBirationalSections.coefficientMap]
  · exact Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R S))
  · simp
  · simp [ProperBirationalSections.coefficientMap]

/-- The tensor-domain comparison follows from this SAME actual original
ring pushout, with both original geometric maps retained. -/
def originalCartesianTensorEquiv (M : X.Modules) :
    (ModuleCat.extendScalars (algebraMap R S)).obj (originalBaseSections f M) ≃+
      (ModuleCat.extendScalars g.appTop.hom).obj (ModuleCat.of Γ(X, ⊤) Γ(M, ⊤)) := by
  letI : Algebra R Γ(X, ⊤) := FlatGlobalSections.sectionsAlgebra f
  letI : Algebra S Γ(Y, ⊤) := FlatGlobalSections.sectionsAlgebra q
  letI : Algebra Γ(X, ⊤) Γ(Y, ⊤) := g.appTop.hom.toAlgebra
  letI : Algebra R Γ(Y, ⊤) :=
    ((ProperBirationalSections.coefficientMap q).comp (algebraMap R S)).toAlgebra
  letI : IsScalarTower R S Γ(Y, ⊤) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsScalarTower R Γ(X, ⊤) Γ(Y, ⊤) :=
    IsScalarTower.of_algebraMap_eq fun r =>
      (RingHom.congr_fun (originalCoefficientSquare f q g H.w) r).symm
  letI : Algebra.IsPushout R S Γ(X, ⊤) Γ(Y, ⊤) :=
    CommRingCat.isPushout_iff_isPushout.mp (originalCartesianSectionSquare f q g H).flip
  letI : IsScalarTower R Γ(X, ⊤) (originalBaseSections f M) :=
    ⟨fun r a m => by
      change (ProperBirationalSections.coefficientMap f r * a) • m =
        ProperBirationalSections.coefficientMap f r • (a • m)
      exact mul_smul _ _ _⟩
  exact (TensorProduct.congr (originalScalarEquiv (R := R) (S := S))
    (LinearEquiv.refl R (originalBaseSections f M))).toAddEquiv |>.trans
      (Algebra.IsPushout.cancelBaseChange R S Γ(X, ⊤) Γ(Y, ⊤)
        (originalBaseSections f M)).symm.toAddEquiv |>.trans
      (TensorProduct.congr (originalScalarEquiv (R := Γ(X, ⊤)) (S := Γ(Y, ⊤))).symm
        (LinearEquiv.refl Γ(X, ⊤) Γ(M, ⊤))).toAddEquiv

/-- Every original tensor keeps the literal original second coefficient map. -/
theorem originalCartesianTensorEquiv_tmul (M : X.Modules) (b : S)
    (s : originalBaseSections f M) :
    originalCartesianTensorEquiv f q g H M (b ⊗ₜ[R, algebraMap R S] s) =
      (ProperBirationalSections.coefficientMap q b) ⊗ₜ[Γ(X, ⊤), g.appTop.hom] s := by
  simp [originalCartesianTensorEquiv, originalScalarEquiv,
    Algebra.IsPushout.cancelBaseChange_symm_tmul]
  rfl

/-- The SAME original map is the native map through the derived original
tensor-domain iso, by its literal pure tensors. -/
theorem originalCartesianMap_eq_sectionExtensionMap (M : X.Modules)
    (z : (ModuleCat.extendScalars (algebraMap R S)).obj (originalBaseSections f M)) :
    originalBaseChangeMap f q g H.w M z =
      sectionExtensionMap g M (originalCartesianTensorEquiv f q g H M z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b s =>
      rw [originalBaseChangeMap_tmul, originalCartesianTensorEquiv_tmul,
        sectionExtensionMap_tmul]
      rfl
  | add z w hz hw => simp only [map_add, hz, hw]

/-- Actual affineness and quasicoherence DERIVE the original map's bijection
on the SAME actual Cartesian base square. -/
theorem originalCartesianMap_bijective_of_affine [IsAffine X] [IsAffine Y]
    (M : X.Modules) [M.IsQuasicoherent] :
    Function.Bijective (originalBaseChangeMap f q g H.w M) := by
  have h : (fun z => originalBaseChangeMap f q g H.w M z) =
      (fun z => sectionExtensionMap g M (originalCartesianTensorEquiv f q g H M z)) :=
    funext (originalCartesianMap_eq_sectionExtensionMap f q g H M)
  rw [show (originalBaseChangeMap f q g H.w M : _ → _) = _ from h]
  exact (sectionExtensionMap_bijective_of_affine g M).comp
    (originalCartesianTensorEquiv f q g H M).bijective

end Cartesian

/-- The chosen-product specialization is EXACTLY the frozen original affine
producer, with no replacement of its rings, sheaf, or coefficient maps. -/
theorem originalCartesianTensorEquiv_chosen {R S : Type u}
    [CommRing R] [CommRing S] [Algebra R S] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [Module.Flat R S]
    [QuasiCompact f] [QuasiSeparated f] (M : X.Modules) :
    originalCartesianTensorEquiv f (FlatGlobalSections.structureMap (S := S) f)
      (FlatGlobalSections.firstProjection (S := S) f)
      (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom (algebraMap R S)))) M =
        originalProductTensorEquiv (S := S) f M := by
  rfl

/-- The actual original map on ANY original affine open is bijective,
through its ACTUAL canonical E comparison and genuine Cartesian square. -/
theorem originalBaseOpenChangeMap_bijective_of_affine {R S : Type u}
    [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (q : Y ⟶ Spec (CommRingCat.of S)) (g : Y ⟶ X)
    (H : IsPullback g q f (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    (M : X.Modules) [M.IsQuasicoherent] (U : X.Opens) (hU : IsAffineOpen U) :
    Function.Bijective (originalBaseOpenChangeMap f q g H.w M U) := by
  let V : Y.Opens := g ⁻¹ᵁ U
  let fU := U.ι ≫ f
  let qV := V.ι ≫ q
  let gU := g ∣_ U
  have h : IsPullback gU qV fU (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
    (isPullback_morphismRestrict g U).paste_vert H
  let : IsAffine U.toScheme := hU
  let : IsAffine V.toScheme := (IsAffine.iff_of_isIso h.isoPullback.hom).mpr inferInstance
  have hb := originalCartesianMap_bijective_of_affine fU qV gU h (M.restrict U.ι)
  let eD := (ModuleCat.extendScalars (algebraMap R S)).mapIso
    (originalBaseRestrictedSectionsIso f M U).symm
  let eT := originalBaseOpenLocalIso q g M U
  have hmap : (fun z => eT.hom (originalBaseOpenChangeMap f q g H.w M U z)) =
      (fun z => originalBaseChangeMap fU qV gU h.w (M.restrict U.ι) (eD.hom z)) := by
    funext z
    exact ConcreteCategory.congr_hom (originalBaseOpenChangeMap_local_square f q g H.w M U) z
  have hcomp : Function.Bijective
      (fun z => eT.hom (originalBaseOpenChangeMap f q g H.w M U z)) := by
    rw [hmap]
    exact hb.comp (ConcreteCategory.bijective_of_isIso eD.hom)
  refine ⟨?_, ?_⟩
  · intro a b hab
    exact hcomp.1 (congrArg (fun s => eT.hom s) hab)
  · intro s
    obtain ⟨z, hz⟩ := hcomp.2 (eT.hom s)
    exact ⟨z, (ConcreteCategory.bijective_of_isIso eT.hom).1 hz⟩

section OpenLaurent
variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of R))
  (q : Y ⟶ Spec (CommRingCat.of R[T;T⁻¹])) (g : Y ⟶ X)

/-- Literal reconstruction of the SAME original open map from its actual
finite Laurent tensor coefficients, retaining all negative powers. -/
theorem originalBaseOpenChangeMap_laurent_reconstruction
    (hg : g ≫ f = q ≫ Spec.map (CommRingCat.ofHom (algebraMap R R[T;T⁻¹])))
    (M : X.Modules) (U : X.Opens)
    (c : ℤ →₀ (originalBaseOpenPresheaf f M).obj (op U)) :
    originalBaseOpenChangeMap f q g hg M U
        ((originalLaurentDomainCoefficients ((originalBaseOpenPresheaf f M).obj (op U))).symm c) =
      c.sum (fun n s => (LaurentPolynomial.T n : R[T;T⁻¹]) •
        (show (originalBaseOpenPresheaf q ((Scheme.Modules.pullback g).obj M)).obj (op (g ⁻¹ᵁ U)) from
          pullbackOpenRestrictMap g M U s)) := by
  rw [originalLaurentDomainCoefficients_symm]
  simp only [Finsupp.sum, map_sum]
  apply Finset.sum_congr rfl
  intro n _hn
  exact originalBaseOpenChangeMap_tmul f q g hg M U _ _

/-- Every section on the SAME original inverse image of an affine open has
UNIQUE finite ORIGINAL open coefficients; no decomposition is an input. -/
theorem exists_unique_original_affine_open_laurent_expansion
    (H : IsPullback g q f (Spec.map (CommRingCat.ofHom (algebraMap R R[T;T⁻¹]))))
    (M : X.Modules) [M.IsQuasicoherent] (U : X.Opens) (hU : IsAffineOpen U)
    (s : (originalBaseOpenPresheaf q ((Scheme.Modules.pullback g).obj M)).obj (op (g ⁻¹ᵁ U))) :
    ∃! c : ℤ →₀ (originalBaseOpenPresheaf f M).obj (op U),
      c.sum (fun n m => (LaurentPolynomial.T n : R[T;T⁻¹]) •
        (show (originalBaseOpenPresheaf q ((Scheme.Modules.pullback g).obj M)).obj (op (g ⁻¹ᵁ U)) from
          pullbackOpenRestrictMap g M U m)) = s := by
  let : Module.Free R R[T;T⁻¹] := Module.Free.of_basis (AddMonoidAlgebra.basis ℤ R)
  have hb := originalBaseOpenChangeMap_bijective_of_affine f q g H M U hU
  obtain ⟨z, hz⟩ := hb.2 s
  let V := (originalBaseOpenPresheaf f M).obj (op U)
  refine ⟨originalLaurentDomainCoefficients V z, ?_, ?_⟩
  · have hc := originalBaseOpenChangeMap_laurent_reconstruction f q g H.w M U
      (originalLaurentDomainCoefficients V z)
    rw [(originalLaurentDomainCoefficients _).symm_apply_apply] at hc
    exact hc.symm.trans hz
  · intro c hc
    apply (originalLaurentDomainCoefficients V).symm.injective
    apply hb.1
    rw [(originalLaurentDomainCoefficients _).symm_apply_apply,
      originalBaseOpenChangeMap_laurent_reconstruction]
    exact hc.trans hz.symm

end OpenLaurent
end EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
