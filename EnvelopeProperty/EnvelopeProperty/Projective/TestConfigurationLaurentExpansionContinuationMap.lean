import ModularCurves.ForMathlib.AffineModuleBaseChange
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Algebra.MonoidAlgebra.Module
import EnvelopeProperty.FlatGlobalSections

/-! # Actual whole section extension before test-configuration Laurent expansion

The map is constructed from the original pullback adjunction. Its affine
bijectivity is derived, not supplied. Laurent tensor coefficients are finite
by the actual monomial basis. Whole nonaffine H0 base change remains a consumer.
-/

open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct ChangeOfRings LaurentPolynomial
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
open Scheme.Modules

/-- The actual pullback-adjunction unit on WHOLE original sections,
retaining the SAME original map on coefficient rings. -/
def pullbackTopRestrictMap {X Y : Scheme.{u}} (g : Y ⟶ X) (M : X.Modules) :
    ModuleCat.of Γ(X, ⊤) Γ(M, ⊤) ⟶
      (ModuleCat.restrictScalars g.appTop.hom).obj
        (ModuleCat.of Γ(Y, ⊤) Γ((pullback g).obj M, ⊤)) :=
  ModuleCat.ofHom (Y := (ModuleCat.restrictScalars g.appTop.hom).obj
    (ModuleCat.of Γ(Y, ⊤) Γ((pullback g).obj M, ⊤)))
    { toFun := (((pullbackPushforwardAdjunction g).unit.app M).val.app (op ⊤)).hom
      map_add' := (((pullbackPushforwardAdjunction g).unit.app M).val.app (op ⊤)).hom.map_add
      map_smul' := (((pullbackPushforwardAdjunction g).unit.app M).val.app (op ⊤)).hom.map_smul }

/-- Canonical transport of the original top-open component is the same
native original whole section, not a new choice of section. -/
theorem pullbackTopRestrictMap_apply {X Y : Scheme.{u}} (g : Y ⟶ X) (M : X.Modules)
    (s : Γ(M, ⊤)) : pullbackTopRestrictMap g M s = affinePullbackUnitTop g M s := by
  have hi : (eqToHom (show (⊤ : Y.Opens) = g ⁻¹ᵁ (⊤ : X.Opens) by simp)).op =
      𝟙 (op (⊤ : Y.Opens)) := Subsingleton.elim _ _
  simp only [affinePullbackUnitTop, hi]
  erw [((pullback g).obj M).presheaf.map_id]
  rfl

/-- The canonical actual whole H0 extension map, constructed by the
native scalar-extension adjunction from the genuine geometric unit. -/
def sectionExtensionMap {X Y : Scheme.{u}} (g : Y ⟶ X) (M : X.Modules) :
    (ModuleCat.extendScalars g.appTop.hom).obj (ModuleCat.of Γ(X, ⊤) Γ(M, ⊤)) ⟶
      ModuleCat.of Γ(Y, ⊤) Γ((pullback g).obj M, ⊤) :=
  ((ModuleCat.extendRestrictScalarsAdj g.appTop.hom).homEquiv _ _).symm
    (pullbackTopRestrictMap g M)

/-- Every actual pure tensor retains its coefficient and original
pullback section, without an assumed section or norm comparison. -/
theorem sectionExtensionMap_tmul {X Y : Scheme.{u}} (g : Y ⟶ X) (M : X.Modules)
    (b : Γ(Y, ⊤)) (s : Γ(M, ⊤)) :
    sectionExtensionMap g M (b ⊗ₜ[Γ(X, ⊤), g.appTop.hom] s) =
      b • affinePullbackUnitTop g M s := by
  let : Module Γ(X, ⊤) Γ((pullback g).obj M, ⊤) := Module.compHom _ g.appTop.hom
  change ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars g.appTop.hom
    (pullbackTopRestrictMap g M) (b ⊗ₜ[Γ(X, ⊤), g.appTop.hom] s) = _
  erw [ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_hom_apply]
  rw [TensorProduct.lift.tmul]
  exact congrArg (fun z => b • z) (pullbackTopRestrictMap_apply g M s)

/-- On actual affine schemes, the SAME canonical whole section map is
the genuine native affine pullback comparison. -/
theorem sectionExtensionMap_eq_affine {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (g : Y ⟶ X) (M : X.Modules) [M.IsQuasicoherent] :
    sectionExtensionMap g M = (affinePullbackΓIso g M).hom := by
  apply ((ModuleCat.extendRestrictScalarsAdj g.appTop.hom).homEquiv _ _).injective
  simp only [sectionExtensionMap, Equiv.apply_symm_apply]
  ext s
  change pullbackTopRestrictMap g M s =
    (affinePullbackΓIso g M).hom ((1 : Γ(Y, ⊤)) ⊗ₜ[Γ(X, ⊤), g.appTop.hom] s)
  exact (pullbackTopRestrictMap_apply g M s).trans
    (affinePullbackΓIso_hom_one_tmul g M s).symm

/-- Actual affineness and quasicoherence DERIVE bijectivity of the
original whole-section extension map. -/
theorem sectionExtensionMap_bijective_of_affine {X Y : Scheme.{u}}
    [IsAffine X] [IsAffine Y] (g : Y ⟶ X) (M : X.Modules) [M.IsQuasicoherent] :
    Function.Bijective (sectionExtensionMap g M) := by
  rw [sectionExtensionMap_eq_affine]
  exact ConcreteCategory.bijective_of_isIso (affinePullbackΓIso g M).hom

section LaurentCoefficients
variable {R V : Type u} [CommRing R] [AddCommGroup V] [Module R V]

/-- The SAME actual Laurent monomials identify the original tensor
module with finitely supported original coefficients. -/
def laurentTensorCoefficients : R[T;T⁻¹] ⊗[R] V ≃ₗ[R] ℤ →₀ V :=
  TensorProduct.equivFinsuppOfBasisLeft (AddMonoidAlgebra.basis ℤ R)

/-- The inverse uses the literal original monomials, retaining every
negative exponent and every original coefficient. -/
theorem laurentTensorCoefficients_symm (c : ℤ →₀ V) :
    (laurentTensorCoefficients (R := R) (V := V)).symm c =
      c.sum (fun n s => (LaurentPolynomial.T n : R[T;T⁻¹]) ⊗ₜ[R] s) := by
  rw [laurentTensorCoefficients, TensorProduct.equivFinsuppOfBasisLeft_symm_apply]
  rfl

/-- Every element of the ACTUAL Laurent tensor module has a unique
finite coefficient family; no decomposition is an input. -/
theorem exists_unique_laurent_tensor_expansion (z : R[T;T⁻¹] ⊗[R] V) :
    ∃! c : ℤ →₀ V,
      c.sum (fun n s => (LaurentPolynomial.T n : R[T;T⁻¹]) ⊗ₜ[R] s) = z := by
  refine ⟨laurentTensorCoefficients z, ?_, ?_⟩
  · exact (laurentTensorCoefficients_symm
      (laurentTensorCoefficients (R := R) (V := V) z)).symm.trans
      ((laurentTensorCoefficients (R := R) (V := V)).symm_apply_apply z)
  · intro c hc
    apply (laurentTensorCoefficients (R := R) (V := V)).symm.injective
    rw [laurentTensorCoefficients_symm, hc,
      (laurentTensorCoefficients (R := R) (V := V)).symm_apply_apply]

end LaurentCoefficients

section OriginalBase
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
  (q : Y ⟶ Spec (CommRingCat.of S)) (g : Y ⟶ X)
  (hg : g ≫ f = q ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)))

/-- The actual coefficient square is derived from the original whole
scheme diagram, with the original ΓSpec comparisons. -/
theorem originalCoefficientSquare
    (hbase : g ≫ f = q ≫ Spec.map (CommRingCat.ofHom (algebraMap R S))) :
    g.appTop.hom.comp (ProperBirationalSections.coefficientMap f) =
      (ProperBirationalSections.coefficientMap q).comp (algebraMap R S) := by
  change ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop ≫ g.appTop).hom = _
  rw [← Scheme.Hom.comp_appTop, hbase, Scheme.Hom.comp_appTop,
    ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

/-- WHOLE original sections with their SAME original base coefficient action. -/
abbrev originalBaseSections {A : Type u} [CommRing A] {Z : Scheme.{u}}
    (π : Z ⟶ Spec (CommRingCat.of A)) (M : Z.Modules) : ModuleCat A :=
  (ModuleCat.restrictScalars (ProperBirationalSections.coefficientMap π)).obj
    (ModuleCat.of Γ(Z, ⊤) Γ(M, ⊤))

/-- The actual original geometric section map over the actual original
base, using only the original scheme square to identify scalar actions. -/
def originalBasePullbackMap (M : X.Modules) :
    originalBaseSections f M ⟶
      (ModuleCat.restrictScalars (algebraMap R S)).obj
        (originalBaseSections q ((pullback g).obj M)) :=
  (ModuleCat.restrictScalars (ProperBirationalSections.coefficientMap f)).map
      (pullbackTopRestrictMap g M) ≫
    ((ModuleCat.restrictScalarsComp'
      (ProperBirationalSections.coefficientMap f) g.appTop.hom
      ((ProperBirationalSections.coefficientMap q).comp (algebraMap R S))
      (originalCoefficientSquare f q g hg).symm).symm.app
        (ModuleCat.of Γ(Y, ⊤) Γ((pullback g).obj M, ⊤))).hom ≫
    ((ModuleCat.restrictScalarsComp (algebraMap R S)
      (ProperBirationalSections.coefficientMap q)).app
        (ModuleCat.of Γ(Y, ⊤) Γ((pullback g).obj M, ⊤))).hom

/-- The genuine whole original base-change map, before any injectivity,
surjectivity or Laurent expansion assertion. -/
def originalBaseChangeMap (M : X.Modules) :
    (ModuleCat.extendScalars (algebraMap R S)).obj (originalBaseSections f M) ⟶
      originalBaseSections q ((pullback g).obj M) :=
  ((ModuleCat.extendRestrictScalarsAdj (algebraMap R S)).homEquiv _ _).symm
    (originalBasePullbackMap f q g hg M)

/-- The actual original base-change map retains both the literal base
coefficient and the SAME original geometrically pulled-back section. -/
theorem originalBaseChangeMap_tmul (M : X.Modules) (b : S)
    (s : originalBaseSections f M) :
    originalBaseChangeMap f q g hg M (b ⊗ₜ[R, algebraMap R S] s) =
      (b • (show originalBaseSections q ((pullback g).obj M) from
        affinePullbackUnitTop g M s)) := by
  let : Module R (originalBaseSections q ((pullback g).obj M)) :=
    Module.compHom _ (algebraMap R S)
  change ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars (algebraMap R S)
    (originalBasePullbackMap f q g hg M) (b ⊗ₜ[R, algebraMap R S] s) = _
  erw [ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_hom_apply]
  rw [TensorProduct.lift.tmul]
  change b • (show originalBaseSections q ((pullback g).obj M) from
    pullbackTopRestrictMap g M s) = _
  exact congrArg (fun z : originalBaseSections q ((pullback g).obj M) => b • z)
    (pullbackTopRestrictMap_apply g M s)

end OriginalBase

section NativeLaurentDomain
variable {R : Type u} [CommRing R]

/-- The actual extension-of-scalars coefficient action is identified
with its ORIGINAL algebra action by the literal identity function. -/
def originalScalarEquiv {S : Type u} [CommRing S] [Algebra R S] :
    (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S) ≃ₗ[R] S where
  toFun := fun s => s
  invFun := fun s => s
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  map_smul' := fun r s => (Algebra.smul_def r (show S from s)).symm

/-- Finite coefficients of the ACTUAL original scalar-extension domain,
including its original restriction-of-scalars action. -/
def originalLaurentDomainCoefficients (V : ModuleCat.{u} R) :
    (ModuleCat.extendScalars (algebraMap R R[T;T⁻¹])).obj V ≃+ (ℤ →₀ V) :=
  (TensorProduct.equivFinsuppOfBasisLeft
    ((AddMonoidAlgebra.basis ℤ R).map
      (originalScalarEquiv (R := R) (S := R[T;T⁻¹])).symm)).toAddEquiv

/-- The finite reconstruction uses the literal native monomials in
the original extension-of-scalars domain, with no supplied decomposition. -/
theorem originalLaurentDomainCoefficients_symm (V : ModuleCat.{u} R) (c : ℤ →₀ V) :
    (originalLaurentDomainCoefficients V).symm c =
      c.sum (fun n s => (LaurentPolynomial.T n : R[T;T⁻¹])
        ⊗ₜ[R, algebraMap R R[T;T⁻¹]] s) := by
  change (TensorProduct.equivFinsuppOfBasisLeft
    ((AddMonoidAlgebra.basis ℤ R).map
      (originalScalarEquiv (R := R) (S := R[T;T⁻¹])).symm)).symm c = _
  rw [TensorProduct.equivFinsuppOfBasisLeft_symm_apply]
  rfl

/-- Every element in the image of the SAME original Laurent section
base-change map has a derived finite family of ORIGINAL global coefficients.
This does not assert surjectivity of the map on a nonaffine scheme. -/
theorem originalBaseChangeMap_laurent_expansion {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R))
    (q : Y ⟶ Spec (CommRingCat.of R[T;T⁻¹])) (g : Y ⟶ X)
    (hg : g ≫ f = q ≫ Spec.map (CommRingCat.ofHom (algebraMap R R[T;T⁻¹])))
    (M : X.Modules)
    (z : (ModuleCat.extendScalars (algebraMap R R[T;T⁻¹])).obj (originalBaseSections f M)) :
    ∃ c : ℤ →₀ originalBaseSections f M,
      originalBaseChangeMap f q g hg M z = c.sum (fun n s =>
        (LaurentPolynomial.T n : R[T;T⁻¹]) •
          (show originalBaseSections q ((pullback g).obj M) from affinePullbackUnitTop g M s)) := by
  let c := originalLaurentDomainCoefficients (originalBaseSections f M) z
  refine ⟨c, ?_⟩
  have hz : c.sum (fun n s => (LaurentPolynomial.T n : R[T;T⁻¹])
      ⊗ₜ[R, algebraMap R R[T;T⁻¹]] s) = z :=
    (originalLaurentDomainCoefficients_symm _ c).symm.trans
      ((originalLaurentDomainCoefficients _).symm_apply_apply z)
  rw [← hz]
  simp only [Finsupp.sum, map_sum]
  apply Finset.sum_congr rfl
  intro n _hn
  exact originalBaseChangeMap_tmul f q g hg M _ _

end NativeLaurentDomain
end EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
