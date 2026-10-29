/-
Mathlib-only proof port. Original source: EnvelopeProperty/ComplexGeometry/Schemes/CotangentSheaf.lean
Upstream SHA256: 5df02ff5b6b4b200adc7820b80a0d39801a4cac156b82234b9055b1244da7620
Upstream canonical-source commit: feaaab87c3197e6e4f18c6176d50b5c739c81b50
Compatibility changes: module imports and enclosing namespace only.
Original mathematical statements and proofs below are preserved.
-/
import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-!
# The actual relative cotangent sheaf

For a scheme over a field, construct the presheaf of relative Kähler
differentials from the structure presheaf, then sheafify it as an
`𝒪_X`-module. This is the cotangent sheaf used to construct the canonical
bundle; no canonical bundle or Hilbert polynomial is prescribed here.
-/

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace TensorProduct

namespace EnvelopeProperty.CanonicalGeometry

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))

/-- The presheaf whose value is the ground field on every open set. -/
def constantRingPresheaf (K : Type u) [CommRing K] (X : Scheme.{u}) :
    X.Opensᵒᵖ ⥤ CommRingCat.{u} :=
  (Functor.const X.Opensᵒᵖ).obj (.of K)

/-- Constant functions as a natural transformation into the actual
structure presheaf, induced by the structural morphism to `Spec K`. -/
noncomputable def schemeConstantPresheafMap : constantRingPresheaf K X ⟶ X.presheaf where
  app U := (Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫
    X.presheaf.map U.unop.leTop.op
  naturality {U V} i := by
    dsimp [constantRingPresheaf]
    simp only [Category.id_comp, Category.assoc, ← Functor.map_comp]
    congr 2

/-- The actual relative cotangent presheaf: its sections on `U` are
`Ω[𝒪_X(U)/K]` and its restrictions are induced by restrictions in `𝒪_X`. -/
noncomputable def cotangentPresheaf : X.PresheafOfModules :=
  PresheafOfModules.DifferentialsConstruction.relativeDifferentials'
    (schemeConstantPresheafMap f)

/-- The universal derivation of the structure presheaf over the ground field. -/
noncomputable def cotangentPresheafDerivation :
    (cotangentPresheaf f).Derivation' (schemeConstantPresheafMap f) :=
  PresheafOfModules.DifferentialsConstruction.derivation'
    (schemeConstantPresheafMap f)

/-- Universality is constructed from the objectwise Kähler universal property. -/
noncomputable def cotangentPresheafUniversal :
    (cotangentPresheafDerivation f).Universal :=
  PresheafOfModules.DifferentialsConstruction.isUniversal'
    (schemeConstantPresheafMap f)

/-- The relative cotangent sheaf is the sheafification of the genuine
relative cotangent presheaf as a sheaf of modules over `𝒪_X`. -/
noncomputable def cotangentSheaf : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    (cotangentPresheaf f)

/-- The canonical sheafification map. -/
noncomputable def cotangentSheafificationMap : cotangentPresheaf f ⟶
    (Scheme.Modules.toPresheafOfModules X).obj (cotangentSheaf f) :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    (cotangentPresheaf f)

/-- Differentiation of actual regular functions, with values in the
underlying presheaf of the relative cotangent sheaf. -/
noncomputable def cotangentDerivation :
    ((Scheme.Modules.toPresheafOfModules X).obj (cotangentSheaf f)).Derivation'
      (schemeConstantPresheafMap f) :=
  (cotangentPresheafDerivation f).postcomp (cotangentSheafificationMap f)

@[simp]
theorem cotangentDerivation_add (U : X.Opens) (a b : Γ(X, U)) :
    (cotangentDerivation f).d (a + b) =
      (cotangentDerivation f).d a + (cotangentDerivation f).d b :=
  map_add _ _ _

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem cotangentDerivation_mul (U : X.Opens) (a b : Γ(X, U)) :
    (cotangentDerivation f).d (X := .op U) (a * b) =
      (a • ((cotangentDerivation f).d b : Γ(cotangentSheaf f, U)) +
        b • ((cotangentDerivation f).d a : Γ(cotangentSheaf f, U)) :
        Γ(cotangentSheaf f, U)) :=
  (cotangentDerivation f).d_mul (X := .op U) a b

/-- Relative differentiation annihilates the structural constant sections. -/
@[simp]
theorem cotangentDerivation_constant (U : X.Opens) (a : K) :
    (cotangentDerivation f).d ((schemeConstantPresheafMap f).app (.op U) a) = 0 :=
  (cotangentDerivation f).d_app (X := .op U) a

/-- Maps from the cotangent presheaf are precisely relative derivations. -/
noncomputable def cotangentPresheafHomEquiv (M : X.PresheafOfModules) :
    (cotangentPresheaf f ⟶ M) ≃ M.Derivation' (schemeConstantPresheafMap f) where
  toFun g := (cotangentPresheafDerivation f).postcomp g
  invFun d := (cotangentPresheafUniversal f).desc d
  left_inv _g := (cotangentPresheafUniversal f).postcomp_injective _ _
    ((cotangentPresheafUniversal f).fac _)
  right_inv d := (cotangentPresheafUniversal f).fac d

/-- The universal property of the actual cotangent sheaf: morphisms of
`𝒪_X`-modules from it correspond bijectively to relative derivations with
values in any sheaf of `𝒪_X`-modules. -/
noncomputable def cotangentSheafHomEquiv (M : X.Modules) :
    (cotangentSheaf f ⟶ M) ≃
      ((Scheme.Modules.toPresheafOfModules X).obj M).Derivation'
        (schemeConstantPresheafMap f) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)).trans
    (cotangentPresheafHomEquiv f _)

/-- Differentiation commutes with restriction to a smaller open set. -/
theorem cotangentDerivation_restrict {U V : X.Opens} (i : U ⟶ V) (a : Γ(X, V)) :
    (cotangentDerivation f).d (X.presheaf.map i.op a) =
      ((cotangentSheaf f).val.map i.op) ((cotangentDerivation f).d a) :=
  (cotangentDerivation f).d_map i.op a

set_option backward.isDefEq.respectTransparency false in
/-- The universal correspondence is postcomposition with differentiation. -/
theorem cotangentSheafHomEquiv_apply (M : X.Modules) (g : cotangentSheaf f ⟶ M) :
    cotangentSheafHomEquiv f M g =
      (cotangentDerivation f).postcomp ((Scheme.Modules.toPresheafOfModules X).map g) := by
  ext U a
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Every relative derivation into a genuine sheaf of modules has a unique
factorization through the actual cotangent sheaf. -/
theorem cotangentSheaf_derivation_factorization (M : X.Modules)
    (d : ((Scheme.Modules.toPresheafOfModules X).obj M).Derivation'
      (schemeConstantPresheafMap f)) :
    ∃! g : cotangentSheaf f ⟶ M,
      (cotangentDerivation f).postcomp ((Scheme.Modules.toPresheafOfModules X).map g) = d := by
  refine ⟨(cotangentSheafHomEquiv f M).symm d, ?_, ?_⟩
  · exact (cotangentSheafHomEquiv_apply f M _).symm.trans
      (Equiv.apply_symm_apply _ d)
  · intro g hg
    apply (cotangentSheafHomEquiv f M).injective
    rw [cotangentSheafHomEquiv_apply, hg, Equiv.apply_symm_apply]

/-- The algebra on regular functions induced by the actual structural map. -/
@[instance_reducible]
noncomputable def cotangentOpenAlgebra (U : X.Opens) : Algebra K Γ(X, U) :=
  ((schemeConstantPresheafMap f).app (.op U)).hom.toAlgebra

set_option backward.isDefEq.respectTransparency false in
/-- The section module uses the genuine ring of regular functions. -/
noncomputable instance cotangentPresheafSectionsModule (U : X.Opens) :
    Module Γ(X, U) ((cotangentPresheaf f).obj (.op U)) :=
  ((cotangentPresheaf f).obj (.op U)).isModule

set_option backward.isDefEq.respectTransparency false in
/-- Exact objectwise comparison with the ordinary algebraic Kähler module. -/
noncomputable def cotangentPresheafSectionsEquiv (U : X.Opens) :
    letI := cotangentOpenAlgebra f U
    (cotangentPresheaf f).obj (.op U) ≃ₗ[Γ(X, U)] KaehlerDifferential K Γ(X, U) := by
  letI := cotangentOpenAlgebra f U
  exact LinearEquiv.refl _ _

set_option backward.isDefEq.respectTransparency false in
/-- A standard smooth chart gives a free actual cotangent presheaf module. -/
theorem cotangentPresheaf_free_of_standardSmooth (U : X.Opens) :
    letI := cotangentOpenAlgebra f U
    Algebra.IsStandardSmooth K Γ(X, U) →
      Module.Free Γ(X, U) ((cotangentPresheaf f).obj (.op U)) := by
  let := cotangentOpenAlgebra f U
  intro h
  let := h
  exact Module.Free.of_equiv (cotangentPresheafSectionsEquiv f U).symm

set_option backward.isDefEq.respectTransparency false in
/-- The rank of the actual module on a standard smooth chart is its relative
dimension, derived from the Kähler module of its coordinate algebra. -/
theorem cotangentPresheaf_rank_of_standardSmooth (U : X.Opens) [Nontrivial Γ(X, U)]
    (n : ℕ) :
    letI := cotangentOpenAlgebra f U
    Algebra.IsStandardSmoothOfRelativeDimension n K Γ(X, U) →
      Module.rank Γ(X, U) ((cotangentPresheaf f).obj (.op U)) = n := by
  let := cotangentOpenAlgebra f U
  intro h
  let := h
  rw [(cotangentPresheafSectionsEquiv f U).rank_eq]
  exact Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n

section AffineLocalization

variable (A : CommRingCat.{u}) [Algebra K A] (r : A)

set_option backward.isDefEq.respectTransparency false in
/-- On a genuine principal affine open, the ordinary relative Kähler module
is the base change of the coordinate-algebra module. -/
noncomputable def affineCotangentLocalizationEquiv :
    letI := ((algebraMap A Γ(Spec A, PrimeSpectrum.basicOpen r)).comp
      (algebraMap K A)).toAlgebra
    Γ(Spec A, PrimeSpectrum.basicOpen r) ⊗[A] KaehlerDifferential K A ≃ₗ[
      Γ(Spec A, PrimeSpectrum.basicOpen r)]
        KaehlerDifferential K Γ(Spec A, PrimeSpectrum.basicOpen r) := by
  let B := Γ(Spec A, PrimeSpectrum.basicOpen r)
  letI := ((algebraMap A B).comp (algebraMap K A)).toAlgebra
  letI : IsScalarTower K A B := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra.FormallyEtale A B :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers r)
  exact KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K A B

/-- On an affine scheme, the structural constants really are the composite
of the coordinate-algebra constants and the usual restriction of regular
functions. -/
theorem affine_schemeConstantPresheafMap (U : (Spec A).Opens) :
    ((schemeConstantPresheafMap (Spec.map (CommRingCat.ofHom (algebraMap K A)))).app
      (.op U)).hom =
    (algebraMap A Γ(Spec A, U)).comp (algebraMap K A) := by
  change ((Scheme.ΓSpecIso (.of K)).inv ≫
    (Spec.map (CommRingCat.ofHom (algebraMap K A))).appTop ≫
    (Spec A).presheaf.map U.leTop.op).hom = _
  rw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The actual affine cotangent presheaf has the standard coordinate-algebra
relative differential module on every open set. -/
noncomputable def affineCotangentPresheafSectionsEquiv (U : (Spec A).Opens) :
    letI := ((algebraMap A Γ(Spec A, U)).comp (algebraMap K A)).toAlgebra
    (cotangentPresheaf (Spec.map (CommRingCat.ofHom (algebraMap K A)))).obj (.op U) ≃ₗ[
      Γ(Spec A, U)] KaehlerDifferential K Γ(Spec A, U) := by
  have e := cotangentPresheafSectionsEquiv
    (Spec.map (CommRingCat.ofHom (algebraMap K A))) U
  have hAlg : cotangentOpenAlgebra (Spec.map (CommRingCat.ofHom (algebraMap K A))) U =
      ((algebraMap A Γ(Spec A, U)).comp (algebraMap K A)).toAlgebra := by
    unfold cotangentOpenAlgebra
    rw [affine_schemeConstantPresheafMap]
  rw [hAlg] at e
  exact e

set_option backward.isDefEq.respectTransparency false in
/-- Exact principal-open localization comparison for the actual relative
cotangent presheaf constructed from the structural morphism. -/
noncomputable def affineCotangentPresheafLocalizationEquiv :
    Γ(Spec A, PrimeSpectrum.basicOpen r) ⊗[A] KaehlerDifferential K A ≃ₗ[
      Γ(Spec A, PrimeSpectrum.basicOpen r)]
        ((cotangentPresheaf (Spec.map (CommRingCat.ofHom (algebraMap K A)))).obj
          (.op (PrimeSpectrum.basicOpen r))) :=
  (affineCotangentLocalizationEquiv A r).trans
    (affineCotangentPresheafSectionsEquiv A (PrimeSpectrum.basicOpen r)).symm

set_option backward.isDefEq.respectTransparency false in
/-- The affine localization comparison is the canonical map on differentials,
rather than an arbitrary module equivalence. -/
theorem affineCotangentLocalizationEquiv_tmul_D
    (a : A) (b : Γ(Spec A, PrimeSpectrum.basicOpen r)) :
    letI := ((algebraMap A Γ(Spec A, PrimeSpectrum.basicOpen r)).comp
      (algebraMap K A)).toAlgebra
    affineCotangentLocalizationEquiv A r (b ⊗ₜ[A] KaehlerDifferential.D K A a) =
      b • KaehlerDifferential.D K Γ(Spec A, PrimeSpectrum.basicOpen r)
        (algebraMap A Γ(Spec A, PrimeSpectrum.basicOpen r) a) := by
  let B := Γ(Spec A, PrimeSpectrum.basicOpen r)
  let := ((algebraMap A B).comp (algebraMap K A)).toAlgebra
  let : IsScalarTower K A B := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.FormallyEtale A B :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers r)
  simp [affineCotangentLocalizationEquiv,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
    KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D]

end AffineLocalization

end EnvelopeProperty.CanonicalGeometry
