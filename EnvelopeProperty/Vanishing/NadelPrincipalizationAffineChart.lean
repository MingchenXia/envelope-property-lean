import EnvelopeProperty.Vanishing.NadelPrincipalization
import EnvelopeProperty.AlgGeom.SmoothFunctionFieldSubalgebras
import EnvelopeProperty.AlgGeom.Canonical.CotangentSmoothLocallyFree

/-! # Original affine function-field charts for global Nadel principalization

The chart algebra, its original ideal, and every structural comparison use
the actual generic germ of the original integral scheme. No local
resolution or comparison certificate is an input.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.NadelPrincipalizationAffineChart

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of k))

/-- The literal image in the original function field of the original affine sections. -/
abbrev algebra (U : X.affineOpens) [Nonempty U.1] :
    letI := f.stalkAlgebra (genericPoint X)
    Subalgebra k X.functionField :=
  f.sectionsFunctionFieldSubalgebra U.1

/-- The actual generic-germ equivalence onto that same original image. -/
def equiv (U : X.affineOpens) [Nonempty U.1] :
    letI := f.sectionsAlgebra U.1
    letI := f.stalkAlgebra (genericPoint X)
    Γ(X, U) ≃ₐ[k] algebra f U :=
  f.sectionsFunctionFieldEquiv U.1

/-- The same actual equivalence viewed on the original coefficient rings. -/
def ringEquiv (U : X.affineOpens) [Nonempty U.1] : Γ(X, U) ≃+* algebra f U := by
  let := f.sectionsAlgebra U.1
  let := f.stalkAlgebra (genericPoint X)
  exact (equiv f U).toRingEquiv

/-- The original function field is the fraction field of this actual chart algebra. -/
theorem algebra_isFractionRing (U : X.affineOpens) [Nonempty U.1] :
    letI := f.stalkAlgebra (genericPoint X)
    IsFractionRing (algebra f U) X.functionField :=
  f.sectionsFunctionFieldSubalgebra_isFractionRing U.1 U.2

attribute [local instance] algebra_isFractionRing

/-- The spectrum isomorphism induced by the same original coefficient equivalence. -/
def specIso (U : X.affineOpens) [Nonempty U.1] :
    Spec (.of (algebra f U)) ≅ Spec (.of Γ(X, U)) :=
  Scheme.Spec.mapIso (ringEquiv f U).toCommRingCatIso.op

/-- The actual coefficient spectrum enters the same original open chart of X. -/
def map (U : X.affineOpens) [Nonempty U.1] : Spec (.of (algebra f U)) ⟶ X :=
  (specIso f U).hom ≫ U.2.fromSpec

instance map_isOpenImmersion (U : X.affineOpens) [Nonempty U.1] :
    IsOpenImmersion (map f U) := by
  let : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  dsimp only [map]
  infer_instance

/-- The chart structure retains the original field and its actual structural algebra. -/
def structureMap (U : X.affineOpens) [Nonempty U.1] :
    Spec (.of (algebra f U)) ⟶ Spec (.of k) := by
  let := f.stalkAlgebra (genericPoint X)
  exact Spec.map (CommRingCat.ofHom (algebraMap k (algebra f U)))

theorem map_structure (U : X.affineOpens) [Nonempty U.1] :
    map f U ≫ f = structureMap f U := by
  let := f.sectionsAlgebra U.1
  let := f.stalkAlgebra (genericPoint X)
  change (Spec.map (CommRingCat.ofHom (ringEquiv f U).toRingHom) ≫ U.2.fromSpec) ≫ f = _
  rw [Category.assoc, CanonicalGeometry.affineChartStructuralMap f U.2]
  change Spec.map (CommRingCat.ofHom (ringEquiv f U).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, U))) =
    Spec.map (CommRingCat.ofHom (algebraMap k (algebra f U)))
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  change (ringEquiv f U) (algebraMap k Γ(X, U) r) = algebraMap k (algebra f U) r
  exact (equiv f U).commutes r

/-- Actual open pullback preserves the original prescribed relative dimension. -/
theorem structureMap_smoothOfRelativeDimension (n : ℕ) [SmoothOfRelativeDimension n f]
    (U : X.affineOpens) [Nonempty U.1] :
    SmoothOfRelativeDimension n (structureMap f U) := by
  have h := smoothOfRelativeDimension_comp (n := 0) (m := n) (map f U) f
  have hc : SmoothOfRelativeDimension n (map f U ≫ f) := by
    simpa only [Nat.zero_add] using h
  exact (map_structure f U) ▸ hc

/-- The image of the same original ideal on the actual generic-germ chart algebra. -/
def ideal (I : X.IdealSheafData) (U : X.affineOpens) [Nonempty U.1] : Ideal (algebra f U) :=
  (I.ideal U).map (ringEquiv f U).toRingHom

theorem ideal_ne_bot (I : X.IdealSheafData) (hI : I.stalkIdeal (genericPoint X) ≠ ⊥)
    (U : X.affineOpens) [Nonempty U.1] : ideal f I U ≠ ⊥ :=
by
  intro hzero
  have hUzero : I.ideal U = ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective (ringEquiv f U).injective).mp hzero
  apply hI
  rw [I.stalkIdeal_eq_map_germ U
    (((genericPoint_spec X).mem_open_set_iff U.1.isOpen).mpr
      (by simpa using (inferInstance : Nonempty U.1))), hUzero, Ideal.map_bot]

/-- The WHOLE actual original ideal pulls back to the original coefficient ideal. -/
theorem comap_ideal (I : X.IdealSheafData) (U : X.affineOpens) [Nonempty U.1] :
    I.comap (map f U) = specIdealSheaf (ideal f I U) := by
  exact comap_specMap_fromSpec U I (ringEquiv f U).toRingHom


end EnvelopeProperty.Vanishing.NadelPrincipalizationAffineChart
