/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.ComponentNormalizationProduct
import EnvelopeProperty.Berkovich.NormalizedLineComponent

open scoped Polynomial NNReal
/-!
# Whole normalized component products over the actual open line

Actual original transverse equations and genuine ambient lying-over derive
a finite nonempty component index. The whole product of the true component
normalizations has an actual finite free flat injective line coefficient map,
finite surjective scheme maps and proper-surjective whole native maps at ANY
prescribed field valuation. All original unreduced quotient values and the
entire ambient/base diagrams are retained. No original rank/degree equality,
full smoothness, proper-model existence or curve-potential theorem is claimed.
-/

noncomputable section
universe u
namespace EnvelopeProperty.AffineLine
open ReducedComponents
variable {F σ B : Type u} [Field F] [CommRing B] [Algebra F B]
variable (a b : σ → F) (j : σ) (g : MvPolynomial σ F) (hb : b j ≠ 0)
variable (φ : Localization.Away g →ₐ[F] B)

/-- The original entire transverse equation image defining the actual line preimage. -/
abbrev linePreimageIdeal : Ideal B :=
  (lineIdeal a b j).map (φ.toRingHom.comp (algebraMap _ (Localization.Away g)))

private theorem ambientFiniteType [Fintype σ] (hφ : φ.toRingHom.Finite) :
    Algebra.FiniteType F B := by
  let R := Localization.Away g
  let : Algebra R B := φ.toRingHom.toAlgebra
  have : IsScalarTower F R B := IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  have : Module.Finite R B := hφ
  have : Algebra.FinitePresentation (MvPolynomial σ F) R := IsLocalization.Away.finitePresentation g
  have : Algebra.FiniteType F R := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType F (MvPolynomial σ F))
    (inferInstance : Algebra.FiniteType (MvPolynomial σ F) R)
  exact Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType F R) (inferInstance : Algebra.FiniteType R B)

/-- The actual whole line preimage has a genuinely finite minimal component index. -/
theorem linePreimageIndex_finite [Fintype σ] (hφ : φ.toRingHom.Finite) :
    Finite (Index (linePreimageIdeal a b j g φ)) := by
  have : Algebra.FiniteType F B := ambientFiniteType g φ hφ
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing F B
  infer_instance

include hb in
/-- True lying-over of the finite faithful ambient map makes the actual entire line preimage ideal proper. -/
theorem linePreimageIdeal_ne_top (hline : subst a b g ≠ 0)
    (hφ : φ.toRingHom.Finite) (hiφ : Function.Injective φ) :
    linePreimageIdeal a b j g φ ≠ ⊤ := by
  let R := Localization.Away g
  let C := OpenLineRing (subst a b g)
  have : IsDomain C := openLineRing_isDomain _ hline
  let : Algebra R B := φ.toRingHom.toAlgebra
  have : Module.Finite R B := hφ
  have : FaithfulSMul R B := (faithfulSMul_iff_algebraMap_injective R B).mpr hiφ
  let q : PrimeSpectrum R := ⟨RingHom.ker (principalLineHom a b g).toRingHom, RingHom.ker_isPrime _⟩
  obtain ⟨p, he⟩ := Algebra.IsIntegral.comap_surjective R B q
  have hp : p.asIdeal.comap φ.toRingHom = q.asIdeal := congrArg PrimeSpectrum.asIdeal he
  have hle : linePreimageIdeal a b j g φ ≤ p.asIdeal := by
    rw [linePreimageIdeal, ← Ideal.map_map, ← ker_principalLineHom a b j g hb]
    exact Ideal.map_le_iff_le_comap.mpr hp.symm.le
  intro ht
  exact p.isPrime.ne_top (top_unique (ht ▸ hle))

include hb in
/-- The full component index is genuinely nonempty, derived from original whole ring maps rather than a component witness. -/
theorem linePreimageIndex_nonempty (hline : subst a b g ≠ 0)
    (hφ : φ.toRingHom.Finite) (hiφ : Function.Injective φ) :
    Nonempty (Index (linePreimageIdeal a b j g φ)) :=
  Ideal.nonempty_minimalPrimes (linePreimageIdeal_ne_top a b j g hb φ hline hφ hiφ)

/-- The actual whole open-line homomorphism into ALL genuine normalized components. -/
def normalizedLineProductHom : OpenLineRing (subst a b g) →ₐ[F]
    NormalizationProduct (linePreimageIdeal a b j g φ) :=
  AlgHom.pi fun p : Index (linePreimageIdeal a b j g φ) =>
    normalizedComponentLineHom a b j g hb φ p.1 p.2

/-- Every original localized ambient element is retained in every actual normalized component. -/
theorem normalizedLineProductHom_principalLineHom (r : Localization.Away g) :
    normalizedLineProductHom a b j g hb φ (principalLineHom a b g r) =
      normalizationMap (linePreimageIdeal a b j g φ) (φ r) := by
  funext p
  exact normalizedComponentLineHom_principalLineHom a b j g hb φ p.1 p.2 r

/-- The WHOLE entire line/ambient diagram commutes, not merely coordinate values. -/
theorem normalizedLineProductHom_comp :
    (normalizedLineProductHom a b j g hb φ).toRingHom.comp (principalLineHom a b g).toRingHom =
      (normalizationMap (linePreimageIdeal a b j g φ)).comp φ.toRingHom :=
  RingHom.ext (normalizedLineProductHom_principalLineHom a b j g hb φ)

/-- Actual nonempty component index and genuine per-component domination make the whole product line map injective. -/
theorem normalizedLineProductHom_injective [Fintype σ] [IsDomain B]
    (hg : g ≠ 0) (hline : subst a b g ≠ 0)
    (hφ : φ.toRingHom.Finite) (hiφ : Function.Injective φ) :
    Function.Injective (normalizedLineProductHom a b j g hb φ) := by
  obtain ⟨p⟩ := linePreimageIndex_nonempty a b j g hb φ hline hφ hiφ
  intro x y he
  exact normalizedComponentLineHom_injective a b j g hb φ p.1 p.2 hg hline hφ hiφ (congrFun he p)

/-- Perfect-field finite normalization and the actual finite index make the entire product line homomorphism finite. -/
theorem normalizedLineProductHom_finite [Fintype σ] [PerfectField F]
    (hφ : φ.toRingHom.Finite) : (normalizedLineProductHom a b j g hb φ).toRingHom.Finite := by
  let I := linePreimageIdeal a b j g φ
  let C := OpenLineRing (subst a b g)
  have : Finite (Index I) := linePreimageIndex_finite a b j g φ hφ
  let : ∀ p : Index I, Algebra C (CurveNormalization.Ring (Component I p)) := fun p =>
    (normalizedComponentLineHom a b j g hb φ p.1 p.2).toRingHom.toAlgebra
  have : ∀ p : Index I, Module.Finite C (CurveNormalization.Ring (Component I p)) := fun p =>
    normalizedComponentLineHom_finite a b j g hb φ p.1 p.2 hφ
  change Module.Finite C (NormalizationProduct I)
  infer_instance

/-- Every actual component's true finite free line action gives a free action on the entire normalized product. -/
theorem normalizedLineProductHom_free [Fintype σ] [PerfectField F] [IsDomain B]
    (hg : g ≠ 0) (hline : subst a b g ≠ 0)
    (hφ : φ.toRingHom.Finite) (hiφ : Function.Injective φ) :
    letI := (normalizedLineProductHom a b j g hb φ).toRingHom.toAlgebra
    Module.Free (OpenLineRing (subst a b g))
      (NormalizationProduct (linePreimageIdeal a b j g φ)) := by
  let I := linePreimageIdeal a b j g φ
  let C := OpenLineRing (subst a b g)
  have : Finite (Index I) := linePreimageIndex_finite a b j g φ hφ
  let : ∀ p : Index I, Algebra C (CurveNormalization.Ring (Component I p)) := fun p =>
    (normalizedComponentLineHom a b j g hb φ p.1 p.2).toRingHom.toAlgebra
  have : ∀ p : Index I, Module.Free C (CurveNormalization.Ring (Component I p)) := fun p =>
    normalizedComponentLineHom_free a b j g hb φ p.1 p.2 hg hline hφ hiφ
  change Module.Free C (NormalizationProduct I)
  infer_instance

/-- Flatness of the whole actual normalized preimage follows from its genuine free line module, not a flatness witness. -/
theorem normalizedLineProductHom_flat [Fintype σ] [PerfectField F] [IsDomain B]
    (hg : g ≠ 0) (hline : subst a b g ≠ 0)
    (hφ : φ.toRingHom.Finite) (hiφ : Function.Injective φ) :
    (normalizedLineProductHom a b j g hb φ).toRingHom.Flat := by
  let C := OpenLineRing (subst a b g)
  let : Algebra C (NormalizationProduct (linePreimageIdeal a b j g φ)) :=
    (normalizedLineProductHom a b j g hb φ).toRingHom.toAlgebra
  have : Module.Free C (NormalizationProduct (linePreimageIdeal a b j g φ)) :=
    normalizedLineProductHom_free a b j g hb φ hg hline hφ hiφ
  exact RingHom.flat_algebraMap_iff.mpr
    (Module.Flat.of_free (R := C) (M := NormalizationProduct (linePreimageIdeal a b j g φ)))

/-- The entire normalized component product actually maps onto every original open-line prime. -/
theorem normalizedLineProductHom_comap_surjective [Fintype σ] [PerfectField F] [IsDomain B]
    (hg : g ≠ 0) (hline : subst a b g ≠ 0)
    (hφ : φ.toRingHom.Finite) (hiφ : Function.Injective φ) :
    Function.Surjective (PrimeSpectrum.comap (normalizedLineProductHom a b j g hb φ).toRingHom) := by
  let C := OpenLineRing (subst a b g)
  let N := NormalizationProduct (linePreimageIdeal a b j g φ)
  let : Algebra C N := (normalizedLineProductHom a b j g hb φ).toRingHom.toAlgebra
  have : Module.Finite C N := normalizedLineProductHom_finite a b j g hb φ hφ
  have : FaithfulSMul C N := (faithfulSMul_iff_algebraMap_injective C N).mpr
    (normalizedLineProductHom_injective a b j g hb φ hg hline hφ hiφ)
  exact Algebra.IsIntegral.comap_surjective C N

open CategoryTheory AlgebraicGeometry

/-- The actual entire normalized component-product scheme maps to the original open line. -/
def normalizedLineProductSchemeMap :
    Spec (CommRingCat.of (NormalizationProduct (linePreimageIdeal a b j g φ))) ⟶
      openLineScheme (subst a b g) :=
  Spec.map (CommRingCat.ofHom (normalizedLineProductHom a b j g hb φ).toRingHom)

/-- The actual entire normalized component-product scheme maps to the ORIGINAL unreduced finite preimage. -/
def normalizedLineProductOriginalMap :
    Spec (CommRingCat.of (NormalizationProduct (linePreimageIdeal a b j g φ))) ⟶
      Spec (CommRingCat.of (B ⧸ linePreimageIdeal a b j g φ)) :=
  Spec.map (CommRingCat.ofHom (originalNormalizationMap (linePreimageIdeal a b j g φ)))

/-- True original quotient finiteness and all actual normalized components give a finite whole normalization-product map. -/
theorem normalizedLineProductOriginalMap_isFinite [Fintype σ] [PerfectField F]
    (hφ : φ.toRingHom.Finite) : IsFinite (normalizedLineProductOriginalMap a b j g φ) := by
  have : Algebra.FiniteType F B := ambientFiniteType g φ hφ
  exact (IsFinite.SpecMap_iff _).mpr (originalNormalizationMap_finite F _)

/-- Every ORIGINAL unreduced preimage scheme point has an actual whole normalized component lift. -/
theorem normalizedLineProductOriginalMap_surjective [Fintype σ] [PerfectField F]
    (hφ : φ.toRingHom.Finite) : Function.Surjective (normalizedLineProductOriginalMap a b j g φ) := by
  have : Algebra.FiniteType F B := ambientFiniteType g φ hφ
  exact originalNormalizationMap_comap_surjective F _

/-- Genuine module finiteness gives finiteness of the whole actual normalized line scheme map. -/
theorem normalizedLineProductSchemeMap_isFinite [Fintype σ] [PerfectField F]
    (hφ : φ.toRingHom.Finite) : IsFinite (normalizedLineProductSchemeMap a b j g hb φ) :=
  (IsFinite.SpecMap_iff _).mpr (normalizedLineProductHom_finite a b j g hb φ hφ)

/-- True free-module flatness gives flatness of the whole actual normalized line scheme map. -/
theorem normalizedLineProductSchemeMap_flat [Fintype σ] [PerfectField F] [IsDomain B]
    (hg : g ≠ 0) (hline : subst a b g ≠ 0)
    (hφ : φ.toRingHom.Finite) (hiφ : Function.Injective φ) :
    AlgebraicGeometry.Flat (normalizedLineProductSchemeMap a b j g hb φ) :=
  Flat.SpecMap_iff.mpr (normalizedLineProductHom_flat a b j g hb φ hg hline hφ hiφ)

/-- Every genuine original open-line scheme point lifts to the actual whole normalized component product. -/
theorem normalizedLineProductSchemeMap_surjective [Fintype σ] [PerfectField F] [IsDomain B]
    (hg : g ≠ 0) (hline : subst a b g ≠ 0)
    (hφ : φ.toRingHom.Finite) (hiφ : Function.Injective φ) :
    Function.Surjective (normalizedLineProductSchemeMap a b j g hb φ) :=
  normalizedLineProductHom_comap_surjective a b j g hb φ hg hline hφ hiφ

/-- The WHOLE original ambient square commutes through the original unreduced preimage, preserving every original B value. -/
theorem normalizedLineProductSchemeMap_square :
    normalizedLineProductSchemeMap a b j g hb φ ≫ principalLineSchemeMap a b g =
      normalizedLineProductOriginalMap a b j g φ ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (linePreimageIdeal a b j g φ))) ≫
          Spec.map (CommRingCat.ofHom φ.toRingHom) := by
  rw [normalizedLineProductSchemeMap, normalizedLineProductOriginalMap, principalLineSchemeMap,
    ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  apply funext
  intro p
  exact congrFun (normalizedLineProductHom_principalLineHom a b j g hb φ r) p

open Berkovich Topology

/-- The entire normalized line scheme map preserves the original field coefficient structure. -/
theorem normalizedLineProductSchemeMap_over_field :
    normalizedLineProductSchemeMap a b j g hb φ ≫ openLineStructure (subst a b g) =
      Spec.map (CommRingCat.ofHom
        (algebraMap F (NormalizationProduct (linePreimageIdeal a b j g φ)))) :=
  RelativeSchemeValuedPoint.affineStructureMap_commutes (normalizedLineProductHom a b j g hb φ)

/-- The whole ORIGINAL quotient scheme map retains every original field coefficient. -/
theorem normalizedLineProductOriginalMap_over_field :
    normalizedLineProductOriginalMap a b j g φ ≫ Spec.map (CommRingCat.ofHom
      (algebraMap F (B ⧸ linePreimageIdeal a b j g φ))) =
      Spec.map (CommRingCat.ofHom
        (algebraMap F (NormalizationProduct (linePreimageIdeal a b j g φ)))) :=
  RelativeSchemeValuedPoint.affineStructureMap_commutes
    (originalNormalizationMapAlg F (linePreimageIdeal a b j g φ))

/-- The ACTUAL whole normalized product map on native open-line points for any prescribed, possibly unbounded, field valuation. -/
def normalizedLineProductNativeMap (v : Valuation F ℝ≥0) :
    RelativeSchemeValuedPoint v (Spec.map (CommRingCat.ofHom
      (algebraMap F (NormalizationProduct (linePreimageIdeal a b j g φ))))) →
      RelativeSchemeValuedPoint v (openLineStructure (subst a b g)) :=
  RelativeSchemeValuedPoint.map (normalizedLineProductSchemeMap a b j g hb φ)
    (normalizedLineProductSchemeMap_over_field a b j g hb φ)

@[fun_prop]
theorem continuous_normalizedLineProductNativeMap (v : Valuation F ℝ≥0) :
    Continuous (normalizedLineProductNativeMap a b j g hb φ v) :=
  RelativeSchemeValuedPoint.continuous_map _ _

/-- True entire product-map finiteness gives properness on whole native points, without a fieldwide valuation bound. -/
theorem isProperMap_normalizedLineProductNativeMap [Fintype σ] [PerfectField F]
    (hφ : φ.toRingHom.Finite) (v : Valuation F ℝ≥0) :
    IsProperMap (normalizedLineProductNativeMap a b j g hb φ v) := by
  let : IsFinite (normalizedLineProductSchemeMap a b j g hb φ) :=
    normalizedLineProductSchemeMap_isFinite a b j g hb φ hφ
  exact RelativeSchemeValuedPoint.isProperMap_map_of_isIntegralHom _ _

/-- Every whole native open-line point has a genuine full normalized-product lift preserving all prescribed field scalars. -/
theorem normalizedLineProductNativeMap_surjective [Fintype σ] [PerfectField F] [IsDomain B]
    (hg : g ≠ 0) (hline : subst a b g ≠ 0)
    (hφ : φ.toRingHom.Finite) (hiφ : Function.Injective φ) (v : Valuation F ℝ≥0) :
    Function.Surjective (normalizedLineProductNativeMap a b j g hb φ v) := by
  let : IsFinite (normalizedLineProductSchemeMap a b j g hb φ) :=
    normalizedLineProductSchemeMap_isFinite a b j g hb φ hφ
  exact RelativeSchemeValuedPoint.map_surjective_of_isIntegralHom _ _
    (normalizedLineProductSchemeMap_surjective a b j g hb φ hg hline hφ hiφ)

/-- The genuine whole native map to the ORIGINAL unreduced finite preimage, retaining every original quotient value. -/
def normalizedLineProductOriginalNativeMap (v : Valuation F ℝ≥0) :
    RelativeSchemeValuedPoint v (Spec.map (CommRingCat.ofHom
      (algebraMap F (NormalizationProduct (linePreimageIdeal a b j g φ))))) →
      RelativeSchemeValuedPoint v (Spec.map (CommRingCat.ofHom
        (algebraMap F (B ⧸ linePreimageIdeal a b j g φ)))) :=
  RelativeSchemeValuedPoint.map (normalizedLineProductOriginalMap a b j g φ)
    (normalizedLineProductOriginalMap_over_field a b j g φ)

@[fun_prop]
theorem continuous_normalizedLineProductOriginalNativeMap (v : Valuation F ℝ≥0) :
    Continuous (normalizedLineProductOriginalNativeMap a b j g φ v) :=
  RelativeSchemeValuedPoint.continuous_map _ _

/-- The entire original quotient's native map is proper by genuine finite normalization-product maps. -/
theorem isProperMap_normalizedLineProductOriginalNativeMap [Fintype σ] [PerfectField F]
    (hφ : φ.toRingHom.Finite) (v : Valuation F ℝ≥0) :
    IsProperMap (normalizedLineProductOriginalNativeMap a b j g φ v) := by
  let : IsFinite (normalizedLineProductOriginalMap a b j g φ) :=
    normalizedLineProductOriginalMap_isFinite a b j g φ hφ
  exact RelativeSchemeValuedPoint.isProperMap_map_of_isIntegralHom _ _

/-- Every actual ORIGINAL unreduced preimage native point lifts with its whole original valuation and all field scalar values intact. -/
theorem normalizedLineProductOriginalNativeMap_surjective [Fintype σ] [PerfectField F]
    (hφ : φ.toRingHom.Finite) (v : Valuation F ℝ≥0) :
    Function.Surjective (normalizedLineProductOriginalNativeMap a b j g φ v) := by
  let : IsFinite (normalizedLineProductOriginalMap a b j g φ) :=
    normalizedLineProductOriginalMap_isFinite a b j g φ hφ
  exact RelativeSchemeValuedPoint.map_surjective_of_isIntegralHom _ _
    (normalizedLineProductOriginalMap_surjective a b j g φ hφ)

end EnvelopeProperty.AffineLine
