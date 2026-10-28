import SGPT.Okounkov.SchemeNativeFormalNaturality
import SGPT.Okounkov.SchemeCoordinateGlobalGerm
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Literal original affine coefficients in the same native formal ring

The affine ring is the ORIGINAL `A`, independently of the preferred chart
ring chosen by smoothness. Its canonical global section, actual original
stalk and actual Taylor series are retained throughout.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Okounkov

open CategoryTheory AlgebraicGeometry BingWangEntropy Filter Set
open TranscendentalNakamaye.FirstPass TranscendentalNakamaye.Pending
open HironakaHolomorphicJetMonomialSpan HironakaActualCoefficientPresentationCentrePower
open HironakaActualFormalCoordinatePowerDivision
open scoped Topology

variable {A : Type} [CommRing A] (f : Spec (.of A) ⟶ Spec (.of ℂ))

/-- The literal original affine point map of the given scheme point. -/
def schemeAffineOriginalPoint (p : SchemeComplexPoint f) : A →+* ℂ :=
  (Spec.preimage p.val).hom

/-- The whole original point map is literally the full-faithfulness preimage of the SAME point morphism. -/
theorem schemeAffineOriginalPoint_apply (p : SchemeComplexPoint f) (a : A) :
    schemeAffineOriginalPoint f p a = (Spec.preimage p.val).hom a :=
  rfl

/-- The actual affine structure and actual point preserve every original complex scalar. -/
theorem schemeAffineOriginalPoint_scalar (p : SchemeComplexPoint f) (c : ℂ) :
    letI := affinePointFieldAlgebra f
    schemeAffineOriginalPoint f p (algebraMap ℂ A c) = c := by
  let := affinePointFieldAlgebra f
  exact (affineSchemePointEquivOfStructure_apply f p (algebraMap ℂ A c)).symm.trans
    ((affineSchemePointEquivOfStructure f p).commutes c)

/-- Original structural constants make the actual point surjective. -/
theorem schemeAffineOriginalPoint_surjective (p : SchemeComplexPoint f) :
    Function.Surjective (schemeAffineOriginalPoint f p) := by
  let := affinePointFieldAlgebra f
  intro c
  exact ⟨algebraMap ℂ A c, schemeAffineOriginalPoint_scalar f p c⟩

/-- The original affine point ideal is its literal evaluation kernel. -/
def schemeAffineOriginalPointIdeal (p : SchemeComplexPoint f) : Ideal A :=
  RingHom.ker (schemeAffineOriginalPoint f p)

theorem schemeAffineOriginalPointIdeal_isMaximal (p : SchemeComplexPoint f) :
    (schemeAffineOriginalPointIdeal f p).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (schemeAffineOriginalPoint f p)
    (schemeAffineOriginalPoint_surjective f p)

instance schemeAffineOriginalPointIdeal_isPrime (p : SchemeComplexPoint f) :
    (schemeAffineOriginalPointIdeal f p).IsPrime :=
  (schemeAffineOriginalPointIdeal_isMaximal f p).isPrime

/-- The actual original prime defined by this SAME evaluation. -/
def schemeAffineOriginalPrime (p : SchemeComplexPoint f) : PrimeSpectrum A :=
  ⟨schemeAffineOriginalPointIdeal f p, inferInstance⟩

/-- The internally constructed evaluation prime is the underlying SAME original scheme point. -/
theorem schemeAffineOriginalPrime_eq_image (p : SchemeComplexPoint f) :
    schemeAffineOriginalPrime f p = schemeComplexPointImage f p := by
  have hp : CommRingCat.ofHom (schemeAffineOriginalPoint f p) = Spec.preimage p.val := rfl
  have he := congrArg (fun k : Spec (.of ℂ) ⟶ Spec (.of A) => k default)
    (Spec.map_preimage p.val)
  rw [← hp, Spec.map_apply] at he
  apply PrimeSpectrum.ext
  have hc : (default : Spec (.of ℂ)).asIdeal = ⊥ :=
    congrArg PrimeSpectrum.asIdeal
      (Subsingleton.elim (show PrimeSpectrum ℂ from (default : Spec (.of ℂ))) ⟨⊥, inferInstance⟩)
  have h := congrArg PrimeSpectrum.asIdeal he
  rw [PrimeSpectrum.comap_asIdeal, hc] at h
  exact h

/-- The actual canonical original affine coefficient in its ORIGINAL scheme stalk. -/
def schemeAffineOriginalStalk (p : SchemeComplexPoint f) :
    A →+* (Spec (.of A)).presheaf.stalk (schemeComplexPointImage f p) :=
  ((Scheme.ΓSpecIso (.of A)).inv ≫
    (Spec (.of A)).presheaf.germ ⊤ (schemeComplexPointImage f p) trivial).hom

/-- The entire original canonical affine stalk coefficient has its SAME literal point value. -/
theorem schemeAffineOriginalStalk_eval (p : SchemeComplexPoint f) (a : A) :
    schemeComplexPointStalkEval f p (schemeAffineOriginalStalk f p a) =
      schemeAffineOriginalPoint f p a := by
  let c : ComplexAffineChart (Spec (.of A)) := ⟨.of A, 𝟙 _, inferInstance⟩
  let z : ComplexAffineChartPoint f c := ⟨p.val, by simpa [c] using p.property⟩
  have hr : schemeAffineOriginalRegularStalk f c z =
      schemeAffineOriginalStalk f (complexAffineChartPointMap f c z) := by
    apply RingHom.ext
    intro a
    change (((Scheme.ΓSpecIso (.of A)).inv ≫
      (Spec (.of A)).presheaf.germ ⊤ (schemeComplexPointImage (c.map ≫ f) z) trivial ≫
      inv (c.map.stalkMap (schemeComplexPointImage (c.map ≫ f) z)) ≫
      ((Spec (.of A)).presheaf.stalkCongr
        (Inseparable.of_eq (schemeComplexPointImage_chart f c z).symm)).hom).hom a) = _
    dsimp only [c]
    have hi (y : Spec (.of A)) : inv ((𝟙 (Spec (.of A)) : Spec (.of A) ⟶ Spec (.of A)).stalkMap y) =
        𝟙 ((Spec (.of A)).presheaf.stalk y) := by
      apply IsIso.inv_eq_of_hom_inv_id
      rw [Scheme.Hom.stalkMap_id]
      rfl
    erw [hi]
    simp only [Category.id_comp, TopCat.Presheaf.stalkCongr_hom,
      TopCat.Presheaf.germ_stalkSpecializes]
    rfl
  have hq : complexAffineChartPointMap f c z = p := by
    apply Subtype.ext
    change p.val ≫ 𝟙 (Spec (.of A)) = p.val
    exact Category.comp_id _
  have he := schemeComplexPointStalkEval_affine f c z a
  change schemeComplexPointStalkEval f (complexAffineChartPointMap f c z)
    (schemeAffineOriginalRegularStalk f c z a) = affineSchemePointEquivOfStructure (c.map ≫ f) z a at he
  rw [hr, hq, affineSchemePointEquivOfStructure_apply] at he
  exact he

/-- The original point localization, not a replacement preferred affine chart ring. -/
abbrev SchemeAffineOriginalLocalRing (p : SchemeComplexPoint f) :=
  Localization.AtPrime (schemeAffineOriginalPointIdeal f p)

/-- Native spectrum stalk isomorphism at the actual evaluation prime. -/
def schemeAffineOriginalStalkEquiv (p : SchemeComplexPoint f) :
    SchemeAffineOriginalLocalRing f p ≃+*
      (Spec (.of A)).presheaf.stalk (schemeComplexPointImage f p) :=
  ((Spec.stalkIso (.of A) (schemeAffineOriginalPrime f p)).symm ≪≫
    (Spec (.of A)).presheaf.stalkCongr
      (Inseparable.of_eq (schemeAffineOriginalPrime_eq_image f p))).commRingCatIsoToRingEquiv

/-- Every original affine coefficient retains its literal canonical stalk germ. -/
theorem schemeAffineOriginalStalkEquiv_algebraMap (p : SchemeComplexPoint f) (a : A) :
    schemeAffineOriginalStalkEquiv f p
      (algebraMap A (SchemeAffineOriginalLocalRing f p) a) = schemeAffineOriginalStalk f p a := by
  have he : CommRingCat.ofHom (algebraMap A (SchemeAffineOriginalLocalRing f p)) ≫
      CommRingCat.ofHom (schemeAffineOriginalStalkEquiv f p).toRingHom =
        (Scheme.ΓSpecIso (.of A)).inv ≫
          (Spec (.of A)).presheaf.germ ⊤ (schemeComplexPointImage f p) trivial := by
    change CommRingCat.ofHom (algebraMap A (SchemeAffineOriginalLocalRing f p)) ≫
      (Spec.stalkIso (.of A) (schemeAffineOriginalPrime f p)).inv ≫
        ((Spec (.of A)).presheaf.stalkCongr
          (Inseparable.of_eq (schemeAffineOriginalPrime_eq_image f p))).hom = _
    erw [Spec.algebraMap_stalkIso_inv_assoc (R := .of A) (schemeAffineOriginalPrime f p)]
    simp only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.germ_stalkSpecializes]
  exact congrArg (fun k : CommRingCat.of A ⟶
    (Spec (.of A)).presheaf.stalk (schemeComplexPointImage f p) => k a) he

/-- Original canonical coefficients factor through the ACTUAL original point localization. -/
theorem schemeAffineOriginalStalk_eq_comp (p : SchemeComplexPoint f) :
    schemeAffineOriginalStalk f p = (schemeAffineOriginalStalkEquiv f p).toRingHom.comp
      (algebraMap A (SchemeAffineOriginalLocalRing f p)) := by
  ext a
  exact (schemeAffineOriginalStalkEquiv_algebraMap f p a).symm

/-- The original affine-to-stalk map is a localization followed by the native spectrum stalk isomorphism. -/
theorem schemeAffineOriginalStalk_flat (p : SchemeComplexPoint f) :
    (schemeAffineOriginalStalk f p).Flat := by
  rw [schemeAffineOriginalStalk_eq_comp]
  apply RingHom.Flat.comp
  · exact RingHom.flat_algebraMap_iff.mpr
      (IsLocalization.flat (SchemeAffineOriginalLocalRing f p)
        (schemeAffineOriginalPointIdeal f p).primeCompl)
  · exact RingHom.Flat.of_bijective (schemeAffineOriginalStalkEquiv f p).bijective

/-- The WHOLE actual original affine point ideal becomes the original stalk maximal ideal. -/
theorem schemeAffineOriginalStalk_map_pointIdeal (p : SchemeComplexPoint f) :
    (schemeAffineOriginalPointIdeal f p).map (schemeAffineOriginalStalk f p) =
      IsLocalRing.maximalIdeal ((Spec (.of A)).presheaf.stalk (schemeComplexPointImage f p)) := by
  rw [schemeAffineOriginalStalk_eq_comp, ← Ideal.map_map,
    IsLocalization.AtPrime.map_eq_maximalIdeal (schemeAffineOriginalPointIdeal f p)
      (SchemeAffineOriginalLocalRing f p)]
  exact IsLocalRing.map_ringEquiv_maximalIdeal (schemeAffineOriginalStalkEquiv f p)

/-- The canonical original affine section retains every SAME structural complex scalar. -/
theorem schemeAffineCanonicalSection_scalar (c : ℂ) :
    letI := affinePointFieldAlgebra f
    (Scheme.ΓSpecIso (.of A)).inv (algebraMap ℂ A c) = schemeGlobalConstants f c := by
  let := affinePointFieldAlgebra f
  have h := Scheme.ΓSpecIso_inv_naturality (Spec.preimage f)
  rw [Spec.map_preimage] at h
  exact congrArg (fun k : CommRingCat.of ℂ ⟶ Γ(Spec (.of A), ⊤) => k c) h

section Formal

variable (n : ℕ) [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]

local instance originalAffineFormalTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance originalAffineFormalCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance originalAffineFormalManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

variable (p : SchemeComplexPoint f)

local instance originalAffinePreferredComplexAlgebra : Algebra ℂ (SchemeCoordinateAffineRing f n p) :=
  affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)

/-- The actual ORIGINAL affine coefficient map to the same native formal ring. -/
def schemeAffineNativeFormal : A →+* MvPowerSeries (Fin n) ℂ :=
  (schemeNativeFormalGerm f n p).comp (schemeAffineOriginalStalk f p)

/-- Every original affine element is exactly the Taylor image of its canonical ORIGINAL stalk germ. -/
theorem schemeAffineNativeFormal_apply (a : A) :
    schemeAffineNativeFormal f n p a =
      schemeNativeFormalGerm f n p ((Spec (.of A)).presheaf.germ ⊤
        (schemeComplexPointImage f p) trivial ((Scheme.ΓSpecIso (.of A)).inv a)) := rfl

/-- Entire original coefficients retain the actual preferred-chart coefficient readback. -/
theorem schemeAffineNativeFormal_globalCoefficient (a : A) :
    schemeAffineNativeFormal f n p a = actualUnshiftedTaylorAlgHom n
      (schemeCoordinateModelGermEquiv n (schemeCoordinateRegularGerm f n p
        (schemeCoordinateGlobalCoefficient f n p ((Scheme.ΓSpecIso (.of A)).inv a)))) := by
  rw [schemeAffineNativeFormal_apply, ← schemeCoordinateStalkEquiv_global f n p]
  exact schemeNativeFormalGerm_regular f n p _

/-- Native evaluation of each original affine coefficient is its SAME literal point value. -/
theorem schemeAffineOriginalStalk_native_eval (a : A) :
    NativeHolGerm.eval (schemeNativeStalkGerm f n p (schemeAffineOriginalStalk f p a)) =
      schemeAffineOriginalPoint f p a := by
  rw [schemeNativeStalkGerm_eval, schemeAffineOriginalStalk_eval]

/-- The formal constant coefficient is the literal original affine point evaluation. -/
theorem schemeAffineNativeFormal_constantCoeff (a : A) :
    MvPowerSeries.constantCoeff (schemeAffineNativeFormal f n p a) =
      schemeAffineOriginalPoint f p a := by
  exact (schemeNativeFormalGerm_constantCoeff f n p _).trans
    (schemeAffineOriginalStalk_eval f p a)

/-- The actual original affine map preserves all structural complex scalars. -/
theorem schemeAffineNativeFormal_scalar (c : ℂ) :
    letI := affinePointFieldAlgebra f
    schemeAffineNativeFormal f n p (algebraMap ℂ A c) = MvPowerSeries.C c := by
  let := affinePointFieldAlgebra f
  rw [schemeAffineNativeFormal_globalCoefficient, schemeAffineCanonicalSection_scalar,
    schemeCoordinateGlobalCoefficient_const, schemeCoordinateRegularGerm_scalar,
    schemeCoordinateModelGermEquiv_const]
  exact (actualUnshiftedTaylorAlgHom n).commutes c

/-- Flatness is derived from actual original localization and actual native Taylor flatness. -/
theorem schemeAffineNativeFormal_flat : (schemeAffineNativeFormal f n p).Flat :=
  (schemeAffineOriginalStalk_flat f p).comp
    (schemeNativeFormalGerm_faithfullyFlat f n p).flat

/-- The WHOLE original stalk maximal ideal has exactly the genuine formal variable image. -/
theorem schemeAffineNativeFormal_originalStalk_map_maximalIdeal :
    (IsLocalRing.maximalIdeal ((Spec (.of A)).presheaf.stalk (schemeComplexPointImage f p))).map
      (schemeNativeFormalGerm f n p) = actualFormalCoordinateIdeal n univ := by
  apply le_antisymm
  · rw [schemeNativeFormalGerm, ← Ideal.map_map,
      ← NativeHolGerm.taylor_map_maximalIdeal (n := n) p]
    exact Ideal.map_mono (IsLocalRing.map_maximalIdeal_le (schemeNativeStalkGerm f n p))
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, _, rfl⟩
    rw [← schemeNativeFormalGerm_centered f n p i]
    apply Ideal.mem_map_of_mem
    rw [← IsLocalRing.maximalIdeal_comap (schemeCoordinateStalkRegularGerm f n p)]
    change schemeCoordinateStalkRegularGerm f n p _ ∈
      IsLocalRing.maximalIdeal (HolGerm (Fin n → ℂ))
    rw [schemeCoordinateStalkRegularGerm_regular, schemeCoordinateCenteredFreeGenerator_germ]
    exact (HolGerm.mem_maximalIdeal_iff _).mpr rfl

/-- The entire literal original point ideal extends to exactly the whole formal variable ideal. -/
theorem schemeAffineNativeFormal_map_pointIdeal :
    (schemeAffineOriginalPointIdeal f p).map (schemeAffineNativeFormal f n p) =
      actualFormalCoordinateIdeal n univ := by
  rw [schemeAffineNativeFormal, ← Ideal.map_map, schemeAffineOriginalStalk_map_pointIdeal]
  exact schemeAffineNativeFormal_originalStalk_map_maximalIdeal f n p

/-- The actual original localization map is the original formal stalk map through Spec.stalkIso. -/
def schemeAffineLocalNativeFormal :
    SchemeAffineOriginalLocalRing f p →+* MvPowerSeries (Fin n) ℂ :=
  (schemeNativeFormalGerm f n p).comp (schemeAffineOriginalStalkEquiv f p).toRingHom

/-- Every original coefficient retains its exact affine Taylor series under original localization. -/
theorem schemeAffineLocalNativeFormal_algebraMap (a : A) :
    schemeAffineLocalNativeFormal f n p
      (algebraMap A (SchemeAffineOriginalLocalRing f p) a) = schemeAffineNativeFormal f n p a := by
  change schemeNativeFormalGerm f n p (schemeAffineOriginalStalkEquiv f p _) = _
  rw [schemeAffineOriginalStalkEquiv_algebraMap]
  rfl

/-- The actual original local affine Taylor map is faithfully flat. -/
theorem schemeAffineLocalNativeFormal_faithfullyFlat :
    (schemeAffineLocalNativeFormal f n p).FaithfullyFlat :=
  RingHom.FaithfullyFlat.stableUnderComposition _ _
    (RingHom.FaithfullyFlat.of_bijective (schemeAffineOriginalStalkEquiv f p).bijective)
    (schemeNativeFormalGerm_faithfullyFlat f n p)

/-- The original localization universal property identifies ANY map retaining all original coefficients. -/
theorem schemeAffineNativeFormal_localization_ext
    (ψ : SchemeAffineOriginalLocalRing f p →+* MvPowerSeries (Fin n) ℂ)
    (hψ : ∀ a, ψ (algebraMap A (SchemeAffineOriginalLocalRing f p) a) =
      schemeAffineNativeFormal f n p a) : ψ = schemeAffineLocalNativeFormal f n p := by
  apply IsLocalization.ringHom_ext (schemeAffineOriginalPointIdeal f p).primeCompl
  apply RingHom.ext
  intro a
  exact (hψ a).trans (schemeAffineLocalNativeFormal_algebraMap f n p a).symm

end Formal

section Morphism

variable {R : Type} [CommRing R] (g : Spec (.of R) ⟶ Spec (.of ℂ))
  (π : Spec (.of A) ⟶ Spec (.of R))

/-- Every literal original affine coefficient commutes with the SAME original morphism stalk map. -/
theorem schemeAffineOriginalStalk_naturality (p : SchemeComplexPoint (π ≫ g)) (r : R) :
    (π.stalkMap (schemeComplexPointImage (π ≫ g) p)).hom
      (schemeAffineOriginalStalk g (schemeComplexPointMap (π ≫ g) g π rfl p) r) =
      schemeAffineOriginalStalk (π ≫ g) p ((Spec.preimage π).hom r) := by
  have h : (Scheme.ΓSpecIso (.of R)).inv ≫
      (Spec (.of R)).presheaf.germ ⊤ (π (schemeComplexPointImage (π ≫ g) p)) trivial ≫
      π.stalkMap (schemeComplexPointImage (π ≫ g) p) =
        Spec.preimage π ≫ (Scheme.ΓSpecIso (.of A)).inv ≫
          (Spec (.of A)).presheaf.germ ⊤ (schemeComplexPointImage (π ≫ g) p) trivial := by
    rw [Scheme.Hom.germ_stalkMap, Scheme.ΓSpecIso_inv_naturality_assoc, Spec.map_preimage]
    rfl
  exact congrArg (fun k : CommRingCat.of R ⟶
    (Spec (.of A)).presheaf.stalk (schemeComplexPointImage (π ≫ g) p) => k r) h

variable (n m : ℕ) [SmoothOfRelativeDimension n (π ≫ g)] [IsSeparated (π ≫ g)]
  [QuasiCompact (π ≫ g)] [SmoothOfRelativeDimension m g] [IsSeparated g] [QuasiCompact g]

/-- The entire original affine coefficient square uses actual formal substitution of the SAME morphism. -/
theorem schemeAffineNativeFormal_naturality (p : SchemeComplexPoint (π ≫ g)) (r : R) :
    schemeAffineNativeFormal (π ≫ g) n p ((Spec.preimage π).hom r) =
      schemeMorphismFormalPullback g π n m p
        (schemeAffineNativeFormal g m (schemeComplexPointMap (π ≫ g) g π rfl p) r) := by
  change schemeNativeFormalGerm (π ≫ g) n p
    (schemeAffineOriginalStalk (π ≫ g) p ((Spec.preimage π).hom r)) = _
  rw [← schemeAffineOriginalStalk_naturality g π p r]
  exact schemeNativeFormalGerm_naturality g π n m p _

end Morphism

end SGPT.Okounkov
