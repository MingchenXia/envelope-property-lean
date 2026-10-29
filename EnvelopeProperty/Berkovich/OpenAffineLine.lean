/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.AffineLine
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.DedekindDomain.Instances

/-!
# Genuine smooth principal-open affine lines

Actual localization homomorphisms construct the open restriction of a nonconstant
rational line inside an ambient polynomial principal open. Whole polynomial and
localized evaluations prove incidence with the given rational point. A genuine
one-generator, empty-relation smooth presentation proves relative dimension one;
the nonzero defining polynomial gives an integral normal Dedekind coordinate ring.
Over an infinite field, a real nonzero localized ambient function restricts nontrivially
to a chosen line, so its true scheme preimage is nonempty and dense.

The construction is independent of analytic point spaces and field norms. It supplies
the open-line construction used in FHX Proposition 5.22, rather than reduction,
normalization, dominance of finite preimage components, or curve potential theory.
-/

open scoped Polynomial
noncomputable section
namespace EnvelopeProperty
open Topology
/-- A nonzero element of an actual domain has dense principal open, via the true localization image. -/
theorem dense_basicOpen_of_ne_zero {R : Type*} [CommRing R] [IsDomain R]
    (r : R) (hr : r ≠ 0) : Dense (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) := by
  have hi : Function.Injective (algebraMap R (Localization.Away r)) :=
    IsLocalization.injective (Localization.Away r)
      (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hr))
  have hd : DenseRange (PrimeSpectrum.comap (algebraMap R (Localization.Away r))) :=
    (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr (by
      rw [(RingHom.injective_iff_ker_eq_bot _).mp hi]
      exact bot_le)
  change Dense (Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away r)))) at hd
  rw [PrimeSpectrum.localization_away_comap_range (Localization.Away r) r] at hd
  exact hd

/-- The actual one-generator empty-relation presentation makes the polynomial line standard smooth of relative dimension one. -/
theorem polynomial_standardSmooth_one (R : Type*) [CommRing R] :
    Algebra.IsStandardSmoothOfRelativeDimension 1 R R[X] := by
  let P : Algebra.PreSubmersivePresentation R (MvPolynomial PUnit.{1} R) PUnit.{1} Empty :=
    { toGenerators := Algebra.Generators.mvPolynomial R PUnit.{1}
      relation := Empty.elim
      span_range_relation_eq_ker := by simp [Algebra.Generators.ker_mvPolynomial]
      map := Empty.elim
      map_inj := fun x => Empty.elim x }
  let Q : Algebra.SubmersivePresentation R (MvPolynomial PUnit.{1} R) PUnit.{1} Empty :=
    { __ := P
      jacobian_isUnit := by
        have he : P.differential = LinearMap.id := Subsingleton.elim _ _
        rw [Algebra.PreSubmersivePresentation.jacobian, he, LinearMap.det_id, map_one]
        exact isUnit_one }
  have : Algebra.IsStandardSmoothOfRelativeDimension 1 R (MvPolynomial PUnit.{1} R) :=
    Q.isStandardSmoothOfRelativeDimension (by simp [Algebra.Presentation.dimension])
  exact Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv 1
    (MvPolynomial.uniqueAlgEquiv R PUnit.{1})
end EnvelopeProperty

namespace EnvelopeProperty.AffineLine
variable {F σ : Type*} [Field F]

/-- The actual coordinate ring of the principal-open line. -/
abbrev OpenLineRing (p : F[X]) := Localization.Away p

/-- Any true nonvanishing parameter gives an actual whole rational evaluator. -/
def openLineEval (p : F[X]) (t : F) (ht : Polynomial.eval t p ≠ 0) :
    OpenLineRing p →ₐ[F] F :=
  IsLocalization.Away.liftAlgHom p
    (f := Polynomial.aeval t) (isUnit_iff_ne_zero.mpr ht)

theorem openLineEval_algebraMap (p : F[X]) (t : F) (ht : Polynomial.eval t p ≠ 0)
    (f : F[X]) : openLineEval p t ht (algebraMap F[X] (OpenLineRing p) f) = Polynomial.eval t f :=
  IsLocalization.Away.lift_eq p (g := (Polynomial.aeval t).toRingHom)
    (isUnit_iff_ne_zero.mpr ht) f

theorem openLineRing_isDomain (p : F[X]) (hp : p ≠ 0) : IsDomain (OpenLineRing p) := by
  apply IsLocalization.isDomain_of_le_nonZeroDivisors (M := Submonoid.powers p) (OpenLineRing p)
  exact Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hp)

theorem openLineRing_finitePresentation (p : F[X]) :
    Algebra.FinitePresentation F (OpenLineRing p) := by
  have : Algebra.FinitePresentation F[X] (OpenLineRing p) := IsLocalization.Away.finitePresentation p
  exact Algebra.FinitePresentation.trans F F[X] (OpenLineRing p)

theorem openLineRing_finiteType (p : F[X]) : Algebra.FiniteType F (OpenLineRing p) := by
  have : Algebra.FinitePresentation F[X] (OpenLineRing p) := IsLocalization.Away.finitePresentation p
  exact Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType F F[X])
    (inferInstance : Algebra.FiniteType F[X] (OpenLineRing p))

theorem openLineRing_smooth (p : F[X]) : Algebra.Smooth F (OpenLineRing p) := by
  have : Algebra.Smooth F F[X] := {}
  have : Algebra.Smooth F[X] (OpenLineRing p) := Algebra.Smooth.of_isLocalization_Away p
  exact Algebra.Smooth.comp F F[X] (OpenLineRing p)

theorem openLineRing_isNoetherian (p : F[X]) : IsNoetherianRing (OpenLineRing p) := by
  have := openLineRing_finiteType p
  exact Algebra.FiniteType.isNoetherianRing F (OpenLineRing p)

theorem openLineRing_standardSmooth_one (p : F[X]) :
    Algebra.IsStandardSmoothOfRelativeDimension 1 F (OpenLineRing p) := by
  have := polynomial_standardSmooth_one F
  have : Algebra.IsStandardSmoothOfRelativeDimension 0 F[X] (OpenLineRing p) :=
    Algebra.IsStandardSmoothOfRelativeDimension.localization_away p
  exact Algebra.IsStandardSmoothOfRelativeDimension.trans (n := 1) (m := 0) F F[X] (OpenLineRing p)

theorem openLineRing_isIntegrallyClosed (p : F[X]) (hp : p ≠ 0) :
    IsIntegrallyClosed (OpenLineRing p) := by
  have := openLineRing_isDomain p hp
  exact isIntegrallyClosed_of_isLocalization (S := OpenLineRing p) (Submonoid.powers p)
    (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hp))

theorem openLineRing_isDedekindDomain (p : F[X]) (hp : p ≠ 0) :
    IsDedekindDomain (OpenLineRing p) := by
  have := openLineRing_isDomain p hp
  exact IsLocalization.isDedekindDomain F[X]
    (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hp)) (OpenLineRing p)

section PrincipalLine
variable {σ : Type*} (a b : σ → F) (g : MvPolynomial σ F)

/-- The actual localized line homomorphism into the ambient principal open. -/
def principalLineHom : Localization.Away g →ₐ[F] OpenLineRing (subst a b g) :=
  IsLocalization.Away.mapₐ (Localization.Away g) (OpenLineRing (subst a b g)) (subst a b) g

theorem principalLineHom_algebraMap (f : MvPolynomial σ F) :
    principalLineHom a b g (algebraMap _ (Localization.Away g) f) =
      algebraMap F[X] (OpenLineRing (subst a b g)) (subst a b f) := by
  simp only [principalLineHom, IsLocalization.Away.mapₐ_apply, IsLocalization.Away.map,
    IsLocalization.map_eq]
  rfl

theorem principalLineHom_surjective (hb : b ≠ 0) : Function.Surjective (principalLineHom a b g) :=
  IsLocalization.Away.mapₐ_surjective_of_surjective g (subst_surjective a b hb)

theorem openLineEval_comp_principalLine (t : F) (ht : MvPolynomial.eval (point a b t) g ≠ 0) :
    (openLineEval (subst a b g) t (by rwa [eval_subst])).comp (principalLineHom a b g) =
      IsLocalization.Away.liftAlgHom g
        (f := MvPolynomial.aeval (point a b t)) (isUnit_iff_ne_zero.mpr ht) := by
  apply IsLocalization.algHom_ext (Submonoid.powers g)
  apply AlgHom.ext
  intro f
  change openLineEval (subst a b g) t (by rwa [eval_subst])
    (principalLineHom a b g (algebraMap _ (Localization.Away g) f)) =
      IsLocalization.Away.liftAlgHom g (f := MvPolynomial.aeval (point a b t))
        (isUnit_iff_ne_zero.mpr ht) (algebraMap _ (Localization.Away g) f)
  simp only [principalLineHom_algebraMap, openLineEval_algebraMap,
    IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq, eval_subst]
  rfl

end PrincipalLine

theorem exists_parameter_avoiding [Infinite F] (p q : F[X]) (hp : p ≠ 0) (hq : q ≠ 0) :
    ∃ t : F, Polynomial.eval t p ≠ 0 ∧ Polynomial.eval t q ≠ 0 := by
  have hpq : p * q ≠ 0 := mul_ne_zero hp hq
  have ht : ∃ t : F, Polynomial.eval t (p * q) ≠ 0 := by
    by_contra! h
    exact hpq (Polynomial.zero_of_eval_zero _ h)
  obtain ⟨t, ht⟩ := ht
  exact ⟨t, mul_ne_zero_iff.mp (by simpa only [Polynomial.eval_mul] using ht)⟩

theorem exists_principal_open_line [Infinite F] [Nonempty σ] {g h : MvPolynomial σ F}
    (a : σ → F) (ha : MvPolynomial.eval a g ≠ 0) (hh : h ≠ 0) :
    ∃ b : σ → F, b ≠ 0 ∧ subst a b g ≠ 0 ∧ subst a b h ≠ 0 ∧
      ∃ t : F, MvPolynomial.eval (point a b t) g ≠ 0 ∧
        MvPolynomial.eval (point a b t) h ≠ 0 := by
  obtain ⟨b, hb, hhline⟩ := exists_direction_subst_ne_zero a hh
  have hgline : subst a b g ≠ 0 := by
    intro hz
    have he := eval_subst_zero a b g
    rw [hz, Polynomial.eval_zero] at he
    exact ha he.symm
  obtain ⟨t, ht⟩ := exists_parameter_avoiding _ _ hgline hhline
  refine ⟨b, hb, hgline, hhline, t, ?_⟩
  simpa only [eval_subst] using ht

/-- A true nonzero ambient localized function has a line with true nonzero restriction. -/
theorem exists_principal_open_line_localized [Infinite F] [Nonempty σ]
    (a : σ → F) {g : MvPolynomial σ F} (ha : MvPolynomial.eval a g ≠ 0)
    (f : Localization.Away g) (hf : f ≠ 0) :
    ∃ b : σ → F, b ≠ 0 ∧ subst a b g ≠ 0 ∧ principalLineHom a b g f ≠ 0 := by
  obtain ⟨n, q, hn⟩ := IsLocalization.Away.surj g f
  have hq : q ≠ 0 := by
    intro hz
    apply hf
    apply (IsLocalization.Away.algebraMap_pow_isUnit (S := Localization.Away g) g n).mul_right_cancel
    simpa only [hz, map_zero, zero_mul] using hn
  obtain ⟨b, hb, hg, hh, _⟩ := exists_principal_open_line a ha hq
  refine ⟨b, hb, hg, ?_⟩
  intro hz
  have he := congrArg (principalLineHom a b g) hn
  rw [map_mul, hz, zero_mul, principalLineHom_algebraMap] at he
  have hi : Function.Injective (algebraMap F[X] (OpenLineRing (subst a b g))) :=
    IsLocalization.injective (OpenLineRing (subst a b g))
      (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hg))
  apply hh
  exact hi (by simpa only [map_zero] using he.symm)

theorem dense_openLine_basicOpen (p q : F[X]) (hp : p ≠ 0) (hq : q ≠ 0) :
    Dense (PrimeSpectrum.basicOpen (algebraMap F[X] (OpenLineRing p) q) :
      Set (PrimeSpectrum (OpenLineRing p))) := by
  have := openLineRing_isDomain p hp
  apply dense_basicOpen_of_ne_zero
  have hi : Function.Injective (algebraMap F[X] (OpenLineRing p)) :=
    IsLocalization.injective (OpenLineRing p)
      (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hp))
  exact fun hz => hq (hi (by simpa only [map_zero] using hz))

theorem nonempty_openLine_basicOpen [Infinite F] (p q : F[X]) (hp : p ≠ 0) (hq : q ≠ 0) :
    (PrimeSpectrum.basicOpen (algebraMap F[X] (OpenLineRing p) q) :
      Set (PrimeSpectrum (OpenLineRing p))).Nonempty := by
  obtain ⟨t, hpt, hqt⟩ := exists_parameter_avoiding p q hp hq
  refine ⟨⟨RingHom.ker (openLineEval p t hpt).toRingHom, RingHom.ker_isPrime _⟩, ?_⟩
  change openLineEval p t hpt (algebraMap F[X] (OpenLineRing p) q) ≠ 0
  rwa [openLineEval_algebraMap]

section Schemes
open AlgebraicGeometry CategoryTheory
universe u
variable {F σ : Type u} [Field F]

/-- The actual scheme of a principal open in the affine line. -/
abbrev openLineScheme (p : F[X]) : Scheme := Spec (CommRingCat.of (OpenLineRing p))

/-- Its genuine open inclusion into the affine line. -/
def openLineInclusion (p : F[X]) : openLineScheme p ⟶ Spec (CommRingCat.of F[X]) :=
  Spec.map (CommRingCat.ofHom (algebraMap F[X] (OpenLineRing p)))

theorem openLineInclusion_isOpenImmersion (p : F[X]) : IsOpenImmersion (openLineInclusion p) := by
  change IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap F[X] (Localization.Away p))))
  infer_instance

theorem openLineInclusion_range (p : F[X]) :
    Set.range (openLineInclusion p) = (PrimeSpectrum.basicOpen p : Set (PrimeSpectrum F[X])) :=
  PrimeSpectrum.localization_away_comap_range _ p

/-- The true structure morphism over the original coefficient field. -/
def openLineStructure (p : F[X]) : openLineScheme p ⟶ Spec (CommRingCat.of F) :=
  Spec.map (CommRingCat.ofHom (algebraMap F (OpenLineRing p)))

theorem openLineStructure_smooth_one (p : F[X]) :
    SmoothOfRelativeDimension 1 (openLineStructure p) := by
  apply (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)).mpr
  apply RingHom.locally_of (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := 1)) _
  exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap 1).mpr
    (openLineRing_standardSmooth_one p)

/-- The actual F-rational point of the open line at a nonvanishing parameter. -/
def openLineSchemePoint (p : F[X]) (t : F) (ht : Polynomial.eval t p ≠ 0) :
    Spec (CommRingCat.of F) ⟶ openLineScheme p :=
  Spec.map (CommRingCat.ofHom (openLineEval p t ht).toRingHom)

theorem openLineSchemePoint_inclusion (p : F[X]) (t : F) (ht : Polynomial.eval t p ≠ 0) :
    openLineSchemePoint p t ht ≫ openLineInclusion p =
      Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom t : F[X] →+* F)) := by
  rw [openLineSchemePoint, openLineInclusion, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (openLineEval_algebraMap p t ht)

/-- The entire actual open-line map into the ambient principal open. -/
def principalLineSchemeMap (a b : σ → F) (g : MvPolynomial σ F) :
    openLineScheme (subst a b g) ⟶ Spec (CommRingCat.of (Localization.Away g)) :=
  Spec.map (CommRingCat.ofHom (principalLineHom a b g).toRingHom)

theorem principalLineSchemeMap_isClosedImmersion (a b : σ → F)
    (g : MvPolynomial σ F) (hb : b ≠ 0) : IsClosedImmersion (principalLineSchemeMap a b g) :=
  IsClosedImmersion.spec_of_surjective _ (principalLineHom_surjective a b g hb)

theorem principalLineSchemeMap_square (a b : σ → F) (g : MvPolynomial σ F) :
    principalLineSchemeMap a b g ≫
      Spec.map (CommRingCat.ofHom (algebraMap _ (Localization.Away g))) =
        openLineInclusion (subst a b g) ≫ schemeMap a b := by
  rw [principalLineSchemeMap, openLineInclusion, schemeMap, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (principalLineHom_algebraMap a b g)

/-- The good principal open is the actual whole preimage of the ambient good open. -/
theorem principalLineSchemeMap_preimage_basicOpen (a b : σ → F)
    (g h : MvPolynomial σ F) :
    principalLineSchemeMap a b g ⁻¹'
      (PrimeSpectrum.basicOpen (algebraMap _ (Localization.Away g) h) :
        Set (PrimeSpectrum (Localization.Away g))) =
      (PrimeSpectrum.basicOpen
        (algebraMap F[X] (OpenLineRing (subst a b g)) (subst a b h)) :
          Set (PrimeSpectrum (OpenLineRing (subst a b g)))) := by
  ext x
  change principalLineHom a b g (algebraMap _ (Localization.Away g) h) ∉ x.asIdeal ↔ _
  rw [principalLineHom_algebraMap]
  rfl

/-- Any nonzero principal-open line is an actual integral scheme. -/
theorem openLineScheme_isIntegral (p : F[X]) (hp : p ≠ 0) :
    IsIntegral (openLineScheme p) := by
  have := openLineRing_isDomain p hp
  infer_instance

/-- The entire actual rational point of an ambient principal open. -/
def ambientPrincipalPoint (a : σ → F) (g : MvPolynomial σ F)
    (ha : MvPolynomial.eval a g ≠ 0) :
    Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of (Localization.Away g)) :=
  Spec.map (CommRingCat.ofHom
    (IsLocalization.Away.liftAlgHom g (f := MvPolynomial.aeval a)
      (isUnit_iff_ne_zero.mpr ha)).toRingHom)

/-- Whole rational evaluation commutes with the actual principal-open line map. -/
theorem openLineSchemePoint_principalLine (a b : σ → F) (g : MvPolynomial σ F)
    (t : F) (ht : MvPolynomial.eval (point a b t) g ≠ 0) :
    openLineSchemePoint (subst a b g) t (by rwa [eval_subst]) ≫
      principalLineSchemeMap a b g = ambientPrincipalPoint (point a b t) g ht := by
  rw [openLineSchemePoint, principalLineSchemeMap, ambientPrincipalPoint, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom (openLineEval_comp_principalLine a b g t ht)

/-- Parameter zero preserves the whole original rational point in the true ambient principal open. -/
theorem principalLineSchemeMap_zero (a b : σ → F) (g : MvPolynomial σ F)
    (ha : MvPolynomial.eval a g ≠ 0) :
    openLineSchemePoint (subst a b g) 0 (by rwa [eval_subst_zero]) ≫
      principalLineSchemeMap a b g = ambientPrincipalPoint a g ha := by
  have he : point a b 0 = a := by
    funext i
    simp only [point, zero_mul, add_zero]
  simpa only [he] using openLineSchemePoint_principalLine a b g 0 (by rwa [he])

/-- A real smooth integral open line through the given whole rational point, with a nonempty dense good open. -/
theorem exists_smooth_principal_open_line [Infinite F] [Nonempty σ]
    (a : σ → F) {g h : MvPolynomial σ F}
    (ha : MvPolynomial.eval a g ≠ 0) (hh : h ≠ 0) :
    ∃ b : σ → F, b ≠ 0 ∧
      IsClosedImmersion (principalLineSchemeMap a b g) ∧
      SmoothOfRelativeDimension 1 (openLineStructure (subst a b g)) ∧
      IsIntegral (openLineScheme (subst a b g)) ∧
      (openLineSchemePoint (subst a b g) 0 (by rwa [eval_subst_zero]) ≫
        principalLineSchemeMap a b g = ambientPrincipalPoint a g ha) ∧
      Dense (PrimeSpectrum.basicOpen
        (algebraMap F[X] (OpenLineRing (subst a b g)) (subst a b h)) :
          Set (PrimeSpectrum (OpenLineRing (subst a b g)))) ∧
      (PrimeSpectrum.basicOpen
        (algebraMap F[X] (OpenLineRing (subst a b g)) (subst a b h)) :
          Set (PrimeSpectrum (OpenLineRing (subst a b g)))).Nonempty := by
  obtain ⟨b, hb, hg, hh, _⟩ := exists_principal_open_line a ha hh
  exact ⟨b, hb, principalLineSchemeMap_isClosedImmersion a b g hb,
    openLineStructure_smooth_one _, openLineScheme_isIntegral _ hg,
    principalLineSchemeMap_zero a b g ha, dense_openLine_basicOpen _ _ hg hh,
    nonempty_openLine_basicOpen _ _ hg hh⟩

/-- A genuine smooth integral open line avoids a true nonzero function on the actual ambient principal open. -/
theorem exists_smooth_principal_open_line_localized [Infinite F] [Nonempty σ]
    (a : σ → F) {g : MvPolynomial σ F} (ha : MvPolynomial.eval a g ≠ 0)
    (f : Localization.Away g) (hf : f ≠ 0) :
    ∃ b : σ → F, b ≠ 0 ∧
      IsClosedImmersion (principalLineSchemeMap a b g) ∧
      SmoothOfRelativeDimension 1 (openLineStructure (subst a b g)) ∧
      IsIntegral (openLineScheme (subst a b g)) ∧
      (openLineSchemePoint (subst a b g) 0 (by rwa [eval_subst_zero]) ≫
        principalLineSchemeMap a b g = ambientPrincipalPoint a g ha) ∧
      Dense ((principalLineSchemeMap a b g) ⁻¹'
        (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum (Localization.Away g)))) ∧
      ((principalLineSchemeMap a b g) ⁻¹'
        (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum (Localization.Away g)))).Nonempty := by
  obtain ⟨b, hb, hg, hf⟩ := exists_principal_open_line_localized a ha f hf
  have : IsDomain (OpenLineRing (subst a b g)) := openLineRing_isDomain _ hg
  have hd : Dense (PrimeSpectrum.basicOpen (principalLineHom a b g f) :
      Set (PrimeSpectrum (OpenLineRing (subst a b g)))) := dense_basicOpen_of_ne_zero _ hf
  refine ⟨b, hb, principalLineSchemeMap_isClosedImmersion a b g hb,
    openLineStructure_smooth_one _, openLineScheme_isIntegral _ hg,
    principalLineSchemeMap_zero a b g ha, ?_, ?_⟩
  · exact hd
  · exact hd.nonempty

end Schemes

end EnvelopeProperty.AffineLine
