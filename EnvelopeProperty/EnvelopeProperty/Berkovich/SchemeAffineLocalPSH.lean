/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SchemeLocalPSH
import EnvelopeProperty.Berkovich.SpectrumLocalPSH
import EnvelopeProperty.Berkovich.AffineUnitFractions

open scoped NNReal Topology
open Topology CategoryTheory AlgebraicGeometry
noncomputable section
universe u
namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] {v : Valuation R ℝ≥0}

local instance (V : (Spec (CommRingCat.of A)).Opens) : Algebra A Γ(Spec (CommRingCat.of A), V) :=
  inferInstanceAs (Algebra A (StructureSheaf.sectionsSubalgebra A V))

/-- The actual native affine homeomorphism retains every ORIGINAL ring value. -/
theorem affineSpectrumHomeomorph_val
    (y : RelativeSchemeValuedPoint v (Spec.map (CommRingCat.ofHom (algebraMap R A)))) (a : A) :
    (affineSpectrumHomeomorph y).1.val a = ValuedPoint.eval (SchemeValuedPoint.toValuedPoint y.1) a := rfl

/-- The inverse actual whole point homeomorphism retains every ORIGINAL ring value. -/
theorem affineSpectrumHomeomorph_symm_val (y : RelativeSpectrum v A) (a : A) :
    ValuedPoint.eval (SchemeValuedPoint.toValuedPoint (affineSpectrumHomeomorph.symm y).1) a = y.1.val a := by
  exact congrArg (fun z : RelativeSpectrum v A => z.1.val a) (affineSpectrumHomeomorph.apply_symm_apply y)

set_option backward.isDefEq.respectTransparency.types false in
/-- Actual coefficient sections agree with the original affine seminorm on the WHOLE support open. -/
theorem affine_eval_algebraMap
    (y : RelativeSchemeValuedPoint v (Spec.map (CommRingCat.ofHom (algebraMap R A))))
    (V : (Spec (CommRingCat.of A)).Opens) (hy : y.1.point ∈ V) (a : A) :
    SchemeValuedPoint.eval y.1 V hy (algebraMap A Γ(Spec (CommRingCat.of A), V) a) =
      (affineSpectrumHomeomorph y).1.val a := by
  rw [affineSpectrumHomeomorph_val]
  have he := SchemeValuedPoint.ofValuedPoint_eval_algebraMap
    (SchemeValuedPoint.toValuedPoint y.1) V hy a
  convert! he using 1; simp only [SchemeValuedPoint.ofValuedPoint_toValuedPoint]
  rfl

/-- Rational signed logarithms of a whole original unit fraction are actual finite-A expressions. -/
theorem unitTropAffine_eq_fractionTrop {V : (Spec (CommRingCat.of A)).Opens} {n : ℕ}
    (a : Fin n → Γ(Spec (CommRingCat.of A), V)ˣ) (b h : Fin n → A)
    (p : (Fin n → ℚ) × ℚ)
    (y : RelativeSchemeValuedPoint v (Spec.map (CommRingCat.ofHom (algebraMap R A))))
    (hy : y.1.point ∈ V)
    (he : ∀ i, SchemeValuedPoint.eval y.1 V hy (a i : Γ(Spec (CommRingCat.of A), V)) =
      (affineSpectrumHomeomorph y).1.val (b i) / (affineSpectrumHomeomorph y).1.val (h i))
    (hb : ∀ i, (affineSpectrumHomeomorph y).1.val (b i) ≠ 0)
    (hh : ∀ i, (affineSpectrumHomeomorph y).1.val (h i) ≠ 0) :
    unitTropAffine a p y hy = RelativeSpectrum.tropAffine (Fin.addCases b h)
      (Fin.addCases p.1 (fun i => -p.1 i), p.2) (affineSpectrumHomeomorph y) := by
  classical
  unfold unitTropAffine RelativeSpectrum.tropAffine
  rw [Fin.sum_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right, Rat.cast_neg, neg_mul, Finset.sum_neg_distrib]
  rw [← sub_eq_add_neg, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [he i, NNReal.coe_div, Real.log_div (by exact_mod_cast hb i) (by exact_mod_cast hh i), mul_sub]

/-- Genuine original regular-unit presentations become finite ORIGINAL ring presentations under the actual affine homeomorphism. -/
theorem IsConvexPLOn.to_affineSpectrum
    {U : Set (RelativeSchemeValuedPoint v (Spec.map (CommRingCat.ofHom (algebraMap R A))))}
    {u : RelativeSchemeValuedPoint v (Spec.map (CommRingCat.ofHom (algebraMap R A))) → EReal}
    (hu : IsConvexPLOn U u) :
    RelativeSpectrum.IsConvexPLOn (affineSpectrumHomeomorph.symm ⁻¹' U)
      (fun y => u (affineSpectrumHomeomorph.symm y)) := by
  classical
  intro x hx
  obtain ⟨W, hW, hxW, hWU, V, hWV, n, a, s, hs, hform⟩ := hu (affineSpectrumHomeomorph.symm x) hx
  have hf (i : Fin n) := SchemeValuedPoint.exists_unit_fraction_near V (a i)
    (affineSpectrumHomeomorph.symm x).1 (hWV _ hxW)
  choose b h hxh hi he using hf
  let N : Set (RelativeSchemeValuedPoint v (Spec.map (CommRingCat.ofHom (algebraMap R A)))) :=
    ⋂ i : Fin n, {y | y.1.point ∈ PrimeSpectrum.basicOpen (h i)}
  have hN : IsOpen N := isOpen_iInter_of_finite fun i =>
    (SchemeValuedPoint.isOpen_point_preimage (X := Spec (CommRingCat.of A)) (PrimeSpectrum.basicOpen (h i))).preimage continuous_subtype_val
  have hxN : affineSpectrumHomeomorph.symm x ∈ N := Set.mem_iInter.mpr hxh
  let liftRat : ((Fin n → ℚ) × ℚ) → ((Fin (n+n) → ℚ) × ℚ) :=
    fun p => (Fin.addCases p.1 (fun i => -p.1 i), p.2)
  refine ⟨affineSpectrumHomeomorph.symm ⁻¹' (W ∩ N),
    (hW.inter hN).preimage affineSpectrumHomeomorph.symm.continuous,
    ⟨hxW, hxN⟩, (fun _ hz => hWU hz.1), n+n, Fin.addCases b h,
    s.image liftRat, hs.image liftRat, ?_, ?_⟩
  · intro z hz k
    have hzN := Set.mem_iInter.mp hz.2
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · simpa only [Fin.addCases_left, affineSpectrumHomeomorph_symm_val] using
        (he i (affineSpectrumHomeomorph.symm z).1 (hzN i)).2.1
    · simpa only [Fin.addCases_right, affineSpectrumHomeomorph_symm_val] using
        (he i (affineSpectrumHomeomorph.symm z).1 (hzN i)).2.2
  · intro z hz
    change u (affineSpectrumHomeomorph.symm z) = _
    rw [hform _ hz.1, Finset.sup'_image]
    congr 1
    apply Finset.sup'_congr hs rfl
    intro p hp
    have hzN := Set.mem_iInter.mp hz.2
    have ht := unitTropAffine_eq_fractionTrop a b h p (affineSpectrumHomeomorph.symm z)
      (hWV _ hz.1)
      (fun i => (he i (affineSpectrumHomeomorph.symm z).1 (hzN i)).1)
      (fun i => (he i (affineSpectrumHomeomorph.symm z).1 (hzN i)).2.1)
      (fun i => (he i (affineSpectrumHomeomorph.symm z).1 (hzN i)).2.2)
    simpa only [Homeomorph.apply_symm_apply, liftRat, Function.comp_apply] using ht

set_option backward.isDefEq.respectTransparency false in
/-- An ORIGINAL coefficient is a true unit on every genuine Zariski open where its basic open contains that open. -/
theorem isUnit_affine_coefficient (V : (Spec (CommRingCat.of A)).Opens) (a : A)
    (hV : V ≤ PrimeSpectrum.basicOpen a) :
    IsUnit (algebraMap A Γ(Spec (CommRingCat.of A), V) a) := by
  apply isUnit_iff_exists_inv.mpr
  refine ⟨StructureSheaf.const 1 a V hV, ?_⟩
  exact StructureSheaf.const_mul_rev a 1 V (by rw [PrimeSpectrum.basicOpen_one]; exact le_top) hV

/-- Finite ORIGINAL coefficient presentations yield genuine regular units on one actual principal open. -/
theorem IsConvexPLOn.of_affineSpectrum {U : Set (RelativeSpectrum v A)} {u : RelativeSpectrum v A → EReal}
    (hu : RelativeSpectrum.IsConvexPLOn U u) :
    IsConvexPLOn (affineSpectrumHomeomorph ⁻¹' U) (fun y => u (affineSpectrumHomeomorph y)) := by
  classical
  intro x hx
  obtain ⟨W, hW, hxW, hWU, n, a, s, hs, ha, hform⟩ := hu (affineSpectrumHomeomorph x) hx
  let V : (Spec (CommRingCat.of A)).Opens := PrimeSpectrum.basicOpen (∏ i, a i)
  have hV (i : Fin n) : V ≤ PrimeSpectrum.basicOpen (a i) := by
    intro z hz
    change (∏ i, a i) ∉ z.asIdeal at hz
    change a i ∉ z.asIdeal
    intro hi
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem a (Finset.mem_univ i)
    apply hz
    rw [hc]
    exact z.asIdeal.mul_mem_right c hi
  have hua (i : Fin n) : IsUnit (algebraMap A Γ(Spec (CommRingCat.of A), V) (a i)) :=
    isUnit_affine_coefficient V (a i) (hV i)
  have hWV : ∀ y ∈ affineSpectrumHomeomorph ⁻¹' W, y.1.point ∈ V := by
    intro y hy
    change (∏ i, a i) ∉ y.1.point.asIdeal
    intro hz
    have hv : (affineSpectrumHomeomorph y).1.val (∏ i, a i) ≠ 0 := by
      rw [map_prod]
      exact Finset.prod_ne_zero_iff.mpr (fun i _ => ha _ hy i)
    exact hv ((ValuedPoint.eval_eq_zero_iff (SchemeValuedPoint.toValuedPoint y.1) _).mpr hz)
  refine ⟨affineSpectrumHomeomorph ⁻¹' W, hW.preimage affineSpectrumHomeomorph.continuous,
    hxW, Set.preimage_mono hWU, V, hWV, n, (fun i => (hua i).unit), s, hs, ?_⟩
  intro y hy
  change u (affineSpectrumHomeomorph y) = _
  rw [hform _ hy]
  congr 1
  apply Finset.sup'_congr hs rfl
  intro p hp
  unfold RelativeSpectrum.tropAffine unitTropAffine
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [IsUnit.unit_spec, affine_eval_algebraMap]

/-- Every actual decreasing sequence of intrinsic presentations becomes an original affine coefficient sequence. -/
theorem IsDecrConvexPLLimitOn.to_affineSpectrum
    {U : Set (RelativeSchemeValuedPoint v (Spec.map (CommRingCat.ofHom (algebraMap R A))))}
    {u : RelativeSchemeValuedPoint v (Spec.map (CommRingCat.ofHom (algebraMap R A))) → EReal}
    (hu : IsDecrConvexPLLimitOn U u) :
    RelativeSpectrum.IsDecrConvexPLLimitOn (affineSpectrumHomeomorph.symm ⁻¹' U)
      (fun y => u (affineSpectrumHomeomorph.symm y)) := by
  obtain ⟨a, ha, hanti, hlim⟩ := hu
  exact ⟨fun j y => a j (affineSpectrumHomeomorph.symm y), fun j => (ha j).to_affineSpectrum,
    fun y hy => hanti _ hy, fun y hy => hlim _ hy⟩

/-- True affine coefficient sequences yield genuine intrinsic regular-unit sequences. -/
theorem IsDecrConvexPLLimitOn.of_affineSpectrum {U : Set (RelativeSpectrum v A)} {u : RelativeSpectrum v A → EReal}
    (hu : RelativeSpectrum.IsDecrConvexPLLimitOn U u) :
    IsDecrConvexPLLimitOn (affineSpectrumHomeomorph ⁻¹' U) (fun y => u (affineSpectrumHomeomorph y)) := by
  obtain ⟨a, ha, hanti, hlim⟩ := hu
  exact ⟨fun j y => a j (affineSpectrumHomeomorph y), fun j => IsConvexPLOn.of_affineSpectrum (ha j),
    fun y hy => hanti _ hy, fun y hy => hlim _ hy⟩

/-- Actual analytic neighborhoods and whole decreasing limits compare under the real affine homeomorphism. -/
theorem IsLocallyPSHOn.to_affineSpectrum
    {U : Set (RelativeSchemeValuedPoint v (Spec.map (CommRingCat.ofHom (algebraMap R A))))}
    {u : RelativeSchemeValuedPoint v (Spec.map (CommRingCat.ofHom (algebraMap R A))) → EReal}
    (hu : IsLocallyPSHOn U u) :
    RelativeSpectrum.IsLocallyPSHOn (affineSpectrumHomeomorph.symm ⁻¹' U)
      (fun y => u (affineSpectrumHomeomorph.symm y)) := by
  intro x hx
  obtain ⟨W, hW, hxW, hWU, hloc⟩ := hu (affineSpectrumHomeomorph.symm x) hx
  exact ⟨affineSpectrumHomeomorph.symm ⁻¹' W, hW.preimage affineSpectrumHomeomorph.symm.continuous,
    hxW, Set.preimage_mono hWU, hloc.to_affineSpectrum⟩

/-- The actual affine finite-coefficient local class gives genuine intrinsic regular-unit presentations. -/
theorem IsLocallyPSHOn.of_affineSpectrum {U : Set (RelativeSpectrum v A)} {u : RelativeSpectrum v A → EReal}
    (hu : RelativeSpectrum.IsLocallyPSHOn U u) :
    IsLocallyPSHOn (affineSpectrumHomeomorph ⁻¹' U) (fun y => u (affineSpectrumHomeomorph y)) := by
  intro x hx
  obtain ⟨W, hW, hxW, hWU, hloc⟩ := hu (affineSpectrumHomeomorph x) hx
  exact ⟨affineSpectrumHomeomorph ⁻¹' W, hW.preimage affineSpectrumHomeomorph.continuous,
    hxW, Set.preimage_mono hWU, IsDecrConvexPLLimitOn.of_affineSpectrum hloc⟩

/-- The independently defined intrinsic and original affine convex-PL classes are genuinely equal. -/
theorem isConvexPLOn_affine_iff
    {U : Set (RelativeSchemeValuedPoint v (Spec.map (CommRingCat.ofHom (algebraMap R A))))}
    {u : RelativeSchemeValuedPoint v (Spec.map (CommRingCat.ofHom (algebraMap R A))) → EReal} :
    IsConvexPLOn U u ↔ RelativeSpectrum.IsConvexPLOn (affineSpectrumHomeomorph.symm ⁻¹' U)
      (fun y => u (affineSpectrumHomeomorph.symm y)) := by
  refine ⟨IsConvexPLOn.to_affineSpectrum, fun h => ?_⟩
  simpa only [Set.preimage_preimage, Function.comp_def, Homeomorph.symm_apply_apply, Set.preimage_id'] using
    (IsConvexPLOn.of_affineSpectrum h)

/-- Actual whole antitone limits agree, with no uniform denominator across the sequence required. -/
theorem isDecrConvexPLLimitOn_affine_iff
    {U : Set (RelativeSchemeValuedPoint v (Spec.map (CommRingCat.ofHom (algebraMap R A))))}
    {u : RelativeSchemeValuedPoint v (Spec.map (CommRingCat.ofHom (algebraMap R A))) → EReal} :
    IsDecrConvexPLLimitOn U u ↔ RelativeSpectrum.IsDecrConvexPLLimitOn (affineSpectrumHomeomorph.symm ⁻¹' U)
      (fun y => u (affineSpectrumHomeomorph.symm y)) := by
  refine ⟨IsDecrConvexPLLimitOn.to_affineSpectrum, fun h => ?_⟩
  simpa only [Set.preimage_preimage, Function.comp_def, Homeomorph.symm_apply_apply, Set.preimage_id'] using
    (IsDecrConvexPLLimitOn.of_affineSpectrum h)

/-- Intrinsic regular-unit local psh agrees with independently defined finite-A local psh on the SAME actual affine scheme. -/
theorem isLocallyPSHOn_affine_iff
    {U : Set (RelativeSchemeValuedPoint v (Spec.map (CommRingCat.ofHom (algebraMap R A))))}
    {u : RelativeSchemeValuedPoint v (Spec.map (CommRingCat.ofHom (algebraMap R A))) → EReal} :
    IsLocallyPSHOn U u ↔ RelativeSpectrum.IsLocallyPSHOn (affineSpectrumHomeomorph.symm ⁻¹' U)
      (fun y => u (affineSpectrumHomeomorph.symm y)) := by
  refine ⟨IsLocallyPSHOn.to_affineSpectrum, fun h => ?_⟩
  simpa only [Set.preimage_preimage, Function.comp_def, Homeomorph.symm_apply_apply, Set.preimage_id'] using
    (IsLocallyPSHOn.of_affineSpectrum h)

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
