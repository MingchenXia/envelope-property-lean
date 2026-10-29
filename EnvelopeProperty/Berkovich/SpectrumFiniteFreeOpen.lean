/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SpectrumFibrePeak
import EnvelopeProperty.Berkovich.SpectrumFiniteNorm
import EnvelopeProperty.Berkovich.SpectrumIntegralProper

/-!
# Genuine finite free maps of real seminorm spectra are open

Actual completed-fibre idempotents give original-element peaks. The fixed
original norm polynomial of (b,1), its joint Gauss continuity and actual positive
fibre multiplicities produce nearby above-threshold branches. Genuine integral
closedness excludes every such branch outside the chosen source open set. This
constructs an actual open image neighborhood. Exact fixed-coefficient preimages
then give the arbitrary prescribed-base relative result. No openness certificate,
field, coefficient bound, reducedness, separability or extra finite-presentation
hypothesis is assumed. Analytic structure sheaves and potentials are separate.
-/

open scoped NNReal Topology
open Topology
noncomputable section
namespace EnvelopeProperty.Berkovich.Spectrum
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- A genuine fixed multivariate Gauss polynomial varies continuously in the entire base point and all radii. -/
theorem continuous_wgaussValuation_prod {σ : Type*} (P : MvPolynomial σ A) :
    Continuous fun p : Spectrum A × (σ → ℝ≥0) => wgaussValuation p.1.val p.2 P := by
  simp only [wgaussValuation_apply, monoWeight, Finsupp.prod]
  exact Continuous.finset_sup_apply fun α _ =>
    ((continuous_val_apply (P.coeff α)).comp continuous_fst).mul
      (continuous_finsetProd _ fun i _ =>
        ((continuous_apply i).comp continuous_snd).pow (α i))

/-- The true finite-free norm form of the original pair `(b,1)` evaluated at the actual threshold radius. -/
def normDisc [Module.Free A B] [Module.Finite A B] (b : B) (x : Spectrum A) (r : ℝ≥0) : ℝ≥0 :=
  wgaussValuation x.val ![1, r] (normForm A ![b, (1 : B)])

/-- This actual original norm expression has the whole fibre product with genuine nonetale multiplicities. -/
theorem normDisc_eq_prod [Module.Free A B] [Module.Finite A B]
    (b : B) (x : Spectrum A) (r : ℝ≥0) :
    normDisc b x r = ∏ y ∈ (finite_preimage_singleton (A := B) x).toFinset,
      max (y.val b) r ^ fibreNormMult A y := by
  rw [normDisc, wgaussValuation_normForm_of_finiteFree]
  apply Finset.prod_congr rfl
  intro y hy
  congr 1
  simp [Finset.univ_fin2, max_comm]

/-- Joint continuity is genuine coefficient Gauss continuity, including zero threshold radius. -/
theorem continuous_normDisc [Module.Free A B] [Module.Finite A B] (b : B) :
    Continuous fun p : Spectrum A × ℝ≥0 => normDisc b p.1 p.2 := by
  exact (continuous_wgaussValuation_prod (normForm A ![b, (1 : B)])).comp
    (continuous_fst.prodMk (continuous_pi fun i => by
      fin_cases i
      · change Continuous (fun _ : Spectrum A × ℝ≥0 => (1 : ℝ≥0))
        exact continuous_const
      · change Continuous (fun p : Spectrum A × ℝ≥0 => p.2)
        exact continuous_snd))


/-- If every actual fibre branch is below a threshold, the whole genuine norm is exactly its free-rank power. -/
theorem normDisc_eq_pow_of_forall [Module.Free A B] [Module.Finite A B]
    (b : B) (x : Spectrum A) (r : ℝ≥0)
    (h : ∀ y : Fibre (B := B) x, y.1.val b ≤ r) :
    normDisc b x r = r ^ Module.finrank A B := by
  classical
  rw [normDisc_eq_prod]
  calc
    (∏ y ∈ (finite_preimage_singleton (A := B) x).toFinset,
        max (y.val b) r ^ fibreNormMult A y) =
        ∏ y ∈ (finite_preimage_singleton (A := B) x).toFinset, r ^ fibreNormMult A y := by
      apply Finset.prod_congr rfl
      intro y hy
      rw [max_eq_right (h ⟨y, (Set.Finite.mem_toFinset (finite_preimage_singleton (A := B) x)).mp hy⟩)]
    _ = r ^ Module.finrank A B := by
      rw [Finset.prod_pow_eq_pow_sum, sum_fibreNormMult]

/-- A genuine above-threshold branch forces a strict original norm inequality, with its actual positive multiplicity. -/
theorem pow_lt_normDisc_of_exists [Module.Free A B] [Module.Finite A B]
    (b : B) (x : Spectrum A) (r : ℝ≥0) (hr : 0 < r)
    (h : ∃ y : Fibre (B := B) x, r < y.1.val b) :
    r ^ Module.finrank A B < normDisc b x r := by
  classical
  obtain ⟨y, hy⟩ := h
  rw [normDisc_eq_prod, ← sum_fibreNormMult (A := B) x, ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_lt_prod (fun z hz => pow_pos hr _) (fun z hz => by gcongr; exact le_max_right _ _)
  refine ⟨y.1, (Set.Finite.mem_toFinset _).mpr y.2, ?_⟩
  exact pow_lt_pow_left₀ (hy.trans_le (le_max_left _ _)) (show (0 : ℝ≥0) ≤ r from zero_le)
    (Nat.one_le_iff_ne_zero.mp (one_le_fibreNormMult y.1))

/-- A strict actual original norm inequality produces a whole above-threshold fibre branch. -/
theorem exists_branch_of_pow_lt_normDisc [Module.Free A B] [Module.Finite A B]
    (b : B) (x : Spectrum A) (r : ℝ≥0)
    (h : r ^ Module.finrank A B < normDisc b x r) :
    ∃ y : Fibre (B := B) x, r < y.1.val b := by
  by_contra hn
  push Not at hn
  exact (ne_of_gt h) (normDisc_eq_pow_of_forall b x r hn)


/-- A genuinely finite free algebra has an open map of actual real-valued multiplicative seminorm spaces, without a field or coefficient bound. -/
theorem isOpenMap_comap_of_finiteFree [Module.Free A B] [Module.Finite A B] :
    IsOpenMap (comap (algebraMap A B)) := by
  classical
  let f : Spectrum B → Spectrum A := comap (algebraMap A B)
  intro U hU
  apply isOpen_iff_forall_mem_open.mpr
  rintro _ ⟨y, hy, rfl⟩
  let x := f y
  obtain ⟨d, b, hd, hb, hsep⟩ := exists_finite_fibre_peak x (⟨y, rfl⟩ : Fibre x)
  let r : Spectrum A → ℝ≥0 := fun z => (1 / 2 : ℝ≥0) * z.val d
  have hr : Continuous r := continuous_const.mul (continuous_val_apply d)
  let C : Set (Spectrum B) := Uᶜ ∩ {z | r (f z) ≤ z.val b}
  have hC : IsClosed C := hU.isClosed_compl.inter
    (isClosed_le (hr.comp (continuous_comap _)) (continuous_val_apply b))
  have himage : IsClosed (f '' C) :=
    isClosedMap_comap_of_isIntegral (algebraMap A B)
      (algebraMap_isIntegral_iff.mpr inferInstance) C hC
  have hximage : x ∉ f '' C := by
    rintro ⟨z, ⟨hzU, hzb⟩, hzx⟩
    have hzy : (⟨z, hzx⟩ : Fibre x) ≠ (⟨y, rfl⟩ : Fibre x) := by
      intro he
      have he' : z = y := congrArg Subtype.val he
      exact hzU (by simpa only [he'] using hy)
    have hs := hsep ⟨z, hzx⟩ hzy
    change r (f z) ≤ z.val b at hzb
    rw [hzx] at hzb
    exact (not_le_of_gt hs) hzb
  let V : Set (Spectrum A) := {z | r z ^ Module.finrank A B < normDisc b z (r z)}
  have hV : IsOpen V := isOpen_lt (hr.pow _) ((continuous_normDisc b).comp
    (continuous_id.prodMk hr))
  have hxV : x ∈ V := by
    apply pow_lt_normDisc_of_exists b x (r x)
    · exact mul_pos (by norm_num) (pos_iff_ne_zero.mpr hd)
    · refine ⟨⟨y, rfl⟩, ?_⟩
      change (1 / 2 : ℝ≥0) * x.val d < y.val b
      rw [hb]
      have hp : 0 < x.val d := pos_iff_ne_zero.mpr hd
      nlinarith
  refine ⟨V ∩ (f '' C)ᶜ, ?_, hV.inter himage.isOpen_compl, ⟨hxV, hximage⟩⟩
  intro z hz
  obtain ⟨w, hw⟩ := exists_branch_of_pow_lt_normDisc b z (r z) hz.1
  refine ⟨w.1, ?_, w.2⟩
  by_contra hwU
  apply hz.2
  refine ⟨w.1, ⟨hwU, ?_⟩, w.2⟩
  change r (f w.1) ≤ w.1.val b
  rw [show f w.1 = z from w.2]
  exact hw.le

end EnvelopeProperty.Berkovich.Spectrum

namespace EnvelopeProperty.Berkovich.RelativeSpectrum
variable {R : Type*} [CommRing R] {v : Valuation R ℝ≥0}
  {A B : Type*} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- Actual finite free algebra-map restriction is open on every prescribed-base seminorm locus. -/
theorem isOpenMap_comap_of_finiteFree (φ : A →ₐ[R] B)
    (hfree : letI := φ.toRingHom.toAlgebra; Module.Free A B)
    (hfinite : φ.toRingHom.Finite) : IsOpenMap (comap (v := v) φ) := by
  let : Algebra A B := φ.toRingHom.toAlgebra
  let : Module.Free A B := hfree
  let : Module.Finite A B := hfinite
  have hf : IsOpenMap (Spectrum.comap φ.toRingHom) := Spectrum.isOpenMap_comap_of_finiteFree
  have heq : Spectrum.comap φ.toRingHom ⁻¹' relativeLocus v A = relativeLocus v B := by
    ext y
    change (∀ r : R, y.val (φ (algebraMap R A r)) = v r) ↔
      ∀ r : R, y.val (algebraMap R B r) = v r
    simp only [φ.commutes]
  let e := Homeomorph.setCongr heq.symm
  have ho := hf.restrictPreimage (relativeLocus v A)
  convert ho.comp e.isOpenMap using 1
  funext x
  apply Subtype.ext
  rfl

end EnvelopeProperty.Berkovich.RelativeSpectrum
