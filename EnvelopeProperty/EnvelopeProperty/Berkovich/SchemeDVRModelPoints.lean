import EnvelopeProperty.Berkovich.DVRNormalizedParameter
import EnvelopeProperty.Berkovich.SchemeCenterBaseChange
import EnvelopeProperty.Projective.GaussModelBridge

/-! # Actual prescribed native points and true centers from original DVR morphisms -/
open scoped NNReal Polynomial
open CategoryTheory AlgebraicGeometry Classical IsDiscreteValuationRing
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint

private theorem center_identity_of_lt_one {R : Type u} [CommRing R] [IsLocalRing R]
    (v : Valuation R ℝ≥0) (hb : ∀ r, v r ≤ 1)
    (hred : ∀ r, v r < 1 ↔ r ∈ IsLocalRing.maximalIdeal R)
    (y : RelativeSchemeValuedPoint v (𝟙 (Spec (CommRingCat.of R)))) :
    center hb y = IsLocalRing.closedPoint R := by
  have hl := centerLift_base hb y
  rw [Category.comp_id] at hl
  unfold center
  rw [hl]
  apply PrimeSpectrum.ext
  ext r
  change centerBaseMap hb y r ∈ IsLocalRing.maximalIdeal (CenterRing y) ↔
    r ∈ IsLocalRing.maximalIdeal R
  rw [Valuation.mem_maximalIdeal_iff]
  change y.1.residueVal (centerBaseMap hb y r) < 1 ↔ _
  change y.1.residueVal (residueBaseMap y r) < 1 ↔ _
  rw [residueBaseMap_val]
  exact hred r

variable {k V : Type u} [Field k] [CommRing V] [IsDomain V]
  [IsDiscreteValuationRing V] [Algebra k V]

private theorem dvrVal_le_one {c : ℝ} (hc : 0 < c) (a : V) :
    (Berk.dvrPoint (AlgHom.id k V) (expNeg c) (ProjBerk.expNeg_le_one hc.le)).val a ≤ 1 :=
  expOrd_le_one (ProjBerk.expNeg_le_one hc.le) _

private theorem dvrVal_lt_one_iff {c : ℝ} (hc : 0 < c) (a : V) :
    (Berk.dvrPoint (AlgHom.id k V) (expNeg c) (ProjBerk.expNeg_le_one hc.le)).val a < 1 ↔
      a ∈ IsLocalRing.maximalIdeal V := by
  change expOrd (expNeg c) (addVal V a) < 1 ↔ _
  constructor
  · intro h
    apply (IsLocalRing.mem_maximalIdeal a).mpr
    intro hu
    rw [addVal_eq_zero_iff.mpr hu,expOrd_zero] at h
    exact (lt_irrefl (1 : ℝ≥0)) h
  · intro ha
    have hord : (1 : ℕ∞) ≤ addVal V a := Order.one_le_iff_ne_zero.mpr
      ((addVal_eq_zero_iff).not.mpr ((IsLocalRing.mem_maximalIdeal a).mp ha))
    have h := expOrd_antitone (ProjBerk.expNeg_le_one hc.le) hord
    have h1 : expOrd (expNeg c) (1 : ℕ∞) = expNeg c := by
      simpa only [Nat.cast_one,pow_one] using expOrd_coe (q := expNeg c) 1
    rw [h1] at h
    exact h.trans_lt (expNeg_lt_one_of_pos hc)

private def identityDVRPoint {c : ℝ} (hc : 0 < c) :
    RelativeSchemeValuedPoint
      (Berk.dvrPoint (AlgHom.id k V) (expNeg c) (ProjBerk.expNeg_le_one hc.le)).val
      (𝟙 (Spec (CommRingCat.of V))) :=
  ⟨SchemeValuedPoint.basePoint _,SchemeValuedPoint.map_id _⟩

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
    {f : X ⟶ Spec (CommRingCat.of R)}

/-- The ACTUAL native model point from the original DVR seminorm and the
whole original DVR scheme map, retaining every original coefficient value. -/
def nativeDVRPoint (q : Spec (CommRingCat.of V) ⟶ X) (φ : R →+* V)
    (hq : q ≫ f = Spec.map (CommRingCat.ofHom φ)) {c : ℝ} (hc : 0 < c) :
    RelativeSchemeValuedPoint
      ((Berk.dvrPoint (AlgHom.id k V) (expNeg c) (ProjBerk.expNeg_le_one hc.le)).val.comap φ) f :=
  mapOverBase φ (fun _ => rfl) q (by simpa only [Category.id_comp] using hq)
    (identityDVRPoint (k := k) (V := V) hc)

/-- Its TRUE original proper-model center is derived as EXACTLY the actual
original DVR closed-point image; no center or metric certificate. -/
theorem center_nativeDVRPoint [IsProper f]
    (q : Spec (CommRingCat.of V) ⟶ X) (φ : R →+* V)
    (hq : q ≫ f = Spec.map (CommRingCat.ofHom φ)) {c : ℝ} (hc : 0 < c) :
    center (fun r => dvrVal_le_one (k := k) hc (φ r)) (nativeDVRPoint (k := k) q φ hq hc) =
      q (IsLocalRing.closedPoint V) := by
  have hi : center (dvrVal_le_one (k := k) hc) (identityDVRPoint (k := k) (V := V) hc) =
      IsLocalRing.closedPoint V := center_identity_of_lt_one _ _ (dvrVal_lt_one_iff (k := k) hc) _
  have h := center_map_overBase
    (v := (Berk.dvrPoint (AlgHom.id k V) (expNeg c) (ProjBerk.expNeg_le_one hc.le)).val.comap φ)
    (w := (Berk.dvrPoint (AlgHom.id k V) (expNeg c) (ProjBerk.expNeg_le_one hc.le)).val) φ (fun _ => rfl) q
    (by simpa only [Category.id_comp] using hq)
    (fun r => dvrVal_le_one (k := k) hc (φ r)) (dvrVal_le_one (k := k) hc)
    (identityDVRPoint (k := k) (V := V) hc)
  rw [hi] at h
  exact h.symm

private theorem center_cast [IsProper f] {v w : Valuation R ℝ≥0} (h : v = w)
    (hbv : ∀ r, v r ≤ 1) (hbw : ∀ r, w r ≤ 1) (y : RelativeSchemeValuedPoint v f) :
    center hbw (h ▸ y) = center hbv y := by
  cases h
  rfl

/-- An actual nonzero vertical parameter CONSTRUCTS the original prescribed
Gauss-base native point with EXACT original closed-point center. -/
theorem exists_nativeDVRPoint_gauss_center
    {f : X ⟶ Spec (CommRingCat.of (Polynomial k))} [IsProper f]
    (q : Spec (CommRingCat.of V) ⟶ X) (t : V) (ht : t ≠ 0)
    (hm : t ∈ IsLocalRing.maximalIdeal V)
    (hq : q ≫ f = Spec.map (CommRingCat.ofHom (Polynomial.aeval t).toRingHom)) :
    ∃ y : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) ProjBerk.gaussRadius) f,
      center ProjBerk.gaussModelCoefficient_le_one y = q (IsLocalRing.closedPoint V) := by
  let K := FractionRing V
  obtain ⟨c,hc,htval,-⟩ := Berk.dvrFractionPoint_exists_normalized_parameter (k := k) (K := K) t ht hm
  have htvalV : (Berk.dvrPoint (AlgHom.id k V) (expNeg c) (ProjBerk.expNeg_le_one hc.le)).val t =
      ProjBerk.gaussRadius := by
    rw [Berk.dvrFractionPoint_val_algebraMap (k := k) (K := K) hc] at htval
    exact htval
  have hgauss (F : k[X]) :
      (Berk.dvrPoint (AlgHom.id k V) (expNeg c) (ProjBerk.expNeg_le_one hc.le)).val
        ((Polynomial.aeval t) F) = gaussValuation (1 : Valuation k ℝ≥0) ProjBerk.gaussRadius F := by
    have h0 : (0 : ℝ≥0) < ProjBerk.gaussRadius := by
      change (0 : ℝ) < Real.exp (-1)
      exact Real.exp_pos _
    have h1 : ProjBerk.gaussRadius < 1 := by
      change Real.exp (-1) < (1 : ℝ)
      exact Real.exp_lt_one_iff.mpr (by norm_num)
    simpa only [htvalV] using Berk.valuation_aeval_eq_gauss_of_lt_one
      (Berk.dvrPoint (AlgHom.id k V) (expNeg c) (ProjBerk.expNeg_le_one hc.le)) t
      (htvalV.symm ▸ h0) (htvalV.symm ▸ h1) F
  have heq : (Berk.dvrPoint (AlgHom.id k V) (expNeg c) (ProjBerk.expNeg_le_one hc.le)).val.comap
      (Polynomial.aeval t).toRingHom = gaussValuation (1 : Valuation k ℝ≥0) ProjBerk.gaussRadius :=
    Valuation.ext hgauss
  let y := nativeDVRPoint (k := k) (R := Polynomial k) (f := f) q (Polynomial.aeval t).toRingHom hq hc
  refine ⟨heq ▸ y,?_⟩
  exact (center_cast heq (fun r => dvrVal_le_one (k := k) hc ((Polynomial.aeval t) r))
    ProjBerk.gaussModelCoefficient_le_one y).trans
      (center_nativeDVRPoint (k := k) (R := Polynomial k) (f := f) q (Polynomial.aeval t).toRingHom hq hc)

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
