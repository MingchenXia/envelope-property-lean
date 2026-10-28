import EnvelopeProperty.Cartier.FrobeniusLiftDifference
import Mathlib.RingTheory.Localization.Away.Basic

/-! # Genuine flat reductions on the actual original Away localizations -/
noncomputable section
namespace EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationFlatReductionLocalization
open FrobeniusLiftDifference
universe u v
variable {S : Type u} {B : Type v} [CommRing S] [CommRing B] {p : ℕ}

private abbrev mappedDenominator (f : S →+* B) (s : S) (d : Submonoid.powers s) :
    Submonoid.powers (f s) :=
  ⟨f d, by
    obtain ⟨n, hn⟩ := d.2
    refine ⟨n, ?_⟩
    exact (map_pow f s n).symm.trans (congrArg f hn)⟩

private def awayMap (f : S →+* B) (s : S) :
    Localization.Away s →+* Localization.Away (f s) :=
  IsLocalization.Away.map (Localization.Away s) (Localization.Away (f s)) f s

private theorem awayMap_fraction (f : S →+* B) (s x : S) (d : Submonoid.powers s) :
    awayMap f s (IsLocalization.mk' (Localization.Away s) x d) =
      IsLocalization.mk' (Localization.Away (f s)) (f x) (mappedDenominator f s d) := by
  dsimp only [awayMap, IsLocalization.Away.map]
  rw [IsLocalization.map_mk']

private theorem residue_p_zero (a : Reduction p S B) : (p : B) = 0 := by
  have h : a.map (p : S) = 0 := (a.kernel_iff _).mpr ⟨1, mul_one _⟩
  simpa only [map_natCast] using h

private theorem away_kernel (a : Reduction p S B) (s : S) (z : Localization.Away s) :
    awayMap a.map s z = 0 ↔ ∃ y : Localization.Away s, (p : Localization.Away s)*y = z := by
  constructor
  · intro hz
    obtain ⟨x, d, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers s) z
    rw [awayMap_fraction, IsLocalization.mk'_eq_zero_iff] at hz
    obtain ⟨m, hm⟩ := hz
    obtain ⟨n, hn⟩ := m.2
    have hx : a.map (s^n*x) = 0 := by
      rw [map_mul, map_pow]
      simpa only [hn] using hm
    obtain ⟨y, hy⟩ := (a.kernel_iff _).mp hx
    let t : Submonoid.powers s := ⟨s^n, ⟨n, rfl⟩⟩
    have hy' : (p : S)*y = x*(t : S) := by simpa only [t, mul_comm] using hy
    refine ⟨IsLocalization.mk' (Localization.Away s) y (d*t), ?_⟩
    calc
      (p : Localization.Away s)*IsLocalization.mk' (Localization.Away s) y (d*t) =
          IsLocalization.mk' (Localization.Away s) ((p : S)*y) (d*t) := by
        simpa only [map_natCast] using
          (IsLocalization.mul_mk'_eq_mk'_of_mul (S := Localization.Away s) (p : S) y (d*t))
      _ = IsLocalization.mk' (Localization.Away s) (x*(t : S)) (d*t) := by rw [hy']
      _ = IsLocalization.mk' (Localization.Away s) x d := IsLocalization.mk'_cancel x d t
  · rintro ⟨y, hy⟩
    have hp : (p : Localization.Away (a.map s)) = 0 := by
      simpa only [map_natCast, map_zero] using
        congrArg (algebraMap B (Localization.Away (a.map s))) (residue_p_zero a)
    rw [← hy, map_mul, map_natCast, hp, zero_mul]

/-- Actual native localization, surjectivity and the ENTIRE original p-kernel formula are DERIVED. -/
def awayReduction (a : Reduction p S B) (s : S) :
    Reduction p (Localization.Away s) (Localization.Away (a.map s)) where
  map := awayMap a.map s
  surjective := by
    apply (IsLocalization.Away.map_surjective_iff (Localization.Away s)
      (Localization.Away (a.map s)) a.map s).mpr
    intro y
    obtain ⟨x, hx⟩ := a.surjective y
    exact ⟨x, 0, by simpa only [pow_zero, one_mul] using hx⟩
  kernel_iff := away_kernel a s

/-- The ENTIRE original coefficient ring square uses the actual native localization maps. -/
theorem awayReduction_triangle (a : Reduction p S B) (s : S) :
    (awayReduction a s).map.comp (algebraMap S (Localization.Away s)) =
      (algebraMap B (Localization.Away (a.map s))).comp a.map := by
  ext x
  change awayMap a.map s (algebraMap S (Localization.Away s) x) =
    algebraMap B (Localization.Away (a.map s)) (a.map x)
  dsimp only [awayMap, IsLocalization.Away.map]
  apply IsLocalization.map_eq

private theorem away_annihilator (b : FlatReduction p S B) (s : S) (z : Localization.Away s)
    (hz : (p : Localization.Away s)*z = 0) : awayMap b.map s z = 0 := by
  obtain ⟨x, d, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers s) z
  have hz' : IsLocalization.mk' (Localization.Away s) ((p : S)*x) d = 0 := by
    simpa only [← IsLocalization.mul_mk'_eq_mk'_of_mul, map_natCast] using hz
  obtain ⟨m, hm⟩ := (IsLocalization.mk'_eq_zero_iff _ _).mp hz'
  have hp : (p : S)*((m : S)*x) = 0 := by
    calc
      (p : S)*((m : S)*x) = (m : S)*((p : S)*x) := by ring
      _ = 0 := hm
  have hbx : b.map ((m : S)*x) = 0 := b.flat _ hp
  rw [awayMap_fraction, IsLocalization.mk'_eq_zero_iff]
  refine ⟨mappedDenominator b.map s m, ?_⟩
  exact (map_mul b.map (m : S) x).symm.trans hbx

/-- The SAME actual localized reduction has derived square-zero and annihilator conditions. -/
def awayFlatReduction (b : FlatReduction p S B) (s : S) :
    FlatReduction p (Localization.Away s) (Localization.Away (b.map s)) where
  toReduction := awayReduction b.toReduction s
  p_sq_zero := by
    simpa only [map_mul, map_natCast, map_zero] using
      congrArg (algebraMap S (Localization.Away s)) b.p_sq_zero
  flat := away_annihilator b s

end EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationFlatReductionLocalization
