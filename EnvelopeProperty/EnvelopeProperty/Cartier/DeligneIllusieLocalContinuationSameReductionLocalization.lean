import EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationRelativeLiftLocalization
import Mathlib.RingTheory.Nilpotent.Basic

/-! # Two genuine lifts on the same actual principal-localized target -/
noncomputable section
namespace EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationSameReductionLocalization
open FrobeniusLiftDifference
open DeligneIllusieLocalContinuationFlatReductionLocalization
open DeligneIllusieLocalContinuationRelativeLiftLocalization
universe u v w z t
variable {S : Type u} {B : Type v} [CommRing S] [CommRing B] {p : ℕ}

/-- The unit is DERIVED inside the actual Away ring from ORIGINAL ker=p and p²=0. -/
theorem sameReduction_isUnit (b : FlatReduction p S B) (s t : S) (h : b.map t = b.map s) :
    IsUnit (algebraMap S (Localization.Away s) t) := by
  obtain ⟨x, hx⟩ := (b.kernel_iff (t-s)).mp (by rw [map_sub, h, sub_self])
  have hn : IsNilpotent (t-s) := by
    refine ⟨2, ?_⟩
    rw [← hx, pow_two]
    calc
      (p : S)*x*((p : S)*x) = ((p : S)*(p : S))*(x*x) := by ring
      _ = 0 := by rw [b.p_sq_zero, zero_mul]
  have hn' := hn.map (algebraMap S (Localization.Away s))
  have hu := hn'.isUnit_add_left_of_commute
    (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away s) s)
    (Commute.all _ _)
  simpa only [← map_add, add_sub_cancel] using hu

private def sameReductionMap (b : FlatReduction p S B) (s t : S) (h : b.map s = b.map t) :
    Localization.Away s →ₐ[S] Localization.Away t :=
  IsLocalization.Away.liftAlgHom (A := S) (S := Localization.Away s)
    (f := Algebra.ofId S (Localization.Away t)) s (sameReduction_isUnit b t s h)

private theorem sameReductionMap_comp (b : FlatReduction p S B) (s t : S)
    (h : b.map s = b.map t) :
    (sameReductionMap b s t h).comp (sameReductionMap b t s h.symm) =
      AlgHom.id S (Localization.Away t) := by
  apply IsLocalization.algHom_ext (Submonoid.powers t)
  ext

/-- ACTUAL native S-algebra equivalence, with BOTH inverse laws derived by localization ext. -/
def sameReductionEquiv (b : FlatReduction p S B) (s t : S) (h : b.map s = b.map t) :
    Localization.Away s ≃ₐ[S] Localization.Away t :=
  AlgEquiv.ofAlgHom (sameReductionMap b s t h) (sameReductionMap b t s h.symm)
    (sameReductionMap_comp b s t h) (sameReductionMap_comp b t s h.symm)

section TwoLifts
variable {C : Type w} {R : Type z} [CommRing C] [CommRing R] [Algebra C R] [Algebra C S]

/-- Both actual lifts now land in the SAME genuine localized target model. -/
def localizedSecondLift (b : FlatReduction p S B) (f g : R →ₐ[C] S)
    (h : b.map.comp f.toRingHom = b.map.comp g.toRingHom) (r : R) :
    Localization.Away r →ₐ[C] Localization.Away (f r) :=
  ((sameReductionEquiv b (g r) (f r) (RingHom.congr_fun h r).symm).toAlgHom.restrictScalars C).comp
    (localizedLift g r)

/-- The ENTIRE original numerator triangle for the second lift into the SAME target. -/
theorem localizedSecondLift_triangle (b : FlatReduction p S B) (f g : R →ₐ[C] S)
    (h : b.map.comp f.toRingHom = b.map.comp g.toRingHom) (r : R) :
    (localizedSecondLift b f g h r).toRingHom.comp (algebraMap R (Localization.Away r)) =
      (algebraMap S (Localization.Away (f r))).comp g.toRingHom := by
  ext x
  change sameReductionEquiv b (g r) (f r) (RingHom.congr_fun h r).symm
      (localizedLift g r (algebraMap R (Localization.Away r) x)) =
    algebraMap S (Localization.Away (f r)) (g x)
  have hL := RingHom.congr_fun (localizedLift_triangle g r) x
  change localizedLift g r (algebraMap R (Localization.Away r) x) =
    algebraMap S (Localization.Away (g r)) (g x) at hL
  rw [hL]
  exact (sameReductionEquiv b (g r) (f r) (RingHom.congr_fun h r).symm).commutes (g x)

variable {A : Type t} [CommRing A]

/-- BOTH whole squares use the SAME ACTUAL residue map and derived target flat reduction. -/
theorem localizedSecondLift_reduction (a : Reduction p R A) (b : FlatReduction p S B)
    (f g : R →ₐ[C] S) (β : A →+* B)
    (hf : b.map.comp f.toRingHom = β.comp a.map)
    (hg : b.map.comp g.toRingHom = β.comp a.map) (r : R) :
    (awayFlatReduction b (f r)).map.comp
        (localizedSecondLift b f g (hf.trans hg.symm) r).toRingHom =
      (localizedResidue a b f.toRingHom β hf r).comp (awayReduction a r).map := by
  rw [← localizedReduction_square a b f β hf r]
  apply IsLocalization.ringHom_ext (Submonoid.powers r)
  ext x
  change (awayFlatReduction b (f r)).map
      (localizedSecondLift b f g (hf.trans hg.symm) r (algebraMap R (Localization.Away r) x)) =
    (awayFlatReduction b (f r)).map (localizedLift f r (algebraMap R (Localization.Away r) x))
  have hG := RingHom.congr_fun (localizedSecondLift_triangle b f g (hf.trans hg.symm) r) x
  change localizedSecondLift b f g (hf.trans hg.symm) r (algebraMap R (Localization.Away r) x) =
    algebraMap S (Localization.Away (f r)) (g x) at hG
  have hF := RingHom.congr_fun (localizedLift_triangle f r) x
  change localizedLift f r (algebraMap R (Localization.Away r) x) =
    algebraMap S (Localization.Away (f r)) (f x) at hF
  have hBG := RingHom.congr_fun (awayReduction_triangle b.toReduction (f r)) (g x)
  change (awayFlatReduction b (f r)).map (algebraMap S (Localization.Away (f r)) (g x)) =
    algebraMap B (Localization.Away (b.map (f r))) (b.map (g x)) at hBG
  have hBF := RingHom.congr_fun (awayReduction_triangle b.toReduction (f r)) (f x)
  change (awayFlatReduction b (f r)).map (algebraMap S (Localization.Away (f r)) (f x)) =
    algebraMap B (Localization.Away (b.map (f r))) (b.map (f x)) at hBF
  rw [hG, hF, hBG, hBF]
  exact congrArg (algebraMap B (Localization.Away (b.map (f r))))
    (RingHom.congr_fun (hg.trans hf.symm) x)
end TwoLifts
end EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationSameReductionLocalization
