import EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationSameReductionLocalization

/-! # Actual principal localization of the original canonical divided lift difference -/
noncomputable section
namespace EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationDifferenceLocalization
open FrobeniusLiftDifference
open DeligneIllusieLocalContinuationFlatReductionLocalization
open DeligneIllusieLocalContinuationRelativeLiftLocalization
open DeligneIllusieLocalContinuationSameReductionLocalization
universe u v w z t
variable {C : Type t} {R : Type u} {S : Type v} {A : Type w} {B : Type z}
  [CommRing C] [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra C R] [Algebra C S] {p : ℕ}
  (a : Reduction p R A) (b : FlatReduction p S B) (f g : R →ₐ[C] S) (φ : A →+* B)
  (hf : b.map.comp f.toRingHom = φ.comp a.map)
  (hg : b.map.comp g.toRingHom = φ.comp a.map)

/-- The original canonical delta for the ACTUAL two lifts into the SAME derived flat model. -/
def localizedDifference (r : R) : Localization.Away (a.map r) → Localization.Away (b.map (f r)) :=
  difference (awayReduction a r) (awayFlatReduction b (f r))
    (localizedResidue a b f.toRingHom φ hf r)
    (localizedLift f r).toRingHom (localizedSecondLift b f g (hf.trans hg.symm) r).toRingHom
    (fun x => RingHom.congr_fun (localizedReduction_square a b f φ hf r) x)
    (fun x => RingHom.congr_fun (localizedSecondLift_reduction a b f g φ hf hg r) x)

/-- ENTIRE actual original delta restriction, transporting an INTERNALLY PRODUCED original divisor. -/
theorem difference_localization (r : R) :
    (algebraMap B (Localization.Away (b.map (f r)))) ∘
        difference a b φ f.toRingHom g.toRingHom
          (fun x => RingHom.congr_fun hf x) (fun x => RingHom.congr_fun hg x) =
      localizedDifference a b f g φ hf hg r ∘ (algebraMap A (Localization.Away (a.map r))) := by
  let a' := awayReduction a r
  let b' := awayFlatReduction b (f r)
  let φ' := localizedResidue a b f.toRingHom φ hf r
  let F := localizedLift f r
  let G := localizedSecondLift b f g (hf.trans hg.symm) r
  have hf' (x : Localization.Away r) : b'.map (F x) = φ' (a'.map x) :=
    RingHom.congr_fun (localizedReduction_square a b f φ hf r) x
  have hg' (x : Localization.Away r) : b'.map (G x) = φ' (a'.map x) :=
    RingHom.congr_fun (localizedSecondLift_reduction a b f g φ hf hg r) x
  funext x
  obtain ⟨z, rfl⟩ := a.surjective x
  have hF := RingHom.congr_fun (localizedLift_triangle f r) z
  change F (algebraMap R (Localization.Away r) z) =
    algebraMap S (Localization.Away (f r)) (f z) at hF
  have hG := RingHom.congr_fun (localizedSecondLift_triangle b f g (hf.trans hg.symm) r) z
  change G (algebraMap R (Localization.Away r) z) =
    algebraMap S (Localization.Away (f r)) (g z) at hG
  have hfz : b.map (f z) = φ (a.map z) := RingHom.congr_fun hf z
  have hgz : b.map (g z) = φ (a.map z) := RingHom.congr_fun hg z
  obtain ⟨u, hu⟩ : ∃ u : S, (p : S)*u = f z-g z :=
    (b.kernel_iff _).mp (by rw [map_sub, hfz, hgz, sub_self])
  have hu' : (p : Localization.Away (f r))*algebraMap S (Localization.Away (f r)) u =
      F (algebraMap R (Localization.Away r) z)-G (algebraMap R (Localization.Away r) z) := by
    calc
      (p : Localization.Away (f r))*algebraMap S (Localization.Away (f r)) u =
          algebraMap S (Localization.Away (f r)) ((p : S)*u) := by rw [map_mul, map_natCast]
      _ = algebraMap S (Localization.Away (f r)) (f z-g z) := congrArg _ hu
      _ = F (algebraMap R (Localization.Away r) z)-G (algebraMap R (Localization.Away r) z) := by
        rw [hF, hG, map_sub]
  have hA := RingHom.congr_fun (awayReduction_triangle a r) z
  change a'.map (algebraMap R (Localization.Away r) z) =
    algebraMap A (Localization.Away (a.map r)) (a.map z) at hA
  have hB := RingHom.congr_fun (awayReduction_triangle b.toReduction (f r)) u
  change b'.map (algebraMap S (Localization.Away (f r)) u) =
    algebraMap B (Localization.Away (b.map (f r))) (b.map u) at hB
  change algebraMap B (Localization.Away (b.map (f r)))
      (difference a b φ f.toRingHom g.toRingHom
        (fun x => RingHom.congr_fun hf x) (fun x => RingHom.congr_fun hg x) (a.map z)) =
    difference a' b' φ' F.toRingHom G.toRingHom hf' hg'
      (algebraMap A (Localization.Away (a.map r)) (a.map z))
  rw [difference_eq_of_lift a b φ f.toRingHom g.toRingHom
      (fun x => RingHom.congr_fun hf x) (fun x => RingHom.congr_fun hg x) z u hu,
    ← hA, difference_eq_of_lift a' b' φ' F.toRingHom G.toRingHom hf' hg'
      (algebraMap R (Localization.Away r) z) (algebraMap S (Localization.Away (f r)) u) hu']
  exact hB.symm
end EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationDifferenceLocalization
