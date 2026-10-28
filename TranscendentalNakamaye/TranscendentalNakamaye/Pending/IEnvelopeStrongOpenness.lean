import TranscendentalNakamaye.Pending.StrongOpennessEnvelope
import TranscendentalNakamaye.Pending.ChoquetRegularization

set_option autoImplicit false

/-!
# The I-envelope comparison from strong openness

Xia's proof of Proposition 3.2.6 (`xia-sgpt:page-0141`) combines three
inputs:

1. Choquet's lemma, proved in `Pending.ChoquetRegularization`;
2. closure of I-equivalence under finite maxima, Proposition 3.2.3 (`xia-sgpt:page-0139`), whose source proof goes
   through the valuative characterization of multiplier ideals (Theorem 1.4.3
   and Proposition 1.4.4);
3. strong openness for increasing sequences (Theorem 1.4.4).

Items 2 and 3 appear below as explicit hypotheses, `IEquivalentMaxClosed` and
`IncreasingStrongOpenness`, and under them `φ` is I-equivalent to its I-envelope.
Both are proved elsewhere: strong openness in `Pending.StrongOpennessRegularRoute`,
max-closure in `Pending.IEquivalentMax` (analytically, from strong openness and Demailly's
approximation theorem); `Pending.IEnvelopeAnalytic` combines them.
-/

open Set

namespace TranscendentalNakamaye.Pending

noncomputable section

open FirstPass
open FirstPass.IEnvelope

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The pointwise maximum of two theta-PSH potentials is theta-PSH. -/
theorem IsThetaPshPotential.max {θ : SmoothRealForm n M 2} {u v : M → EReal}
    (hu : IsThetaPshPotential θ u) (hv : IsThetaPshPotential θ v) :
    IsThetaPshPotential θ (fun x => Max.max (u x) (v x)) := by
  refine ⟨fun e z hz => ?_, hu.2.mono fun x => le_max_left _ _⟩
  obtain ⟨W, ρ, hzW, hρ, _⟩ := hu.1 e z hz
  refine ⟨W, ρ, hzW, hρ, ?_⟩
  have hF := chartCorrectedFamily_plurisubharmonicOn (F := {u, v})
    (by rintro _ (rfl | rfl); exacts [hu, hv]) e hρ
  have h1 := hF _ ⟨u, by simp, rfl⟩
  have h2 := hF _ ⟨v, by simp, rfl⟩
  convert h1.max h2 using 2 with y
  exact (max_add_add_right _ _ _).symm

/-- I-equivalence to a fixed theta-PSH potential is closed under pointwise
maxima of theta-PSH potentials: the case `ψ = ψ'` of `φ ∨ φ' ∼_I ψ ∨ ψ'` in
Xia, Proposition 3.2.3.  Proved as
`IEquivalentMax.iEquivalentMaxClosed_of_strongOpenness`. -/
def IEquivalentMaxClosed (θ : SmoothRealForm n M 2) : Prop :=
  ∀ φ u v : M → EReal, IsThetaPshPotential θ φ → IsThetaPshPotential θ u →
    IsThetaPshPotential θ v → IEquivalentOnManifold (n := n) u φ →
    IEquivalentOnManifold (n := n) v φ →
    IEquivalentOnManifold (n := n) (fun x => Max.max (u x) (v x)) φ

/-- Assuming strong openness and max-closure, `I(c P_θ[φ]_I) ⊆ I(cφ)` for
every positive exponent. -/
theorem iOrderOnManifold_iSingularityEnvelope_self_of_strongOpenness
    [CompactSpace M] [Nonempty M] (hSO : IncreasingStrongOpenness n)
    {θ : SmoothRealForm n M 2} (hmax : IEquivalentMaxClosed θ)
    (hlocal : HasSmoothLocalPotentials θ) {φ : M → EReal}
    (hφ : IsThetaPshPotential θ φ) :
    IOrderOnManifold (n := n) (iSingularityEnvelope θ φ) φ := by
  obtain ⟨ψ, hψF, hψ⟩ :=
    exists_seq_uscRegularization_iSup_eq (iSingularityCompetitors_nonempty hφ)
  -- Partial maxima of the Choquet sequence.
  let w : ℕ → M → EReal := fun i =>
    Nat.rec (ψ 0) (fun k wk => fun x => Max.max (wk x) (ψ (k + 1) x)) i
  have hw_succ : ∀ i, w (i + 1) = fun x => Max.max (w i x) (ψ (i + 1) x) :=
    fun _ => rfl
  have hw : ∀ i, IsThetaPshPotential θ (w i) ∧ w i ≤ 0 ∧
      IEquivalentOnManifold (n := n) (w i) φ := by
    intro i
    induction i with
    | zero => exact ⟨(hψF 0).1.1, (hψF 0).1.2, (hψF 0).2⟩
    | succ i ih =>
      rw [hw_succ]
      exact ⟨IsThetaPshPotential.max ih.1 (hψF _).1.1,
        fun x => max_le (ih.2.1 x) ((hψF _).1.2 x),
        hmax φ _ _ hφ ih.1 (hψF _).1.1 ih.2.2 (hψF _).2⟩
  have hmono : Monotone w := monotone_nat_of_le_succ fun i x => by
    rw [hw_succ]
    exact le_max_left _ _
  have hsup : (⨆ i, w i) = ⨆ i, ψ i := by
    apply le_antisymm
    · refine iSup_le fun i => ?_
      induction i with
      | zero => exact le_iSup ψ 0
      | succ i ih =>
        rw [hw_succ]
        intro x
        exact max_le (ih x) (le_iSup ψ (i + 1) x)
    · refine iSup_mono fun i => ?_
      cases i with
      | zero => exact le_rfl
      | succ i =>
        rw [hw_succ]
        intro x
        exact le_max_right _ _
  have h := iOrderOnManifold_uscRegularization_iSup_of_strongOpenness hSO hlocal
    (fun i => (hw i).1) (fun i => (hw i).2.1) hmono (fun i => (hw i).2.2.1)
  rwa [hsup, hψ] at h

/-- Xia, Proposition 3.2.6, assuming strong openness and max-closure: a
genuine theta-PSH potential is I-equivalent to its I-envelope. -/
theorem iEquivalent_iSingularityEnvelope_of_strongOpenness
    [CompactSpace M] [Nonempty M] (hSO : IncreasingStrongOpenness n)
    (θ : SmoothRealForm n M 2) (hmax : IEquivalentMaxClosed θ)
    (hlocal : HasSmoothLocalPotentials θ) (φ : M → EReal)
    (hφ : IsThetaPshPotential θ φ) :
    IEquivalentOnManifold (n := n) φ (iSingularityEnvelope θ φ) :=
  ⟨iOrderOnManifold_iSingularityEnvelope hlocal hφ,
    iOrderOnManifold_iSingularityEnvelope_self_of_strongOpenness hSO hmax hlocal hφ⟩

end

end TranscendentalNakamaye.Pending
