import EnvelopeProperty.AlgGeom.CohomologyEulerAdditivity

/-! # Actual finite Euler sums from the genuine cohomology long exact sequence -/
open CategoryTheory Limits
noncomputable section
universe u
namespace EnvelopeProperty.CohomologyFiniteEuler
variable {k : Type u} [Field k]

/-- The finite alternating sum of the SAME actual cohomology dimensions. -/
def partialEuler (C : CochainComplex (ModuleCat.{u} k) ℕ) (N : ℕ) : ℤ :=
  ∑ i ∈ Finset.range N, (-1 : ℤ)^i * Module.finrank k (C.homology i)

private theorem exact_three_rank {A B C D : ModuleCat.{u} k}
    [Module.Finite k A] [Module.Finite k B] [Module.Finite k C]
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D)
    (hab : LinearMap.range a.hom = LinearMap.ker b.hom)
    (hbc : LinearMap.range b.hom = LinearMap.ker c.hom) :
    (Module.finrank k A : ℤ) - Module.finrank k B + Module.finrank k C =
      Module.finrank k (LinearMap.ker a.hom) + Module.finrank k (LinearMap.range c.hom) := by
  have h0 := a.hom.finrank_range_add_finrank_ker
  have h1 := b.hom.finrank_range_add_finrank_ker
  have h2 := c.hom.finrank_range_add_finrank_ker
  rw [← hab] at h1
  rw [← hbc] at h2
  omega

variable (S : ShortComplex (CochainComplex (ModuleCat.{u} k) ℕ)) (hS : S.ShortExact)
variable [∀ i, Module.Finite k (S.X₁.homology i)]
  [∀ i, Module.Finite k (S.X₂.homology i)] [∀ i, Module.Finite k (S.X₃.homology i)]

private def connectingRank (n : ℕ) : ℤ :=
  Module.finrank k (LinearMap.range (hS.δ n (n+1) rfl).hom)

private theorem rank_balance_zero :
    (Module.finrank k (S.X₁.homology 0) : ℤ) - Module.finrank k (S.X₂.homology 0) +
      Module.finrank k (S.X₃.homology 0) = connectingRank S hS 0 := by
  let a := HomologicalComplex.homologyMap S.f 0
  let b := HomologicalComplex.homologyMap S.g 0
  let c := hS.δ 0 1 rfl
  have hmono : Mono (S.f.f 0) := by
    exact (hS.map_of_exact (HomologicalComplex.eval (ModuleCat.{u} k) (.up ℕ) 0)).mono_f
  let : Mono (S.f.f 0) := hmono
  have ha : Function.Injective a := by
    have : Mono a := HomologicalComplex.mono_homologyMap_of_mono_of_not_rel S.f 0
      (fun i hi => by change i+1=0 at hi; omega)
    exact (ModuleCat.mono_iff_injective a).mp inferInstance
  have h := exact_three_rank a b c (hS.homology_exact₂ 0).moduleCat_range_eq_ker
    (hS.homology_exact₃ 0 1 rfl).moduleCat_range_eq_ker
  rw [LinearMap.ker_eq_bot.mpr ha, finrank_bot, Nat.cast_zero, zero_add] at h
  exact h

private theorem rank_balance_succ (n : ℕ) :
    (Module.finrank k (S.X₁.homology (n+1)) : ℤ) - Module.finrank k (S.X₂.homology (n+1)) +
      Module.finrank k (S.X₃.homology (n+1)) = connectingRank S hS n + connectingRank S hS (n+1) := by
  have h := exact_three_rank (HomologicalComplex.homologyMap S.f (n+1))
    (HomologicalComplex.homologyMap S.g (n+1)) (hS.δ (n+1) (n+1+1) rfl)
    (hS.homology_exact₂ (n+1)).moduleCat_range_eq_ker
    (hS.homology_exact₃ (n+1) (n+1+1) rfl).moduleCat_range_eq_ker
  rw [← (hS.homology_exact₁ n (n+1) rfl).moduleCat_range_eq_ker] at h
  exact h

private theorem alternating_rank_sum (N : ℕ) :
    (∑ i ∈ Finset.range (N+1), (-1 : ℤ)^i *
      ((Module.finrank k (S.X₁.homology i) : ℤ) - Module.finrank k (S.X₂.homology i) +
        Module.finrank k (S.X₃.homology i))) = (-1 : ℤ)^N * connectingRank S hS N := by
  induction N with
  | zero => simpa using rank_balance_zero S hS
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, rank_balance_succ S hS N, pow_succ]
    ring

include hS in
/-- Genuine finite Euler additivity uses the actual original long exact
sequence and vanishing of its actual last target, with no supplied rank
or connecting-map exactness certificate. -/
theorem partialEuler_add (N : ℕ) (hN : IsZero (S.X₁.homology (N+1))) :
    partialEuler S.X₂ (N+1) = partialEuler S.X₁ (N+1) + partialEuler S.X₃ (N+1) := by
  have hz : connectingRank S hS N = 0 := by
    unfold connectingRank
    rw [hN.eq_of_tgt (hS.δ N (N+1) rfl) 0]
    simp
  have h := alternating_rank_sum S hS N
  rw [hz, mul_zero] at h
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib] at h
  unfold partialEuler
  omega

end EnvelopeProperty.CohomologyFiniteEuler
