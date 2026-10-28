/-
Copyright (c) 2026 Envelope Property Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import EnvelopeProperty.Berkovich.LineBinaryWholeGluing
import EnvelopeProperty.Potential.LineFiniteCoverGrowth

/-! # Genuine whole finite-cover gluing in the ORIGINAL completed function rings -/
open scoped NNReal Polynomial Topology
open Polynomial Topology
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
variable {K : Type*} [NormedField K] [IsUltrametricDist K] [IsAlgClosed K]
  {m : ℕ} {ι : Type*} [Fintype ι] {n : ι → ℕ}
variable (U : FCStandardAffinoid (NormedField.valuation (K := K)) m)
  (V : ∀ i, FCStandardAffinoid (NormedField.valuation (K := K)) (n i))
  (hVU : ∀ i, (V i).carrier ⊆ U.carrier)
  (hcover : ∀ x ∈ U.carrier, ∃ i, x ∈ (V i).carrier)

omit [IsAlgClosed K] [Fintype ι] in
private theorem finiteGlue_piece_subset {q : ℕ}
    (S : Finset ι) (W : FCStandardAffinoid (NormedField.valuation (K := K)) q)
    (hW : W.carrier = ⋃ i ∈ S, (V i).carrier) (i : ι) (hi : i ∈ S) :
    (V i).carrier ⊆ W.carrier := by
  intro x hx
  rw [hW]
  exact Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨hi,hx⟩⟩

include hcover in
/-- The actual finite closed cover constructs a WHOLE original glue with EVERY exact restriction and exact original joint norm. -/
theorem exists_unique_finite_cover_glue (f : ∀ i, (V i).AnalyticFunctions)
    (hcompat : ∀ i j x (hi : x ∈ (V i).carrier) (hj : x ∈ (V j).carrier),
      (V i).evaluationToH ⟨x,hi⟩ (f i) = (V j).evaluationToH ⟨x,hj⟩ (f j)) :
    ∃! g : U.AnalyticFunctions,
      (∀ i, U.analyticRestriction (V i) (hVU i) g = f i) ∧
      ‖g‖₊ = Finset.univ.sup (fun i => ‖f i‖₊) := by
  classical
  let P (S : Finset ι) : Prop :=
    ∃ (q : ℕ) (W : FCStandardAffinoid (NormedField.valuation (K := K)) q)
      (hW : W.carrier = ⋃ i ∈ S, (V i).carrier) (g : W.AnalyticFunctions),
      ∀ i (hi : i ∈ S), W.analyticRestriction (V i) (finiteGlue_piece_subset V S W hW i hi) g = f i
  have hseed (i : ι) : P {i} := by
    have hW : (V i).carrier = ⋃ j ∈ ({i} : Finset ι), (V j).carrier := by ext x; simp
    refine ⟨n i,V i,hW,f i,fun j hj => ?_⟩
    have hji : j = i := Finset.mem_singleton.mp hj
    subst j
    rw [(V i).analyticRestriction_self]
    rfl
  have hstep (S : Finset ι) (hS : P S) (j : ι) (hj : j ∉ S)
      (hne : ((⋃ i ∈ S, (V i).carrier) ∩ (V j).carrier).Nonempty) : P (S.cons j hj) := by
    obtain ⟨q,W,hW,g,hg⟩ := hS
    have hne' : (W.carrier ∩ (V j).carrier).Nonempty := by simpa only [hW] using hne
    obtain ⟨r,A,hA,hglue⟩ := W.exists_unique_binary_glue (V j) hne'
    have hcg : ∀ x (hxW : x ∈ W.carrier) (hxj : x ∈ (V j).carrier),
        W.evaluationToH ⟨x,hxW⟩ g = (V j).evaluationToH ⟨x,hxj⟩ (f j) := by
      intro x hxW hxj
      have hx : x ∈ ⋃ i ∈ S, (V i).carrier := hW ▸ hxW
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hiS,hxi⟩ := Set.mem_iUnion.mp hi
      have he := congrArg ((V i).evaluationToH ⟨x,hxi⟩) (hg i hiS)
      rw [W.analyticRestriction_evaluation] at he
      exact he.trans (hcompat i j x hxi hxj)
    obtain ⟨a,ha,_⟩ := hglue g (f j) hcg
    have hA' : A.carrier = ⋃ i ∈ S.cons j hj, (V i).carrier := by
      rw [hA,hW]
      ext x
      simp only [Set.mem_union,Set.mem_iUnion,Finset.mem_cons]
      constructor
      · rintro (⟨i,hi,hxi⟩ | hxj)
        · exact ⟨i,Or.inr hi,hxi⟩
        · exact ⟨j,Or.inl rfl,hxj⟩
      · rintro ⟨i,(hij | hi),hxi⟩
        · subst i
          exact Or.inr hxi
        · exact Or.inl ⟨i,hi,hxi⟩
    refine ⟨r,A,hA',a,fun i hi => ?_⟩
    rcases Finset.mem_cons.mp hi with hij | hiS
    · subst i
      exact ha.2.1
    · have hsub := finiteGlue_piece_subset V S W hW i hiS
      have he := congrArg (W.analyticRestriction (V i) hsub) ha.1
      change ((W.analyticRestriction (V i) hsub).comp (A.analyticRestriction W _)) a = _ at he
      rw [A.analyticRestriction_comp] at he
      exact he.trans (hg i hiS)
  obtain ⟨q,W,hW,g,hg⟩ := U.finite_cover_overlap_induction V hVU hcover P hseed hstep
  have hWU : W.carrier = U.carrier := by
    rw [hW]
    ext x
    simp only [Set.mem_iUnion,Finset.mem_univ,exists_true_left]
    exact ⟨fun ⟨i,hi⟩ => hVU i hi,fun hx => hcover x hx⟩
  let a := W.analyticRestriction U hWU.symm.subset g
  have ha (i : ι) : U.analyticRestriction (V i) (hVU i) a = f i := by
    change ((U.analyticRestriction (V i) (hVU i)).comp (W.analyticRestriction U _)) g = f i
    rw [W.analyticRestriction_comp]
    exact hg i (Finset.mem_univ i)
  have hn : ‖a‖₊ = Finset.univ.sup (fun i => ‖f i‖₊) := by
    rw [U.nnnorm_eq_cover_restrictions V hVU hcover a]
    simp_rw [ha]
  refine ⟨a,⟨ha,hn⟩,fun b hb => ?_⟩
  exact U.analyticFunctions_eq_of_cover_restrictions_eq V hVU hcover b a
    (fun i => (hb.1 i).trans (ha i).symm)

/-- The LITERAL subring of original whole covering functions agreeing in the SAME original H(x) at EVERY common point. -/
def analyticCompatibleFamilies : Subring (∀ i, (V i).AnalyticFunctions) where
  carrier := {f | ∀ i j x (hi : x ∈ (V i).carrier) (hj : x ∈ (V j).carrier),
    (V i).evaluationToH ⟨x,hi⟩ (f i) = (V j).evaluationToH ⟨x,hj⟩ (f j)}
  zero_mem' := by
    change ∀ i j x hi hj, (V i).evaluationToH ⟨x,hi⟩ 0 = (V j).evaluationToH ⟨x,hj⟩ 0
    intro i j x hi hj
    rw [map_zero,map_zero]
  one_mem' := by
    change ∀ i j x hi hj, (V i).evaluationToH ⟨x,hi⟩ 1 = (V j).evaluationToH ⟨x,hj⟩ 1
    intro i j x hi hj
    rw [map_one,map_one]
  add_mem' := by
    intro f g hf hg i j x hi hj
    change (V i).evaluationToH ⟨x,hi⟩ (f i+g i) = (V j).evaluationToH ⟨x,hj⟩ (f j+g j)
    rw [map_add,map_add,hf i j x hi hj,hg i j x hi hj]
  mul_mem' := by
    intro f g hf hg i j x hi hj
    change (V i).evaluationToH ⟨x,hi⟩ (f i*g i) = (V j).evaluationToH ⟨x,hj⟩ (f j*g j)
    rw [map_mul,map_mul,hf i j x hi hj,hg i j x hi hj]
  neg_mem' := by
    intro f hf i j x hi hj
    change (V i).evaluationToH ⟨x,hi⟩ (-f i) = (V j).evaluationToH ⟨x,hj⟩ (-f j)
    rw [map_neg,map_neg,hf i j x hi hj]

private def finiteGlue_compatibleRestriction : U.AnalyticFunctions →+* analyticCompatibleFamilies V :=
  (U.analyticCoverRestriction V hVU).codRestrict (analyticCompatibleFamilies V) (by
    intro f i j x hi hj
    change (V i).evaluationToH ⟨x,hi⟩ (U.analyticRestriction (V i) (hVU i) f) =
      (V j).evaluationToH ⟨x,hj⟩ (U.analyticRestriction (V j) (hVU j) f)
    rw [U.analyticRestriction_evaluation,U.analyticRestriction_evaluation])

/-- The SAME original whole finite-cover restriction is a genuine RingEquiv onto the actual matching-family subring. -/
def analyticCoverRestrictionEquiv : U.AnalyticFunctions ≃+* analyticCompatibleFamilies V :=
  RingEquiv.ofBijective (finiteGlue_compatibleRestriction U V hVU) (by
    constructor
    · intro f g h
      exact U.analyticCoverRestriction_injective V hVU hcover (congrArg Subtype.val h)
    · intro f
      obtain ⟨g,hg,_⟩ := U.exists_unique_finite_cover_glue V hVU hcover f.1 f.2
      refine ⟨g,Subtype.ext (funext fun i => ?_)⟩
      exact hg.1 i)

/-- EVERY forward coordinate is the literal pre-existing whole original restriction. -/
theorem analyticCoverRestrictionEquiv_apply (f : U.AnalyticFunctions) (i : ι) :
    (U.analyticCoverRestrictionEquiv V hVU hcover f).1 i =
      U.analyticRestriction (V i) (hVU i) f := rfl

/-- EVERY inverse coordinate is an equality of WHOLE original completed functions. -/
theorem analyticCoverRestrictionEquiv_symm_restriction (f : analyticCompatibleFamilies V) (i : ι) :
    U.analyticRestriction (V i) (hVU i) ((U.analyticCoverRestrictionEquiv V hVU hcover).symm f) =
      f.1 i := by
  have he := congrArg (fun g : analyticCompatibleFamilies V => g.1 i)
    ((U.analyticCoverRestrictionEquiv V hVU hcover).apply_symm_apply f)
  exact he

/-- The actual matching-family maximum norm is EXACTLY the original function norm. -/
theorem nnnorm_analyticCoverRestrictionEquiv (f : U.AnalyticFunctions) :
    ‖U.analyticCoverRestrictionEquiv V hVU hcover f‖₊ = ‖f‖₊ := by
  change ‖U.analyticCoverRestriction V hVU f‖₊ = ‖f‖₊
  rw [Pi.nnnorm_def]
  exact (U.nnnorm_eq_cover_restrictions V hVU hcover f).symm

/-- The genuine whole restriction RingEquiv is an isometry for the ORIGINAL norms. -/
theorem isometry_analyticCoverRestrictionEquiv : Isometry (U.analyticCoverRestrictionEquiv V hVU hcover) := by
  apply AddMonoidHomClass.isometry_of_norm
  intro f
  exact congrArg NNReal.toReal (U.nnnorm_analyticCoverRestrictionEquiv V hVU hcover f)

end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
