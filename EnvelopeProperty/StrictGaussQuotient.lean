/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.StrictGaussDivision
import EnvelopeProperty.MonicGaussQuotient

/-! # Original strict analytic principal ideals and genuine finite MODULE quotients -/
open scoped Polynomial NNReal Topology
open Polynomial Topology
noncomputable section
namespace EnvelopeProperty.CompletedMonicDivision
variable {A : Type*} [SeminormedCommRing A] [IsUltrametricDist A] [T0Space A] [CompleteSpace A]

/-- The ORIGINAL analytic ideal of p+h, not a radical or closure replacement. -/
def perturbedIdeal (r : ℝ≥0) (hr : 0 < r) (p : A[X]) (h : Ring (A := A) r hr) :
    Ideal (Ring (A := A) r hr) := Ideal.span {polynomialMap r hr p+h}

/-- Membership in the ORIGINAL analytic ideal is precisely zero original polynomial remainder. -/
theorem mem_perturbedIdeal_iff (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (h : Ring (A := A) r hr) (hh : ‖h‖₊ < r ^ p.natDegree) (f : Ring (A := A) r hr) :
    f ∈ perturbedIdeal r hr p h ↔ perturbedRemainder r hr hp hbound h hh f = 0 := by
  rw [perturbedIdeal, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨q, hq⟩
    have he := perturbedNormalForm_unique r hr hp hbound h hh
      (perturbedQuotient r hr hp hbound h hh f) q (perturbedRemainder r hr hp hbound h hh f) 0
      (degree_perturbedRemainder_lt r hr hp hbound h hh f) (by simp)
      ((perturbed_reconstruction r hr hp hbound h hh f).trans (by simpa using hq))
    exact he.2
  · intro he
    refine ⟨perturbedQuotient r hr hp hbound h hh f, ?_⟩
    simpa only [he, map_zero, add_zero] using (perturbed_reconstruction r hr hp hbound h hh f).symm

/-- The ORIGINAL strict analytic principal ideal itself is genuinely closed. -/
theorem isClosed_perturbedIdeal (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (h : Ring (A := A) r hr) (hh : ‖h‖₊ < r ^ p.natDegree) :
    IsClosed (perturbedIdeal r hr p h : Set (Ring (A := A) r hr)) := by
  have he : (perturbedIdeal r hr p h : Set (Ring (A := A) r hr)) =
      (perturbedRemainderMap r hr hp hbound h hh) ⁻¹' {0} := by
    ext f
    change f ∈ perturbedIdeal r hr p h ↔
      polynomialMap r hr (perturbedRemainder r hr hp hbound h hh f) = 0
    rw [mem_perturbedIdeal_iff r hr hp hbound h hh,
      ← (polynomialMap r hr).map_zero, (polynomialMap_injective r hr).eq_iff]
  rw [he]
  exact isClosed_singleton.preimage (perturbedRemainderMap r hr hp hbound h hh).continuous

omit [CompleteSpace A] in
private theorem polynomial_mem_perturbedIdeal_iff (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (h : Ring (A := A) r hr) (hh : ‖h‖₊ < r ^ p.natDegree) (s : A[X])
    (hs : s.degree < (p.natDegree : WithBot ℕ)) :
    polynomialMap r hr s ∈ perturbedIdeal r hr p h ↔ s = 0 := by
  constructor
  · intro he
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp he
    have hu := perturbedNormalForm_unique r hr hp hbound h hh q 0 0 s (by simp) hs
      (by simpa only [map_zero, add_zero, mul_zero, zero_add] using hq.symm)
    exact hu.2.symm
  · rintro rfl
    simp

omit [IsUltrametricDist A] [T0Space A] [CompleteSpace A] in
private theorem degree_modByMonicHom_lt {p : A[X]} (hp : p.Monic) (z : AdjoinRoot p) :
    (AdjoinRoot.modByMonicHom hp z).degree < (p.natDegree : WithBot ℕ) := by
  obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective z
  rw [AdjoinRoot.modByMonicHom_mk]
  rcases subsingleton_or_nontrivial A with h | h
  · let := h
    rw [show f %ₘ p = 0 from Subsingleton.elim _ _]
    simp
  · let := h
    exact (degree_modByMonic_lt f hp).trans_le p.degree_le_natDegree

omit [IsUltrametricDist A] [T0Space A] [CompleteSpace A] in
private theorem modByMonic_eq_self_of_degree_lt {p s : A[X]} (hp : p.Monic)
    (hs : s.degree < (p.natDegree : WithBot ℕ)) : s %ₘ p = s := by
  rcases subsingleton_or_nontrivial A with h | h
  · exact Subsingleton.elim _ _
  · let := h
    exact (modByMonic_eq_self_iff hp).mpr (by rw [degree_eq_natDegree hp.ne_zero]; exact hs)

private def polynomialAlgHom (r : ℝ≥0) (hr : 0 < r) : A[X] →ₐ[A] Ring (A := A) r hr :=
  { polynomialMap r hr with commutes' _ := rfl }

private def originalRemainderToPerturbedQuotient (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (h : Ring (A := A) r hr) : AdjoinRoot p →ₗ[A] (Ring (A := A) r hr ⧸ perturbedIdeal r hr p h) :=
  (((Ideal.Quotient.mkₐ A (perturbedIdeal r hr p h)).comp (polynomialAlgHom r hr)).toLinearMap).comp
    (AdjoinRoot.modByMonicHom hp)

omit [CompleteSpace A] in
private theorem originalRemainderToPerturbedQuotient_injective (r : ℝ≥0) (hr : 0 < r)
    {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (h : Ring (A := A) r hr) (hh : ‖h‖₊ < r ^ p.natDegree) :
    Function.Injective (originalRemainderToPerturbedQuotient r hr hp h) := by
  intro u v he
  have hz : originalRemainderToPerturbedQuotient r hr hp h (u-v) = 0 := by
    rw [map_sub, he, sub_self]
  change Ideal.Quotient.mk (perturbedIdeal r hr p h)
    (polynomialMap r hr (AdjoinRoot.modByMonicHom hp (u-v))) = 0 at hz
  have hs := (polynomial_mem_perturbedIdeal_iff r hr hp hbound h hh _
    (degree_modByMonicHom_lt hp (u-v))).mp (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  apply sub_eq_zero.mp
  apply (AdjoinRoot.mk_leftInverse hp).injective
  rw [map_zero]
  exact hs

/-- The SAME original strict remainder represents the actual quotient class. -/
theorem quotient_mk_perturbedRemainder (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (h : Ring (A := A) r hr) (hh : ‖h‖₊ < r ^ p.natDegree) (f : Ring (A := A) r hr) :
    Ideal.Quotient.mk (perturbedIdeal r hr p h) (polynomialMap r hr (perturbedRemainder r hr hp hbound h hh f)) =
      Ideal.Quotient.mk (perturbedIdeal r hr p h) f := by
  have hg0 : Ideal.Quotient.mk (perturbedIdeal r hr p h) (polynomialMap r hr p+h) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  simpa only [map_add, map_mul, hg0, zero_mul, zero_add] using
    congrArg (Ideal.Quotient.mk (perturbedIdeal r hr p h))
      (perturbed_reconstruction r hr hp hbound h hh f)

private theorem originalRemainderToPerturbedQuotient_surjective (r : ℝ≥0) (hr : 0 < r)
    {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (h : Ring (A := A) r hr) (hh : ‖h‖₊ < r ^ p.natDegree) :
    Function.Surjective (originalRemainderToPerturbedQuotient r hr hp h) := by
  intro z
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective z
  refine ⟨AdjoinRoot.mk p (perturbedRemainder r hr hp hbound h hh f), ?_⟩
  change Ideal.Quotient.mk (perturbedIdeal r hr p h)
    (polynomialMap r hr (AdjoinRoot.modByMonicHom hp (AdjoinRoot.mk p
      (perturbedRemainder r hr hp hbound h hh f)))) = _
  rw [AdjoinRoot.modByMonicHom_mk, modByMonic_eq_self_of_degree_lt hp
    (degree_perturbedRemainder_lt r hr hp hbound h hh f)]
  exact quotient_mk_perturbedRemainder r hr hp hbound h hh f

/-- The true perturbed quotient is equivalent to the ORIGINAL algebraic remainder MODULE only. -/
def perturbedQuotientLinearEquiv (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (h : Ring (A := A) r hr) (hh : ‖h‖₊ < r ^ p.natDegree) :
    AdjoinRoot p ≃ₗ[A] (Ring (A := A) r hr ⧸ perturbedIdeal r hr p h) :=
  LinearEquiv.ofBijective (originalRemainderToPerturbedQuotient r hr hp h)
    ⟨originalRemainderToPerturbedQuotient_injective r hr hp hbound h hh,
      originalRemainderToPerturbedQuotient_surjective r hr hp hbound h hh⟩

/-- The actual MODULE map takes an original algebraic class through its genuine monic remainder. -/
theorem perturbedQuotientLinearEquiv_mk (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (h : Ring (A := A) r hr) (hh : ‖h‖₊ < r ^ p.natDegree) (f : A[X]) :
    perturbedQuotientLinearEquiv r hr hp hbound h hh (AdjoinRoot.mk p f) =
      Ideal.Quotient.mk (perturbedIdeal r hr p h) (polynomialMap r hr (f %ₘ p)) := rfl

/-- The ORIGINAL power classes give an actual finite free basis, including the zero coefficient ring. -/
def perturbedQuotientBasis (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (h : Ring (A := A) r hr) (hh : ‖h‖₊ < r ^ p.natDegree) :
    Module.Basis (Fin p.natDegree) A (Ring (A := A) r hr ⧸ perturbedIdeal r hr p h) :=
  (AdjoinRoot.powerBasisAux' hp).map (perturbedQuotientLinearEquiv r hr hp hbound h hh)

/-- EVERY constructed basis vector is exactly its ORIGINAL coordinate power class. -/
theorem perturbedQuotientBasis_apply (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (h : Ring (A := A) r hr) (hh : ‖h‖₊ < r ^ p.natDegree) (i : Fin p.natDegree) :
    perturbedQuotientBasis r hr hp hbound h hh i =
      Ideal.Quotient.mk (perturbedIdeal r hr p h) (polynomialMap r hr (X ^ (i : ℕ))) := by
  classical
  have hb : AdjoinRoot.powerBasisAux' hp i = AdjoinRoot.mk p (X ^ (i : ℕ)) := by
    simp only [AdjoinRoot.powerBasisAux', Module.Basis.coe_ofEquivFun, LinearEquiv.coe_symm_mk]
    rw [Finset.sum_eq_single i]
    · simp only [Pi.single_eq_same, monomial_one_right_eq_X_pow]
    · intro j _ hji
      rw [Pi.single_eq_of_ne hji, map_zero]
    · simp
  change perturbedQuotientLinearEquiv r hr hp hbound h hh (AdjoinRoot.powerBasisAux' hp i) = _
  rw [hb, perturbedQuotientLinearEquiv_mk, modByMonic_eq_self_of_degree_lt hp]
  exact (degree_X_pow_le (n := (i : ℕ))).trans_lt (by exact_mod_cast i.isLt)

/-- Actual freeness is DERIVED from the true finite original remainder basis. -/
theorem perturbedQuotientModuleFree (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (h : Ring (A := A) r hr) (hh : ‖h‖₊ < r ^ p.natDegree) :
    Module.Free A (Ring (A := A) r hr ⧸ perturbedIdeal r hr p h) :=
  Module.Free.of_basis (perturbedQuotientBasis r hr hp hbound h hh)

/-- The true analytic quotient is a finite module over the SAME original coefficient ring. -/
theorem perturbedQuotientModuleFinite (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (h : Ring (A := A) r hr) (hh : ‖h‖₊ < r ^ p.natDegree) :
    Module.Finite A (Ring (A := A) r hr ⧸ perturbedIdeal r hr p h) :=
  Module.Finite.of_basis (perturbedQuotientBasis r hr hp hbound h hh)

/-- The WHOLE original strict polynomial remainder depends only on the true analytic quotient class. -/
theorem perturbedRemainder_eq_of_quotient_eq (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (h : Ring (A := A) r hr) (hh : ‖h‖₊ < r ^ p.natDegree) {f g : Ring (A := A) r hr}
    (he : Ideal.Quotient.mk (perturbedIdeal r hr p h) f = Ideal.Quotient.mk (perturbedIdeal r hr p h) g) :
    perturbedRemainder r hr hp hbound h hh f = perturbedRemainder r hr hp hbound h hh g := by
  have hz := (mem_perturbedIdeal_iff r hr hp hbound h hh (f-g)).mp (Ideal.Quotient.eq.mp he)
  have hmap : perturbedRemainderMap r hr hp hbound h hh (f-g) = 0 := by
    change polynomialMap r hr (perturbedRemainder r hr hp hbound h hh (f-g)) = 0
    rw [hz, map_zero]
  rw [map_sub, sub_eq_zero] at hmap
  exact polynomialMap_injective r hr hmap

/-- The true strict-principal quotient infimum norm equals its ORIGINAL polynomial remainder norm. -/
theorem norm_perturbedQuotient_mk_eq_gauss_remainder (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (h : Ring (A := A) r hr) (hh : ‖h‖₊ < r ^ p.natDegree) (f : Ring (A := A) r hr) :
    ‖Ideal.Quotient.mk (perturbedIdeal r hr p h) f‖ =
      (MonicGaussDivision.gauss r (perturbedRemainder r hr hp hbound h hh f) : ℝ) := by
  apply le_antisymm
  · have he := quotient_mk_perturbedRemainder r hr hp hbound h hh f
    calc
      ‖Ideal.Quotient.mk (perturbedIdeal r hr p h) f‖ =
          ‖Ideal.Quotient.mk (perturbedIdeal r hr p h)
            (polynomialMap r hr (perturbedRemainder r hr hp hbound h hh f))‖ := congrArg norm he.symm
      _ ≤ ‖polynomialMap r hr (perturbedRemainder r hr hp hbound h hh f)‖ := Ideal.Quotient.norm_mk_le _ _
      _ = _ := congrArg ((↑) : ℝ≥0 → ℝ) (nnnorm_polynomialMap r hr _)
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨g, hg, hgn⟩ := Ideal.Quotient.norm_mk_lt
      (Ideal.Quotient.mk (perturbedIdeal r hr p h) f) hε
    have hR := perturbedRemainder_eq_of_quotient_eq r hr hp hbound h hh hg
    have hboundg := gauss_perturbedRemainder_le r hr hp hbound h hh g
    rw [hR] at hboundg
    exact (show (MonicGaussDivision.gauss r (perturbedRemainder r hr hp hbound h hh f) : ℝ) ≤ ‖g‖ from
      NNReal.coe_le_coe.mpr hboundg).trans hgn.le

/-- The true norm infimum is ATTAINED by a SAME-A original polynomial representative. -/
theorem perturbedQuotient_norm_attained (r : ℝ≥0) (hr : 0 < r) {p : A[X]} (hp : p.Monic)
    (hbound : ∀ i < p.natDegree, ‖p.coeff i‖₊ * r ^ i ≤ r ^ p.natDegree)
    (h : Ring (A := A) r hr) (hh : ‖h‖₊ < r ^ p.natDegree)
    (z : Ring (A := A) r hr ⧸ perturbedIdeal r hr p h) :
    ∃ s : A[X], s.degree < (p.natDegree : WithBot ℕ) ∧
      Ideal.Quotient.mk (perturbedIdeal r hr p h) (polynomialMap r hr s) = z ∧
        ‖polynomialMap r hr s‖ = ‖z‖ := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective z
  refine ⟨perturbedRemainder r hr hp hbound h hh f, degree_perturbedRemainder_lt r hr hp hbound h hh f,
    quotient_mk_perturbedRemainder r hr hp hbound h hh f, ?_⟩
  rw [norm_perturbedQuotient_mk_eq_gauss_remainder]
  exact congrArg ((↑) : ℝ≥0 → ℝ) (nnnorm_polynomialMap r hr _)

end EnvelopeProperty.CompletedMonicDivision
