import EnvelopeProperty.Vanishing.NadelMixedKummerSmoothCore

/-! # The actual n+q differential basis of the mixed root ambient algebra

The basis is constructed from the ORIGINAL etale coordinates and ORIGINAL
root variables, with the already proved genuine original partial derivations.
-/

noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelMixedKummer.Dimension
open Module
variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
  {n q : ℕ} (x : Fin n → R) (hx : (MvPolynomial.aeval (R := k) x).toRingHom.Etale)

/-- The actual old coordinates and actual original root variables in the
SAME entire ambient polynomial algebra. -/
def coordinate : (Fin n ⊕ Fin q) → MvPolynomial (Fin q) R :=
  Sum.elim (fun i => MvPolynomial.C (x i)) MvPolynomial.X

/-- The genuine original partials evaluate to the identity coordinate matrix. -/
theorem partial_coordinate (i j : Fin n ⊕ Fin q) :
    SmoothSource.ambientDerivative x hx i (coordinate x j) = if j = i then 1 else 0 := by
  classical
  rcases i with i | i <;> rcases j with j | j
  · change coefficientDerivation (Char0.etalePartialDeriv x hx i) (MvPolynomial.C (x j)) = _
    rw [coefficientDerivation_C, Char0.etalePartialDeriv_apply]
    split_ifs <;> simp_all
  · change coefficientDerivation (Char0.etalePartialDeriv x hx i) (MvPolynomial.X j) = _
    simp only [coefficientDerivation_X, Sum.inr_ne_inl, if_false]
  · change MvPolynomial.pderiv i (MvPolynomial.C (x j)) = _
    simp only [MvPolynomial.pderiv_C, Sum.inl_ne_inr, if_false]
  · change MvPolynomial.pderiv i (MvPolynomial.X j) = _
    simp [MvPolynomial.pderiv_X, Pi.single_apply, eq_comm]

include hx in
/-- Actual differentials of the original coordinates are linearly independent,
proved by the actual original partial derivations and no differential certificate. -/
theorem coordinateD_linearIndependent : LinearIndependent (MvPolynomial (Fin q) R)
    (fun i => KaehlerDifferential.D k (MvPolynomial (Fin q) R) (coordinate x i)) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro a ha i
  have he := congrArg (SmoothSource.ambientDerivative x hx i).liftKaehlerDifferential ha
  simpa only [map_sum, map_smul, Derivation.liftKaehlerDifferential_comp_D,
    partial_coordinate, map_zero, ite_smul, smul_zero, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] using he

include hx in
/-- The actual differentials of the same old/root coordinates span the entire
native absolute differential module of the SAME ambient algebra. -/
theorem span_coordinateD : Submodule.span (MvPolynomial (Fin q) R)
    (Set.range (fun i => KaehlerDifferential.D k (MvPolynomial (Fin q) R) (coordinate x i))) = ⊤ := by
  classical
  let W := Submodule.span (MvPolynomial (Fin q) R)
    (Set.range (fun i => KaehlerDifferential.D k (MvPolynomial (Fin q) R) (coordinate x i)))
  have hcoeff : ∀ r : R, KaehlerDifferential.D k (MvPolynomial (Fin q) R) (MvPolynomial.C r) ∈ W := by
    intro r
    have hb : ∀ w : KaehlerDifferential k R,
        KaehlerDifferential.map k k R (MvPolynomial (Fin q) R) w ∈ W := by
      intro w
      have hw : w ∈ Submodule.span R (Set.range (Char0.etaleDifferentialBasis x hx)) := by
        rw [Basis.span_eq]
        trivial
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
      · rintro _ ⟨i, rfl⟩
        rw [Char0.etaleDifferentialBasis_apply, KaehlerDifferential.map_D]
        exact Submodule.subset_span ⟨Sum.inl i, rfl⟩
      · rw [map_zero]
        exact W.zero_mem
      · intro a b _ _ ha hb
        rw [map_add]
        exact W.add_mem ha hb
      · intro a b _ hb
        rw [map_smul]
        exact W.smul_of_tower_mem a hb
    exact (KaehlerDifferential.map_D k k R (MvPolynomial (Fin q) R) r) ▸ hb (KaehlerDifferential.D k R r)
  have hall : ∀ f : MvPolynomial (Fin q) R, KaehlerDifferential.D k (MvPolynomial (Fin q) R) f ∈ W := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C r => exact hcoeff r
    | add f g hf hg => rw [map_add]; exact W.add_mem hf hg
    | mul_X f i hf =>
        rw [Derivation.leibniz]
        exact W.add_mem (W.smul_mem _ (Submodule.subset_span ⟨Sum.inr i, rfl⟩)) (W.smul_mem _ hf)
  apply le_antisymm le_top
  rw [← KaehlerDifferential.span_range_derivation k (MvPolynomial (Fin q) R)]
  exact Submodule.span_le.mpr (by rintro _ ⟨f, rfl⟩; exact hall f)

/-- The genuine n+q ambient differential basis, constructed from the ORIGINAL
coordinate and root functions. -/
def ambientBasis : Basis (Fin n ⊕ Fin q) (MvPolynomial (Fin q) R)
    (KaehlerDifferential k (MvPolynomial (Fin q) R)) :=
  Basis.mk (coordinateD_linearIndependent x hx) (by rw [span_coordinateD x hx])

/-- Its vectors are the actual original universal differentials. -/
theorem ambientBasis_apply (i : Fin n ⊕ Fin q) :
    ambientBasis x hx i = KaehlerDifferential.D k (MvPolynomial (Fin q) R) (coordinate x i) :=
  Basis.mk_apply _ _ _

end EnvelopeProperty.Vanishing.NadelMixedKummer.Dimension
