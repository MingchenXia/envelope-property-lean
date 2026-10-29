import EnvelopeProperty.DeligneIllusie.WittTwo

/-!
# Witt Two Frobenius

The actual full-Witt-induced length-two coefficient Frobenius automorphism. -/

noncomputable section
namespace EnvelopeProperty.DeligneIllusie.WittTwoFrobenius

variable (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] [CharP k p]

/-- Actual full Witt Frobenius descends to the original length-two quotient. -/
def frobenius : WittTwo.Ring p k →+* WittTwo.Ring p k :=
  RingHom.liftOfRightInverse (WittVector.truncate 2)
    TruncatedWittVector.out TruncatedWittVector.truncateFun_out
    ⟨(WittVector.truncate 2).comp WittVector.frobenius, by
      intro x hx
      rw [RingHom.mem_ker]
      apply TruncatedWittVector.ext
      intro i
      rw [RingHom.comp_apply, WittVector.coeff_truncate, WittVector.coeff_frobenius_charP,
        (WittVector.mem_ker_truncate 2 x).mp hx i i.is_lt,
        zero_pow (Fact.out : p.Prime).ne_zero, TruncatedWittVector.coeff_zero]⟩

/-- Both actual original Witt coordinates retain their genuine coefficient Frobenius. -/
theorem frobenius_coeff (x : WittTwo.Ring p k) (i : Fin 2) :
    (frobenius p k x).coeff i = x.coeff i ^ p := by
  change (WittVector.truncate 2 (WittVector.frobenius x.out)).coeff i = _
  rw [WittVector.coeff_truncate, WittVector.coeff_frobenius_charP,
    TruncatedWittVector.coeff_out]

/-- Original reduction commutes with actual Witt and actual residue Frobenius. -/
theorem reduction_frobenius (x : WittTwo.Ring p k) :
    WittTwo.reduction p k (frobenius p k x) = (WittTwo.reduction p k x) ^ p := by
  rw [WittTwo.reduction_apply, WittTwo.reduction_apply, frobenius_coeff]

variable [PerfectRing k p]

/-- Perfectness of the original field proves bijectivity of the SAME original Witt map. -/
theorem frobenius_bijective : Function.Bijective (frobenius p k) := by
  constructor
  · intro x y h
    apply TruncatedWittVector.ext
    intro i
    apply (frobeniusEquiv k p).injective
    change x.coeff i ^ p = y.coeff i ^ p
    rw [← frobenius_coeff, ← frobenius_coeff, h]
  · intro x
    refine ⟨TruncatedWittVector.mk p (fun i => (frobeniusEquiv k p).symm (x.coeff i)), ?_⟩
    apply TruncatedWittVector.ext
    intro i
    rw [frobenius_coeff, TruncatedWittVector.coeff_mk]
    exact (frobeniusEquiv k p).apply_symm_apply (x.coeff i)

/-- The actual coefficient Frobenius automorphism of the SAME original length-two Witt ring. -/
def frobeniusEquiv : WittTwo.Ring p k ≃+* WittTwo.Ring p k :=
  RingEquiv.ofBijective (frobenius p k) (frobenius_bijective p k)

end EnvelopeProperty.DeligneIllusie.WittTwoFrobenius
