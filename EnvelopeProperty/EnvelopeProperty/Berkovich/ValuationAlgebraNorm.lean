/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.LocalAlgebraNorm
import EnvelopeProperty.Berkovich.NormForm

/-!
# Scalar valuations of nonetale local algebra norms

The complete-field scalar norm identity holds for inseparable field extensions
as well: minimal-polynomial roots are used with their genuine repetitions.
Finite local algebras then contribute local length times residue degree.
Products require an actual given decomposition into finite local factors;
no global Artinian decomposition is assumed or asserted in this module.
-/

open scoped NNReal IntermediateField
open Polynomial
noncomputable section
namespace EnvelopeProperty

/-- The scalar norm identity for a finite field extension, including inseparable
extensions. Roots are retained with their genuine minimal-polynomial multiplicity. -/
theorem valuation_algebraNorm_eq_pow_of_finite {H L : Type*} [NormedField H]
    [CompleteSpace H] [IsUltrametricDist H] [Field L] [Algebra H L]
    [FiniteDimensional H L] (w : Valuation L ℝ≥0)
    (hw : ∀ c : H, w (algebraMap H L c) = ‖c‖₊) (b : L) :
    (NormedField.valuation (K := H)) (Algebra.norm H b) = w b ^ Module.finrank H L := by
  classical
  obtain ⟨wΩ, hwΩ⟩ := Valuation.exists_extends_norm (K := H) (L := AlgebraicClosure H)
  have hb : IsIntegral H b := Algebra.IsIntegral.isIntegral b
  let pb := IntermediateField.adjoin.powerBasis hb
  have hroot : ∀ r ∈ (minpoly H b).aroots (AlgebraicClosure H), wΩ r = w b := by
    intro r hr
    have hr' : aeval r (minpoly H pb.gen) = 0 := by
      rw [IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen]
      exact (mem_aroots.mp hr).2
    let τ := pb.lift r hr'
    let wF := w.comap (algebraMap H⟮b⟯ L)
    have hval : wΩ.comap τ.toRingHom = wF := Valuation.eq_of_extends_norm
      (fun c => by
        change wΩ (τ (algebraMap H H⟮b⟯ c)) = ‖c‖₊
        rw [AlgHom.commutes, hwΩ])
      (fun c => by
        change w (algebraMap H⟮b⟯ L (algebraMap H H⟮b⟯ c)) = ‖c‖₊
        rw [← IsScalarTower.algebraMap_apply, hw])
    have hv := congrArg (fun v : Valuation H⟮b⟯ ℝ≥0 => v pb.gen) hval
    change wΩ (τ pb.gen) = w (algebraMap H⟮b⟯ L pb.gen) at hv
    have hτgen : τ pb.gen = r := pb.lift_gen r hr'
    have hgen : algebraMap H⟮b⟯ L pb.gen = b := by
      change algebraMap H⟮b⟯ L (IntermediateField.adjoin.powerBasis hb).gen = b
      rw [IntermediateField.adjoin.powerBasis_gen, IntermediateField.AdjoinSimple.algebraMap_gen]
    rwa [hτgen, hgen] at hv
  change ‖Algebra.norm H b‖₊ = _
  rw [← hwΩ (Algebra.norm H b), Algebra.norm_eq_prod_roots (AlgebraicClosure H) (IsAlgClosed.splits _),
    map_pow, map_multiset_prod]
  have hmap : ((minpoly H b).aroots (AlgebraicClosure H)).map wΩ =
      ((minpoly H b).aroots (AlgebraicClosure H)).map (fun _ => w b) :=
    Multiset.map_congr rfl hroot
  rw [hmap, Multiset.map_const', Multiset.prod_replicate, ← pow_mul]
  have hdegree : ((minpoly H b).aroots (AlgebraicClosure H)).card =
      Module.finrank H H⟮b⟯ := by
    change ((minpoly H b).map (algebraMap H (AlgebraicClosure H))).roots.card = _
    rw [← (IsAlgClosed.splits ((minpoly H b).map (algebraMap H (AlgebraicClosure H)))).natDegree_eq_card_roots,
      (minpoly.monic hb).natDegree_map]
    exact (IntermediateField.adjoin.finrank hb).symm
  rw [hdegree, Module.finrank_mul_finrank H H⟮b⟯ L]

/-- A finite local algebra contributes its residue degree times its actual local
length. Neither reducedness nor separability is required. -/
theorem valuation_algebraNorm_eq_pow_of_local {H E : Type*} [NormedField H]
    [CompleteSpace H] [IsUltrametricDist H] [CommRing E] [Algebra H E]
    [FiniteDimensional H E] [IsLocalRing E]
    (w : Valuation (IsLocalRing.ResidueField E) ℝ≥0)
    (hw : ∀ c : H, w (algebraMap H (IsLocalRing.ResidueField E) c) = ‖c‖₊) (b : E) :
    (NormedField.valuation (K := H)) (Algebra.norm H b) =
      w (IsLocalRing.residue E b) ^ ((Module.length E E).toNat *
        Module.finrank H (IsLocalRing.ResidueField E)) := by
  rw [algebraNorm_eq_residueNorm_pow_length, map_pow,
    valuation_algebraNorm_eq_pow_of_finite w hw, ← pow_mul, Nat.mul_comm]

/-- Genuine product decompositions into finite local factors give the full scalar
norm product with local length and residue degree, including nilpotents and inseparability. -/
theorem valuation_algebraNorm_eq_prod_of_localAlgEquiv {H E ι : Type*} [NormedField H]
    [CompleteSpace H] [IsUltrametricDist H] [CommRing E] [Algebra H E]
    [Fintype ι] {L : ι → Type*} [∀ i, CommRing (L i)] [∀ i, Algebra H (L i)]
    [∀ i, FiniteDimensional H (L i)] [∀ i, IsLocalRing (L i)]
    (e : E ≃ₐ[H] ∀ i, L i) (w : ∀ i, Valuation (IsLocalRing.ResidueField (L i)) ℝ≥0)
    (hw : ∀ i (c : H), w i (algebraMap H (IsLocalRing.ResidueField (L i)) c) = ‖c‖₊)
    (b : E) :
    (NormedField.valuation (K := H)) (Algebra.norm H b) =
      ∏ i, w i (IsLocalRing.residue (L i) (e b i)) ^
        ((Module.length (L i) (L i)).toNat * Module.finrank H (IsLocalRing.ResidueField (L i))) := by
  rw [← Algebra.norm_eq_of_algEquiv e, algebraNorm_pi, map_prod]
  exact Finset.prod_congr rfl fun i _ => valuation_algebraNorm_eq_pow_of_local (w i) (hw i) _

end EnvelopeProperty
