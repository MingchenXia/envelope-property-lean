import EnvelopeProperty.Cartier.SchemeRelativeFrobeniusAffineMap
import EnvelopeProperty.Cartier.RelativeFrobeniusCoefficient

/-! # The genuine relative Frobenius kills every original relative derivation

The native pushout generation and actual geometric section-ring triangles
give closed coefficients even for a zero source ring, without `CharP B p`.
Route: `blueprint/src/smooth-scheme-relative-frobenius-complex.tex`.
-/
noncomputable section
namespace EnvelopeProperty.Cartier.SchemeRelativeFrobeniusAffineMap
open CategoryTheory Limits
universe u v
variable {k B : Type u} [Field k] [CommRing B]
variable (α : k →+* B) (p : ℕ) [Fact p.Prime] [CharP k p]

/-- Where the native map is defined, the genuine geometric section map is that
same entire original relative Frobenius map. -/
theorem ringMap_eq_native [CharP B p] :
    ringMap α p = RelativeFrobenius.map α p := by
  apply pushout.hom_ext
  · exact (coefficient_ringMap α p).trans (RelativeFrobenius.coefficientMap_map α p).symm
  · change RelativeFrobenius.sourceMap α p ≫ ringMap α p =
      RelativeFrobenius.sourceMap α p ≫ RelativeFrobenius.map α p
    calc
      _ = absoluteRingMap α p := source_ringMap α p
      _ = CommRingCat.ofHom (frobenius B p) := by
        ext b
        exact absoluteRingMap_apply α p b
      _ = _ := (RelativeFrobenius.sourceMap_map α p).symm

variable [Algebra k B]

/-- Every original relative derivation kills all actual pulled-back coefficients,
including over the zero ring. No characteristic instance on `B` is used. -/
theorem derivation_ringMap_eq_zero {M : Type v} [AddCommGroup M] [Module B M]
    [Module k M] [IsScalarTower k B M]
    (δ : Derivation k B M) (x : RelativeFrobenius.twist (algebraMap k B) p) :
    δ ((ringMap (algebraMap k B) p).hom x) = 0 := by
  have hpB : (p : B) = 0 := by
    simpa only [map_natCast, map_zero] using
      congrArg (algebraMap k B) (CharP.cast_eq_zero k p)
  have hx : x ∈ Subring.closure
      (Set.range (RelativeFrobenius.coefficientMap (algebraMap k B) p) ∪
        Set.range (RelativeFrobenius.sourceMap (algebraMap k B) p)) := by
    have ht : Subring.closure
        (Set.range (RelativeFrobenius.coefficientMap (algebraMap k B) p) ∪
          Set.range (RelativeFrobenius.sourceMap (algebraMap k B) p)) = ⊤ :=
      CommRingCat.closure_range_union_range_eq_top_of_isPushout
        (IsPushout.of_hasPushout (CommRingCat.ofHom (frobenius k p))
          (CommRingCat.ofHom (algebraMap k B)))
    rw [ht]
    trivial
  induction hx using Subring.closure_induction with
  | mem y hy =>
    rcases hy with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · have h := congrArg (fun g : CommRingCat.of k ⟶ CommRingCat.of B => g.hom a)
        (coefficient_ringMap (algebraMap k B) p)
      change (ringMap (algebraMap k B) p).hom
        ((RelativeFrobenius.coefficientMap (algebraMap k B) p).hom a) = algebraMap k B a at h
      rw [h, Derivation.map_algebraMap]
    · rw [source_ringMap_apply, Derivation.leibniz_pow, ← smul_assoc,
        nsmul_eq_mul, hpB, zero_mul, zero_smul]
  | zero => rw [map_zero, map_zero]
  | one => rw [map_one, Derivation.map_one_eq_zero]
  | add a b ha hb hda hdb => rw [map_add, map_add, hda, hdb, add_zero]
  | neg a ha hda => rw [map_neg, map_neg, hda, neg_zero]
  | mul a b ha hb hda hdb =>
    rw [map_mul, Derivation.leibniz, hda, hdb, smul_zero, smul_zero, add_zero]

/-- The actual universal differential kills the entire true geometric relative
Frobenius image, with zero endpoints included. -/
theorem D_ringMap_eq_zero (x : RelativeFrobenius.twist (algebraMap k B) p) :
    KaehlerDifferential.D k B ((ringMap (algebraMap k B) p).hom x) = 0 :=
  derivation_ringMap_eq_zero p (KaehlerDifferential.D k B) x

set_option pp.universes true
set_option pp.deepTerms true
set_option pp.proofs true
#check @ringMap_eq_native
#print axioms ringMap_eq_native
#check @derivation_ringMap_eq_zero
#print axioms derivation_ringMap_eq_zero
#check @D_ringMap_eq_zero
#print axioms D_ringMap_eq_zero
end EnvelopeProperty.Cartier.SchemeRelativeFrobeniusAffineMap
