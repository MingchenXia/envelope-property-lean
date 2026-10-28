import EnvelopeProperty.AlgGeom.CyclicSectionSNCAdaptedRoundedTransitions

/-! # Strict actual original rounded transition laws

True original restriction and actual frame/component-unit laws prove all
whole-map identities and compositions. Every actual rounded coordinate is
computed internally from the same original basis.
-/

noncomputable section
universe u
open AlgebraicGeometry CategoryTheory
open Scheme.Modules
open scoped BigOperators
attribute [local instance] OreLocalization.instAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace EnvelopeProperty.CyclicSectionSNCAdaptedRoundedFunctoriality
open CyclicSectionSNCAdaptedFramedAtlas CyclicSectionSNCAdaptedFramedUnits
open CyclicSectionSNCAdaptedRoundedCharts CyclicSectionSNCAdaptedRoundedTransitions

private theorem hom_repr {R S A B I : Type*} [CommRing R] [CommRing S]
    [CommRing A] [CommRing B] [Algebra R A] [Algebra S B] [Fintype I]
    (ba : Module.Basis I R A) (bb : Module.Basis I S B)
    (ρ : R →+* S) (f : A →+* B) (δ : I → S)
    (hs : ∀ r x, f (r • x) = ρ r • f x)
    (hb : ∀ i, f (ba i) = δ i • bb i) (x : A) (i : I) :
    bb.repr (f x) i = δ i * ρ (ba.repr x i) := by
  classical
  have he : f x = ∑ j, (δ j * ρ (ba.repr x j)) • bb j := by
    calc
      _ = f (∑ j, ba.repr x j • ba j) := congrArg f (ba.sum_repr x).symm
      _ = _ := by simp only [_root_.map_sum, hs, hb, smul_smul, mul_comm]
  rw [he]
  exact congrFun (bb.repr_sum_self (fun j => δ j * ρ (ba.repr x j))) i

private theorem hom_ext_repr {S A B I : Type*} [CommRing S] [CommRing A] [CommRing B]
    [Algebra S B] (b : Module.Basis I S B) (f g : A →+* B)
    (he : ∀ x i, b.repr (f x) i = b.repr (g x) i) : f = g := by
  ext x
  apply b.repr.injective
  exact Finsupp.ext (he x)

variable {X : Scheme.{u}} [IsIntegral X]
variable {L : X.Modules} {n : ℕ} {s : unitObj X ⟶ CanonicalGeometry.bundleTensorPower L n}
variable {F : Scheme.DivisorFamily X} {a : F.ι → ℕ}

/-- The actual original identity fixes the WHOLE actual fraction ring. -/
theorem fractionMap_id (c : Chart L n s F a) :
    fractionMap (𝟙 c) = RingHom.id (FractionRing (coefficientRing c)) := by
  let := coefficientDomain c
  apply IsLocalization.ringHom_ext (nonZeroDivisors (coefficientRing c))
  ext r
  change fractionMap (𝟙 c)
    (algebraMap (coefficientRing c) (FractionRing (coefficientRing c)) r) = _
  rw [fractionMap_algebraMap, restriction_id]
  rfl

/-- The genuine original fraction restrictions compose as WHOLE actual RingHoms. -/
theorem fractionMap_comp {c d e : Chart L n s F a} (h : c ⟶ d) (k : d ⟶ e) :
    (fractionMap h).comp (fractionMap k) = fractionMap (h ≫ k) := by
  let := coefficientDomain c
  let := coefficientDomain d
  let := coefficientDomain e
  apply IsLocalization.ringHom_ext (nonZeroDivisors (coefficientRing e))
  ext r
  change fractionMap h (fractionMap k
      (algebraMap (coefficientRing e) (FractionRing (coefficientRing e)) r)) =
    fractionMap (h ≫ k)
      (algebraMap (coefficientRing e) (FractionRing (coefficientRing e)) r)
  rw [fractionMap_algebraMap, fractionMap_algebraMap, fractionMap_algebraMap, restriction_comp]
  rfl

/-- The original identity fixes the ENTIRE actual generic quotient. -/
theorem genericMap_id (c : Chart L n s F a) : genericMap (𝟙 c) = RingHom.id (genericRing c) := by
  let := coefficientDomain c
  apply AdjoinRoot.ringHom_ext
  · ext r
    change genericMap (𝟙 c)
      (algebraMap (FractionRing (coefficientRing c)) (genericRing c) r) = _
    rw [genericMap_fraction, fractionMap_id]
    rfl
  · change genericMap (𝟙 c) (CyclicSectionAlgebra.root n _) = CyclicSectionAlgebra.root n _
    rw [genericMap_root, frameUnit_id]
    simp only [Units.val_one, map_one, one_mul]

/-- Actual original generic transitions compose on the ENTIRE literal original quotients. -/
theorem genericMap_comp {c d e : Chart L n s F a} (h : c ⟶ d) (k : d ⟶ e) :
    (genericMap h).comp (genericMap k) = genericMap (h ≫ k) := by
  let := coefficientDomain c
  let := coefficientDomain d
  let := coefficientDomain e
  apply AdjoinRoot.ringHom_ext
  · ext r
    change genericMap h (genericMap k
        (algebraMap (FractionRing (coefficientRing e)) (genericRing e) r)) =
      genericMap (h ≫ k) (algebraMap (FractionRing (coefficientRing e)) (genericRing e) r)
    rw [genericMap_fraction, genericMap_fraction, genericMap_fraction]
    exact congrArg (algebraMap (FractionRing (coefficientRing c)) (genericRing c))
      (RingHom.congr_fun (fractionMap_comp h k) r)
  · change genericMap h (genericMap k (CyclicSectionAlgebra.root n _)) =
      genericMap (h ≫ k) (CyclicSectionAlgebra.root n _)
    rw [genericMap_root, map_mul, genericMap_algebraMap, genericMap_root, genericMap_root,
      frameUnit_comp]
    simp only [Units.val_mul, Units.coe_map, map_mul, mul_assoc]
    exact mul_left_comm _ _ _

/-- EVERY actual original element has its full original rounded-coordinate transition formula. -/
theorem roundedMap_repr {c d : Chart L n s F a} (h : c ⟶ d) (hn : 0 < n)
    (x : roundedRing d hn) (i : Fin n) :
    (basis c hn).repr (roundedMap h hn x) i =
      (diagonalUnit h (i : ℕ) : coefficientRing c) * restriction h ((basis d hn).repr x i) :=
  hom_repr (basis d hn) (basis c hn) (restriction h) (roundedMap h hn)
    (fun j => (diagonalUnit h (j : ℕ) : coefficientRing c))
    (roundedMap_smul h hn) (roundedMap_basis h hn) x i

/-- The original identity fixes the ENTIRE actual rounded chart algebra. -/
theorem roundedMap_id (c : Chart L n s F a) (hn : 0 < n) :
    roundedMap (𝟙 c) hn = RingHom.id (roundedRing c hn) := by
  apply hom_ext_repr (basis c hn)
  intro x i
  rw [roundedMap_repr, diagonalUnit_id, restriction_id]
  simp only [Units.val_one, one_mul, RingHom.id_apply]

/-- Whole rounded transition composition is DERIVED from actual basis coordinates and true unit laws. -/
theorem roundedMap_comp {c d e : Chart L n s F a} (h : c ⟶ d) (k : d ⟶ e) (hn : 0 < n) :
    (roundedMap h hn).comp (roundedMap k hn) = roundedMap (h ≫ k) hn := by
  apply hom_ext_repr (basis c hn)
  intro x i
  change (basis c hn).repr (roundedMap h hn (roundedMap k hn x)) i = _
  rw [roundedMap_repr, roundedMap_repr, roundedMap_repr, restriction_comp, diagonalUnit_comp]
  simp only [map_mul, Units.val_mul, Units.coe_map, RingHom.comp_apply, mul_assoc]
  rfl

end EnvelopeProperty.CyclicSectionSNCAdaptedRoundedFunctoriality
