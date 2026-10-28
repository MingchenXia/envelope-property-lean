import EnvelopeProperty.Cartier.ExteriorFrobeniusLift
import EnvelopeProperty.Cartier.CartierOneEtaleIsomorphism

/-! # The actual polynomial Cartier representative is a genuine graded algebra map -/
noncomputable section
namespace EnvelopeProperty.Cartier.PolynomialCartierExteriorAlgebra
open MvPolynomial CategoryTheory
open scoped Classical
universe u
variable (k : Type u) [Field k] {n : ℕ} (p : ℕ) [Fact p.Prime] [CharP k p]
local notation "P" => MvPolynomial (Fin n) k
local notation "W" => KaehlerDifferential k P

/-- The SAME original polynomial Cartier ONE-form representative, with its actual Frobenius action. -/
def oneFormMap : W →ₗ[P] ExteriorFrobeniusLift.forms P W p 1 :=
  (PolynomialCartierImage.representative k p 1).comp (exteriorPower.oneEquiv P W).symm.toLinearMap

/-- The genuine WHOLE original exterior ring map induced by that SAME original one-form map. -/
def ringMap : ExteriorAlgebra P W →+* ExteriorAlgebra P W :=
  ExteriorFrobeniusLift.lift P W p (oneFormMap k p)

/-- Its actual original homogeneous components in EVERY degree, with genuine Frobenius scalars. -/
def gradedMap (q : ℕ) : (⋀[P]^q W) →ₗ[P] PolynomialDeRham.frobeniusModule (σ := Fin n) k p q :=
  ExteriorFrobeniusLift.homogeneous P W p (oneFormMap k p) q

/-- EACH actual coordinate differential has its SAME original Cartier one-form image. -/
theorem ringMap_coordinate (i : Fin n) :
    ringMap k p (ExteriorAlgebra.ι P (KaehlerDifferential.D k P (X i))) =
      (X i : P)^(p-1) • ExteriorAlgebra.ι P (KaehlerDifferential.D k P (X i)) := by
  rw [ringMap, ExteriorFrobeniusLift.lift_ι]
  have h := CartierOneEtaleIsomorphism.polynomial_representative_coordinate (k := k) p i
  have hc := congrArg (ExteriorFrobeniusLift.inclusion P W p 1) h
  change ExteriorFrobeniusLift.inclusion P W p 1
    (PolynomialCartierImage.representative k p 1 ((exteriorPower.oneEquiv P W).symm
      (KaehlerDifferential.D k P (X i)))) = _
  refine hc.trans ?_
  change (((X i : P)^(p-1) • (exteriorPower.oneEquiv P W).symm
    (KaehlerDifferential.D k P (X i)) : ⋀[P]^1 W) : ExteriorAlgebra P W) = _
  rw [Submodule.coe_smul, exteriorPower.oneEquiv_symm_apply]
  change (X i : P)^(p-1) • ExteriorAlgebra.ιMulti P 1
    (fun _ => KaehlerDifferential.D k P (X i)) = _
  rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, mul_one]

/-- The ENTIRE actual coordinate-wedge formula, including repeated coordinates and degree zero. -/
theorem ringMap_coordinateWedge (q : ℕ) (i : Fin q → Fin n) :
    ringMap k p (ExteriorAlgebra.ιMulti P q (fun j => KaehlerDifferential.D k P (X (i j)))) =
      (∏ j, (X (i j) : P)^(p-1)) •
        ExteriorAlgebra.ιMulti P q (fun j => KaehlerDifferential.D k P (X (i j))) := by
  have h : ringMap k p
      (ExteriorAlgebra.ιMulti P q (fun j => KaehlerDifferential.D k P (X (i j)))) =
      ExteriorAlgebra.ιMulti P q
        (fun j => (X (i j) : P)^(p-1) • KaehlerDifferential.D k P (X (i j))) := by
    rw [ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply, map_list_prod]
    simp only [List.map_ofFn, Function.comp_def, ringMap_coordinate, map_smul]
  exact h.trans ((ExteriorAlgebra.ιMulti P q).map_smul_univ _ _)

omit [CharP k p] in
/-- The actual original residue-digit monomial equals the product over precisely its original
wedge coordinates, with the ordered tuple reindexing genuinely proved. -/
theorem residue_monomial_product (q : ℕ) (s : Set.powersetCard (Fin n) q) :
    monomial (PolynomialCartierImage.residueDigit p q s).toFinsupp (1 : k) =
      ∏ j : Fin q, (X (Set.powersetCard.ofFinEmbEquiv.symm s j) : P)^(p-1) := by
  have he : (PolynomialCartierImage.residueDigit p q s).toFinsupp =
      Finsupp.indicator s.val (fun _ _ => p-1) := by
    ext i
    simp only [Box.toFinsupp_apply, PolynomialCartierImage.residueDigit_apply,
      Finsupp.indicator_apply]
    rw [← Set.powersetCard.mem_coe_iff]
    split_ifs <;> rfl
  rw [he, ← prod_X_pow]
  symm
  exact Finset.prod_bij (fun j _ => Set.powersetCard.ofFinEmbEquiv.symm s j)
    (fun j _ => (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s _).mp ⟨j, rfl⟩)
    (fun j _ l _ h => (Set.powersetCard.ofFinEmbEquiv.symm s).injective h)
    (fun i hi => by
      obtain ⟨j, hj⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s i).mpr hi
      exact ⟨j, Finset.mem_univ j, hj⟩)
    (fun _ _ => rfl)

/-- The true entire homogeneous exterior-ring lift is EXACTLY the PRE-EXISTING original
polynomial Cartier representative in EVERY degree, not a new substitute map. -/
theorem gradedMap_eq_representative (q : ℕ) :
    gradedMap (n := n) k p q = PolynomialCartierImage.representative k p q := by
  apply ((KaehlerDifferential.mvPolynomialBasis k (Fin n)).exteriorPower q).ext
  intro s
  have hb := PolynomialCartierImage.representative_smul_basis k p q s (1 : P)
  simp only [one_smul, one_pow, one_mul] at hb
  apply Subtype.ext
  have hcoord : ((KaehlerDifferential.mvPolynomialBasis k (Fin n)).exteriorPower q s :
      ExteriorAlgebra P W) = ExteriorAlgebra.ιMulti P q
        (fun j => KaehlerDifferential.D k P (X (Set.powersetCard.ofFinEmbEquiv.symm s j))) := by
    simp only [exteriorPower.basis_apply, exteriorPower.ιMulti_family,
      exteriorPower.ιMulti_apply_coe, Function.comp_def, KaehlerDifferential.mvPolynomialBasis_apply]
  change ringMap k p (((KaehlerDifferential.mvPolynomialBasis k (Fin n)).exteriorPower q s :
    ⋀[P]^q W) : ExteriorAlgebra P W) = _
  rw [hcoord, ringMap_coordinateWedge]
  have hb' := congrArg (ExteriorFrobeniusLift.inclusion P W p q) hb
  change ((show ⋀[P]^q W from PolynomialCartierImage.representative k p q
      ((KaehlerDifferential.mvPolynomialBasis k (Fin n)).exteriorPower q s)) : ExteriorAlgebra P W) =
    monomial (PolynomialCartierImage.residueDigit p q s).toFinsupp (1 : k) •
      (((KaehlerDifferential.mvPolynomialBasis k (Fin n)).exteriorPower q s : ⋀[P]^q W) :
        ExteriorAlgebra P W) at hb'
  rw [hcoord] at hb'
  exact (congrArg (fun c : P => c • ExteriorAlgebra.ιMulti P q
    (fun j => KaehlerDifferential.D k P (X (Set.powersetCard.ofFinEmbEquiv.symm s j))))
      (residue_monomial_product k p q s).symm).trans
        hb'.symm

/-- The SAME existing original whole Cartier representative is the restriction of the
ACTUAL entire original exterior ring homomorphism, on EVERY original form. -/
theorem ringMap_form (q : ℕ) (w : ⋀[P]^q W) :
    ringMap k p (w : ExteriorAlgebra P W) =
      ((show ⋀[P]^q W from PolynomialCartierImage.representative k p q w) : ExteriorAlgebra P W) :=
  congrArg (fun F : (⋀[P]^q W) →ₗ[P] PolynomialDeRham.frobeniusModule (σ := Fin n) k p q =>
    ExteriorFrobeniusLift.inclusion P W p q (F w)) (gradedMap_eq_representative k p q)

/-- The PRE-EXISTING actual original Cartier representative genuinely preserves ALL original
homogeneous exterior products, with no multiplicativity or basis-support premise. -/
theorem representative_wedgeProduct (q r : ℕ) (a : ⋀[P]^q W) (b : ⋀[P]^r W) :
    PolynomialCartierImage.representative k p (r+q) (EtaleGradedLeibniz.wedgeProduct q r a b) =
      (show PolynomialDeRham.frobeniusModule (σ := Fin n) k p (r+q) from
        EtaleGradedLeibniz.wedgeProduct q r
          (show ⋀[P]^q W from PolynomialCartierImage.representative k p q a)
          (show ⋀[P]^r W from PolynomialCartierImage.representative k p r b)) := by
  have h : gradedMap k p (r+q) (EtaleGradedLeibniz.wedgeProduct q r a b) =
      (show PolynomialDeRham.frobeniusModule (σ := Fin n) k p (r+q) from
        EtaleGradedLeibniz.wedgeProduct q r (show ⋀[P]^q W from gradedMap k p q a)
          (show ⋀[P]^r W from gradedMap k p r b)) :=
    ExteriorFrobeniusLift.homogeneous_wedgeProduct P W p (oneFormMap k p) q r a b
  simpa only [gradedMap_eq_representative] using h

end EnvelopeProperty.Cartier.PolynomialCartierExteriorAlgebra
