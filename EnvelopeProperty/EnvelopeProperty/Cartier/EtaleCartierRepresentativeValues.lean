import EnvelopeProperty.Cartier.EtaleCartierCycleRepresentatives
import EnvelopeProperty.Cartier.PolynomialCartierExteriorAlgebra

/-! # Whole actual etale Cartier representatives and original polynomial base change -/
noncomputable section
namespace EnvelopeProperty.Cartier.EtaleCartierRepresentativeValues
open CategoryTheory MvPolynomial
open scoped Classical TensorProduct ChangeOfRings
universe u

private theorem scalar_hom_ext_basis {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) {M : ModuleCat.{u} A} {N : ModuleCat.{u} B} {I : Type*} (e : Module.Basis I A M)
    (φ ψ : (ModuleCat.extendScalars f).obj M ⟶ N)
    (h : ∀ i, φ ((1 : B) ⊗ₜ[A,f] e i) = ψ ((1 : B) ⊗ₜ[A,f] e i)) : φ = ψ := by
  apply ((ModuleCat.extendRestrictScalarsAdj f).homEquiv M N).injective
  apply ModuleCat.hom_ext
  apply e.ext
  intro i
  change φ ((1 : B) ⊗ₜ[A,f] e i) = ψ ((1 : B) ⊗ₜ[A,f] e i)
  exact h i

section General
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B] {n : ℕ}
variable (v : Fin n → B) (hv : (MvPolynomial.aeval (R := R) v).toRingHom.Etale)
variable (p : ℕ) [Fact p.Prime] [CharP B p]
local notation "W" => KaehlerDifferential R B

/-- The SAME genuine whole exterior Frobenius ring map for the INTERNALLY constructed
original etale Cartier one-cycle map. -/
def ringMap : ExteriorAlgebra B W →+* ExteriorAlgebra B W :=
  ExteriorFrobeniusLift.lift B W p (EtaleClosedExteriorLift.oneFormMap v hv p
    (EtaleCartierCycleRepresentatives.coordinateCycleMap v hv p))

/-- EVERY actual coordinate vector has precisely its ORIGINAL Cartier one-form image. -/
theorem ringMap_coordinate (i : Fin n) :
    ringMap v hv p (ExteriorAlgebra.ι B (KaehlerDifferential.D R B (v i))) =
      (v i)^(p-1) • ExteriorAlgebra.ι B (KaehlerDifferential.D R B (v i)) := by
  rw [ringMap, ExteriorFrobeniusLift.lift_ι]
  have h := EtaleCartierCycleRepresentatives.coordinateCycleMap_D v hv p i
  have hc := congrArg (fun z : EtaleCohomologyProducts.cycles v hv p 1 =>
    ExteriorFrobeniusLift.inclusion B W p 1 z.val) h
  refine hc.trans ?_
  change ((((v i)^(p-1)) • (exteriorPower.oneEquiv B W).symm
    (KaehlerDifferential.D R B (v i)) : ⋀[B]^1 W) : ExteriorAlgebra B W) = _
  rw [Submodule.coe_smul, exteriorPower.oneEquiv_symm_apply]
  change (v i)^(p-1) • ExteriorAlgebra.ιMulti B 1
    (fun _ => KaehlerDifferential.D R B (v i)) = _
  rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, mul_one]

/-- The actual entire coordinate-tuple formula, including repetitions and zero degree. -/
theorem ringMap_coordinateWedge (q : ℕ) (i : Fin q → Fin n) :
    ringMap v hv p (ExteriorAlgebra.ιMulti B q (fun j => KaehlerDifferential.D R B (v (i j)))) =
      (∏ j, v (i j)^(p-1)) •
        ExteriorAlgebra.ιMulti B q (fun j => KaehlerDifferential.D R B (v (i j))) := by
  have h : ringMap v hv p (ExteriorAlgebra.ιMulti B q
        (fun j => KaehlerDifferential.D R B (v (i j)))) =
      ExteriorAlgebra.ιMulti B q (fun j => v (i j)^(p-1) •
        KaehlerDifferential.D R B (v (i j))) := by
    rw [ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply, map_list_prod]
    simp only [List.map_ofFn, Function.comp_def, ringMap_coordinate, map_smul]
  exact h.trans ((ExteriorAlgebra.ιMulti B q).map_smul_univ _ _)

/-- EVERY original etale exterior-basis representative has its exact original Cartier
monomial coefficient and SAME entire original wedge, in ALL degrees. -/
theorem cycleRepresentative_basis (q : ℕ) (s : Set.powersetCard (Fin n) q) :
    (EtaleCartierCycleRepresentatives.cycleRepresentative v hv p q
      ((Char0.etaleDifferentialBasis v hv).exteriorPower q s)).val =
      (show EtaleDeRham.frobeniusModule (R := R) (B := B) p q from
        (∏ j : Fin q, v (Set.powersetCard.ofFinEmbEquiv.symm s j)^(p-1)) •
          (Char0.etaleDifferentialBasis v hv).exteriorPower q s) := by
  apply Subtype.ext
  have hcoord : ((Char0.etaleDifferentialBasis v hv).exteriorPower q s : ExteriorAlgebra B W) =
      ExteriorAlgebra.ιMulti B q
        (fun j => KaehlerDifferential.D R B (v (Set.powersetCard.ofFinEmbEquiv.symm s j))) := by
    simp only [exteriorPower.basis_apply, exteriorPower.ιMulti_family,
      exteriorPower.ιMulti_apply_coe, Function.comp_def, Char0.etaleDifferentialBasis_apply]
  change ringMap v hv p (((Char0.etaleDifferentialBasis v hv).exteriorPower q s : ⋀[B]^q W) :
    ExteriorAlgebra B W) = (∏ j : Fin q, v (Set.powersetCard.ofFinEmbEquiv.symm s j)^(p-1)) •
      (((Char0.etaleDifferentialBasis v hv).exteriorPower q s : ⋀[B]^q W) : ExteriorAlgebra B W)
  rw [hcoord, ringMap_coordinateWedge]

end General
section Field
variable {k B : Type u} [Field k] [CommRing B] [Algebra k B] {n : ℕ}
variable (v : Fin n → B) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
variable (p : ℕ) [Fact p.Prime] [CharP k p] [CharP B p]
local notation "P" => MvPolynomial (Fin n) k
local notation "V" => KaehlerDifferential k B

/-- The TRUE original polynomial representative maps to the SAME actual etale representative
on EVERY original exterior-basis form, including zero degree, without perfectness. -/
theorem polynomial_representative_map_basis (q : ℕ) (s : Set.powersetCard (Fin n) q) :
    EtaleDeRham.polynomialFormMap v hv q
      (PolynomialCartierImage.originalRepresentative k p q
        ((KaehlerDifferential.mvPolynomialBasis k (Fin n)).exteriorPower q s)) =
      (show ⋀[B]^q V from (EtaleCartierCycleRepresentatives.cycleRepresentative v hv p q
        ((Char0.etaleDifferentialBasis v hv).exteriorPower q s)).val) := by
  have h := PolynomialCartierImage.originalRepresentative_smul_basis k p q s (1 : P)
  simp only [one_smul, one_pow, one_mul] at h
  rw [h, EtaleDeRham.polynomialFormMap_smul_basis,
    PolynomialCartierExteriorAlgebra.residue_monomial_product, map_prod]
  simp only [map_pow, MvPolynomial.aeval_X]
  exact congrArg (fun z : EtaleDeRham.frobeniusModule (R := k) (B := B) p q =>
    (show ⋀[B]^q V from z)) (cycleRepresentative_basis v hv p q s).symm

/-- Native scalar extension of the PRE-EXISTING original polynomial representative,
followed by the genuine whole original Frobenius form base-change isomorphism. -/
def scalarRepresentative (q : ℕ) :
    (ModuleCat.extendScalars (MvPolynomial.aeval (R := k) v).toRingHom).obj
      (ModuleCat.of P (⋀[P]^q (KaehlerDifferential k P))) ⟶
        EtaleDeRham.frobeniusModule (R := k) (B := B) p q :=
  (ModuleCat.extendScalars (MvPolynomial.aeval (R := k) v).toRingHom).map
    (ModuleCat.ofHom (X := ModuleCat.of P (⋀[P]^q (KaehlerDifferential k P)))
      (Y := PolynomialDeRham.frobeniusModule (σ := Fin n) k p q)
      (PolynomialCartierImage.representative k p q)) ≫
        (EtaleExteriorBaseChange.frobeniusFormIso v hv p q).hom

/-- EVERY original scalar-extended exterior-basis form has its SAME entire actual original
etale representative, with no coefficient/form comparison premise. -/
theorem scalarRepresentative_one_basis (q : ℕ) (s : Set.powersetCard (Fin n) q) :
    (scalarRepresentative v hv p q).hom
      ((1 : B) ⊗ₜ[P,(MvPolynomial.aeval (R := k) v).toRingHom]
        ((KaehlerDifferential.mvPolynomialBasis k (Fin n)).exteriorPower q s)) =
      (EtaleCartierCycleRepresentatives.cycleRepresentative v hv p q
        ((Char0.etaleDifferentialBasis v hv).exteriorPower q s)).val := by
  have ht := ModuleCat.ExtendScalars.map_tmul (MvPolynomial.aeval (R := k) v).toRingHom
    (ModuleCat.ofHom (X := ModuleCat.of P (⋀[P]^q (KaehlerDifferential k P)))
      (Y := PolynomialDeRham.frobeniusModule (σ := Fin n) k p q)
      (PolynomialCartierImage.representative k p q)) (1 : B)
        ((KaehlerDifferential.mvPolynomialBasis k (Fin n)).exteriorPower q s)
  have hx := EtaleExteriorBaseChange.frobeniusFormIso_one_tmul v hv p q
    (PolynomialCartierImage.originalRepresentative k p q
      ((KaehlerDifferential.mvPolynomialBasis k (Fin n)).exteriorPower q s))
  exact (congrArg (EtaleExteriorBaseChange.frobeniusFormIso v hv p q).hom.hom ht).trans
    (hx.trans (polynomial_representative_map_basis v hv p q s))

/-- The ENTIRE internally constructed original etale representative is EXACTLY genuine native
scalar extension of the SAME pre-existing polynomial representative, in EVERY degree.
This is equality of whole native maps, not a certificate or selected basis-only endpoint. -/
theorem representative_scalarExtension (q : ℕ) :
    (EtaleExteriorBaseChange.exteriorIso v hv q).hom ≫
      ModuleCat.ofHom (X := ModuleCat.of B (⋀[B]^q V))
        (Y := EtaleDeRham.frobeniusModule (R := k) (B := B) p q)
        (EtaleClosedExteriorLift.representative v hv p
          (EtaleCartierCycleRepresentatives.coordinateCycleMap v hv p) q) =
      scalarRepresentative v hv p q := by
  apply scalar_hom_ext_basis (MvPolynomial.aeval (R := k) v).toRingHom
    ((KaehlerDifferential.mvPolynomialBasis k (Fin n)).exteriorPower q)
  intro s
  have hb : (EtaleExteriorBaseChange.exteriorIso v hv q).hom.hom
      ((1 : B) ⊗ₜ[P,(MvPolynomial.aeval (R := k) v).toRingHom]
        ((KaehlerDifferential.mvPolynomialBasis k (Fin n)).exteriorPower q s)) =
        (Char0.etaleDifferentialBasis v hv).exteriorPower q s := by
    exact (EtaleExteriorBaseChange.exteriorIso_tmul_basis v hv q (1 : B) s).trans (one_smul B _)
  exact (congrArg (EtaleClosedExteriorLift.representative v hv p
    (EtaleCartierCycleRepresentatives.coordinateCycleMap v hv p) q).toFun hb).trans
      (scalarRepresentative_one_basis v hv p q s).symm

end Field
end EnvelopeProperty.Cartier.EtaleCartierRepresentativeValues
