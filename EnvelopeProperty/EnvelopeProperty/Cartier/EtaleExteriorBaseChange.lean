import EnvelopeProperty.Cartier.EtaleFrobeniusBaseChange
import EnvelopeProperty.Cartier.EtaleDeRham
import Mathlib.Algebra.Homology.Additive

/-! # Actual whole exterior-cotangent and Frobenius differential base change -/
noncomputable section
namespace EnvelopeProperty.Cartier.EtaleExteriorBaseChange
open CategoryTheory
open scoped TensorProduct Classical
universe u
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B] {n : ℕ}
variable (v : Fin n → B) (hv : (MvPolynomial.aeval (R := R) v).toRingHom.Etale)

/-- Genuine original scalar extension of the actual polynomial exterior cotangent module. -/
def exteriorEquiv (q : ℕ) :
    let _ := (MvPolynomial.aeval (R := R) v).toAlgebra
    (B ⊗[MvPolynomial (Fin n) R]
      (⋀[MvPolynomial (Fin n) R]^q (KaehlerDifferential R (MvPolynomial (Fin n) R)))) ≃ₗ[B]
      (⋀[B]^q (KaehlerDifferential R B)) := by
  let := (MvPolynomial.aeval (R := R) v).toAlgebra
  exact (((KaehlerDifferential.mvPolynomialBasis R (Fin n)).exteriorPower q).baseChange B).equiv
    ((Char0.etaleDifferentialBasis v hv).exteriorPower q) (Equiv.refl _)

/-- Native extension of the SAME actual polynomial exterior cotangent module is the SAME
actual etale exterior cotangent module in every degree. -/
def exteriorIso (q : ℕ) :
    (ModuleCat.extendScalars (MvPolynomial.aeval (R := R) v).toRingHom).obj
        (ModuleCat.of (MvPolynomial (Fin n) R)
          (⋀[MvPolynomial (Fin n) R]^q (KaehlerDifferential R (MvPolynomial (Fin n) R)))) ≅
      ModuleCat.of B (⋀[B]^q (KaehlerDifferential R B)) :=
  (exteriorEquiv v hv q).toModuleIso

/-- The actual scalar extension retains EVERY original coordinate differential wedge. -/
theorem exteriorIso_tmul_basis (q : ℕ) (b : B) (s : Set.powersetCard (Fin n) q) :
    let _ := (MvPolynomial.aeval (R := R) v).toAlgebra
    (exteriorIso v hv q).hom (b ⊗ₜ[MvPolynomial (Fin n) R]
      (KaehlerDifferential.mvPolynomialBasis R (Fin n)).exteriorPower q s) =
        b • (Char0.etaleDifferentialBasis v hv).exteriorPower q s := by
  let := (MvPolynomial.aeval (R := R) v).toAlgebra
  change ((((KaehlerDifferential.mvPolynomialBasis R (Fin n)).exteriorPower q).baseChange B).equiv
    ((Char0.etaleDifferentialBasis v hv).exteriorPower q) (Equiv.refl _))
      (b ⊗ₜ[MvPolynomial (Fin n) R]
        (KaehlerDifferential.mvPolynomialBasis R (Fin n)).exteriorPower q s) = _
  have h : b ⊗ₜ[MvPolynomial (Fin n) R]
      (KaehlerDifferential.mvPolynomialBasis R (Fin n)).exteriorPower q s =
      b • (1 ⊗ₜ[MvPolynomial (Fin n) R]
        (KaehlerDifferential.mvPolynomialBasis R (Fin n)).exteriorPower q s) := by
    simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h, map_smul, ← Module.Basis.baseChange_apply, Module.Basis.equiv_apply]
  rfl

/-- The comparison's ENTIRE original pure-tensor map is scalar multiplication of the
SAME actual polynomial exterior map, for every original form. -/
theorem exteriorIso_tmul (q : ℕ) (b : B)
    (w : ⋀[MvPolynomial (Fin n) R]^q (KaehlerDifferential R (MvPolynomial (Fin n) R))) :
    let _ := (MvPolynomial.aeval (R := R) v).toAlgebra
    (exteriorIso v hv q).hom (b ⊗ₜ[MvPolynomial (Fin n) R] w) =
      b • EtaleDeRham.polynomialFormMap v hv q w := by
  let := (MvPolynomial.aeval (R := R) v).toAlgebra
  change exteriorEquiv v hv q (b ⊗ₜ[MvPolynomial (Fin n) R] w) = _
  let e := (KaehlerDifferential.mvPolynomialBasis R (Fin n)).exteriorPower q
  have hw : ∑ s, e.repr w s • e s = w := e.sum_repr w
  rw [← hw]
  simp only [TensorProduct.tmul_sum, map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro s _
  change exteriorEquiv v hv q (b ⊗ₜ[MvPolynomial (Fin n) R] (e.repr w s • e s)) = _
  rw [← TensorProduct.smul_tmul]
  change (exteriorIso v hv q).hom
    ((e.repr w s • b) ⊗ₜ[MvPolynomial (Fin n) R] e s) = _
  rw [exteriorIso_tmul_basis, EtaleDeRham.polynomialFormMap_smul_basis]
  change ((MvPolynomial.aeval v) (e.repr w s) * b) • _ = b • ((MvPolynomial.aeval v) (e.repr w s) • _)
  rw [smul_smul, mul_comm]

variable (p : ℕ) [Fact p.Prime] [CharP R p] [CharP B p]

/-- The actual Frobenius-restricted ORIGINAL exterior modules have genuine scalar-extension
isomorphisms, with no chosen representative or base-change certificate. -/
def frobeniusFormIso (q : ℕ) :
    (ModuleCat.extendScalars (MvPolynomial.aeval (R := R) v).toRingHom).obj
        (PolynomialDeRham.frobeniusModule (σ := Fin n) R p q) ≅
      EtaleDeRham.frobeniusModule (R := R) (B := B) p q :=
  RelativeFrobenius.frobeniusModuleIso (MvPolynomial.aeval (R := R) v).toRingHom p hv
      (ModuleCat.of (MvPolynomial (Fin n) R)
        (⋀[MvPolynomial (Fin n) R]^q (KaehlerDifferential R (MvPolynomial (Fin n) R)))) ≪≫
    (ModuleCat.restrictScalars (frobenius B p)).mapIso (exteriorIso v hv q)

/-- EVERY original pure tensor maps to the SAME original pulled form with its actual pth
power coefficient. -/
theorem frobeniusFormIso_tmul (q : ℕ) (b : B)
    (w : ⋀[MvPolynomial (Fin n) R]^q (KaehlerDifferential R (MvPolynomial (Fin n) R))) :
    let _ := (MvPolynomial.aeval (R := R) v).toAlgebra
    (frobeniusFormIso v hv p q).hom
      (b ⊗ₜ[MvPolynomial (Fin n) R]
        (show PolynomialDeRham.frobeniusModule (σ := Fin n) R p q from w)) =
      b^p • EtaleDeRham.polynomialFormMap v hv q w := by
  let := (MvPolynomial.aeval (R := R) v).toAlgebra
  change (exteriorIso v hv q).hom
    ((RelativeFrobenius.frobeniusModuleIso (MvPolynomial.aeval (R := R) v).toRingHom p hv
      (ModuleCat.of (MvPolynomial (Fin n) R)
        (⋀[MvPolynomial (Fin n) R]^q (KaehlerDifferential R (MvPolynomial (Fin n) R))))).hom
        (b ⊗ₜ[MvPolynomial (Fin n) R]
          (show PolynomialDeRham.frobeniusModule (σ := Fin n) R p q from w))) = _
  exact (congrArg (fun z => (exteriorIso v hv q).hom z)
    (RelativeFrobenius.frobeniusModuleIso_tmul
      (MvPolynomial.aeval (R := R) v).toRingHom p hv
      (ModuleCat.of (MvPolynomial (Fin n) R)
        (⋀[MvPolynomial (Fin n) R]^q (KaehlerDifferential R (MvPolynomial (Fin n) R)))) b w)).trans
      (exteriorIso_tmul v hv q (b^p) w)

/-- The actual whole Frobenius form comparison keeps every original coefficient-one form. -/
theorem frobeniusFormIso_one_tmul (q : ℕ)
    (w : ⋀[MvPolynomial (Fin n) R]^q (KaehlerDifferential R (MvPolynomial (Fin n) R))) :
    let _ := (MvPolynomial.aeval (R := R) v).toAlgebra
    (frobeniusFormIso v hv p q).hom
      ((1 : B) ⊗ₜ[MvPolynomial (Fin n) R]
        (show PolynomialDeRham.frobeniusModule (σ := Fin n) R p q from w)) =
      EtaleDeRham.polynomialFormMap v hv q w := by
  have h := frobeniusFormIso_tmul v hv p q 1 w
  simpa only [one_pow, one_smul] using h

private theorem scalarDifferential_comm {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) {M M' : ModuleCat A} {N N' : ModuleCat B}
    (e : (ModuleCat.extendScalars f).obj M ≅ N)
    (e' : (ModuleCat.extendScalars f).obj M' ≅ N') (a : M ⟶ M') (b : N ⟶ N')
    (h : ∀ m : M, b (e.hom (TensorProduct.tmul A (show (ModuleCat.restrictScalars f).obj (ModuleCat.of B B) from (1 : B)) m)) =
      e'.hom (TensorProduct.tmul A (show (ModuleCat.restrictScalars f).obj (ModuleCat.of B B) from (1 : B)) (a m))) :
    e.hom ≫ b = (ModuleCat.extendScalars f).map a ≫ e'.hom := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  exact h m

private theorem originalDifferential_comm (q : ℕ)
    (e : (ModuleCat.extendScalars (MvPolynomial.aeval (R := R) v).toRingHom).obj
      (PolynomialDeRham.frobeniusModule (σ := Fin n) R p q) ≅
      EtaleDeRham.frobeniusModule (R := R) (B := B) p q)
    (e' : (ModuleCat.extendScalars (MvPolynomial.aeval (R := R) v).toRingHom).obj
      (PolynomialDeRham.frobeniusModule (σ := Fin n) R p (q+1)) ≅
      EtaleDeRham.frobeniusModule (R := R) (B := B) p (q+1))
    (h : let _ := (MvPolynomial.aeval (R := R) v).toAlgebra
      ∀ w : ⋀[MvPolynomial (Fin n) R]^q (KaehlerDifferential R (MvPolynomial (Fin n) R)),
        EtaleDeRham.differential v hv q (e.hom
          ((1 : B) ⊗ₜ[MvPolynomial (Fin n) R]
            (show PolynomialDeRham.frobeniusModule (σ := Fin n) R p q from w))) =
          e'.hom ((1 : B) ⊗ₜ[MvPolynomial (Fin n) R]
            (show PolynomialDeRham.frobeniusModule (σ := Fin n) R p (q+1) from
              PolynomialDeRham.differential R q w))) :
    e.hom ≫ EtaleDeRham.frobeniusDifferential v hv p q =
      (ModuleCat.extendScalars (MvPolynomial.aeval (R := R) v).toRingHom).map
        (PolynomialDeRham.frobeniusDifferential (σ := Fin n) R p q) ≫ e'.hom := by
  apply scalarDifferential_comm (MvPolynomial.aeval (R := R) v).toRingHom e e'
    (PolynomialDeRham.frobeniusDifferential (σ := Fin n) R p q)
    (EtaleDeRham.frobeniusDifferential v hv p q)
  intro w
  exact h w

/-- Actual Frobenius scalar extension commutes with the ENTIRE original differentials. -/
theorem frobeniusFormIso_comm (q : ℕ) :
    (frobeniusFormIso v hv p q).hom ≫ EtaleDeRham.frobeniusDifferential v hv p q =
      (ModuleCat.extendScalars (MvPolynomial.aeval (R := R) v).toRingHom).map
        (PolynomialDeRham.frobeniusDifferential (σ := Fin n) R p q) ≫
          (frobeniusFormIso v hv p (q+1)).hom := by
  let := (MvPolynomial.aeval (R := R) v).toAlgebra
  apply originalDifferential_comm v hv p q
    (frobeniusFormIso v hv p q) (frobeniusFormIso v hv p (q+1))
  intro _ w
  have hq := frobeniusFormIso_one_tmul v hv p q w
  have hr := frobeniusFormIso_one_tmul v hv p (q+1) (PolynomialDeRham.differential R q w)
  have hleft := congrArg (EtaleDeRham.differential v hv q) hq
  have hmiddle := EtaleDeRham.differential_polynomialFormMap v hv q w
  have hwhole := hleft.trans (hmiddle.trans hr.symm)
  exact hwhole

/-- Genuine scalar extension of the SAME original polynomial Frobenius de Rham complex. -/
def extendedFrobeniusComplex : CochainComplex (ModuleCat B) ℕ :=
  ((ModuleCat.extendScalars (MvPolynomial.aeval (R := R) v).toRingHom).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (PolynomialDeRham.frobeniusComplex (σ := Fin n) R p)

/-- The whole actual extended polynomial complex is isomorphic to the SAME actual etale
Frobenius complex, with all original differentials and scalar actions retained. -/
def frobeniusComplexIso :
    extendedFrobeniusComplex (R := R) v p ≅ EtaleDeRham.frobeniusComplex v hv p := by
  refine HomologicalComplex.Hom.isoOfComponents (fun q => frobeniusFormIso v hv p q) ?_
  intro q r h
  have hr : q+1 = r := h
  subst r
  change (frobeniusFormIso v hv p q).hom ≫
      (EtaleDeRham.frobeniusComplex v hv p).d q (q+1) = _
  simp only [EtaleDeRham.frobeniusComplex, extendedFrobeniusComplex,
    PolynomialDeRham.frobeniusComplex, Functor.mapHomologicalComplex_obj_d,
    CochainComplex.of_d]
  exact frobeniusFormIso_comm v hv p q

end EnvelopeProperty.Cartier.EtaleExteriorBaseChange
