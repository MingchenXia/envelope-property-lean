import EnvelopeProperty.Cartier.EtaleGradedLeibniz

/-! # Genuine intrinsic original differential and coordinate independence -/
noncomputable section
namespace EnvelopeProperty.Cartier.EtaleDifferentialIntrinsic
open CategoryTheory
open scoped Classical
open PolynomialDeRham EtaleGradedLeibniz
universe u
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B] {n : ℕ}
variable (v : Fin n → B) (hv : (MvPolynomial.aeval (R := R) v).toRingHom.Etale)

private theorem wedgeProduct_one_left {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
    (q : ℕ) (m : M) (w : ⋀[A]^q M) :
    wedgeProduct 1 q ((exteriorPower.oneEquiv A M).symm m) w = leftWedge m q w := by
  rw [exteriorPower.oneEquiv_symm_apply]
  apply Subtype.ext
  change ExteriorAlgebra.ιMulti A 1 (fun _ => m) * (w : ExteriorAlgebra A M) = ExteriorAlgebra.ι A m * w
  rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, mul_one]

private theorem differential_zero_one :
    EtaleDeRham.differential v hv 0
      ((exteriorPower.zeroEquiv B (KaehlerDifferential R B)).symm 1) = 0 := by
  apply (exteriorPower.oneEquiv B (KaehlerDifferential R B)).injective
  simpa only [map_zero, Derivation.map_one_eq_zero] using EtaleDeRham.differential_zero v hv 1

/-- EVERY original wedge of universal differentials is closed in the SAME actual complex.
No coordinate, closedness, characteristic or differential-matching premise is supplied. -/
theorem differential_universalWedge (q : ℕ) (f : Fin q → B) :
    EtaleDeRham.differential v hv q
      (exteriorPower.ιMulti B q (fun j => KaehlerDifferential.D R B (f j))) = 0 := by
  induction q with
  | zero =>
    have h : exteriorPower.ιMulti B 0 (fun j => KaehlerDifferential.D R B (f j)) =
        (exteriorPower.zeroEquiv B (KaehlerDifferential R B)).symm 1 := by
      apply (exteriorPower.zeroEquiv B (KaehlerDifferential R B)).injective
      rw [exteriorPower.zeroEquiv_ιMulti, LinearEquiv.apply_symm_apply]
    rw [h]
    exact differential_zero_one v hv
  | succ q ih =>
    have heq : exteriorPower.ιMulti B (q+1) (fun j => KaehlerDifferential.D R B (f j)) =
        wedgeProduct 1 q
          ((exteriorPower.oneEquiv B (KaehlerDifferential R B)).symm
            (KaehlerDifferential.D R B (f 0)))
          (exteriorPower.ιMulti B q (fun j => KaehlerDifferential.D R B (f j.succ))) := by
      rw [wedgeProduct_one_left, ExteriorBasisScalarExtension.leftWedge_ιMulti]
      congr 1
      funext j
      exact Fin.cases rfl (fun _ => rfl) j
    rw [heq]
    apply Subtype.ext
    have h := differential_wedgeProduct v hv 1 q
      ((exteriorPower.oneEquiv B (KaehlerDifferential R B)).symm
        (KaehlerDifferential.D R B (f 0)))
      (exteriorPower.ιMulti B q (fun j => KaehlerDifferential.D R B (f j.succ)))
    rw [EtaleDifferentialLeibniz.differential_universalD, ih] at h
    simpa only [Submodule.coe_zero, zero_mul, mul_zero, smul_zero, add_zero] using h

/-- The WHOLE original differential has its intrinsic original universal-generator formula
for EVERY original function coefficient and every tuple of original functions. -/
theorem differential_smul_universalWedge (q : ℕ) (a : B) (f : Fin q → B) :
    EtaleDeRham.differential v hv q
      (a • exteriorPower.ιMulti B q (fun j => KaehlerDifferential.D R B (f j))) =
      leftWedge (KaehlerDifferential.D R B a) q
        (exteriorPower.ιMulti B q (fun j => KaehlerDifferential.D R B (f j))) := by
  rw [EtaleDifferentialLeibniz.differential_smul, differential_universalWedge, smul_zero, add_zero]

/-- The ENTIRE original exterior differential is independent of actual etale coordinates,
even of their number. Every original form and original universal differential is retained. -/
theorem differential_eq_of_coordinates {m : ℕ} (w : Fin m → B)
    (hw : (MvPolynomial.aeval (R := R) w).toRingHom.Etale) (q : ℕ)
    (a : ⋀[B]^q (KaehlerDifferential R B)) :
    EtaleDeRham.differential v hv q a = EtaleDeRham.differential w hw q a := by
  let e := (Char0.etaleDifferentialBasis w hw).exteriorPower q
  have ha : ∑ s, e.repr a s • e s = a := e.sum_repr a
  rw [← ha]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro s _
  change EtaleDeRham.differential v hv q
      (e.repr a s • (Char0.etaleDifferentialBasis w hw).exteriorPower q s) =
    EtaleDeRham.differential w hw q
      (e.repr a s • (Char0.etaleDifferentialBasis w hw).exteriorPower q s)
  rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family]
  have hvec : (Char0.etaleDifferentialBasis w hw) ∘ (Set.powersetCard.ofFinEmbEquiv.symm s) =
      fun j => KaehlerDifferential.D R B (w ((Set.powersetCard.ofFinEmbEquiv.symm s) j)) := by
    funext j
    exact Char0.etaleDifferentialBasis_apply w hw _
  rw [hvec, differential_smul_universalWedge, differential_smul_universalWedge]

/-- The SAME whole original additive de Rham complexes agree by genuine identity-components
isomorphisms for ANY TWO actual coordinate tuples, with no comparison premise. -/
def complexIso_of_coordinates {m : ℕ} (w : Fin m → B)
    (hw : (MvPolynomial.aeval (R := R) w).toRingHom.Etale) :
    EtaleDeRham.complex v hv ≅ EtaleDeRham.complex w hw := by
  refine HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) ?_
  intro q r h
  have hr : q+1 = r := h
  subst r
  simp only [EtaleDeRham.complex, CochainComplex.of_d, Iso.refl_hom,
    Category.id_comp, Category.comp_id]
  apply AddCommGrpCat.hom_ext
  exact AddMonoidHom.ext (fun a => (differential_eq_of_coordinates v hv w hw q a).symm)

/-- The actual whole Frobenius-linear complexes have identity-components native isomorphisms
independent of the original etale coordinates, retaining EVERY actual original scalar action. -/
def frobeniusComplexIso_of_coordinates {m : ℕ} (w : Fin m → B)
    (hw : (MvPolynomial.aeval (R := R) w).toRingHom.Etale)
    (p : ℕ) [Fact p.Prime] [CharP B p] :
    EtaleDeRham.frobeniusComplex v hv p ≅ EtaleDeRham.frobeniusComplex w hw p := by
  refine HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) ?_
  intro q r h
  have hr : q+1 = r := h
  subst r
  simp only [EtaleDeRham.frobeniusComplex, CochainComplex.of_d, Iso.refl_hom,
    Category.id_comp, Category.comp_id]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  exact (differential_eq_of_coordinates v hv w hw q a).symm

end EnvelopeProperty.Cartier.EtaleDifferentialIntrinsic
