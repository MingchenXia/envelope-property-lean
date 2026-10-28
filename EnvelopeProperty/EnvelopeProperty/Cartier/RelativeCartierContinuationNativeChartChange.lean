import EnvelopeProperty.Cartier.RelativeCartierContinuationNativeAllAlgebraNaturality
import EnvelopeProperty.Cartier.RelativeCartierContinuationEtaleChartChange

/-! # Genuine identity-component native geometric-beta chart maps, including zero -/
noncomputable section
namespace EnvelopeProperty.Cartier.RelativeNativeChartChange
open CategoryTheory
universe u

private theorem transportSquare {C : Type*} [Category* C] {P Q R S : C}
    (e : P ≅ Q) (f : R ≅ S) (a : P ⟶ R) (b : Q ⟶ S)
    (h : a ≫ f.hom = e.hom ≫ b) : e.inv ≫ a = b ≫ f.inv := by
  calc
    e.inv ≫ a = (e.inv ≫ (a ≫ f.hom)) ≫ f.inv := by simp [Category.assoc]
    _ = (e.inv ≫ (e.hom ≫ b)) ≫ f.inv := by rw [h]
    _ = b ≫ f.inv := by simp

variable {k B : Type u} [Field k] [CommRing B] [Algebra k B]
variable {n m : ℕ} (v : Fin n → B) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
variable (w : Fin m → B) (hw : (MvPolynomial.aeval (R := k) w).toRingHom.Etale)
variable (p : ℕ) [Fact p.Prime] [CharP k p]
local notation "T" => RelativeFrobenius.twist (algebraMap k B) p
local notation "Kv" => SchemeRelativeFrobeniusAffineDeRham.complex v hv p
local notation "Kw" => SchemeRelativeFrobeniusAffineDeRham.complex w hw p

/-- The ACTUAL native geometric-beta complexes have their ORIGINAL identity components. -/
def complexIso : (Kv) ≅ (Kw) := by
  refine HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) ?_
  intro q r h
  have hr : q+1 = r := h
  subst r
  simp only [SchemeRelativeFrobeniusAffineDeRham.complex, CochainComplex.of_d,
    Iso.refl_hom, Category.id_comp, Category.comp_id]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  exact (EtaleDifferentialIntrinsic.differential_eq_of_coordinates v hv w hw q a).symm

/-- EVERY original native chart comparison component is EXACTLY the original identity. -/
theorem complexIso_hom_f (q : ℕ) :
    (complexIso v hv w hw p).hom.f q =
      𝟙 (SchemeRelativeFrobeniusAffineDeRham.formModule (k := k) (B := B) p q) := rfl

/-- The original entire chart map to itself is the actual whole identity. -/
theorem complexIso_refl : complexIso v hv v hv p = Iso.refl (Kv) := by
  apply Iso.ext
  ext q
  rfl

/-- SAME original whole native chart maps compose strictly. -/
theorem complexIso_hom_trans {l : ℕ} (z : Fin l → B)
    (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale) :
    (complexIso v hv w hw p).hom ≫ (complexIso w hw z hz p).hom =
      (complexIso v hv z hz p).hom := by
  ext q
  rfl

/-- Actual native HomologicalComplex homology of the SAME whole native chart map. -/
def homologyIso (q : ℕ) : (Kv).homology q ≅ (Kw).homology q :=
  (HomologicalComplex.homologyFunctor (ModuleCat T) (ComplexShape.up ℕ) q).mapIso
    (complexIso v hv w hw p)

/-- SAME actual native homology chart maps satisfy their whole strict composition law. -/
theorem homologyIso_hom_trans {l : ℕ} (z : Fin l → B)
    (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale) (q : ℕ) :
    (homologyIso v hv w hw p q).hom ≫ (homologyIso w hw z hz p q).hom =
      (homologyIso v hv z hz p q).hom := by
  change (HomologicalComplex.homologyFunctor (ModuleCat T) (ComplexShape.up ℕ) q).map
      (complexIso v hv w hw p).hom ≫
    (HomologicalComplex.homologyFunctor (ModuleCat T) (ComplexShape.up ℕ) q).map
      (complexIso w hw z hz p).hom = _
  rw [← Functor.map_comp, complexIso_hom_trans]
  rfl

/-- Genuine full native/geometric comparison square wherever endpoint characteristic exists. -/
theorem complexIso_native_square [CharP B p] :
    (complexIso v hv w hw p).hom ≫
        (RelativeNativeAllAlgebraCartier.complexIso_native w hw p).hom =
      (RelativeNativeAllAlgebraCartier.complexIso_native v hv p).hom ≫
        (RelativeEtaleChartChange.complexIso v hv w hw p).hom := by
  ext q a
  rfl

/-- Actual native homology preserves the SAME full-complex comparison square. -/
theorem homologyIso_native_square [CharP B p] (q : ℕ) :
    (homologyIso v hv w hw p q).hom ≫
        (RelativeNativeAllAlgebraCartier.homologyIso_native w hw p q).hom =
      (RelativeNativeAllAlgebraCartier.homologyIso_native v hv p q).hom ≫
        (RelativeEtaleChartChange.homologyIso v hv w hw p q).hom := by
  change (HomologicalComplex.homologyFunctor (ModuleCat T) (ComplexShape.up ℕ) q).map
      (complexIso v hv w hw p).hom ≫
    (HomologicalComplex.homologyFunctor (ModuleCat T) (ComplexShape.up ℕ) q).map
      (RelativeNativeAllAlgebraCartier.complexIso_native w hw p).hom = _
  rw [← Functor.map_comp, complexIso_native_square, Functor.map_comp]
  rfl

attribute [local instance] RelativeEtaleCartierDomain.coefficientAlgebra

/-- SAME genuine T-linear Cartier in EVERY degree is independent of actual chart,
including zero B, with no endpoint characteristic/perfection premise. -/
theorem inverseCartierIso_chartChange (q : ℕ) :
    (RelativeNativeAllAlgebraCartier.inverseCartierIso v hv p q).hom ≫
      (homologyIso v hv w hw p q).hom =
    (RelativeNativeAllAlgebraCartier.inverseCartierIso w hw p q).hom := by
  classical
  by_cases h : Nontrivial B
  · let := h
    let : CharP B p := charP_of_injective_algebraMap (algebraMap k B).injective p
    rw [RelativeNativeAllAlgebraCartier.inverseCartierIso_eq_native,
      RelativeNativeAllAlgebraCartier.inverseCartierIso_eq_native]
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [transportSquare
      (RelativeNativeAllAlgebraCartier.homologyIso_native v hv p q)
      (RelativeNativeAllAlgebraCartier.homologyIso_native w hw p q)
      (homologyIso v hv w hw p q).hom
      (RelativeEtaleChartChange.homologyIso v hv w hw p q).hom
      (homologyIso_native_square v hv w hw p q)]
    rw [← Category.assoc, RelativeEtaleChartChange.inverseCartierIso_chartChange]
  · let : Subsingleton B := not_nontrivial_iff_subsingleton.mp h
    exact (RelativeNativeAllAlgebraCartier.actualHomology_isZero w hw p q).eq_of_tgt _ _

end EnvelopeProperty.Cartier.RelativeNativeChartChange
