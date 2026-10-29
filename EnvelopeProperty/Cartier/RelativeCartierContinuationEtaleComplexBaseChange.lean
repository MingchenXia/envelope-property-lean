import EnvelopeProperty.Cartier.RelativeCartierContinuationEtaleBaseChange
import EnvelopeProperty.Cartier.RelativeCartierContinuationPolynomialCohomologyResidual
import EnvelopeProperty.Cartier.EtaleExteriorBaseChange
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # Native relative etale de Rham complexes genuinely base change

All original form modules and whole differentials are retained. Scalar extension
uses the actual map of native relative twists and its genuinely derived flatness.
-/
noncomputable section
namespace EnvelopeProperty.Cartier.RelativeEtaleComplexBaseChange
open CategoryTheory Limits
open scoped TensorProduct
universe u

private def twistOver {k A B : Type u} [CommRing k] [CommRing A] [CommRing B]
    (α : k →+* A) (β : k →+* B) (f : A →+* B) (h : f.comp α = β)
    (p : ℕ) [Fact p.Prime] [CharP k p] :
    RelativeFrobenius.twist α p ⟶ RelativeFrobenius.twist β p := by
  subst β
  exact RelativeEtaleBaseChange.twistMap α f p

private theorem twistOver_coefficient {k A B : Type u} [CommRing k] [CommRing A] [CommRing B]
    (α : k →+* A) (β : k →+* B) (f : A →+* B) (h : f.comp α = β)
    (p : ℕ) [Fact p.Prime] [CharP k p] :
    RelativeFrobenius.coefficientMap α p ≫ twistOver α β f h p =
      RelativeFrobenius.coefficientMap β p := by
  subst β
  exact RelativeEtaleBaseChange.coefficientMap_twistMap α f p

private theorem twistOver_source {k A B : Type u} [CommRing k] [CommRing A] [CommRing B]
    (α : k →+* A) (β : k →+* B) (f : A →+* B) (h : f.comp α = β)
    (p : ℕ) [Fact p.Prime] [CharP k p] :
    RelativeFrobenius.sourceMap α p ≫ twistOver α β f h p =
      CommRingCat.ofHom f ≫ RelativeFrobenius.sourceMap β p := by
  subst β
  exact RelativeEtaleBaseChange.sourceMap_twistMap α f p

private theorem twistOver_etale {k A B : Type u} [CommRing k] [CommRing A] [CommRing B]
    (α : k →+* A) (β : k →+* B) (f : A →+* B) (h : f.comp α = β)
    (p : ℕ) [Fact p.Prime] [CharP k p] (hf : f.Etale) :
    (twistOver α β f h p).hom.Etale := by
  subst β
  exact RelativeEtaleBaseChange.twistMap_etale α f p hf

private theorem twistOver_square {k A B : Type u} [CommRing k] [CommRing A] [CommRing B]
    (α : k →+* A) (β : k →+* B) (f : A →+* B) (h : f.comp α = β)
    (p : ℕ) [Fact p.Prime] [CharP k p] [CharP A p] [CharP B p] (hf : f.Etale) :
    IsPushout (RelativeFrobenius.map α p) (twistOver α β f h p)
      (CommRingCat.ofHom f) (RelativeFrobenius.map β p) := by
  subst β
  exact RelativeEtaleBaseChange.relativeSquare α f p hf

variable {k B : Type u} [Field k] [CommRing B] [Algebra k B] {n : ℕ}
variable (v : Fin n → B) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
local notation "P" => MvPolynomial (Fin n) k

private theorem chart_comp : (MvPolynomial.aeval (R := k) v).toRingHom.comp (algebraMap k P) =
    algebraMap k B := by
  ext a
  exact (MvPolynomial.aeval v).commutes a

variable (p : ℕ) [Fact p.Prime] [CharP k p] [CharP B p]
local notation "TP" => RelativeFrobenius.twist (algebraMap k P) p
local notation "TB" => RelativeFrobenius.twist (algebraMap k B) p
local notation "KP" => RelativeEtaleDeRham.complex (MvPolynomial.X : Fin n → P)
  (RelativePolynomialCartier.polynomialEtale k n) p

/-- The actual chart induces a map of the SAME native relative twists, with original B base map. -/
def chartTwistMap : TP ⟶ TB :=
  twistOver (algebraMap k P) (algebraMap k B) (MvPolynomial.aeval v).toRingHom (chart_comp v) p

omit [CharP B p] in
/-- The actual chart-induced twist map retains the SAME entire original coefficient inclusion. -/
theorem chartTwistMap_coefficient : RelativeFrobenius.coefficientMap (algebraMap k P) p ≫
    chartTwistMap (k := k) v p = RelativeFrobenius.coefficientMap (algebraMap k B) p :=
  twistOver_coefficient (algebraMap k P) (algebraMap k B) (MvPolynomial.aeval v).toRingHom
    (chart_comp v) p

omit [CharP B p] in
/-- The actual chart-induced twist map commutes with the SAME entire original source inclusions. -/
theorem chartTwistMap_source : RelativeFrobenius.sourceMap (algebraMap k P) p ≫
    chartTwistMap (k := k) v p = CommRingCat.ofHom (MvPolynomial.aeval v).toRingHom ≫
      RelativeFrobenius.sourceMap (algebraMap k B) p :=
  twistOver_source (algebraMap k P) (algebraMap k B) (MvPolynomial.aeval v).toRingHom
    (chart_comp v) p

include hv in
omit [CharP B p] in
/-- Etaleness of the ORIGINAL chart derives etaleness of its actual native twist map. -/
theorem chartTwistMap_etale : (chartTwistMap (k := k) v p).hom.Etale :=
  twistOver_etale (algebraMap k P) (algebraMap k B) (MvPolynomial.aeval v).toRingHom
    (chart_comp v) p hv

include hv in
/-- The actual ORIGINAL relative Frobenius chart square is a genuine native pushout. -/
theorem chartSquare : IsPushout (RelativeFrobenius.map (algebraMap k P) p) (chartTwistMap (k := k) v p)
    (CommRingCat.ofHom (MvPolynomial.aeval v).toRingHom) (RelativeFrobenius.map (algebraMap k B) p) :=
  twistOver_square (algebraMap k P) (algebraMap k B) (MvPolynomial.aeval v).toRingHom
    (chart_comp v) p hv

/-- Native extension of EVERY original relative form module is the SAME native etale form module. -/
def formIso (q : ℕ) :
    (ModuleCat.extendScalars (chartTwistMap (k := k) v p).hom).obj
      (RelativeEtaleDeRham.formModule (R := k) (B := P) p q) ≅
      RelativeEtaleDeRham.formModule (R := k) (B := B) p q :=
  RingPushoutScalarExchange.moduleIso (RelativeFrobenius.map (algebraMap k P) p)
    (chartTwistMap (k := k) v p) (CommRingCat.ofHom (MvPolynomial.aeval v).toRingHom)
    (RelativeFrobenius.map (algebraMap k B) p) (chartSquare v hv p)
    (ModuleCat.of P (⋀[P]^q (KaehlerDifferential k P))) ≪≫
      (ModuleCat.restrictScalars (RelativeFrobenius.map (algebraMap k B) p).hom).mapIso
        (EtaleExteriorBaseChange.exteriorIso v hv q)

/-- Every original pure tensor maps to the SAME pulled form with its actual relative coefficient. -/
theorem formIso_tmul (q : ℕ) (t : TB) (w : ⋀[P]^q (KaehlerDifferential k P)) :
    let _ := (chartTwistMap (k := k) v p).hom.toAlgebra
    (formIso v hv p q).hom (t ⊗ₜ[TP]
      (show RelativeEtaleDeRham.formModule (R := k) (B := P) p q from w)) =
        (show RelativeEtaleDeRham.formModule (R := k) (B := B) p q from
          (RelativeFrobenius.map (algebraMap k B) p).hom t • EtaleDeRham.polynomialFormMap v hv q w) := by
  let := (chartTwistMap (k := k) v p).hom.toAlgebra
  let := (MvPolynomial.aeval (R := k) v).toAlgebra
  change (EtaleExteriorBaseChange.exteriorIso v hv q).hom
    ((RingPushoutScalarExchange.moduleIso (RelativeFrobenius.map (algebraMap k P) p)
      (chartTwistMap (k := k) v p) (CommRingCat.ofHom (MvPolynomial.aeval v).toRingHom)
      (RelativeFrobenius.map (algebraMap k B) p) (chartSquare v hv p)
      (ModuleCat.of P (⋀[P]^q (KaehlerDifferential k P)))).hom
        (t ⊗ₜ[TP] (show RelativeEtaleDeRham.formModule (R := k) (B := P) p q from w))) = _
  exact (congrArg (fun z => (EtaleExteriorBaseChange.exteriorIso v hv q).hom z)
    (RingPushoutScalarExchange.moduleIso_tmul (RelativeFrobenius.map (algebraMap k P) p)
      (chartTwistMap (k := k) v p) (CommRingCat.ofHom (MvPolynomial.aeval v).toRingHom)
      (RelativeFrobenius.map (algebraMap k B) p) (chartSquare v hv p)
      (ModuleCat.of P (⋀[P]^q (KaehlerDifferential k P))) t w)).trans
    (EtaleExteriorBaseChange.exteriorIso_tmul v hv q
      ((RelativeFrobenius.map (algebraMap k B) p).hom t) w)

/-- Coefficient-one tensors give precisely EVERY original pulled polynomial form. -/
theorem formIso_one_tmul (q : ℕ) (w : ⋀[P]^q (KaehlerDifferential k P)) :
    let _ := (chartTwistMap (k := k) v p).hom.toAlgebra
    (formIso v hv p q).hom ((1 : TB) ⊗ₜ[TP]
      (show RelativeEtaleDeRham.formModule (R := k) (B := P) p q from w)) =
        (show RelativeEtaleDeRham.formModule (R := k) (B := B) p q from
          EtaleDeRham.polynomialFormMap v hv q w) := by
  simpa only [map_one, one_smul] using formIso_tmul v hv p q (1 : TB) w

/-- EVERY original base coefficient acts by its SAME original value on the whole pulled form. -/
theorem formIso_coefficient (q : ℕ) (a : k) (w : ⋀[P]^q (KaehlerDifferential k P)) :
    let _ := (chartTwistMap (k := k) v p).hom.toAlgebra
    (formIso v hv p q).hom
      ((RelativeFrobenius.coefficientMap (algebraMap k B) p).hom a ⊗ₜ[TP]
        (show RelativeEtaleDeRham.formModule (R := k) (B := P) p q from w)) =
      (show RelativeEtaleDeRham.formModule (R := k) (B := B) p q from
        (algebraMap k B a) • EtaleDeRham.polynomialFormMap v hv q w) := by
  rw [formIso_tmul]
  have h := congrArg (fun h : CommRingCat.of k ⟶ CommRingCat.of B => h.hom a)
    (RelativeFrobenius.coefficientMap_map (algebraMap k B) p)
  exact congrArg (fun b => b • EtaleDeRham.polynomialFormMap v hv q w) h

private theorem scalarDifferential_comm {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) {M M' : ModuleCat A} {N N' : ModuleCat B}
    (e : (ModuleCat.extendScalars f).obj M ≅ N)
    (e' : (ModuleCat.extendScalars f).obj M' ≅ N') (a : M ⟶ M') (b : N ⟶ N')
    (h : let _ := f.toAlgebra
      ∀ m : M, b (e.hom ((1 : B) ⊗ₜ[A] m)) = e'.hom ((1 : B) ⊗ₜ[A] (a m))) :
    e.hom ≫ b = (ModuleCat.extendScalars f).map a ≫ e'.hom := by
  let := f.toAlgebra
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  exact h m

private theorem originalDifferential_comm (q : ℕ)
    (e : (ModuleCat.extendScalars (chartTwistMap (k := k) v p).hom).obj
      (RelativeEtaleDeRham.formModule (R := k) (B := P) p q) ≅
      RelativeEtaleDeRham.formModule (R := k) (B := B) p q)
    (e' : (ModuleCat.extendScalars (chartTwistMap (k := k) v p).hom).obj
      (RelativeEtaleDeRham.formModule (R := k) (B := P) p (q+1)) ≅
      RelativeEtaleDeRham.formModule (R := k) (B := B) p (q+1))
    (h : let _ := (chartTwistMap (k := k) v p).hom.toAlgebra
      ∀ w : ⋀[P]^q (KaehlerDifferential k P),
        EtaleDeRham.differential v hv q (e.hom ((1 : TB) ⊗ₜ[TP]
          (show RelativeEtaleDeRham.formModule (R := k) (B := P) p q from w))) =
        e'.hom ((1 : TB) ⊗ₜ[TP]
          (show RelativeEtaleDeRham.formModule (R := k) (B := P) p (q+1) from
            EtaleDeRham.differential (MvPolynomial.X : Fin n → P)
              (RelativePolynomialCartier.polynomialEtale k n) q w))) :
    e.hom ≫ RelativeEtaleDeRham.differential v hv p q =
      (ModuleCat.extendScalars (chartTwistMap (k := k) v p).hom).map
        (RelativeEtaleDeRham.differential (MvPolynomial.X : Fin n → P)
          (RelativePolynomialCartier.polynomialEtale k n) p q) ≫ e'.hom := by
  apply scalarDifferential_comm (chartTwistMap (k := k) v p).hom e e'
    (RelativeEtaleDeRham.differential (MvPolynomial.X : Fin n → P)
      (RelativePolynomialCartier.polynomialEtale k n) p q)
    (RelativeEtaleDeRham.differential v hv p q)
  intro _ w
  exact h w

/-- EVERY original coefficient-one tensor has the SAME actual original differential value. -/
theorem formIso_differential_one_tmul (q : ℕ) (w : ⋀[P]^q (KaehlerDifferential k P)) :
    let _ := (chartTwistMap (k := k) v p).hom.toAlgebra
    EtaleDeRham.differential v hv q ((formIso v hv p q).hom ((1 : TB) ⊗ₜ[TP]
      (show RelativeEtaleDeRham.formModule (R := k) (B := P) p q from w))) =
    (formIso v hv p (q+1)).hom ((1 : TB) ⊗ₜ[TP]
      (show RelativeEtaleDeRham.formModule (R := k) (B := P) p (q+1) from
        EtaleDeRham.differential (MvPolynomial.X : Fin n → P)
          (RelativePolynomialCartier.polynomialEtale k n) q w)) := by
  have hq := formIso_one_tmul v hv p q w
  have hr := formIso_one_tmul v hv p (q+1)
    (EtaleDeRham.differential (MvPolynomial.X : Fin n → P)
      (RelativePolynomialCartier.polynomialEtale k n) q w)
  have hm := (EtaleDeRham.differential_polynomialFormMap v hv q w).trans
    (congrArg (EtaleDeRham.polynomialFormMap v hv (q+1))
      (RelativePolynomialCartier.differential_polynomial k n q w).symm)
  exact (congrArg (EtaleDeRham.differential v hv q) hq).trans (hm.trans hr.symm)

/-- Native relative scalar extension commutes with the ENTIRE original de Rham differential. -/
theorem formIso_comm (q : ℕ) :
    (formIso v hv p q).hom ≫ RelativeEtaleDeRham.differential v hv p q =
      (ModuleCat.extendScalars (chartTwistMap (k := k) v p).hom).map
        (RelativeEtaleDeRham.differential (MvPolynomial.X : Fin n → P)
          (RelativePolynomialCartier.polynomialEtale k n) p q) ≫ (formIso v hv p (q+1)).hom := by
  apply originalDifferential_comm v hv p q (formIso v hv p q) (formIso v hv p (q+1))
  exact formIso_differential_one_tmul v hv p q

/-- Actual scalar extension of the SAME native relative polynomial de Rham complex. -/
def extendedComplex : CochainComplex (ModuleCat TB) ℕ :=
  ((ModuleCat.extendScalars (chartTwistMap (k := k) v p).hom).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj KP

/-- The WHOLE actual native relative polynomial and etale complexes genuinely base change. -/
def complexIso : extendedComplex v p ≅ RelativeEtaleDeRham.complex v hv p := by
  refine HomologicalComplex.Hom.isoOfComponents (fun q => formIso v hv p q) ?_
  intro q r h
  have hr : q+1 = r := h
  subst r
  simp only [RelativeEtaleDeRham.complex, extendedComplex, Functor.mapHomologicalComplex_obj_d,
    CochainComplex.of_d]
  exact formIso_comm v hv p q

private def flatHomologyIso {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : f.Flat) (C : CochainComplex (ModuleCat.{u} A) ℕ) (q : ℕ) :
    (((ModuleCat.extendScalars f).mapHomologicalComplex (ComplexShape.up ℕ)).obj C).homology q ≅
      (ModuleCat.extendScalars f).obj (C.homology q) := by
  let : PreservesFiniteLimits (ModuleCat.extendScalars.{u} f) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  exact (C.sc q).mapHomologyIso (ModuleCat.extendScalars f)

/-- Every native etale cohomology degree is the actual flat extension of native polynomial Hq. -/
def homologyIso (q : ℕ) : (RelativeEtaleDeRham.complex v hv p).homology q ≅
    (ModuleCat.extendScalars (chartTwistMap (k := k) v p).hom).obj ((KP).homology q) :=
  ((HomologicalComplex.homologyFunctor (ModuleCat TB) (ComplexShape.up ℕ) q).mapIso
    (complexIso v hv p)).symm ≪≫
      flatHomologyIso (chartTwistMap (k := k) v p).hom
        (RingHom.Etale.iff_flat_and_formallyUnramified.mp (chartTwistMap_etale v hv p)).1 KP q

end EnvelopeProperty.Cartier.RelativeEtaleComplexBaseChange
