import EnvelopeProperty.Cartier.IntrinsicCartierOne
import EnvelopeProperty.Cartier.EtaleDifferentialNaturality
import EnvelopeProperty.Algebra.ModuleHomologyScalarRestriction

/-! # Actual canonical one-form Cartier naturality for arbitrary original coefficient maps -/
noncomputable section
namespace EnvelopeProperty.Cartier.IntrinsicCartierOneNaturality
open CategoryTheory
open IntrinsicCartierOne
universe u

private theorem actualClass_map {A : Type u} [CommRing A]
    {S T : ShortComplex (ModuleCat A)} (φ : S ⟶ T)
    (z : LinearMap.ker S.g.hom) (w : LinearMap.ker T.g.hom)
    (hzw : φ.τ₂ z.val = w.val) :
    ShortComplex.homologyMap φ (S.homologyπ (S.moduleCatCyclesIso.inv z)) =
      T.homologyπ (T.moduleCatCyclesIso.inv w) := by
  have hc : ShortComplex.cyclesMap φ (S.moduleCatCyclesIso.inv z) =
      T.moduleCatCyclesIso.inv w := by
    apply (ModuleCat.mono_iff_injective T.iCycles).mp inferInstance
    have h := congrArg (fun F : S.cycles ⟶ T.X₂ => F (S.moduleCatCyclesIso.inv z))
      (ShortComplex.cyclesMap_i φ)
    change T.iCycles (ShortComplex.cyclesMap φ (S.moduleCatCyclesIso.inv z)) =
      φ.τ₂ (S.iCycles (S.moduleCatCyclesIso.inv z)) at h
    exact h.trans ((congrArg φ.τ₂ (S.moduleCatCyclesIso_inv_iCycles_apply z)).trans
      (hzw.trans (T.moduleCatCyclesIso_inv_iCycles_apply w).symm))
  have h := congrArg (fun F : S.cycles ⟶ T.homology => F (S.moduleCatCyclesIso.inv z))
    (ShortComplex.homologyπ_naturality φ)
  change ShortComplex.homologyMap φ (S.homologyπ (S.moduleCatCyclesIso.inv z)) =
    T.homologyπ (ShortComplex.cyclesMap φ (S.moduleCatCyclesIso.inv z)) at h
  exact h.trans (congrArg T.homologyπ hc)


variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
variable {n m : ℕ} (v : Fin n → A) (hv : (MvPolynomial.aeval (R := R) v).toRingHom.Etale)
variable (w : Fin m → B) (hw : (MvPolynomial.aeval (R := R) w).toRingHom.Etale)
variable (p : ℕ) [Fact p.Prime] [CharP A p] [CharP B p]

/-- The SAME original native canonical maps give the ACTUAL short-complex morphism for
ANY actual coefficient map A->B; no etaleness or flatness of that map is assumed. -/
def shortComplexMap : shortComplex v hv p ⟶
    (shortComplex w hw p).map (ModuleCat.restrictScalars (algebraMap A B)) where
  τ₁ := EtaleDifferentialNaturality.frobeniusFormMap (R := R) p 0
  τ₂ := EtaleDifferentialNaturality.frobeniusFormMap (R := R) p 1
  τ₃ := EtaleDifferentialNaturality.frobeniusFormMap (R := R) p 2
  comm₁₂ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact EtaleDifferentialNaturality.differential_canonicalMap v hv w hw 0 a
  comm₂₃ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact EtaleDifferentialNaturality.differential_canonicalMap v hv w hw 1 a

/-- The WHOLE genuine native cohomology map, with actual scalar-restriction preservation. -/
def homologyMap : (shortComplex v hv p).homology ⟶
    (ModuleCat.restrictScalars (algebraMap A B)).obj (shortComplex w hw p).homology :=
  ShortComplex.homologyMap (shortComplexMap v hv w hw p) ≫
    (ModuleHomologyScalarRestriction.homologyIso (algebraMap A B) (shortComplex w hw p)).hom

/-- EVERY actual original cycle class is carried by the SAME native canonical map on the
ENTIRE original one-form, without a cohomology-comparison premise. -/
theorem cycleClass_map (z : LinearMap.ker (shortComplex v hv p).g.hom)
    (z' : LinearMap.ker (shortComplex w hw p).g.hom)
    (hz : Char0.canonicalDifferentialLinearMap (k := R) (R := A) (A := B) 1 z.val = z'.val) :
    homologyMap v hv w hw p (cycleClass v hv p z) = cycleClass w hw p z' := by
  let F := ModuleCat.restrictScalars (algebraMap A B)
  let t : LinearMap.ker ((shortComplex w hw p).map F).g.hom := ⟨z'.val, z'.property⟩
  have ht : (shortComplexMap v hv w hw p).τ₂ z.val = t.val := hz
  have h := actualClass_map (shortComplexMap v hv w hw p) z t ht
  have h' := congrArg
    (ModuleHomologyScalarRestriction.homologyIso (algebraMap A B) (shortComplex w hw p)).hom h
  rw [cycleClass_eq, cycleClass_eq]
  exact h'.trans (ModuleHomologyScalarRestriction.cycleClass_comparison
    (algebraMap A B) (shortComplex w hw p) t z' rfl)

private theorem canonicalMap_one_D (a : A) :
    Char0.canonicalDifferentialLinearMap (k := R) (R := A) (A := B) 1
      ((exteriorPower.oneEquiv A (KaehlerDifferential R A)).symm (KaehlerDifferential.D R A a)) =
      (exteriorPower.oneEquiv B (KaehlerDifferential R B)).symm
        (KaehlerDifferential.D R B (algebraMap A B a)) := by
  have h : (exteriorPower.oneEquiv A (KaehlerDifferential R A)).symm
      (KaehlerDifferential.D R A a) = exteriorPower.ιMulti A 1
        (fun _ => KaehlerDifferential.D R A a) := by
    apply (exteriorPower.oneEquiv A (KaehlerDifferential R A)).injective
    rw [LinearEquiv.apply_symm_apply, exteriorPower.oneEquiv_ιMulti]
  rw [h, Char0.canonicalDifferentialLinearMap_wedge]
  apply (exteriorPower.oneEquiv B (KaehlerDifferential R B)).injective
  rw [exteriorPower.oneEquiv_ιMulti, LinearEquiv.apply_symm_apply, KaehlerDifferential.map_D]

omit [Fact p.Prime] [CharP A p] [CharP B p] in
/-- The actual original generator ONE-FORMS retain the SAME original coefficient map. -/
theorem generatorForm_map (a : A) :
    Char0.canonicalDifferentialLinearMap (k := R) (R := A) (A := B) 1
      (generatorForm (R := R) p a) = generatorForm (R := R) p (algebraMap A B a) := by
  rw [generatorForm, map_smul, canonicalMap_one_D, ← IsScalarTower.algebraMap_smul B,
    map_pow]
  rfl

/-- EVERY original Cartier function class is natural for the ACTUAL coefficient map. -/
theorem generatorClass_map (a : A) :
    homologyMap v hv w hw p (generatorClass v hv p a) =
      generatorClass w hw p (algebraMap A B a) :=
  cycleClass_map v hv w hw p (generatorCycle v hv p a)
    (generatorCycle w hw p (algebraMap A B a)) (generatorForm_map p a)

/-- The SAME original native Kaehler map, genuinely linear into native scalar restriction. -/
def cotangentMap : ModuleCat.of A (KaehlerDifferential R A) ⟶
    (ModuleCat.restrictScalars (algebraMap A B)).obj
      (ModuleCat.of B (KaehlerDifferential R B)) :=
  ModuleCat.ofHom (X := ModuleCat.of A (KaehlerDifferential R A))
    (Y := (ModuleCat.restrictScalars (algebraMap A B)).obj
      (ModuleCat.of B (KaehlerDifferential R B)))
    { toFun := fun z => KaehlerDifferential.map R R A B z
      map_add' := (KaehlerDifferential.map R R A B).map_add
      map_smul' := fun a z => ((KaehlerDifferential.map R R A B).map_smul a z).trans
        (IsScalarTower.algebraMap_smul B a _).symm }

/-- The WHOLE actual inverse Cartier one-form map commutes with EVERY original coefficient
map between the original etale algebras, with no comparison/naturality certificate. -/
theorem inverseCartier_naturality :
    ModuleCat.ofHom (inverseCartier v hv p) ≫ homologyMap v hv w hw p =
      cotangentMap (R := R) (A := A) (B := B) ≫
        (ModuleCat.restrictScalars (algebraMap A B)).map (ModuleCat.ofHom (inverseCartier w hw p)) := by
  let T := (ModuleCat.restrictScalars (algebraMap A B)).obj (shortComplex w hw p).homology
  let : Module R T := Module.compHom T (algebraMap R A)
  let : IsScalarTower R A T := IsScalarTower.of_compHom R A T
  apply ModuleCat.hom_ext
  apply Derivation.liftKaehlerDifferential_unique
  apply Derivation.ext
  intro a
  change homologyMap v hv w hw p (inverseCartier v hv p (KaehlerDifferential.D R A a)) =
    inverseCartier w hw p (KaehlerDifferential.map R R A B (KaehlerDifferential.D R A a))
  rw [inverseCartier_D, KaehlerDifferential.map_D, inverseCartier_D]
  exact generatorClass_map v hv w hw p a

end EnvelopeProperty.Cartier.IntrinsicCartierOneNaturality
