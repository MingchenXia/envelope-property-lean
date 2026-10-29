import EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationCartierComparison
import Mathlib.Algebra.Homology.Single
import Mathlib.Algebra.Homology.Homotopy

/-! # Actual native degree-one local DI cochain maps and homotopies -/

noncomputable section
namespace EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationNativeHomotopy

open CategoryTheory Category Limits FrobeniusLiftDifference
open scoped Classical

universe u
variable {K B : Type u} [CommRing K] [CommRing B] [Algebra K B]
  {p : ℕ} [Fact p.Prime] [CharP K p] [CharP B p]

attribute [local instance] DeligneIllusieLocalContinuationDividedFrobenius.coefficientAlgebra

/-- The actual cotangent module over the original coefficient algebra on the actual twist. -/
abbrev sourceModule : ModuleCat (RelativeFrobenius.twist (algebraMap K B) p) :=
  ModuleCat.of (RelativeFrobenius.twist (algebraMap K B) p)
    (KaehlerDifferential K (RelativeFrobenius.twist (algebraMap K B) p))

/-- The genuine local DI one-form summand, concentrated in degree ONE. -/
def sourceComplex : CochainComplex (ModuleCat (RelativeFrobenius.twist (algebraMap K B) p)) ℕ :=
  (HomologicalComplex.single (ModuleCat (RelativeFrobenius.twist (algebraMap K B) p))
    (ComplexShape.up ℕ) 1).obj (sourceModule (K := K) (B := B) (p := p))

omit [CharP B p] in
private theorem source_d (i j : ℕ) : (sourceComplex (K := K) (B := B) (p := p)).d i j = 0 := rfl

private theorem complex_d {m : ℕ} (w : Fin m → B)
    (hw : (MvPolynomial.aeval (R := K) w).toRingHom.Etale) (j : ℕ) :
    (RelativeEtaleDeRham.complex w hw p).d j (j+1) = RelativeEtaleDeRham.differential w hw p j :=
  CochainComplex.of_d _ _ j

variable {C S R : Type u} [CommRing C] [CommRing S] [CommRing R]
  [Algebra C K] [Algebra C S] [Algebra S B] [Algebra C B]
  [IsScalarTower C S B] [IsScalarTower C K B] [SMulCommClass K S B]
  [Algebra.FormallySmooth C S]
  {n m : ℕ} (v : Fin n → S) (hv : (MvPolynomial.aeval (R := C) v).toRingHom.Etale)
  (w : Fin m → B) (hw : (MvPolynomial.aeval (R := K) w).toRingHom.Etale)
  (c : Reduction p C K) (a : Reduction p R (RelativeFrobenius.twist (algebraMap K B) p))
  (b : FlatReduction p S B) (hc : algebraMap C K = c.map) (hb : algebraMap S B = b.map)
  (f g : R →+* S)
  (hf : ∀ r, b.map (f r) = (RelativeFrobenius.map (algebraMap K B) p).hom (a.map r))
  (hg : ∀ r, b.map (g r) = (RelativeFrobenius.map (algebraMap K B) p).hom (a.map r))
  (ι : C →+* R)
  (hι : ∀ r, a.map (ι r) = algebraMap K (RelativeFrobenius.twist (algebraMap K B) p) (c.map r))
  (hbasef : ∀ r, f (ι r) = algebraMap C S r)
  (hbaseg : ∀ r, g (ι r) = algebraMap C S r)

/-- Actual geometric closedness constructs a genuine native cochain map from the DI one-form summand. -/
def cochainMap : sourceComplex (K := K) (B := B) (p := p) ⟶ RelativeEtaleDeRham.complex w hw p :=
  HomologicalComplex.mkHomFromSingle
    (K := RelativeEtaleDeRham.complex w hw p) (j := 1)
    (A := sourceModule (K := K) (B := B) (p := p))
    (ModuleCat.ofHom (X := sourceModule (K := K) (B := B) (p := p))
      (Y := RelativeEtaleDeRham.formModule (R := K) (B := B) p 1)
      (DeligneIllusieLocalContinuationClosedness.oneFormMap c a b hc hb f hf ι hι hbasef))
    (fun j hj => by
      have hj' : 1+1 = j := hj
      subst j
      rw [complex_d w hw 1]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro ω
      change EtaleDeRham.differential w hw 1
        ((exteriorPower.oneEquiv B (KaehlerDifferential K B)).symm
          (DeligneIllusieLocalContinuationDividedFrobenius.cotangentMap c a b hc hb f hf ι hι hbasef ω)) = 0
      exact DeligneIllusieLocalContinuationClosedness.cotangentMap_closed v hv w hw c a b hc hb f hf ι hι hbasef ω)

/-- Its entire degree-one component is the SAME actual one-form map under the canonical source identity. -/
theorem cochainMap_f_one : (cochainMap v hv w hw c a b hc hb f hf ι hι hbasef).f 1 =
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 1 (sourceModule (K := K) (B := B) (p := p))).hom ≫
      ModuleCat.ofHom (X := sourceModule (K := K) (B := B) (p := p))
      (Y := RelativeEtaleDeRham.formModule (R := K) (B := B) p 1)
      (DeligneIllusieLocalContinuationClosedness.oneFormMap c a b hc hb f hf ι hι hbasef) := by
  unfold cochainMap
  exact HomologicalComplex.mkHomFromSingle_f _ _

/-- The actual divided-difference cotangent map in native degree ZERO, with its original restricted action. -/
def zeroFormHomotopy :
    KaehlerDifferential K (RelativeFrobenius.twist (algebraMap K B) p) →ₗ[RelativeFrobenius.twist (algebraMap K B) p]
      RelativeEtaleDeRham.formModule (R := K) (B := B) p 0 := by
  let : Module (RelativeFrobenius.twist (algebraMap K B) p) B :=
    Module.compHom B (RelativeFrobenius.map (algebraMap K B) p).hom
  let H := DeligneIllusieLocalContinuationOneFormHomotopy.homotopyTerm c a b f g hf hg ι hι hbasef hbaseg
  exact
    { toFun := fun ω => (exteriorPower.zeroEquiv B (KaehlerDifferential K B)).symm (H ω)
      map_add' := fun η ζ => by rw [map_add, map_add]; rfl
      map_smul' := fun t η => by
        change (exteriorPower.zeroEquiv B (KaehlerDifferential K B)).symm (H (t • η)) =
          (RelativeFrobenius.map (algebraMap K B) p).hom t •
            (exteriorPower.zeroEquiv B (KaehlerDifferential K B)).symm (H η)
        rw [map_smul]
        exact map_smul (exteriorPower.zeroEquiv B (KaehlerDifferential K B)).symm _ _ }

omit [Algebra C K] [Algebra S B] [Algebra C B]
  [IsScalarTower C S B] [IsScalarTower C K B] [SMulCommClass K S B] [Algebra.FormallySmooth C S] in
/-- EVERY original native zero-form homotopy value is the original divided ring-difference value. -/
theorem zeroFormHomotopy_apply (ω : KaehlerDifferential K (RelativeFrobenius.twist (algebraMap K B) p)) :
    letI : Module (RelativeFrobenius.twist (algebraMap K B) p) B :=
      Module.compHom B (RelativeFrobenius.map (algebraMap K B) p).hom
    zeroFormHomotopy c a b f g hf hg ι hι hbasef hbaseg ω =
      (exteriorPower.zeroEquiv B (KaehlerDifferential K B)).symm
        (DeligneIllusieLocalContinuationOneFormHomotopy.homotopyTerm c a b f g hf hg ι hι hbasef hbaseg ω) := rfl

/-- The ENTIRE same native one-form maps differ by the ACTUAL native degree-zero differential. -/
theorem oneFormMap_sub :
    DeligneIllusieLocalContinuationClosedness.oneFormMap c a b hc hb f hf ι hι hbasef -
        DeligneIllusieLocalContinuationClosedness.oneFormMap c a b hc hb g hg ι hι hbaseg =
      (RelativeEtaleDeRham.differential w hw p 0).hom.comp
        (zeroFormHomotopy c a b f g hf hg ι hι hbasef hbaseg) := by
  let : Module (RelativeFrobenius.twist (algebraMap K B) p) B :=
    Module.compHom B (RelativeFrobenius.map (algebraMap K B) p).hom
  let : Module (RelativeFrobenius.twist (algebraMap K B) p) (KaehlerDifferential K B) :=
    Module.compHom _ (RelativeFrobenius.map (algebraMap K B) p).hom
  apply LinearMap.ext
  intro ω
  apply (exteriorPower.oneEquiv B (KaehlerDifferential K B)).injective
  have h := congrArg (fun L :
      KaehlerDifferential K (RelativeFrobenius.twist (algebraMap K B) p) →ₗ[RelativeFrobenius.twist (algebraMap K B) p]
        KaehlerDifferential K B => L ω)
    (DeligneIllusieLocalContinuationOneFormHomotopy.cotangentMap_sub c a b hc hb f g hf hg ι hι hbasef hbaseg)
  simp only [LinearMap.sub_apply, LinearMap.comp_apply,
    DeligneIllusieLocalContinuationOneFormHomotopy.relativeDifferential_apply] at h
  rw [LinearMap.sub_apply, LinearMap.comp_apply,
    DeligneIllusieLocalContinuationClosedness.oneFormMap_apply,
    DeligneIllusieLocalContinuationClosedness.oneFormMap_apply, zeroFormHomotopy_apply,
    DeligneIllusieLocalContinuationCartierComparison.native_differential_zero]
  let Xf := DeligneIllusieLocalContinuationDividedFrobenius.cotangentMap c a b hc hb f hf ι hι hbasef
  let Xg := DeligneIllusieLocalContinuationDividedFrobenius.cotangentMap c a b hc hb g hg ι hι hbaseg
  let H := DeligneIllusieLocalContinuationOneFormHomotopy.homotopyTerm c a b f g hf hg ι hι hbasef hbaseg
  change (exteriorPower.oneEquiv B (KaehlerDifferential K B))
      (((exteriorPower.oneEquiv B (KaehlerDifferential K B)).symm (Xf ω) -
        (exteriorPower.oneEquiv B (KaehlerDifferential K B)).symm (Xg ω)) : ⋀[B]^1 (KaehlerDifferential K B)) =
    (exteriorPower.oneEquiv B (KaehlerDifferential K B))
      ((exteriorPower.oneEquiv B (KaehlerDifferential K B)).symm (KaehlerDifferential.D K B (H ω)))
  simpa only [map_sub, LinearEquiv.apply_symm_apply] using h

private def homotopyFamily (i j : ℕ) (h : (ComplexShape.up ℕ).Rel j i) :
    (sourceComplex (K := K) (B := B) (p := p)).X i ⟶ (RelativeEtaleDeRham.complex w hw p).X j :=
  if hi : i = 1 then
    (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℕ) 1
      (sourceModule (K := K) (B := B) (p := p)) i hi).hom ≫
      ModuleCat.ofHom (X := sourceModule (K := K) (B := B) (p := p))
      (Y := RelativeEtaleDeRham.formModule (R := K) (B := B) p 0)
      (zeroFormHomotopy c a b f g hf hg ι hι hbasef hbaseg) ≫
        ((RelativeEtaleDeRham.complex w hw p).XIsoOfEq (show j = 0 by change j+1 = i at h; omega)).inv
  else 0

omit [Algebra C K] [Algebra S B] [Algebra C B]
  [IsScalarTower C S B] [IsScalarTower C K B] [SMulCommClass K S B] [Algebra.FormallySmooth C S] in
private theorem homotopyFamily_one_zero (h : (ComplexShape.up ℕ).Rel 0 1) :
    homotopyFamily w hw c a b f g hf hg ι hι hbasef hbaseg 1 0 h =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 1 (sourceModule (K := K) (B := B) (p := p))).hom ≫
        ModuleCat.ofHom (X := sourceModule (K := K) (B := B) (p := p))
      (Y := RelativeEtaleDeRham.formModule (R := K) (B := B) p 0)
      (zeroFormHomotopy c a b f g hf hg ι hι hbasef hbaseg) := by
  simp only [homotopyFamily, dif_pos rfl, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv,
    HomologicalComplex.singleObjXSelf]
  let e := HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 1
    (sourceModule (K := K) (B := B) (p := p))
  let H0 : sourceModule (K := K) (B := B) (p := p) ⟶
      RelativeEtaleDeRham.formModule (R := K) (B := B) p 0 :=
    ModuleCat.ofHom (X := sourceModule (K := K) (B := B) (p := p))
      (Y := RelativeEtaleDeRham.formModule (R := K) (B := B) p 0)
      (zeroFormHomotopy c a b f g hf hg ι hι hbasef hbaseg)
  change e.hom ≫ H0 ≫ 𝟙 (RelativeEtaleDeRham.formModule (R := K) (B := B) p 0) = e.hom ≫ H0
  exact congrArg (fun α : sourceModule (K := K) (B := B) (p := p) ⟶
    RelativeEtaleDeRham.formModule (R := K) (B := B) p 0 => e.hom ≫ α) (Category.comp_id H0)

private theorem cochain_sub_eq_null :
    cochainMap v hv w hw c a b hc hb f hf ι hι hbasef - cochainMap v hv w hw c a b hc hb g hg ι hι hbaseg =
      Homotopy.nullHomotopicMap' (homotopyFamily w hw c a b f g hf hg ι hι hbasef hbaseg) := by
  apply HomologicalComplex.from_single_hom_ext
  rw [HomologicalComplex.sub_f_apply, cochainMap_f_one, cochainMap_f_one,
    Homotopy.nullHomotopicMap'_f (show (ComplexShape.up ℕ).Rel 0 1 from rfl)
      (show (ComplexShape.up ℕ).Rel 1 2 from rfl),
    source_d, zero_comp, zero_add, homotopyFamily_one_zero, complex_d w hw 0]
  let e := HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 1
    (sourceModule (K := K) (B := B) (p := p))
  let φf : sourceModule (K := K) (B := B) (p := p) ⟶
      RelativeEtaleDeRham.formModule (R := K) (B := B) p 1 :=
    ModuleCat.ofHom (X := sourceModule (K := K) (B := B) (p := p))
      (Y := RelativeEtaleDeRham.formModule (R := K) (B := B) p 1)
      (DeligneIllusieLocalContinuationClosedness.oneFormMap c a b hc hb f hf ι hι hbasef)
  let φg : sourceModule (K := K) (B := B) (p := p) ⟶
      RelativeEtaleDeRham.formModule (R := K) (B := B) p 1 :=
    ModuleCat.ofHom (X := sourceModule (K := K) (B := B) (p := p))
      (Y := RelativeEtaleDeRham.formModule (R := K) (B := B) p 1)
      (DeligneIllusieLocalContinuationClosedness.oneFormMap c a b hc hb g hg ι hι hbaseg)
  let H0 : sourceModule (K := K) (B := B) (p := p) ⟶
      RelativeEtaleDeRham.formModule (R := K) (B := B) p 0 :=
    ModuleCat.ofHom (X := sourceModule (K := K) (B := B) (p := p))
      (Y := RelativeEtaleDeRham.formModule (R := K) (B := B) p 0)
      (zeroFormHomotopy c a b f g hf hg ι hι hbasef hbaseg)
  change e.hom ≫ φf - e.hom ≫ φg = (e.hom ≫ H0) ≫ RelativeEtaleDeRham.differential w hw p 0
  have hφ : φf-φg = H0 ≫ RelativeEtaleDeRham.differential w hw p 0 := by
    apply ModuleCat.hom_ext
    exact oneFormMap_sub w hw c a b hc hb f g hf hg ι hι hbasef hbaseg
  calc
    e.hom ≫ φf - e.hom ≫ φg = e.hom ≫ (φf-φg) := (Preadditive.comp_sub e.hom φf φg).symm
    _ = e.hom ≫ (H0 ≫ RelativeEtaleDeRham.differential w hw p 0) :=
      congrArg (fun α : sourceModule (K := K) (B := B) (p := p) ⟶
        RelativeEtaleDeRham.formModule (R := K) (B := B) p 1 => e.hom ≫ α) hφ
    _ = (e.hom ≫ H0) ≫ RelativeEtaleDeRham.differential w hw p 0 := (Category.assoc _ _ _).symm

/-- The ACTUAL native local one-form cochain maps have an actual Mathlib Homotopy, derived internally. -/
def homotopy :
    Homotopy (cochainMap v hv w hw c a b hc hb f hf ι hι hbasef)
      (cochainMap v hv w hw c a b hc hb g hg ι hι hbaseg) :=
  Homotopy.equivSubZero.symm
    ((Homotopy.ofEq (cochain_sub_eq_null v hv w hw c a b hc hb f g hf hg ι hι hbasef hbaseg)).trans
      (Homotopy.nullHomotopy' (homotopyFamily w hw c a b f g hf hg ι hι hbasef hbaseg)))

/-- The native (1,0) homotopy component is the SAME actual original divided-difference term. -/
theorem homotopy_one_zero : (homotopy v hv w hw c a b hc hb f g hf hg ι hι hbasef hbaseg).hom 1 0 =
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 1 (sourceModule (K := K) (B := B) (p := p))).hom ≫
      ModuleCat.ofHom (X := sourceModule (K := K) (B := B) (p := p))
      (Y := RelativeEtaleDeRham.formModule (R := K) (B := B) p 0)
      (zeroFormHomotopy c a b f g hf hg ι hι hbasef hbaseg) := by
  simp [homotopy, Homotopy.equivSubZero, Homotopy.trans, Homotopy.ofEq,
    Homotopy.nullHomotopy', homotopyFamily_one_zero]
  rfl

end EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationNativeHomotopy
