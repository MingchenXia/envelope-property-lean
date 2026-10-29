import EnvelopeProperty.Cartier.SchemeRelativeFrobeniusBasisDifferential
import EnvelopeProperty.Cartier.RelativeCartierContinuationEtaleCartierMultiplicativity
import EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationCechTotalAugmentation
import ModularCurves.EllipticCurve.PoleSheaf
import ModularCurves.ForMathlib.TotalComplexUpNatDecomposition

/-! # Exterior products for the Čech de Rham total complex

The wedge product of the exterior presheaves of a presheaf of modules is transported to the
exterior sheaves through the monoidal structure of sheafification. On sections of the de Rham forms
of the Frobenius twist it gives a bilinear product, and on étale affine opens the differential
satisfies the graded Leibniz rule.
-/

noncomputable section

namespace EnvelopeProperty.Cartier.DeligneIllusieCechCupProduct

open AlgebraicGeometry CategoryTheory Category Limits Opposite MonoidalCategory
open scoped TensorProduct

universe u

variable {X : Scheme.{u}}

noncomputable local instance : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

noncomputable local instance : MonoidalCategory (SheafOfModules X.ringCatSheaf) := by
  change MonoidalCategory X.Modules
  exact Scheme.Modules.monoidalCategory X

local instance (U : X.Opensᵒᵖ) : CommRing (X.ringCatSheaf.obj.obj U) :=
  inferInstanceAs (CommRing (X.presheaf.obj U))

set_option backward.isDefEq.respectTransparency false in
local instance originalPresheafSectionModule (P : X.PresheafOfModules) (U : X.Opensᵒᵖ) :
    Module (X.presheaf.obj U) (P.obj U) := (P.obj U).isModule

set_option backward.isDefEq.respectTransparency false in
local instance originalSheafSectionModule (M : X.Modules) (U : X.Opens) :
    Module Γ(X,U) Γ(M,U) := (M.val.obj (op U)).isModule

set_option backward.isDefEq.respectTransparency false in
local instance originalSheafCommSectionModule (M : X.Modules) (U : X.Opens) :
    Module (X.sheaf.obj.obj (op U)) Γ(M,U) := (M.val.obj (op U)).isModule

set_option backward.isDefEq.respectTransparency false in
local instance sheafificationIsLocalization :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).IsLocalization
      (PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.obj)) := by
  change (PresheafOfModules.sheafification
      (𝟙 (⟨X.sheaf.obj ⋙ forget₂ CommRingCat RingCat,
        X.ringCatSheaf.property⟩ : TopCat.Sheaf RingCat X).obj)).IsLocalization
    (PresheafOfModules.sheafificationW
      (𝟙 (⟨X.sheaf.obj ⋙ forget₂ CommRingCat RingCat,
        X.ringCatSheaf.property⟩ : TopCat.Sheaf RingCat X).obj))
  infer_instance

local instance sheafificationWIsMonoidal :
    (PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.obj)).IsMonoidal := by
  change (PresheafOfModules.sheafificationW
    (𝟙 (⟨X.sheaf.obj ⋙ forget₂ CommRingCat RingCat,
      X.ringCatSheaf.property⟩ : TopCat.Sheaf RingCat X).obj)).IsMonoidal
  infer_instance

noncomputable local instance originalSheafificationMonoidal :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).Monoidal :=
  inferInstanceAs ((Localization.Monoidal.toMonoidalCategory
    (L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
    (W := PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.obj))
    (Iso.refl _)).Monoidal)

/-- The wedge product `⋀^q P ⊗ ⋀^r P ⟶ ⋀^(r+q) P` of exterior presheaves, compatible with the
restriction maps of the coefficient rings. -/
def exteriorPresheafProduct (P : X.PresheafOfModules) (q r : ℕ) :
    CanonicalGeometry.exteriorPresheaf (R := X.presheaf) P q ⊗
        CanonicalGeometry.exteriorPresheaf (R := X.presheaf) P r ⟶
      CanonicalGeometry.exteriorPresheaf (R := X.presheaf) P (r+q) where
  app U := ModuleCat.ofHom (TensorProduct.lift
    (EtaleGradedLeibniz.wedgeProduct (A := X.presheaf.obj U) (M := P.obj U) q r))
  naturality {U V} i := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro a b
    let φ : P.obj U →ₛₗ[(X.presheaf.map i).hom] P.obj V :=
      { toFun := P.map i
        map_add' := (P.map i).hom.map_add
        map_smul' := P.map_smul i }
    change EtaleGradedLeibniz.wedgeProduct q r
        (CanonicalGeometry.exteriorSemilinearMap (X.presheaf.map i).hom φ q a)
        (CanonicalGeometry.exteriorSemilinearMap (X.presheaf.map i).hom φ r b) =
      CanonicalGeometry.exteriorSemilinearMap (X.presheaf.map i).hom φ (r+q)
        (EtaleGradedLeibniz.wedgeProduct q r a b)
    exact (RelativeEtaleCartierMultiplicativity.exteriorSemilinearMap_wedgeProduct
      (X.presheaf.map i).hom φ q r a b).symm

/-- On every open, the product of `a ⊗ b` is the wedge product of `a` and `b`. -/
theorem exteriorPresheafProduct_tmul (P : X.PresheafOfModules) (q r : ℕ)
    (U : X.Opensᵒᵖ)
    (a : (CanonicalGeometry.exteriorPresheaf (R := X.presheaf) P q).obj U)
    (b : (CanonicalGeometry.exteriorPresheaf (R := X.presheaf) P r).obj U) :
    (exteriorPresheafProduct P q r).app U (a ⊗ₜ b) =
      EtaleGradedLeibniz.wedgeProduct q r a b := rfl

/-- The wedge product of exterior sheaves: the sheafification of `exteriorPresheafProduct`,
through the monoidal structure of sheafification. -/
def exteriorSheafProduct (P : X.PresheafOfModules) (q r : ℕ) :
    CanonicalGeometry.exteriorSheaf P q ⊗ CanonicalGeometry.exteriorSheaf P r ⟶
      CanonicalGeometry.exteriorSheaf P (r+q) :=
  Functor.LaxMonoidal.μ (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
      (CanonicalGeometry.exteriorPresheaf (R := X.presheaf) P q)
      (CanonicalGeometry.exteriorPresheaf (R := X.presheaf) P r) ≫
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (exteriorPresheafProduct P q r)

/-- The comultiplication `δ` of sheafification followed by `exteriorSheafProduct` is the
sheafification of the presheaf product. -/
theorem exteriorSheafProduct_cotensorator (P : X.PresheafOfModules) (q r : ℕ) :
    Functor.OplaxMonoidal.δ (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
        (CanonicalGeometry.exteriorPresheaf (R := X.presheaf) P q)
        (CanonicalGeometry.exteriorPresheaf (R := X.presheaf) P r) ≫
      exteriorSheafProduct P q r =
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (exteriorPresheafProduct P q r) := by
  let L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let A := CanonicalGeometry.exteriorPresheaf (R := X.presheaf) P q
  let B := CanonicalGeometry.exteriorPresheaf (R := X.presheaf) P r
  let φ := L.map (exteriorPresheafProduct P q r)
  change Functor.OplaxMonoidal.δ L A B ≫ (Functor.LaxMonoidal.μ L A B ≫ φ) = φ
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ φ) (Functor.Monoidal.δ_μ L A B)).trans (id_comp φ))

/-- `exteriorSheafProduct`, with source the explicit tensor product of sheaves of modules. -/
def exteriorSheafProductExplicit (P : X.PresheafOfModules) (q r : ℕ) :
    CanonicalGeometry.bundleTensor (CanonicalGeometry.exteriorSheaf P q)
        (CanonicalGeometry.exteriorSheaf P r) ⟶
      CanonicalGeometry.exteriorSheaf P (r+q) :=
  (ModularCurves.monoidalTensorObjIso _ _).inv ≫ exteriorSheafProduct P q r

set_option backward.isDefEq.respectTransparency false in
/-- The bilinear wedge product on sections of the exterior sheaves over an open `U`. -/
def exteriorSheafProductSection (P : X.PresheafOfModules) (q r : ℕ) (U : X.Opens) :
    Γ(CanonicalGeometry.exteriorSheaf P q,U) →ₗ[Γ(X,U)]
      Γ(CanonicalGeometry.exteriorSheaf P r,U) →ₗ[Γ(X,U)]
        Γ(CanonicalGeometry.exteriorSheaf P (r+q),U) :=
  (CanonicalGeometry.tensorSectionBilinear
    (CanonicalGeometry.exteriorSheaf P q) (CanonicalGeometry.exteriorSheaf P r) U).compr₂
      ((exteriorSheafProductExplicit P q r).val.app (op U)).hom

set_option backward.isDefEq.respectTransparency false in
/-- On images of presheaf sections under the sheafification unit, the product of sections is the
wedge product; this holds on every open, including the empty one. -/
theorem exteriorSheafProductSection_unit (P : X.PresheafOfModules) (q r : ℕ)
    (U : X.Opens)
    (a : (CanonicalGeometry.exteriorPresheaf (R := X.presheaf) P q).obj (op U))
    (b : (CanonicalGeometry.exteriorPresheaf (R := X.presheaf) P r).obj (op U)) :
    exteriorSheafProductSection P q r U
        ((CanonicalGeometry.exteriorSheafificationMap P q).app (op U) a)
        ((CanonicalGeometry.exteriorSheafificationMap P r).app (op U) b) =
      (CanonicalGeometry.exteriorSheafificationMap P (r+q)).app (op U)
        (EtaleGradedLeibniz.wedgeProduct q r a b) := by
  let L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let η := (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit
  let A := CanonicalGeometry.exteriorPresheaf (R := X.presheaf) P q
  let B := CanonicalGeometry.exteriorPresheaf (R := X.presheaf) P r
  let z := (η.app (A ⊗ B)).app (op U) (a ⊗ₜ b)
  change (exteriorSheafProduct P q r).val.app (op U)
      (ModularCurves.tensorSection (L.obj A) (L.obj B) U
        ((η.app A).app (op U) a) ((η.app B).app (op U) b)) = _
  rw [← ModularCurves.sheafification_δ_unit_tmul_eq_tensorSection A B U a b]
  have h := congrArg (fun g => g.val.app (op U) z)
    (exteriorSheafProduct_cotensorator P q r)
  change (exteriorSheafProduct P q r).val.app (op U)
      ((Functor.OplaxMonoidal.δ L A B).val.app (op U) z) =
        (L.map (exteriorPresheafProduct P q r)).val.app (op U) z at h
  rw [h]
  have hn := congrArg (fun g => g.app (op U) (a ⊗ₜ b))
    (η.naturality (exteriorPresheafProduct P q r))
  change (η.app (CanonicalGeometry.exteriorPresheaf (R := X.presheaf) P (r+q))).app (op U)
      ((exteriorPresheafProduct P q r).app (op U) (a ⊗ₜ b)) =
    (L.map (exteriorPresheafProduct P q r)).val.app (op U) z at hn
  exact hn.symm.trans (congrArg
    (fun c => (η.app (CanonicalGeometry.exteriorPresheaf (R := X.presheaf) P (r+q))).app (op U) c)
    (exteriorPresheafProduct_tmul P q r (op U) a b))

set_option backward.isDefEq.respectTransparency false in
/-- The product of sections commutes with restriction. -/
theorem exteriorSheafProductSection_restrict (P : X.PresheafOfModules) (q r : ℕ)
    {U V : X.Opens} (i : V ⟶ U)
    (a : Γ(CanonicalGeometry.exteriorSheaf P q,U))
    (b : Γ(CanonicalGeometry.exteriorSheaf P r,U)) :
    (CanonicalGeometry.exteriorSheaf P (r+q)).val.map i.op
        (exteriorSheafProductSection P q r U a b) =
      exteriorSheafProductSection P q r V
        ((CanonicalGeometry.exteriorSheaf P q).val.map i.op a)
        ((CanonicalGeometry.exteriorSheaf P r).val.map i.op b) := by
  unfold exteriorSheafProductSection
  change (CanonicalGeometry.exteriorSheaf P (r+q)).val.map i.op
      ((exteriorSheafProductExplicit P q r).val.app (op U)
        (CanonicalGeometry.tensorSection _ _ U a b)) = _
  rw [← PresheafOfModules.naturality_apply, CanonicalGeometry.tensorSection_restrict]
  rfl

section ActualFrobenius

variable {k : Type u} [Field k] (f : X ⟶ Spec (CommRingCat.of k))
  (p : ℕ) [Fact p.Prime] [CharP k p]

local notation "Y" => SchemeRelativeFrobenius.twist p f
local notation "Fr" => SchemeRelativeFrobenius.map p f
local notation "E" q => SchemeRelativeFrobeniusDeRham.formModule f p q

set_option backward.isDefEq.respectTransparency false in
/-- The wedge product of sections of the de Rham forms on the Frobenius twist, bilinear for the
action of the structure ring of the twist through Frobenius. -/
def formWedge (q r : ℕ) (W : (Y).Opens) :
    Γ(E q,W) →ₗ[Γ(Y,W)] Γ(E r,W) →ₗ[Γ(Y,W)] Γ(E (r+q),W) where
  toFun a :=
    { toFun := fun b => exteriorSheafProductSection (CanonicalGeometry.cotangentPresheaf f)
        q r ((Fr) ⁻¹ᵁ W) a b
      map_add' := fun b c => map_add _ b c
      map_smul' := fun c b => by
        change exteriorSheafProductSection (CanonicalGeometry.cotangentPresheaf f)
            q r ((Fr) ⁻¹ᵁ W) a (((Fr).app W).hom c •
              (show Γ(CanonicalGeometry.exteriorCotangentSheaf f r,(Fr) ⁻¹ᵁ W) from b)) =
          ((Fr).app W).hom c • exteriorSheafProductSection
            (CanonicalGeometry.cotangentPresheaf f) q r ((Fr) ⁻¹ᵁ W) a b
        exact map_smul _ _ _ }
  map_add' a b := by
    ext c
    exact LinearMap.congr_fun (map_add
      (exteriorSheafProductSection (CanonicalGeometry.cotangentPresheaf f)
        q r ((Fr) ⁻¹ᵁ W)) a b) c
  map_smul' c a := by
    ext b
    change exteriorSheafProductSection (CanonicalGeometry.cotangentPresheaf f)
        q r ((Fr) ⁻¹ᵁ W) (((Fr).app W).hom c •
          (show Γ(CanonicalGeometry.exteriorCotangentSheaf f q,(Fr) ⁻¹ᵁ W) from a)) b =
      ((Fr).app W).hom c • exteriorSheafProductSection
        (CanonicalGeometry.cotangentPresheaf f) q r ((Fr) ⁻¹ᵁ W) a b
    exact LinearMap.congr_fun (map_smul
      (exteriorSheafProductSection (CanonicalGeometry.cotangentPresheaf f)
        q r ((Fr) ⁻¹ᵁ W)) (((Fr).app W).hom c)
      (show Γ(CanonicalGeometry.exteriorCotangentSheaf f q,(Fr) ⁻¹ᵁ W) from a))
      (show Γ(CanonicalGeometry.exteriorCotangentSheaf f r,(Fr) ⁻¹ᵁ W) from b)

set_option backward.isDefEq.respectTransparency false in
/-- Restriction preserves `formWedge`. -/
theorem formWedge_restrict (q r : ℕ) {V W : (Y).Opens} (i : V ⟶ W)
    (a : Γ(E q,W)) (b : Γ(E r,W)) :
    (E (r+q)).val.map i.op (formWedge f p q r W a b) =
      formWedge f p q r V ((E q).val.map i.op a) ((E r).val.map i.op b) := by
  exact exteriorSheafProductSection_restrict
    (CanonicalGeometry.cotangentPresheaf f) q r
    ((TopologicalSpace.Opens.map (Fr).base).map i) a b

set_option backward.isDefEq.respectTransparency false in
/-- On an étale affine open, `formWedge` of images under `unitEquiv` is the image of the wedge
product of presheaf sections. -/
theorem formWedge_unit (q r : ℕ) (W : (Y).Opens)
    (hV : IsAffineOpen ((Fr) ⁻¹ᵁ W)) {m : ℕ}
    (v : Fin m → Γ(X,(Fr) ⁻¹ᵁ W))
    (hv : letI := CanonicalGeometry.cotangentOpenAlgebra f ((Fr) ⁻¹ᵁ W);
      (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
    (a : (CanonicalGeometry.exteriorCotangentPresheaf f q).obj (op ((Fr) ⁻¹ᵁ W)))
    (b : (CanonicalGeometry.exteriorCotangentPresheaf f r).obj (op ((Fr) ⁻¹ᵁ W))) :
    formWedge f p q r W (EtaleAffineSectionDifferential.unitEquiv f hV v hv q a)
        (EtaleAffineSectionDifferential.unitEquiv f hV v hv r b) =
      EtaleAffineSectionDifferential.unitEquiv f hV v hv (r+q)
        (EtaleGradedLeibniz.wedgeProduct q r a b) :=
  exteriorSheafProductSection_unit (CanonicalGeometry.cotangentPresheaf f) q r
    ((Fr) ⁻¹ᵁ W) a b

end ActualFrobenius

section OriginalExteriorNativeBridge

variable {k : Type u} [Field k] (f : X ⟶ Spec (CommRingCat.of k)) (V : X.Opens)

set_option backward.isDefEq.respectTransparency false in
/-- The exterior powers of the cotangent presheaf over `V` are identified with the exterior powers
of the Kähler differentials of `Γ(X, V)` over `k`. -/
def actualRawExteriorEquiv (q : ℕ) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f V
    (CanonicalGeometry.exteriorCotangentPresheaf f q).obj (op V) ≃ₗ[Γ(X,V)]
      ⋀[Γ(X,V)]^q (KaehlerDifferential k Γ(X,V)) := by
  letI := CanonicalGeometry.cotangentOpenAlgebra f V
  exact CanonicalGeometry.exteriorLinearEquiv
    (CanonicalGeometry.cotangentPresheafSectionsEquiv f V) q

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- `actualRawExteriorEquiv` is the identity on underlying elements. -/
theorem actualRawExteriorEquiv_apply (q : ℕ)
    (a : (CanonicalGeometry.exteriorCotangentPresheaf f q).obj (op V)) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f V
    actualRawExteriorEquiv f V q a =
      (show ⋀[Γ(X,V)]^q (KaehlerDifferential k Γ(X,V)) from a) := by
  let _ := CanonicalGeometry.cotangentOpenAlgebra f V
  change exteriorPower.map q
      (LinearMap.id (R := Γ(X,V)) (M := KaehlerDifferential k Γ(X,V)))
      (show ⋀[Γ(X,V)]^q (KaehlerDifferential k Γ(X,V)) from a) =
    (show ⋀[Γ(X,V)]^q (KaehlerDifferential k Γ(X,V)) from a)

  exact LinearMap.congr_fun
    (exteriorPower.map_id (R := Γ(X,V)) (M := KaehlerDifferential k Γ(X,V)) (n := q))
    (show ⋀[Γ(X,V)]^q (KaehlerDifferential k Γ(X,V)) from a)

private theorem exteriorLinearEquiv_empty {R M N : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) :
    CanonicalGeometry.exteriorLinearEquiv e 0 ((exteriorPower.zeroEquiv R M).symm 1) =
      (exteriorPower.zeroEquiv R N).symm 1 := by
  have h : (exteriorPower.zeroEquiv R M).symm 1 =
      exteriorPower.ιMulti R 0 (fun j => Fin.elim0 j) := by
    apply (exteriorPower.zeroEquiv R M).injective
    rw [LinearEquiv.apply_symm_apply, exteriorPower.zeroEquiv_ιMulti]
  apply (exteriorPower.zeroEquiv R N).injective
  rw [h, CanonicalGeometry.exteriorLinearEquiv_ιMulti,
    exteriorPower.zeroEquiv_ιMulti, LinearEquiv.apply_symm_apply]

private theorem native_empty_closed {K B : Type u} [CommRing K] [CommRing B]
    [Algebra K B] {m : ℕ} (v : Fin m → B) (hv : (MvPolynomial.aeval (R := K) v).Etale) :
    EtaleDeRham.differential v hv 0
      ((exteriorPower.zeroEquiv B (KaehlerDifferential K B)).symm 1) = 0 := by
  apply (exteriorPower.oneEquiv B (KaehlerDifferential K B)).injective
  simpa only [map_zero, Derivation.map_one_eq_zero] using
    EtaleDeRham.differential_zero v hv 1

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- `actualRawExteriorEquiv` carries the raw differential of the presheaf model to the de Rham
differential `EtaleDeRham.differential` of étale coordinates. -/
theorem actualRawExteriorEquiv_rawDifferential {m : ℕ} (v : Fin m → Γ(X,V))
    (hv : letI := CanonicalGeometry.cotangentOpenAlgebra f V;
      (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
    (q : ℕ) (a : (CanonicalGeometry.exteriorCotangentPresheaf f q).obj (op V)) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f V
    actualRawExteriorEquiv f V (q+1) (EtaleAffineSectionDifferential.rawDifferential f v hv q a) =
      EtaleDeRham.differential v hv q (actualRawExteriorEquiv f V q a) := by
  let _ := CanonicalGeometry.cotangentOpenAlgebra f V
  have hl := actualRawExteriorEquiv_apply f V (q+1)
    (EtaleAffineSectionDifferential.rawDifferential f v hv q a)
  have hd :
      (show ⋀[Γ(X,V)]^(q+1) (KaehlerDifferential k Γ(X,V)) from
        EtaleAffineSectionDifferential.rawDifferential f v hv q a) =
      EtaleDeRham.differential v hv q
        (show ⋀[Γ(X,V)]^q (KaehlerDifferential k Γ(X,V)) from a) := rfl
  have hr := congrArg (fun z : ⋀[Γ(X,V)]^q (KaehlerDifferential k Γ(X,V)) =>
    EtaleDeRham.differential v hv q z) (actualRawExteriorEquiv_apply f V q a)
  exact hl.trans (hd.trans hr.symm)

set_option backward.isDefEq.respectTransparency false in
/-- `actualRawExteriorEquiv` sends the unit of the degree-zero exterior power to the unit. -/
theorem actualRawExteriorEquiv_empty :
    letI := CanonicalGeometry.cotangentOpenAlgebra f V
    actualRawExteriorEquiv f V 0
        ((exteriorPower.zeroEquiv Γ(X,V) ((CanonicalGeometry.cotangentPresheaf f).obj (op V))).symm 1) =
      (exteriorPower.zeroEquiv Γ(X,V) (KaehlerDifferential k Γ(X,V))).symm 1 := by
  let _ := CanonicalGeometry.cotangentOpenAlgebra f V
  exact exteriorLinearEquiv_empty (CanonicalGeometry.cotangentPresheafSectionsEquiv f V)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The unit of the degree-zero exterior power is closed for the raw differential. -/
theorem rawDifferential_empty {m : ℕ} (v : Fin m → Γ(X,V))
    (hv : letI := CanonicalGeometry.cotangentOpenAlgebra f V;
      (MvPolynomial.aeval (R := k) v).toRingHom.Etale) :
    EtaleAffineSectionDifferential.rawDifferential f v hv 0
      ((exteriorPower.zeroEquiv Γ(X,V)
        ((CanonicalGeometry.cotangentPresheaf f).obj (op V))).symm 1) = 0 := by
  let _ := CanonicalGeometry.cotangentOpenAlgebra f V
  apply (actualRawExteriorEquiv f V 1).injective
  have hd := actualRawExteriorEquiv_rawDifferential f V v hv 0
    ((exteriorPower.zeroEquiv Γ(X,V)
      ((CanonicalGeometry.cotangentPresheaf f).obj (op V))).symm 1)
  have he := congrArg (fun z : ⋀[Γ(X,V)]^0 (KaehlerDifferential k Γ(X,V)) =>
    EtaleDeRham.differential v hv 0 z) (actualRawExteriorEquiv_empty f V)
  exact hd.trans (he.trans ((native_empty_closed v hv).trans
    (map_zero (actualRawExteriorEquiv f V 1)).symm))

private theorem exteriorLinearEquiv_eq_semilinear {R M N : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (q : ℕ) (a : ⋀[R]^q M) :
    CanonicalGeometry.exteriorLinearEquiv e q a =
      CanonicalGeometry.exteriorSemilinearMap (RingHom.id R) e.toLinearMap q a := by
  have h : (CanonicalGeometry.exteriorLinearEquiv e q).toLinearMap =
      CanonicalGeometry.exteriorSemilinearMap (RingHom.id R) e.toLinearMap q := by
    apply LinearMap.ext_on (exteriorPower.ιMulti_span R q M)
    rintro _ ⟨m, rfl⟩
    exact (CanonicalGeometry.exteriorLinearEquiv_ιMulti e q m).trans
      (CanonicalGeometry.exteriorSemilinearMap_ιMulti (RingHom.id R) e.toLinearMap q m).symm
  exact LinearMap.congr_fun h a

private theorem exteriorLinearEquiv_wedge {R M N : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (q r : ℕ) (a : ⋀[R]^q M) (b : ⋀[R]^r M) :
    CanonicalGeometry.exteriorLinearEquiv e (r+q) (EtaleGradedLeibniz.wedgeProduct q r a b) =
      EtaleGradedLeibniz.wedgeProduct q r
        (CanonicalGeometry.exteriorLinearEquiv e q a)
        (CanonicalGeometry.exteriorLinearEquiv e r b) :=
  (exteriorLinearEquiv_eq_semilinear e (r+q) (EtaleGradedLeibniz.wedgeProduct q r a b)).trans
    ((RelativeEtaleCartierMultiplicativity.exteriorSemilinearMap_wedgeProduct
      (RingHom.id R) e.toLinearMap q r a b).trans
      (congrArg₂ (fun x y => EtaleGradedLeibniz.wedgeProduct q r x y)
        (exteriorLinearEquiv_eq_semilinear e q a).symm
        (exteriorLinearEquiv_eq_semilinear e r b).symm))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- `actualRawExteriorEquiv` is multiplicative for the wedge products. -/
theorem actualRawExteriorEquiv_wedgeProduct (q r : ℕ)
    (a : (CanonicalGeometry.exteriorCotangentPresheaf f q).obj (op V))
    (b : (CanonicalGeometry.exteriorCotangentPresheaf f r).obj (op V)) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f V
    actualRawExteriorEquiv f V (r+q) (EtaleGradedLeibniz.wedgeProduct q r a b) =
      EtaleGradedLeibniz.wedgeProduct q r
        (actualRawExteriorEquiv f V q a) (actualRawExteriorEquiv f V r b) := by
  let _ := CanonicalGeometry.cotangentOpenAlgebra f V
  exact exteriorLinearEquiv_wedge (CanonicalGeometry.cotangentPresheafSectionsEquiv f V) q r a b

private def rawDegreeCast {a b : ℕ} (h : a = b)
    (s : (CanonicalGeometry.exteriorCotangentPresheaf f a).obj (op V)) :
    (CanonicalGeometry.exteriorCotangentPresheaf f b).obj (op V) := h ▸ s

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem actualRawExteriorEquiv_cast {a b : ℕ} (h : a = b)
    (s : (CanonicalGeometry.exteriorCotangentPresheaf f a).obj (op V)) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f V
    (actualRawExteriorEquiv f V b).toFun (rawDegreeCast f V h s) =
      (h ▸ (actualRawExteriorEquiv f V a).toFun s :
        ⋀[Γ(X,V)]^b (KaehlerDifferential k Γ(X,V))) := by
  subst b
  rfl

private theorem native_wedge_differential {K B : Type u} [CommRing K] [CommRing B]
    [Algebra K B] {m : ℕ} (v : Fin m → B) (hv : (MvPolynomial.aeval (R := K) v).Etale)
    (q r : ℕ) (a : ⋀[B]^q (KaehlerDifferential K B))
    (b : ⋀[B]^r (KaehlerDifferential K B)) :
    EtaleDeRham.differential v hv (r+q) (EtaleGradedLeibniz.wedgeProduct q r a b) =
      EtaleGradedLeibniz.wedgeProduct (q+1) r (EtaleDeRham.differential v hv q a) b +
        (-1 : ℤ)^q • ((show r+1+q = r+q+1 by omega) ▸
          EtaleGradedLeibniz.wedgeProduct q (r+1) a (EtaleDeRham.differential v hv r b)) := by
  apply Subtype.ext
  have hc {i j : ℕ} (h : i = j) (s : ⋀[B]^i (KaehlerDifferential K B)) :
      ((h ▸ s : ⋀[B]^j (KaehlerDifferential K B)) :
        ExteriorAlgebra B (KaehlerDifferential K B)) = s := by
    subst j
    rfl
  simpa only [Submodule.coe_add, Submodule.coe_smul, hc,
    EtaleGradedLeibniz.coe_wedgeProduct, ← Int.cast_smul_eq_zsmul B,
    Int.cast_pow, Int.cast_neg, Int.cast_one] using
      EtaleGradedLeibniz.differential_wedgeProduct v hv q r a b

private theorem linearEquiv_sum_reflect {R A B : Type u} [CommRing R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (e : A ≃ₗ[R] B) (z : ℤ) {l u v : A} {L U V : B}
    (hl : e l = L) (hu : e u = U) (hv : e v = V) (h : L = U + z • V) :
    l = u + z • v := by
  apply e.injective
  rw [map_add, map_zsmul, hl, hu, hv]
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The graded Leibniz rule for the raw differential, deduced from the Leibniz rule for
`EtaleDeRham.differential` through `actualRawExteriorEquiv`. -/
theorem rawDifferential_wedgeProduct {m : ℕ} (v : Fin m → Γ(X,V))
    (hv : letI := CanonicalGeometry.cotangentOpenAlgebra f V;
      (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
    (q r : ℕ) (a : (CanonicalGeometry.exteriorCotangentPresheaf f q).obj (op V))
    (b : (CanonicalGeometry.exteriorCotangentPresheaf f r).obj (op V)) :
    EtaleAffineSectionDifferential.rawDifferential f v hv (r+q)
        (EtaleGradedLeibniz.wedgeProduct q r a b) =
      (show (CanonicalGeometry.exteriorCotangentPresheaf f (r+q+1)).obj (op V) from
        EtaleGradedLeibniz.wedgeProduct (q+1) r
          (EtaleAffineSectionDifferential.rawDifferential f v hv q a) b) +
      (-1 : ℤ)^q • rawDegreeCast f V (show r+1+q = r+q+1 by omega)
        (EtaleGradedLeibniz.wedgeProduct q (r+1) a
          (EtaleAffineSectionDifferential.rawDifferential f v hv r b)) := by
  let _ := CanonicalGeometry.cotangentOpenAlgebra f V
  let ea := actualRawExteriorEquiv f V q a
  let eb := actualRawExteriorEquiv f V r b
  let da := EtaleAffineSectionDifferential.rawDifferential f v hv q a
  let db := EtaleAffineSectionDifferential.rawDifferential f v hv r b
  let hdeg : r+1+q = r+q+1 := by omega
  have hleft :
      actualRawExteriorEquiv f V (r+q+1)
        (EtaleAffineSectionDifferential.rawDifferential f v hv (r+q)
          (EtaleGradedLeibniz.wedgeProduct q r a b)) =
      EtaleDeRham.differential v hv (r+q) (EtaleGradedLeibniz.wedgeProduct q r ea eb) :=
    (actualRawExteriorEquiv_rawDifferential f V v hv (r+q)
      (EtaleGradedLeibniz.wedgeProduct q r a b)).trans
      (congrArg (fun z : ⋀[Γ(X,V)]^(r+q) (KaehlerDifferential k Γ(X,V)) =>
        EtaleDeRham.differential v hv (r+q) z)
        (actualRawExteriorEquiv_wedgeProduct f V q r a b))
  have hfirst :
      actualRawExteriorEquiv f V (r+q+1) (EtaleGradedLeibniz.wedgeProduct (q+1) r da b) =
      EtaleGradedLeibniz.wedgeProduct (q+1) r (EtaleDeRham.differential v hv q ea) eb :=
    (actualRawExteriorEquiv_wedgeProduct f V (q+1) r da b).trans
      (congrArg (fun z : ⋀[Γ(X,V)]^(q+1) (KaehlerDifferential k Γ(X,V)) =>
        EtaleGradedLeibniz.wedgeProduct (q+1) r z eb)
        (actualRawExteriorEquiv_rawDifferential f V v hv q a))
  have hsecond :
      actualRawExteriorEquiv f V (r+q+1)
        (rawDegreeCast f V hdeg (EtaleGradedLeibniz.wedgeProduct q (r+1) a db)) =
      (hdeg ▸ EtaleGradedLeibniz.wedgeProduct q (r+1) ea
        (EtaleDeRham.differential v hv r eb)) :=
    (actualRawExteriorEquiv_cast f V hdeg
      (EtaleGradedLeibniz.wedgeProduct q (r+1) a db)).trans
      (congrArg (fun z : ⋀[Γ(X,V)]^(r+1+q) (KaehlerDifferential k Γ(X,V)) =>
        (hdeg ▸ z : ⋀[Γ(X,V)]^(r+q+1) (KaehlerDifferential k Γ(X,V))))
        ((actualRawExteriorEquiv_wedgeProduct f V q (r+1) a db).trans
          (congrArg (fun z : ⋀[Γ(X,V)]^(r+1) (KaehlerDifferential k Γ(X,V)) =>
            EtaleGradedLeibniz.wedgeProduct q (r+1) ea z)
            (actualRawExteriorEquiv_rawDifferential f V v hv r b))))
  exact linearEquiv_sum_reflect
    (R := Γ(X,V))
    (A := (CanonicalGeometry.exteriorCotangentPresheaf f (r+q+1)).obj (op V))
    (B := ⋀[Γ(X,V)]^(r+q+1) (KaehlerDifferential k Γ(X,V)))
    (actualRawExteriorEquiv f V (r+q+1)) ((-1 : ℤ)^q)
    (l := EtaleAffineSectionDifferential.rawDifferential f v hv (r+q)
      (EtaleGradedLeibniz.wedgeProduct q r a b))
    (u := (show (CanonicalGeometry.exteriorCotangentPresheaf f (r+q+1)).obj (op V) from
      EtaleGradedLeibniz.wedgeProduct (q+1) r da b))
    (v := rawDegreeCast f V hdeg (EtaleGradedLeibniz.wedgeProduct q (r+1) a db))
    (L := EtaleDeRham.differential v hv (r+q) (EtaleGradedLeibniz.wedgeProduct q r ea eb))
    (U := EtaleGradedLeibniz.wedgeProduct (q+1) r (EtaleDeRham.differential v hv q ea) eb)
    (V := (hdeg ▸ EtaleGradedLeibniz.wedgeProduct q (r+1) ea
      (EtaleDeRham.differential v hv r eb)))
    hleft hfirst hsecond (native_wedge_differential v hv q r ea eb)

private def originalDegreeCast {a b : ℕ} (h : a = b) (V : X.Opens)
    (s : Γ(CanonicalGeometry.exteriorCotangentSheaf f a,V)) :
    Γ(CanonicalGeometry.exteriorCotangentSheaf f b,V) := h ▸ s

private theorem originalDegreeCast_unit {a b : ℕ} (h : a = b)
    {V : X.Opens} (hV : IsAffineOpen V) {m : ℕ} (v : Fin m → Γ(X,V))
    (hv : letI := CanonicalGeometry.cotangentOpenAlgebra f V;
      (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
    (s : (CanonicalGeometry.exteriorCotangentPresheaf f a).obj (op V)) :
    originalDegreeCast f h V (EtaleAffineSectionDifferential.unitEquiv f hV v hv a s) =
      EtaleAffineSectionDifferential.unitEquiv f hV v hv b (rawDegreeCast f V h s) := by
  subst b
  rfl

private theorem originalUnit_eq {V : X.Opens} (hV : IsAffineOpen V)
    {m : ℕ} (v : Fin m → Γ(X,V))
    (hv : letI := CanonicalGeometry.cotangentOpenAlgebra f V;
      (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
    (q : ℕ) (a : (CanonicalGeometry.exteriorCotangentPresheaf f q).obj (op V)) :
    EtaleAffineSectionDifferential.unitEquiv f hV v hv q a =
      (CanonicalGeometry.exteriorSheafificationMap
        (CanonicalGeometry.cotangentPresheaf f) q).app (op V) a :=
  EtaleAffineSectionDifferential.unitEquiv_apply f hV v hv q a

set_option backward.isDefEq.respectTransparency false in
private theorem originalProduct_unit {V : X.Opens} (hV : IsAffineOpen V)
    {m : ℕ} (v : Fin m → Γ(X,V))
    (hv : letI := CanonicalGeometry.cotangentOpenAlgebra f V;
      (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
    (q r : ℕ) (a : (CanonicalGeometry.exteriorCotangentPresheaf f q).obj (op V))
    (b : (CanonicalGeometry.exteriorCotangentPresheaf f r).obj (op V)) :
    (show Γ(CanonicalGeometry.exteriorCotangentSheaf f (r+q),V) from
      exteriorSheafProductSection (CanonicalGeometry.cotangentPresheaf f) q r V
        (EtaleAffineSectionDifferential.unitEquiv f hV v hv q a)
        (EtaleAffineSectionDifferential.unitEquiv f hV v hv r b)) =
      EtaleAffineSectionDifferential.unitEquiv f hV v hv (r+q)
        (EtaleGradedLeibniz.wedgeProduct q r a b) :=
  (congrArg₂ (fun (x : Γ(CanonicalGeometry.exteriorCotangentSheaf f q,V))
      (y : Γ(CanonicalGeometry.exteriorCotangentSheaf f r,V)) =>
      (show Γ(CanonicalGeometry.exteriorCotangentSheaf f (r+q),V) from
        exteriorSheafProductSection (CanonicalGeometry.cotangentPresheaf f) q r V x y))
    (originalUnit_eq f hV v hv q a) (originalUnit_eq f hV v hv r b)).trans
      ((exteriorSheafProductSection_unit (CanonicalGeometry.cotangentPresheaf f) q r V a b).trans
        (originalUnit_eq f hV v hv (r+q) (EtaleGradedLeibniz.wedgeProduct q r a b)).symm)

private theorem additive_eq_chain {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    (e : G →+ H) (z : ℤ) {t x y : G} {l u v : H}
    (ht : t = x + z • y) (hl : l = e t) (hu : u = e x) (hv : v = e y) :
    l = u + z • v := by
  calc
    l = e t := hl
    _ = e (x + z • y) := congrArg e ht
    _ = e x + z • e y := by rw [map_add, map_zsmul]
    _ = u + z • v := congrArg₂ (fun a b : H => a + z • b) hu.symm hv.symm

private theorem linearEquiv_eq_chain {R G H : Type u} [CommRing R]
    [AddCommGroup G] [Module R G] [AddCommGroup H] [Module R H]
    (e : G ≃ₗ[R] H) (z : ℤ) {t x y : G} {l u v : H}
    (ht : t = x + z • y) (hl : l = e t) (hu : u = e x) (hv : v = e y) :
    l = u + z • v :=
  additive_eq_chain e.toLinearMap.toAddMonoidHom z ht hl hu hv

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option diagnostics true in
theorem affineSectionProduct_differential {V : X.Opens} (hV : IsAffineOpen V)
    {m : ℕ} (v : Fin m → Γ(X,V))
    (hv : letI := CanonicalGeometry.cotangentOpenAlgebra f V;
      (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
    (q r : ℕ) (a' : Γ(CanonicalGeometry.exteriorCotangentSheaf f q,V))
    (b' : Γ(CanonicalGeometry.exteriorCotangentSheaf f r,V)) :
    EtaleAffineSectionDifferential.differential f hV v hv (r+q)
        (exteriorSheafProductSection (CanonicalGeometry.cotangentPresheaf f) q r V a' b') =
      (show Γ(CanonicalGeometry.exteriorCotangentSheaf f (r+q+1),V) from
        exteriorSheafProductSection (CanonicalGeometry.cotangentPresheaf f) (q+1) r V
          (EtaleAffineSectionDifferential.differential f hV v hv q a') b') +
      (-1 : ℤ)^q • originalDegreeCast f (show r+1+q = r+q+1 by omega) V
        (exteriorSheafProductSection (CanonicalGeometry.cotangentPresheaf f) q (r+1) V a'
          (EtaleAffineSectionDifferential.differential f hV v hv r b')) := by
  let _ := CanonicalGeometry.cotangentOpenAlgebra f V
  obtain ⟨a, ha₀⟩ := (EtaleAffineSectionDifferential.unitEquiv f hV v hv q).surjective a'
  obtain ⟨b, hb₀⟩ := (EtaleAffineSectionDifferential.unitEquiv f hV v hv r).surjective b'
  have ha : EtaleAffineSectionDifferential.unitEquiv f hV v hv q a = a' := ha₀
  have hb : EtaleAffineSectionDifferential.unitEquiv f hV v hv r b = b' := hb₀
  rw [← ha, ← hb]
  let da := EtaleAffineSectionDifferential.rawDifferential f v hv q a
  let db := EtaleAffineSectionDifferential.rawDifferential f v hv r b
  let hdeg : r+1+q = r+q+1 := by omega
  let x : (CanonicalGeometry.exteriorCotangentPresheaf f (r+q+1)).obj (op V) :=
    EtaleGradedLeibniz.wedgeProduct (q+1) r da b
  let y : (CanonicalGeometry.exteriorCotangentPresheaf f (r+q+1)).obj (op V) :=
    rawDegreeCast f V hdeg (EtaleGradedLeibniz.wedgeProduct q (r+1) a db)
  have hleft :
      EtaleAffineSectionDifferential.differential f hV v hv (r+q)
        (exteriorSheafProductSection (CanonicalGeometry.cotangentPresheaf f) q r V
          (EtaleAffineSectionDifferential.unitEquiv f hV v hv q a)
          (EtaleAffineSectionDifferential.unitEquiv f hV v hv r b)) =
        (show Γ(CanonicalGeometry.exteriorCotangentSheaf f (r+q+1),V) from
          EtaleAffineSectionDifferential.unitEquiv f hV v hv (r+q+1)
            (EtaleAffineSectionDifferential.rawDifferential f v hv (r+q)
              (EtaleGradedLeibniz.wedgeProduct q r a b))) :=
    (congrArg (fun z : Γ(CanonicalGeometry.exteriorCotangentSheaf f (r+q),V) =>
      EtaleAffineSectionDifferential.differential f hV v hv (r+q) z)
      (originalProduct_unit f hV v hv q r a b)).trans
      (EtaleAffineSectionDifferential.differential_unit f hV v hv (r+q)
        (EtaleGradedLeibniz.wedgeProduct q r a b))
  have hfirst :
      (show Γ(CanonicalGeometry.exteriorCotangentSheaf f (r+q+1),V) from
        exteriorSheafProductSection (CanonicalGeometry.cotangentPresheaf f) (q+1) r V
          (EtaleAffineSectionDifferential.differential f hV v hv q
            (EtaleAffineSectionDifferential.unitEquiv f hV v hv q a))
          (EtaleAffineSectionDifferential.unitEquiv f hV v hv r b)) =
      EtaleAffineSectionDifferential.unitEquiv f hV v hv (r+q+1) x :=
    (congrArg (fun z : Γ(CanonicalGeometry.exteriorCotangentSheaf f (q+1),V) =>
      (show Γ(CanonicalGeometry.exteriorCotangentSheaf f (r+q+1),V) from
        exteriorSheafProductSection (CanonicalGeometry.cotangentPresheaf f) (q+1) r V z
          (EtaleAffineSectionDifferential.unitEquiv f hV v hv r b)))
      (EtaleAffineSectionDifferential.differential_unit f hV v hv q a)).trans
      (originalProduct_unit f hV v hv (q+1) r da b)
  have hsecond :
      originalDegreeCast f hdeg V
        (exteriorSheafProductSection (CanonicalGeometry.cotangentPresheaf f) q (r+1) V
          (EtaleAffineSectionDifferential.unitEquiv f hV v hv q a)
          (EtaleAffineSectionDifferential.differential f hV v hv r
            (EtaleAffineSectionDifferential.unitEquiv f hV v hv r b))) =
      EtaleAffineSectionDifferential.unitEquiv f hV v hv (r+q+1) y :=
    (congrArg (fun z : Γ(CanonicalGeometry.exteriorCotangentSheaf f (r+1),V) =>
      originalDegreeCast f hdeg V
        (exteriorSheafProductSection (CanonicalGeometry.cotangentPresheaf f) q (r+1) V
          (EtaleAffineSectionDifferential.unitEquiv f hV v hv q a) z))
      (EtaleAffineSectionDifferential.differential_unit f hV v hv r b)).trans
      ((congrArg (fun z : Γ(CanonicalGeometry.exteriorCotangentSheaf f (r+1+q),V) =>
        originalDegreeCast f hdeg V z) (originalProduct_unit f hV v hv q (r+1) a db)).trans
          (originalDegreeCast_unit f hdeg hV v hv
            (EtaleGradedLeibniz.wedgeProduct q (r+1) a db)))
  have hraw : EtaleAffineSectionDifferential.rawDifferential f v hv (r+q)
      (EtaleGradedLeibniz.wedgeProduct q r a b) = x + (-1 : ℤ)^q • y :=
    rawDifferential_wedgeProduct f V v hv q r a b
  let e := EtaleAffineSectionDifferential.unitEquiv f hV v hv (r+q+1)
  have hsum : e (x + (-1 : ℤ)^q • y) = e x + (-1 : ℤ)^q • e y := by
    have hadd : e (x + (-1 : ℤ)^q • y) = e x + e ((-1 : ℤ)^q • y) :=
      e.map_add x ((-1 : ℤ)^q • y)
    have hsmul : e ((-1 : ℤ)^q • y) = (-1 : ℤ)^q • e y :=
      map_zsmul e.toAddEquiv ((-1 : ℤ)^q) y
    exact Eq.trans (α := Γ(CanonicalGeometry.exteriorCotangentSheaf f (r+q+1),V))
      hadd (congrArg (fun z : Γ(CanonicalGeometry.exteriorCotangentSheaf f (r+q+1),V) =>
        e x + z) hsmul)
  have hunit :
      e (EtaleAffineSectionDifferential.rawDifferential f v hv (r+q)
        (EtaleGradedLeibniz.wedgeProduct q r a b)) = e (x + (-1 : ℤ)^q • y) :=
    congrArg (fun z : (CanonicalGeometry.exteriorCotangentPresheaf f (r+q+1)).obj (op V) =>
      (show Γ(CanonicalGeometry.exteriorCotangentSheaf f (r+q+1),V) from e z)) hraw
  have hright :
      e x + (-1 : ℤ)^q • e y =
        (show Γ(CanonicalGeometry.exteriorCotangentSheaf f (r+q+1),V) from
          exteriorSheafProductSection (CanonicalGeometry.cotangentPresheaf f) (q+1) r V
            (EtaleAffineSectionDifferential.differential f hV v hv q
              (EtaleAffineSectionDifferential.unitEquiv f hV v hv q a))
            (EtaleAffineSectionDifferential.unitEquiv f hV v hv r b)) +
        (-1 : ℤ)^q • originalDegreeCast f hdeg V
          (exteriorSheafProductSection (CanonicalGeometry.cotangentPresheaf f) q (r+1) V
            (EtaleAffineSectionDifferential.unitEquiv f hV v hv q a)
            (EtaleAffineSectionDifferential.differential f hV v hv r
              (EtaleAffineSectionDifferential.unitEquiv f hV v hv r b))) :=
    congrArg₂ (fun (s t : Γ(CanonicalGeometry.exteriorCotangentSheaf f (r+q+1),V)) =>
      s + (-1 : ℤ)^q • t) hfirst.symm hsecond.symm
  have hresult := hleft.trans (hunit.trans (hsum.trans hright))
  exact hresult

end OriginalExteriorNativeBridge

/-! ### Pushed exterior sections

The sections over `W` of the de Rham forms of the Frobenius twist are identified, as additive
groups, with the sections over the preimage of `W` of the exterior cotangent sheaf. The two module
structures differ: the structure ring of the twist acts through Frobenius. -/

section PushedExteriorSections

variable {k : Type u} [Field k] (f : X ⟶ Spec (CommRingCat.of k))
  (p : ℕ) [Fact p.Prime] [CharP k p]

local notation "Y" => SchemeRelativeFrobenius.twist p f
local notation "Fr" => SchemeRelativeFrobenius.map p f
local notation "E" q => SchemeRelativeFrobeniusDeRham.formModule f p q

/-- The additive identification of sections of the de Rham forms on the twist with sections of
the exterior cotangent sheaf on the preimage. -/
def pushedExteriorSectionEquiv (q : ℕ) (W : (Y).Opens) :
    Γ(E q,W) ≃+ Γ(CanonicalGeometry.exteriorCotangentSheaf f q,(Fr) ⁻¹ᵁ W) :=
  AddEquiv.refl _

theorem pushedExteriorSectionEquiv_apply (q : ℕ) (W : (Y).Opens) (s : Γ(E q,W)) :
    (pushedExteriorSectionEquiv f p q W).toFun s =
      (show Γ(CanonicalGeometry.exteriorCotangentSheaf f q,(Fr) ⁻¹ᵁ W) from s) := rfl

theorem pushedExteriorSectionEquiv_wedge (q r : ℕ) (W : (Y).Opens)
    (a : Γ(E q,W)) (b : Γ(E r,W)) :
    (pushedExteriorSectionEquiv f p (r+q) W).toFun (formWedge f p q r W a b) =
      exteriorSheafProductSection (CanonicalGeometry.cotangentPresheaf f) q r ((Fr) ⁻¹ᵁ W)
        ((pushedExteriorSectionEquiv f p q W).toFun a)
        ((pushedExteriorSectionEquiv f p r W).toFun b) := rfl

variable (n : ℕ) [SmoothOfRelativeDimension n f]

private def pushedBasisDifferential (q : ℕ)
    (W : {W : (Y).Opens // W ∈ RelativeTwistedAffineBasis.basicOpens f p n}) :
    Γ(CanonicalGeometry.exteriorCotangentSheaf f q,(Fr) ⁻¹ᵁ W.val) →+
      Γ(CanonicalGeometry.exteriorCotangentSheaf f (q+1),(Fr) ⁻¹ᵁ W.val) :=
  ((pushedExteriorSectionEquiv f p (q+1) W.val).toAddMonoidHom.comp
    ((SchemeRelativeFrobeniusBasisDifferential.differential f p n q).val.app
      (op W.val)).hom.toAddMonoidHom).comp
    (pushedExteriorSectionEquiv f p q W.val).symm.toAddMonoidHom

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pushedBasisDifferential_eq_affine (q : ℕ)
    (W : {W : (Y).Opens // W ∈ RelativeTwistedAffineBasis.basicOpens f p n}) :
    pushedBasisDifferential f p n q W =
      EtaleAffineSectionDifferential.differential f
        (SchemeRelativeFrobeniusBasisDifferential.source_isAffine f p n W.val W.property)
        (SchemeRelativeFrobeniusBasisDifferential.coordinates f p n W)
        (SchemeRelativeFrobeniusBasisDifferential.coordinates_etale f p n W) q := by
  apply AddMonoidHom.ext
  intro s
  have h := SchemeRelativeFrobeniusBasisDifferential.differential_app f p n q W
    ((pushedExteriorSectionEquiv f p q W.val).symm.toFun s)
  have he := congrArg (fun t : Γ(E (q+1),W.val) =>
    (pushedExteriorSectionEquiv f p (q+1) W.val).toFun t) h
  exact he

end PushedExteriorSections

end EnvelopeProperty.Cartier.DeligneIllusieCechCupProduct
