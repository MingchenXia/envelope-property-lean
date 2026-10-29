import EnvelopeProperty.AlgGeom.Canonical.SpecGlobalEtaleCoordinates
import EnvelopeProperty.AlgGeom.Canonical.AffineCanonicalSheafImage
import EnvelopeProperty.Char0.EtaleCoordinateIsomorphism

/-! # SAME original spectrum coefficients and full Jacobians in the native square -/

open CategoryTheory AlgebraicGeometry Opposite

namespace EnvelopeProperty.CanonicalGeometry

universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (k : Type u) [Field k] (A : CommRingCat.{u}) [Algebra k A]

/-- The actual original native coefficient map, for a structurally equal
original scheme morphism; only its proved algebra-commutation proof transports. -/
def affineGammaSpecAlgEquivOfStructuralEq (f : Spec A ⟶ Spec (.of k))
    (hf : f = affineStructuralMap k A) :
    letI := affineChartAlgebra f ⊤
    A ≃ₐ[k] Γ(Spec A, ⊤) := by
  letI := affineChartAlgebra f ⊤
  refine { (Scheme.ΓSpecIso A).symm.commRingCatIsoToRingEquiv with commutes' := ?_ }
  intro a
  subst f
  exact (affineGammaSpecAlgEquiv k A).commutes a

/-- The ENTIRE coefficient map remains literally the native original map. -/
theorem affineGammaSpecAlgEquivOfStructuralEq_apply (f : Spec A ⟶ Spec (.of k))
    (hf : f = affineStructuralMap k A) (a : A) :
    letI := affineChartAlgebra f ⊤
    affineGammaSpecAlgEquivOfStructuralEq k A f hf a = (Scheme.ΓSpecIso A).inv.hom a := by
  rfl


variable (B : CommRingCat.{u}) [Algebra k B] (φ : A →ₐ[k] B)

/-- The literal native section map is an algebra map for the SAME original
source and composite target structural morphisms. -/
def affineSpecSectionAlgebraHom :
    let f := affineStructuralMap k A
    let g := Spec.map (CommRingCat.ofHom φ.toRingHom)
    letI := affineChartAlgebra f ⊤
    letI := affineChartAlgebra (g ≫ f) ⊤
    Γ(Spec A, ⊤) →ₐ[k] Γ(Spec B, ⊤) := by
  let f := affineStructuralMap k A
  let g := Spec.map (CommRingCat.ofHom φ.toRingHom)
  letI := affineChartAlgebra f ⊤
  letI := affineChartAlgebra (g ≫ f) ⊤
  exact schemeMorphismSectionAlgebraHom f g ⊤

/-- The SAME original native spectrum/global-sections square commutes on
EVERY original coefficient, with no supplied square-match premise. -/
theorem affineSpecSectionAlgebraHom_naturality (a : A) :
    let f := affineStructuralMap k A
    let g := Spec.map (CommRingCat.ofHom φ.toRingHom)
    letI := affineChartAlgebra f ⊤
    letI := affineChartAlgebra (g ≫ f) ⊤
    affineSpecSectionAlgebraHom k A B φ (affineGammaSpecAlgEquiv k A a) =
      affineGammaSpecAlgEquivOfStructuralEq k B (g ≫ f)
        (affineAlgebraMap_structuralSquare k A B φ) (φ a) := by
  let f := affineStructuralMap k A
  let g := Spec.map (CommRingCat.ofHom φ.toRingHom)
  let := affineChartAlgebra f ⊤
  let := affineChartAlgebra (g ≫ f) ⊤
  change g.appTop.hom ((Scheme.ΓSpecIso A).inv.hom a) =
    (Scheme.ΓSpecIso B).inv.hom (φ a)
  have h := congrArg (fun e : A ⟶ Scheme.Γ.obj (.op (Spec B)) => e.hom a)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ.toRingHom))
  exact h.symm


/-- The FULL actual all-original-source-functions Jacobian ideal in the
SAME original section rings is exactly the native coefficient image of the
FULL original Jacobian ideal, with every basis internally derived. -/
theorem affineSpecRelativeJacobianIdeal {n : ℕ}
    (z : Fin n → A) (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale)
    (v : Fin n → B) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale) :
    let f := affineStructuralMap k A
    let g := Spec.map (CommRingCat.ofHom φ.toRingHom)
    letI := affineChartAlgebra f ⊤
    letI := affineChartAlgebra (g ≫ f) ⊤
    let e := affineGammaSpecAlgEquivOfStructuralEq k B (g ≫ f)
      (affineAlgebraMap_structuralSquare k A B φ)
    letI : Algebra Γ(Spec A, ⊤) Γ(Spec B, ⊤) := g.appTop.hom.toAlgebra
    letI : Algebra A B := φ.toAlgebra
    Char0.affineRelativeJacobianIdeal (R := Γ(Spec A, ⊤))
        (Char0.etaleDifferentialBasis (fun i => e (v i))
          (Char0.etaleCoordinates_map_algEquiv e v hv)) =
      (Char0.affineRelativeJacobianIdeal (R := A)
        (Char0.etaleDifferentialBasis v hv)).map (Scheme.ΓSpecIso B).inv.hom := by
  let f := affineStructuralMap k A
  let g := Spec.map (CommRingCat.ofHom φ.toRingHom)
  let := affineChartAlgebra f ⊤
  let := affineChartAlgebra (g ≫ f) ⊤
  let e := affineGammaSpecAlgEquivOfStructuralEq k B (g ≫ f)
    (affineAlgebraMap_structuralSquare k A B φ)
  have h := Char0.affineRelativeJacobianIdeal_map_of_algEquivs e
    (affineGammaSpecAlgEquiv k A) φ (affineSpecSectionAlgebraHom k A B φ)
    (affineSpecSectionAlgebraHom_naturality k A B φ) z hz v hv
  have he : e.toRingHom = (Scheme.ΓSpecIso B).inv.hom := by
    ext b
    exact affineGammaSpecAlgEquivOfStructuralEq_apply k B (g ≫ f)
      (affineAlgebraMap_structuralSquare k A B φ) b
  simpa only [he] using h

end
end EnvelopeProperty.CanonicalGeometry
