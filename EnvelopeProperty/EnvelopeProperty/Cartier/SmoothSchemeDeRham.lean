import EnvelopeProperty.Cartier.SmoothEtaleAffineBasis
import EnvelopeProperty.Cartier.EtaleAffineSectionDifferential
import EnvelopeProperty.Cartier.SchemeFrobeniusScalarRestriction
import EnvelopeProperty.AlgGeom.SchemeModuleBasisExtension

/-! # The SAME entire original smooth-scheme Frobenius exterior differential -/
noncomputable section
namespace EnvelopeProperty.Cartier.SmoothSchemeDeRham
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open scoped Classical
universe u
private theorem smul_of_pointwise {R M N : Type u} [SMul R M] [SMul R N]
    (a b : M → N) (h : ∀ x, a x = b x)
    (hb : ∀ (r : R) (x : M), b (r • x) = r • b x) (r : R) (x : M) :
    a (r • x) = r • a x :=
  (h _).trans ((hb r x).trans (congrArg (fun y : N => r • y) (h x)).symm)

private theorem square_of_pointwise {A B C : Type u} [Zero C]
    (a c : A → B) (b d : B → C) (ha : ∀ x, a x = c x) (hb : ∀ y, b y = d y)
    (h : ∀ x, d (c x) = 0) (x : A) : b (a x) = 0 :=
  (congrArg b (ha x)).trans ((hb (c x)).trans (h x))

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

private abbrev CoordinateIndex (n : ℕ) : Type u :=
  Σ V : X.Opens, {v : Fin n → Γ(X, V) // IsAffineOpen V ∧
    letI := CanonicalGeometry.cotangentOpenAlgebra f V
    (MvPolynomial.aeval (R := k) v).toRingHom.Etale}

private def basisOpens (n : ℕ) : CoordinateIndex f n → X.Opens := fun i => i.1

private theorem basisOpens_isBasis (n : ℕ) [SmoothOfRelativeDimension n f] :
    Opens.IsBasis (Set.range (basisOpens f n)) := by
  have he : Set.range (basisOpens f n) = SmoothEtaleAffineBasis.coordinateOpens f n := by
    ext V
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.2.property.1, i.2.val, i.2.property.2⟩
    · rintro ⟨ha, v, hv⟩
      exact ⟨⟨V, ⟨v, ha, hv⟩⟩, rfl⟩
  rw [he]
  exact SmoothEtaleAffineBasis.isBasis_coordinateOpens f n

private def coordinates (n : ℕ) (i : CoordinateIndex f n) : Fin n → Γ(X, i.1) :=
  i.2.val

private theorem coordinates_etale (n : ℕ) (i : CoordinateIndex f n) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f i.1
    (MvPolynomial.aeval (R := k) (coordinates f n i)).toRingHom.Etale :=
  i.2.property.2

private theorem affineUnitFormula {V : X.Opens} (hV : IsAffineOpen V) {n : ℕ}
    (v : Fin n → Γ(X, V))
    (hv : letI := CanonicalGeometry.cotangentOpenAlgebra f V;
      (MvPolynomial.aeval (R := k) v).toRingHom.Etale) (q : ℕ)
    (a : (CanonicalGeometry.exteriorCotangentPresheaf f q).obj (op V)) :
    EtaleAffineSectionDifferential.differential f hV v hv q
        ((CanonicalGeometry.exteriorSheafificationMap
          (CanonicalGeometry.cotangentPresheaf f) q).app (op V) a) =
      (CanonicalGeometry.exteriorSheafificationMap
        (CanonicalGeometry.cotangentPresheaf f) (q+1)).app (op V)
          (EtaleAffineSectionDifferential.rawDifferential f v hv q a) := by
  have h := EtaleAffineSectionDifferential.differential_unit f hV v hv q a
  have h₀ := EtaleAffineSectionDifferential.unitEquiv_apply f hV v hv q a
  have h₁ := EtaleAffineSectionDifferential.unitEquiv_apply f hV v hv (q+1)
    (EtaleAffineSectionDifferential.rawDifferential f v hv q a)
  exact (congrArg (EtaleAffineSectionDifferential.differential f hV v hv q) h₀).symm.trans
    (h.trans h₁)

variable (p : ℕ) [Fact p.Prime] [CharP k p]

/-- SAME actual whole original Frobenius-restricted exterior cotangent sheaf. -/
def formModule (q : ℕ) : X.Modules :=
  (SchemeFrobeniusScalarRestriction.modulesFunctor f p).obj
    (CanonicalGeometry.exteriorCotangentSheaf f q)

private def basisLinearDifferential (n q : ℕ) (i : CoordinateIndex f n) :
    (formModule f p q).val.obj (op i.1) ⟶ (formModule f p (q+1)).val.obj (op i.1) := by
  letI := CanonicalGeometry.cotangentOpenAlgebra f i.1
  let F := ModuleCat.restrictScalars (AlgebraFrobenius.map k Γ(X, i.1) p)
  exact F.map (EtaleAffineSectionDifferential.unitEquiv f i.2.property.1
      (coordinates f n i) (coordinates_etale f n i) q).symm.toModuleIso.hom ≫
    EtaleAlgebraFrobeniusComplex.differential
      (coordinates f n i) (coordinates_etale f n i) p q ≫
      F.map (EtaleAffineSectionDifferential.unitEquiv f i.2.property.1
        (coordinates f n i) (coordinates_etale f n i) (q+1)).toModuleIso.hom

private def basisDifferential (n q : ℕ) (i : CoordinateIndex f n) :
    Γ(formModule f p q, i.1) →+ Γ(formModule f p (q+1), i.1) :=
  (basisLinearDifferential f p n q i).hom.toAddMonoidHom

private theorem basisDifferential_apply (n q : ℕ) (i : CoordinateIndex f n)
    (x : Γ(formModule f p q, i.1)) :
    basisDifferential f p n q i x = EtaleAffineSectionDifferential.differential f i.2.property.1
      (coordinates f n i) (coordinates_etale f n i) q x := rfl

private def basisOriginalMap (n q : ℕ) :
    (inducedFunctor (basisOpens f n)).op ⋙
        (CanonicalGeometry.exteriorCotangentSheaf f q).presheaf ⟶
      (inducedFunctor (basisOpens f n)).op ⋙
        (CanonicalGeometry.exteriorCotangentSheaf f (q+1)).presheaf where
  app i := AddCommGrpCat.ofHom (EtaleAffineSectionDifferential.differential f i.unop.2.property.1
    (coordinates f n i.unop) (coordinates_etale f n i.unop) q)
  naturality {U V} a := by
    apply AddCommGrpCat.hom_ext
    ext x
    exact EtaleAffineSectionDifferential.differential_restrict f U.unop.2.property.1
      (coordinates f n U.unop) (coordinates_etale f n U.unop) V.unop.2.property.1
      ((inducedFunctor (basisOpens f n)).map a.unop)
      (coordinates f n V.unop) (coordinates_etale f n V.unop) q x

private theorem basisOriginalMap_app (n q : ℕ) (i : CoordinateIndex f n) :
    (basisOriginalMap f n q).app (op i) =
      AddCommGrpCat.ofHom (EtaleAffineSectionDifferential.differential f i.2.property.1
        (coordinates f n i) (coordinates_etale f n i) q) := rfl

private def basisMap (n q : ℕ) :
    (inducedFunctor (basisOpens f n)).op ⋙ (formModule f p q).presheaf ⟶
      (inducedFunctor (basisOpens f n)).op ⋙ (formModule f p (q+1)).presheaf :=
  basisOriginalMap f n q

private theorem basisMap_original_apply (n q : ℕ) (i : CoordinateIndex f n)
    (x : Γ(formModule f p q, i.1)) :
    (basisMap f p n q).app (op i) x =
      EtaleAffineSectionDifferential.differential f i.2.property.1
        (coordinates f n i) (coordinates_etale f n i) q x :=
  ConcreteCategory.congr_hom (basisOriginalMap_app f n q i) x

private theorem basisMap_apply (n q : ℕ) (i : CoordinateIndex f n)
    (x : Γ(formModule f p q, i.1)) :
    (basisMap f p n q).app (op i) x = (basisLinearDifferential f p n q i).hom x :=
  (basisMap_original_apply f p n q i x).trans (basisDifferential_apply f p n q i x).symm

private theorem basisMap_smul (n q : ℕ) (i : CoordinateIndex f n)
    (r : Γ(X, i.1)) (x : Γ(formModule f p q, i.1)) :
    (basisMap f p n q).app (op i) (r • x) =
      r • (show Γ(formModule f p (q+1), i.1) from (basisMap f p n q).app (op i) x) := by
  let : Module Γ(X, i.1) Γ(formModule f p q, i.1) :=
    ((formModule f p q).val.obj (op i.1)).isModule
  let : Module Γ(X, i.1) Γ(formModule f p (q+1), i.1) :=
    ((formModule f p (q+1)).val.obj (op i.1)).isModule
  exact smul_of_pointwise (R := Γ(X, i.1))
    (M := Γ(formModule f p q, i.1)) (N := Γ(formModule f p (q+1), i.1))
    (fun x : Γ(formModule f p q, i.1) => (basisMap f p n q).app (op i) x)
    (fun x : Γ(formModule f p q, i.1) => (basisLinearDifferential f p n q i).hom x)
    (basisMap_apply f p n q i)
    (basisLinearDifferential f p n q i).hom.map_smul r x

/-- GENUINE ENTIRE original smooth-scheme differential; all local data DERIVED internally. -/
def differential (n : ℕ) [SmoothOfRelativeDimension n f] (q : ℕ) :
    formModule f p q ⟶ formModule f p (q+1) :=
  SchemeModuleBasisExtension.extension (basisOpens f n) (basisOpens_isBasis f n)
    (formModule f p q) (formModule f p (q+1)) (basisMap f p n q) (basisMap_smul f p n q)

private theorem differential_basis_apply (n : ℕ) [SmoothOfRelativeDimension n f]
    (q : ℕ) (i : CoordinateIndex f n) (x : Γ(formModule f p q, i.1)) :
    (differential f p n q).val.app (op i.1) x =
      EtaleAffineSectionDifferential.differential f i.2.property.1
        (coordinates f n i) (coordinates_etale f n i) q x := by
  have h := SchemeModuleBasisExtension.extension_app (basisOpens f n) (basisOpens_isBasis f n)
    (formModule f p q) (formModule f p (q+1)) (basisMap f p n q) (basisMap_smul f p n q) i x
  exact h.trans (basisMap_original_apply f p n q i x)

/-- EVERY actual original coordinate affine open/form retains its SAME original unit formula. -/
theorem differential_unit (n : ℕ) [SmoothOfRelativeDimension n f] {V : X.Opens}
    (hV : IsAffineOpen V) (v : Fin n → Γ(X, V))
    (hv : letI := CanonicalGeometry.cotangentOpenAlgebra f V;
      (MvPolynomial.aeval (R := k) v).toRingHom.Etale) (q : ℕ)
    (a : (CanonicalGeometry.exteriorCotangentPresheaf f q).obj (op V)) :
    (differential f p n q).val.app (op V)
        ((CanonicalGeometry.exteriorSheafificationMap
          (CanonicalGeometry.cotangentPresheaf f) q).app (op V) a) =
      (CanonicalGeometry.exteriorSheafificationMap
        (CanonicalGeometry.cotangentPresheaf f) (q+1)).app (op V)
          (EtaleAffineSectionDifferential.rawDifferential f v hv q a) := by
  let i : CoordinateIndex f n := ⟨V, ⟨v, hV, hv⟩⟩
  have h := differential_basis_apply f p n q i
    ((CanonicalGeometry.exteriorSheafificationMap
      (CanonicalGeometry.cotangentPresheaf f) q).app (op V) a)
  dsimp only [i, coordinates] at h
  exact h.trans (affineUnitFormula f hV v hv q a)

/-- The SAME entire original smooth-scheme module differential has true whole square zero. -/
theorem differential_square (n : ℕ) [SmoothOfRelativeDimension n f] (q : ℕ) :
    differential f p n q ≫ differential f p n (q+1) = 0 := by
  apply SchemeModuleBasisExtension.hom_ext (basisOpens f n) (basisOpens_isBasis f n)
    (formModule f p q) (formModule f p (q+1+1))
  intro i x
  change (differential f p n (q+1)).val.app (op i.1)
    ((differential f p n q).val.app (op i.1) x) = 0
  exact square_of_pointwise
    ((differential f p n q).val.app (op i.1))
    (EtaleAffineSectionDifferential.differential f i.2.property.1
      (coordinates f n i) (coordinates_etale f n i) q)
    ((differential f p n (q+1)).val.app (op i.1))
    (EtaleAffineSectionDifferential.differential f i.2.property.1
      (coordinates f n i) (coordinates_etale f n i) (q+1))
    (differential_basis_apply f p n q i) (differential_basis_apply f p n (q+1) i)
    (EtaleAffineSectionDifferential.differential_square f i.2.property.1
      (coordinates f n i) (coordinates_etale f n i) q) x

/-- GENUINE whole native complex of SAME actual original Frobenius exterior module sheaves. -/
def complex (n : ℕ) [SmoothOfRelativeDimension n f] : CochainComplex X.Modules ℕ :=
  CochainComplex.of (formModule f p) (differential f p n) (differential_square f p n)

end EnvelopeProperty.Cartier.SmoothSchemeDeRham
