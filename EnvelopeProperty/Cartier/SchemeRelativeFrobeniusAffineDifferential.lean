import EnvelopeProperty.Cartier.SchemeRelativeFrobeniusBasisDifferential

/-! # The genuine global differential on every original affine coordinate chart -/
noncomputable section
namespace EnvelopeProperty.Cartier.SchemeRelativeFrobeniusAffineDifferential
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of k)) (p : ℕ) [Fact p.Prime] [CharP k p]
local notation "Y" => SchemeRelativeFrobenius.twist p f
local notation "Fr" => SchemeRelativeFrobenius.map p f
local notation "E" => SchemeRelativeFrobeniusDeRham.formModule f p

/-- The entire original twisted coordinate open is its actual principal open at one. -/
theorem twistedOpen_mem_basis {U : X.Opens} (hU : IsAffineOpen U)
    {n : ℕ} (v : Fin n → Γ(X,U))
    (hv : letI := CanonicalGeometry.cotangentOpenAlgebra f U;
      (MvPolynomial.aeval (R := k) v).toRingHom.Etale) :
    RelativeTwistedAffineBasis.twistedOpen f p U ∈
      RelativeTwistedAffineBasis.basicOpens f p n :=
  ⟨U, ⟨hU, v, hv⟩, 1, (Scheme.basicOpen_one _).symm⟩

variable (n : ℕ) [SmoothOfRelativeDimension n f]

/-- The entire original additive-group component on EVERY actual basis member. -/
theorem differential_presheaf_app (q : ℕ)
    (W : {W : (Y).Opens // W ∈ RelativeTwistedAffineBasis.basicOpens f p n}) :
    (SchemeRelativeFrobeniusBasisDifferential.differential f p n q).mapPresheaf.app (op W.val) =
      AddCommGrpCat.ofHom (SchemeRelativeFrobeniusBasisDifferential.component f p n q W) := by
  apply AddCommGrpCat.hom_ext
  ext s
  exact SchemeRelativeFrobeniusBasisDifferential.differential_app f p n q W s

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The SAME global differential intertwines the original restriction for ANY original etale tuple. -/
theorem differential_twistedOpen {U : X.Opens} (hU : IsAffineOpen U)
    (v : Fin n → Γ(X,U))
    (hv : letI := CanonicalGeometry.cotangentOpenAlgebra f U;
      (MvPolynomial.aeval (R := k) v).toRingHom.Etale) (q : ℕ) :
    (CanonicalGeometry.exteriorCotangentSheaf f q).presheaf.map
        (eqToHom (RelativeTwistedAffineBasis.relative_preimage f p U)).op ≫
      (SchemeRelativeFrobeniusBasisDifferential.differential f p n q).mapPresheaf.app
        (op (RelativeTwistedAffineBasis.twistedOpen f p U)) =
      AddCommGrpCat.ofHom (EtaleAffineSectionDifferential.differential f hU v hv q) ≫
        (CanonicalGeometry.exteriorCotangentSheaf f (q+1)).presheaf.map
          (eqToHom (RelativeTwistedAffineBasis.relative_preimage f p U)).op := by
  let W : {W : (Y).Opens // W ∈ RelativeTwistedAffineBasis.basicOpens f p n} :=
    ⟨RelativeTwistedAffineBasis.twistedOpen f p U, twistedOpen_mem_basis f p hU v hv⟩
  rw [show (SchemeRelativeFrobeniusBasisDifferential.differential f p n q).mapPresheaf.app
      (op (RelativeTwistedAffineBasis.twistedOpen f p U)) =
        AddCommGrpCat.ofHom (SchemeRelativeFrobeniusBasisDifferential.component f p n q W) from
    differential_presheaf_app f p n q W]
  apply AddCommGrpCat.hom_ext
  ext s
  exact EtaleAffineSectionDifferential.differential_restrict f hU v hv
    (SchemeRelativeFrobeniusBasisDifferential.source_isAffine f p n W.val W.property)
    (eqToHom (RelativeTwistedAffineBasis.relative_preimage f p U))
    (SchemeRelativeFrobeniusBasisDifferential.coordinates f p n W)
    (SchemeRelativeFrobeniusBasisDifferential.coordinates_etale f p n W) q s

set_option pp.fullNames true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
#check @twistedOpen_mem_basis
#print axioms twistedOpen_mem_basis
#check @differential_presheaf_app
#print axioms differential_presheaf_app
#check @differential_twistedOpen
#print axioms differential_twistedOpen
end EnvelopeProperty.Cartier.SchemeRelativeFrobeniusAffineDifferential
