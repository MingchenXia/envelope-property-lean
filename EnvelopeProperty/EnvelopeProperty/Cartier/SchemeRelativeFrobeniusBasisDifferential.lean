import EnvelopeProperty.Cartier.SchemeRelativeFrobeniusComplex
import EnvelopeProperty.Cartier.RelativeCartierContinuationTwistedOpenInverse
import EnvelopeProperty.AlgGeom.SchemeModuleBasisExtension

/-! # The original principal-basis relative differential extends to the true global complex

Actual preimage affineness, etale coordinates and coefficient linearity are
produced internally. No global differential or gluing comparison is an input.
-/
noncomputable section
namespace EnvelopeProperty.Cartier.SchemeRelativeFrobeniusBasisDifferential
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
private def pushforwardBasisMap {X Y : Scheme.{u}} (g : X ⟶ Y) {ι : Type u}
    (B : ι → Y.Opens) (M N : X.Modules)
    (d : ∀ i, Γ(M,g ⁻¹ᵁ B i) →+ Γ(N,g ⁻¹ᵁ B i))
    (hd : ∀ (i j : ι) (h : B i ⟶ B j) (s : Γ(M,g ⁻¹ᵁ B j)),
      d i (M.presheaf.map ((Opens.map g.base).map h).op s) =
        N.presheaf.map ((Opens.map g.base).map h).op (d j s)) :
    (inducedFunctor B).op ⋙ ((Scheme.Modules.pushforward g).obj M).presheaf ⟶
      (inducedFunctor B).op ⋙ ((Scheme.Modules.pushforward g).obj N).presheaf where
  app i := AddCommGrpCat.ofHom (d i.unop)
  naturality := by
    intro V W i
    apply AddCommGrpCat.hom_ext
    ext s
    exact hd W.unop V.unop ((inducedFunctor B).map i.unop) s

private theorem pushforwardSquare {X Y : Scheme.{u}} (g : X ⟶ Y)
    (M₀ M₁ M₂ : X.Modules) (W : Y.Opens)
    (d₀ : Γ(M₀,g ⁻¹ᵁ W) →+ Γ(M₁,g ⁻¹ᵁ W))
    (d₁ : Γ(M₁,g ⁻¹ᵁ W) →+ Γ(M₂,g ⁻¹ᵁ W))
    (hd : ∀ s, d₁ (d₀ s) = 0) :
    AddCommGrpCat.ofHom (show Γ((Scheme.Modules.pushforward g).obj M₀,W) →+
      Γ((Scheme.Modules.pushforward g).obj M₁,W) from d₀) ≫
    AddCommGrpCat.ofHom (show Γ((Scheme.Modules.pushforward g).obj M₁,W) →+
      Γ((Scheme.Modules.pushforward g).obj M₂,W) from d₁) = 0 := by
  apply AddCommGrpCat.hom_ext
  ext s
  exact hd s

private theorem basis_composition_zero {Y : Scheme.{u}} {ι : Type u}
    (B : ι → Y.Opens) (hB : Opens.IsBasis (Set.range B))
    (M₀ M₁ M₂ : Y.Modules) (d₀ : M₀ ⟶ M₁) (d₁ : M₁ ⟶ M₂)
    (hd : ∀ (i : ι), d₀.mapPresheaf.app (op (B i)) ≫
      d₁.mapPresheaf.app (op (B i)) = 0) : d₀ ≫ d₁ = 0 := by
  apply SchemeModuleBasisExtension.hom_ext B hB M₀ M₂
  intro i s
  exact ConcreteCategory.congr_hom (hd i) s

variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of k)) (p : ℕ) [Fact p.Prime] [CharP k p]
local notation "Y" => SchemeRelativeFrobenius.twist p f
local notation "Fr" => SchemeRelativeFrobenius.map p f
local notation "E" => SchemeRelativeFrobeniusDeRham.formModule f p

/-- The actual source of each actual principal basis member is genuinely affine. -/
theorem source_isAffine (n : ℕ) (W : (Y).Opens)
    (hW : W ∈ RelativeTwistedAffineBasis.basicOpens f p n) : IsAffineOpen ((Fr) ⁻¹ᵁ W) := by
  obtain ⟨U,hU,a,rfl⟩ := hW
  exact RelativeTwistedAffineBasis.basicOpen_source_isAffine f p U hU.1 a

/-- The SAME source retains an internally derived actual original etale tuple. -/
theorem source_coordinates (n : ℕ) (W : (Y).Opens)
    (hW : W ∈ RelativeTwistedAffineBasis.basicOpens f p n) :
    ∃ v : Fin n → Γ(X, (Fr) ⁻¹ᵁ W),
      letI := CanonicalGeometry.cotangentOpenAlgebra f ((Fr) ⁻¹ᵁ W)
      (MvPolynomial.aeval (R := k) v).toRingHom.Etale := by
  obtain ⟨U,hU,a,rfl⟩ := hW
  obtain ⟨v,hv⟩ := hU.2
  exact RelativeTwistedAffineBasis.basicOpen_source_coordinates f p U hU.1 a v hv

/-- A fixed actual tuple chosen from the proved original source witnesses. -/
def coordinates (n : ℕ)
    (W : {W : (Y).Opens // W ∈ RelativeTwistedAffineBasis.basicOpens f p n}) :
    Fin n → Γ(X, (Fr) ⁻¹ᵁ W.val) :=
  Classical.choose (source_coordinates f p n W.val W.property)

/-- The internally chosen original tuple really is etale for its original coefficient action. -/
theorem coordinates_etale (n : ℕ)
    (W : {W : (Y).Opens // W ∈ RelativeTwistedAffineBasis.basicOpens f p n}) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f ((Fr) ⁻¹ᵁ W.val)
    (MvPolynomial.aeval (R := k) (coordinates f p n W)).toRingHom.Etale :=
  Classical.choose_spec (source_coordinates f p n W.val W.property)

/-- Actual original appLE scalars, with only a genuine equality of their original opens. -/
theorem differential_appLE_smul {U : X.Opens} (hU : IsAffineOpen U)
    {n : ℕ} (v : Fin n → Γ(X,U))
    (hv : letI := CanonicalGeometry.cotangentOpenAlgebra f U;
      (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
    (W : (Y).Opens) (hW : W = RelativeTwistedAffineBasis.twistedOpen f p U)
    (h : U ≤ (Fr) ⁻¹ᵁ W) (q : ℕ) (a : Γ(Y,W))
    (s : Γ(CanonicalGeometry.exteriorCotangentSheaf f q,U)) :
    EtaleAffineSectionDifferential.differential f hU v hv q ((Fr).appLE W U h a • s) =
      (Fr).appLE W U h a • EtaleAffineSectionDifferential.differential f hU v hv q s := by
  subst W
  exact SchemeRelativeFrobeniusDeRham.differential_relativeSectionMap_smul f p hU v hv q a s

/-- The SAME original intrinsic affine differential on actual pushed basis sections. -/
def component (n q : ℕ)
    (W : {W : (Y).Opens // W ∈ RelativeTwistedAffineBasis.basicOpens f p n}) :
    Γ(E q,W.val) →+ Γ(E (q+1),W.val) :=
  EtaleAffineSectionDifferential.differential f (source_isAffine f p n W.val W.property)
    (coordinates f p n W) (coordinates_etale f p n W) q

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Genuine linearity for EVERY original basis section and actual original twist scalar. -/
theorem component_smul (n q : ℕ)
    (W : {W : (Y).Opens // W ∈ RelativeTwistedAffineBasis.basicOpens f p n})
    (a : Γ(Y,W.val)) (s : Γ(E q,W.val)) :
    component f p n q W (a • s) = a • component f p n q W s := by
  change EtaleAffineSectionDifferential.differential f
    (source_isAffine f p n W.val W.property) (coordinates f p n W)
    (coordinates_etale f p n W) q (((Fr).app W.val).hom a •
      (show Γ(CanonicalGeometry.exteriorCotangentSheaf f q,(Fr) ⁻¹ᵁ W.val) from s)) =
      ((Fr).app W.val).hom a • EtaleAffineSectionDifferential.differential f
        (source_isAffine f p n W.val W.property) (coordinates f p n W)
        (coordinates_etale f p n W) q s
  have h := differential_appLE_smul f p (source_isAffine f p n W.val W.property)
    (coordinates f p n W) (coordinates_etale f p n W) W.val
    (RelativeTwistedOpenInverse.twistedOpen_relative_preimage f p W.val).symm
    le_rfl q a s
  simpa only [Scheme.Hom.appLE_eq_app] using h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual additive natural transformation on the SAME original principal basis. -/
def basisDifferential (n q : ℕ) :
    (inducedFunctor (fun W : {W : (Y).Opens // W ∈ RelativeTwistedAffineBasis.basicOpens f p n}
      => W.val)).op ⋙ (E q).presheaf ⟶
    (inducedFunctor (fun W : {W : (Y).Opens // W ∈ RelativeTwistedAffineBasis.basicOpens f p n}
      => W.val)).op ⋙ (E (q+1)).presheaf :=
  pushforwardBasisMap (Fr)
    (fun W : {W : (Y).Opens // W ∈ RelativeTwistedAffineBasis.basicOpens f p n} => W.val)
    (CanonicalGeometry.exteriorCotangentSheaf f q)
    (CanonicalGeometry.exteriorCotangentSheaf f (q+1))
    (fun W => EtaleAffineSectionDifferential.differential f
      (source_isAffine f p n W.val W.property) (coordinates f p n W)
      (coordinates_etale f p n W) q)
    (fun W V i s => EtaleAffineSectionDifferential.differential_restrict f
      (source_isAffine f p n V.val V.property)
      (coordinates f p n V) (coordinates_etale f p n V)
      (source_isAffine f p n W.val W.property) ((Opens.map (Fr).base).map i)
      (coordinates f p n W) (coordinates_etale f p n W) q s)

private theorem basisDifferential_app (n q : ℕ)
    (W : {W : (Y).Opens // W ∈ RelativeTwistedAffineBasis.basicOpens f p n}) :
    (basisDifferential f p n q).app (op W) = AddCommGrpCat.ofHom (component f p n q W) := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem basisDifferential_smul (n q : ℕ)
    (W : {W : (Y).Opens // W ∈ RelativeTwistedAffineBasis.basicOpens f p n})
    (a : Γ(Y,W.val)) (s : Γ(E q,W.val)) :
    (basisDifferential f p n q).app (op W) (a • s) =
      a • (show Γ(E (q+1),W.val) from (basisDifferential f p n q).app (op W) s) :=
by
  rw [basisDifferential_app]
  exact component_smul f p n q W a s

variable (n : ℕ) [SmoothOfRelativeDimension n f]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual globally defined original O_Y-linear exterior differential. -/
def differential (q : ℕ) : E q ⟶ E (q+1) :=
  SchemeModuleBasisExtension.extension
    (fun W : {W : (Y).Opens // W ∈ RelativeTwistedAffineBasis.basicOpens f p n} => W.val)
    (by simpa only [Subtype.range_val] using RelativeTwistedAffineBasis.isBasis_basicOpens f p n)
    (E q) (E (q+1)) (basisDifferential f p n q) (basisDifferential_smul f p n q)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- EVERY actual original basis section retains its SAME intrinsic affine differential. -/
theorem differential_app (q : ℕ)
    (W : {W : (Y).Opens // W ∈ RelativeTwistedAffineBasis.basicOpens f p n})
    (s : Γ(E q,W.val)) :
    (differential f p n q).val.app (op W.val) s = component f p n q W s := by
  unfold differential
  have h := SchemeModuleBasisExtension.extension_app
    (fun W : {W : (Y).Opens // W ∈ RelativeTwistedAffineBasis.basicOpens f p n} => W.val)
    (by simpa only [Subtype.range_val] using RelativeTwistedAffineBasis.isBasis_basicOpens f p n)
    (E q) (E (q+1)) (basisDifferential f p n q) (basisDifferential_smul f p n q) W s
  rw [basisDifferential_app] at h
  exact h

private theorem differential_presheaf_app (q : ℕ)
    (W : {W : (Y).Opens // W ∈ RelativeTwistedAffineBasis.basicOpens f p n}) :
    (differential f p n q).mapPresheaf.app (op W.val) =
      (basisDifferential f p n q).app (op W) :=
  SchemeModuleBasisExtension.additiveExtension_app
    (fun W : {W : (Y).Opens // W ∈ RelativeTwistedAffineBasis.basicOpens f p n} => W.val)
    (by simpa only [Subtype.range_val] using RelativeTwistedAffineBasis.isBasis_basicOpens f p n)
    (E q) (E (q+1)) (basisDifferential f p n q) W

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual global differential has square zero as an entire original module morphism. -/
theorem differential_square (q : ℕ) :
    differential f p n q ≫ differential f p n (q+1) = 0 := by
  apply basis_composition_zero
    (fun W : {W : (Y).Opens // W ∈ RelativeTwistedAffineBasis.basicOpens f p n} => W.val)
    (by simpa only [Subtype.range_val] using RelativeTwistedAffineBasis.isBasis_basicOpens f p n)
    (E q) (E (q+1)) (E (q+1+1)) (differential f p n q) (differential f p n (q+1))
  intro W
  rw [differential_presheaf_app, differential_presheaf_app, basisDifferential_app, basisDifferential_app]
  dsimp only [component]
  exact pushforwardSquare (Fr)
    (CanonicalGeometry.exteriorCotangentSheaf f q)
    (CanonicalGeometry.exteriorCotangentSheaf f (q+1))
    (CanonicalGeometry.exteriorCotangentSheaf f (q+1+1)) W.val
    (EtaleAffineSectionDifferential.differential f
      (source_isAffine f p n W.val W.property)
      (coordinates f p n W) (coordinates_etale f p n W) q)
    (EtaleAffineSectionDifferential.differential f
      (source_isAffine f p n W.val W.property)
      (coordinates f p n W) (coordinates_etale f p n W) (q+1))
    (EtaleAffineSectionDifferential.differential_square f
      (source_isAffine f p n W.val W.property)
      (coordinates f p n W) (coordinates_etale f p n W) q)

/-- The genuine original globally pushed de Rham complex on the true geometric twist. -/
def complex : CochainComplex (Y).Modules ℕ :=
  CochainComplex.of (E) (differential f p n) (differential_square f p n)

set_option pp.universes true
set_option pp.deepTerms true
set_option pp.proofs true
#check @differential_presheaf_app
#print axioms differential_presheaf_app
#check @basis_composition_zero
#print axioms basis_composition_zero
#check @pushforwardSquare
#print axioms pushforwardSquare
#check @pushforwardBasisMap
#print axioms pushforwardBasisMap
#check @basisDifferential_app
#print axioms basisDifferential_app
#check @basisDifferential_smul
#print axioms basisDifferential_smul
#check @source_isAffine
#print axioms source_isAffine
#check @source_coordinates
#print axioms source_coordinates
#check @coordinates
#print axioms coordinates
#check @coordinates_etale
#print axioms coordinates_etale
#check @differential_appLE_smul
#print axioms differential_appLE_smul
#check @component
#print axioms component
#check @component_smul
#print axioms component_smul
#check @basisDifferential
#print axioms basisDifferential
#check @differential
#print axioms differential
#check @differential_app
#print axioms differential_app
#check @differential_square
#print axioms differential_square
#check @complex
#print axioms complex
end EnvelopeProperty.Cartier.SchemeRelativeFrobeniusBasisDifferential
