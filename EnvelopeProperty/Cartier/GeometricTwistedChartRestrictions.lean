import EnvelopeProperty.Cartier.RelativeCartierContinuationTwistedAffineSections
import EnvelopeProperty.Cartier.EtaleSchemeSectionDifferential
import EnvelopeProperty.Cartier.SmoothEtaleAffineCover
import EnvelopeProperty.Cartier.RelativeCartierContinuationGlobalCotangentExchange
import EnvelopeProperty.Cartier.RelativeCartierContinuationEtaleCartierNaturality

/-! # Original twisted-chart restrictions and their derived honest-coordinate cover -/

noncomputable section
namespace EnvelopeProperty.Cartier.GeometricTwistedChartRestrictions
open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
universe u

variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of k)) (p : ℕ) [Fact p.Prime] [CharP k p]
local notation "Y" => SchemeRelativeFrobenius.twist p f
local notation "π₁" => pullback.fst f (SchemeRelativeFrobenius.baseMap (k := k) p)
local notation "π₂" => pullback.snd f (SchemeRelativeFrobenius.baseMap (k := k) p)
local notation "W[" U "]" => RelativeTwistedAffineBasis.twistedOpen f p U
local notation "B[" U "]" => X.presheaf.obj (op U)
local notation "α[" U "]" => @CommRingCat.Hom.hom (CommRingCat.of k)
  (X.presheaf.obj (op U)) (NatTrans.app (CanonicalGeometry.schemeConstantPresheafMap f) (op U))
local notation "T[" U "]" => RelativeFrobenius.twist (α[U]) p
local notation "s[" U "]" => RelativeFrobenius.sourceMap (α[U]) p
local notation "c[" U "]" => RelativeFrobenius.coefficientMap (α[U]) p
local notation "δ[" U "]" => RelativeTwistedAffineSections.coefficientSectionMap f p U
variable {U V : X.Opens} (i : U ⟶ V)

/-- The original first-projection inverse images carry the original open inclusion. -/
def twistedInclusion : W[U] ⟶ W[V] :=
  homOfLE (by intro y hy; exact i.le hy)

/-- The original structural section restriction induces the genuine native twist map. -/
def twistRestrictionMap : T[V] ⟶ T[U] := by
  letI := CanonicalGeometry.cotangentOpenAlgebra f V
  letI := CanonicalGeometry.cotangentOpenAlgebra f U
  letI := (EtaleSchemeSectionDifferential.restrictionAlgebraHom f i).toAlgebra
  letI : IsScalarTower k (B[V]) (B[U]) := IsScalarTower.of_algebraMap_eq
    fun a => ((EtaleSchemeSectionDifferential.restrictionAlgebraHom f i).commutes a).symm
  exact RelativeEtaleCartierNaturality.twistMap (k := k) (A := B[V]) (B := B[U]) p

/-- The same native twist restriction retains the whole original coefficient triangle. -/
theorem twistRestrictionMap_coefficient : c[V] ≫ twistRestrictionMap f p i = c[U] := by
  let := CanonicalGeometry.cotangentOpenAlgebra f V
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  let := (EtaleSchemeSectionDifferential.restrictionAlgebraHom f i).toAlgebra
  let : IsScalarTower k (B[V]) (B[U]) := IsScalarTower.of_algebraMap_eq
    fun a => ((EtaleSchemeSectionDifferential.restrictionAlgebraHom f i).commutes a).symm
  exact RelativeEtaleCartierNaturality.twistMap_coefficient (k := k) (A := B[V]) (B := B[U]) p

/-- The same native twist restriction retains the whole original source triangle. -/
theorem twistRestrictionMap_source : s[V] ≫ twistRestrictionMap f p i =
    X.presheaf.map i.op ≫ s[U] := by
  let := CanonicalGeometry.cotangentOpenAlgebra f V
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  let := (EtaleSchemeSectionDifferential.restrictionAlgebraHom f i).toAlgebra
  let : IsScalarTower k (B[V]) (B[U]) := IsScalarTower.of_algebraMap_eq
    fun a => ((EtaleSchemeSectionDifferential.restrictionAlgebraHom f i).commutes a).symm
  exact RelativeEtaleCartierNaturality.twistMap_source (k := k) (A := B[V]) (B := B[U]) p

/-- Original geometric coefficients commute with the original twisted-open restriction. -/
theorem coefficient_restrict : δ[V] ≫ (Y).presheaf.map (twistedInclusion f p i).op = δ[U] := by
  have h := (CanonicalGeometry.schemeConstantPresheafMap (π₂)).naturality
    (twistedInclusion f p i).op
  change (𝟙 (CommRingCat.of k)) ≫ δ[U] =
    δ[V] ≫ (Y).presheaf.map (twistedInclusion f p i).op at h
  exact h.symm.trans (Category.id_comp _)

/-- Original first-projection source sections commute with the same actual restriction. -/
theorem source_restrict : X.presheaf.map i.op ≫ (π₁).app U =
    (π₁).app V ≫ (Y).presheaf.map (twistedInclusion f p i).op :=
  (π₁).naturality i.op

/-- The entire ORIGINAL section-ring chart isomorphism commutes with actual affine restriction. -/
theorem sectionsIso_naturality (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    (Y).presheaf.map (twistedInclusion f p i).op ≫
        (RelativeTwistedAffineCharts.sectionsIso f p U hU).hom =
      (RelativeTwistedAffineCharts.sectionsIso f p V hV).hom ≫ twistRestrictionMap f p i := by
  let σU : Γ(Y, W[U]) ≅ T[U] := RelativeTwistedAffineCharts.sectionsIso f p U hU
  let σV : Γ(Y, W[V]) ≅ T[V] := RelativeTwistedAffineCharts.sectionsIso f p V hV
  let r := (Y).presheaf.map (twistedInclusion f p i).op
  let τ := twistRestrictionMap f p i
  have hcU : δ[U] ≫ σU.hom = c[U] :=
    RelativeTwistedAffineSections.sectionsIso_coefficient f p U hU
  have hcV : c[V] ≫ σV.inv = δ[V] := RelativeGlobalCotangentExchange.inverseCoefficientSquare
    (δ[V]) (c[V]) σV (RelativeTwistedAffineSections.sectionsIso_coefficient f p V hV)
  have hsU : (π₁).app U ≫ σU.hom = s[U] :=
    (congrArg (fun a : Γ(X, U) ⟶ Γ(Y, W[U]) => a ≫ σU.hom)
      (Scheme.Hom.appLE_eq_app (π₁))).symm.trans
        (RelativeTwistedAffineSections.sectionsIso_source f p U hU)
  have hsV : s[V] ≫ σV.inv = (π₁).app V :=
    RelativeGlobalCotangentExchange.inverseCoefficientSquare ((π₁).app V) (s[V]) σV
      ((congrArg (fun a : Γ(X, V) ⟶ Γ(Y, W[V]) => a ≫ σV.hom)
        (Scheme.Hom.appLE_eq_app (π₁))).symm.trans
          (RelativeTwistedAffineSections.sectionsIso_source f p V hV))
  have ht : σV.inv ≫ (r ≫ σU.hom) = τ := by
    apply pushout.hom_ext
    · change c[V] ≫ (σV.inv ≫ (r ≫ σU.hom)) = c[V] ≫ τ
      calc
        _ = (c[V] ≫ σV.inv) ≫ (r ≫ σU.hom) := (Category.assoc _ _ _).symm
        _ = δ[V] ≫ (r ≫ σU.hom) := congrArg (fun a => a ≫ (r ≫ σU.hom)) hcV
        _ = (δ[V] ≫ r) ≫ σU.hom := (Category.assoc _ _ _).symm
        _ = δ[U] ≫ σU.hom := congrArg (fun a => a ≫ σU.hom) (coefficient_restrict f p i)
        _ = c[U] := hcU
        _ = c[V] ≫ τ := (twistRestrictionMap_coefficient f p i).symm
    · change s[V] ≫ (σV.inv ≫ (r ≫ σU.hom)) = s[V] ≫ τ
      calc
        _ = (s[V] ≫ σV.inv) ≫ (r ≫ σU.hom) := (Category.assoc _ _ _).symm
        _ = (π₁).app V ≫ (r ≫ σU.hom) := congrArg (fun a => a ≫ (r ≫ σU.hom)) hsV
        _ = ((π₁).app V ≫ r) ≫ σU.hom := (Category.assoc _ _ _).symm
        _ = (X.presheaf.map i.op ≫ (π₁).app U) ≫ σU.hom :=
          congrArg (fun a => a ≫ σU.hom) (source_restrict f p i).symm
        _ = X.presheaf.map i.op ≫ ((π₁).app U ≫ σU.hom) := Category.assoc _ _ _
        _ = X.presheaf.map i.op ≫ s[U] := congrArg (fun a => X.presheaf.map i.op ≫ a) hsU
        _ = s[V] ≫ τ := (twistRestrictionMap_source f p i).symm
  exact (σV.hom_inv_id_assoc (r ≫ σU.hom)).symm.trans (congrArg (fun a => σV.hom ≫ a) ht)

/-- Smoothness derives an honest-coordinate affine cover of the SAME actual geometric twist. -/
theorem exists_twisted_affine_etale_cover (n : ℕ) [SmoothOfRelativeDimension n f] :
    ∃ U : X → X.Opens, (∀ x, IsAffineOpen (U x)) ∧ (∀ x, x ∈ U x) ∧
      IsOpenCover (fun x => W[U x]) ∧ (∀ x, IsAffineOpen (W[U x])) ∧ ∀ x,
        letI := CanonicalGeometry.cotangentOpenAlgebra f (U x)
        ∃ v : Fin n → Γ(X, U x), (MvPolynomial.aeval (R := k) v).toRingHom.Etale := by
  obtain ⟨U, hU, hmem, _, het⟩ := SmoothEtaleAffineCover.exists_affine_etale_cover f n
  refine ⟨U, hU, hmem, ?_, fun x => RelativeTwistedAffineBasis.twistedOpen_isAffine f p (U x) (hU x), het⟩
  change (⨆ x, W[U x]) = ⊤
  apply le_antisymm le_top
  intro y _
  exact Opens.mem_iSup.mpr ⟨(π₁).base y, hmem _⟩

end EnvelopeProperty.Cartier.GeometricTwistedChartRestrictions
