import EnvelopeProperty.Cartier.SchemeRelativeFrobenius
import EnvelopeProperty.Cartier.SmoothEtaleAffineBasis

/-! # Actual affine cover and principal basis on the TRUE geometric twist

The original relative inverse images and localized etale tuples are derived.
No perfectness, characteristic instance on section rings or basis certificate.
-/
noncomputable section
namespace EnvelopeProperty.Cartier.RelativeTwistedAffineBasis
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
universe u
variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of k)) (p : ℕ) [Fact p.Prime] [CharP k p]
local notation "Y" => SchemeRelativeFrobenius.twist p f
local notation "Fk" => SchemeRelativeFrobenius.baseMap (k := k) p
local notation "π" => (pullback.fst f Fk : Y ⟶ X)
local notation "Fr" => SchemeRelativeFrobenius.map p f

/-- The actual first projection is affine by genuine base change of an affine morphism. -/
theorem projection_isAffineHom : IsAffineHom (π) := by
  let : MorphismProperty.IsStableUnderBaseChange (@IsAffineHom.{u}) :=
    isAffineHom_isStableUnderBaseChange
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @IsAffineHom.{u}) (IsPullback.of_hasPullback f Fk).flip
    (inferInstance : IsAffineHom Fk)

/-- The SAME actual open inverse image in the TRUE geometric twist. -/
def twistedOpen (U : X.Opens) : (Y).Opens := (π) ⁻¹ᵁ U

/-- Every original affine open has its genuine affine twisted open. -/
theorem twistedOpen_isAffine (U : X.Opens) (hU : IsAffineOpen U) :
    IsAffineOpen (twistedOpen f p U) := by
  let := projection_isAffineHom f p
  exact hU.preimage (π)

/-- Relative Frobenius has EXACTLY the SAME original open U as its inverse image. -/
theorem relative_preimage (U : X.Opens) : (Fr) ⁻¹ᵁ twistedOpen f p U = U := by
  have h := congrArg (fun z : X ⟶ X => z ⁻¹ᵁ U) (SchemeRelativeFrobenius.map_fst p f)
  exact h.trans (SchemeFrobenius.preimage_eq f p U)

/-- The actual inverse image of EVERY twisted principal open is the original principal open
of its actual pulled section, with the section target literally the original U. -/
theorem basicOpen_preimage (U : X.Opens) (a : Γ(Y, twistedOpen f p U)) :
    (Fr) ⁻¹ᵁ (Y).basicOpen a = X.basicOpen
      ((Fr).appLE (twistedOpen f p U) U (relative_preimage f p U).symm.le a) := by
  have hle : (Fr) ⁻¹ᵁ (Y).basicOpen a ≤ U := by
    apply le_trans (show (Fr) ⁻¹ᵁ (Y).basicOpen a ≤ (Fr) ⁻¹ᵁ twistedOpen f p U from
      fun x hx => (Y).basicOpen_le a hx)
    exact (relative_preimage f p U).le
  exact ((Scheme.basicOpen_appLE (Fr) U (twistedOpen f p U)
    (relative_preimage f p U).symm.le a).trans (inf_eq_right.mpr hle)).symm

/-- Every original relative inverse image of such a principal open is genuinely affine. -/
theorem basicOpen_source_isAffine (U : X.Opens) (hU : IsAffineOpen U)
    (a : Γ(Y, twistedOpen f p U)) : IsAffineOpen ((Fr) ⁻¹ᵁ (Y).basicOpen a) := by
  erw [basicOpen_preimage f p U a]
  exact hU.basicOpen _

/-- Original etale coordinates RESTRICT through the actual principal section map to supply
an actual etale tuple on the SAME relative inverse-image open. -/
theorem basicOpen_source_coordinates (U : X.Opens) (hU : IsAffineOpen U)
    (a : Γ(Y, twistedOpen f p U)) {n : ℕ} (v : Fin n → Γ(X, U))
    (hv : letI := CanonicalGeometry.cotangentOpenAlgebra f U;
      (MvPolynomial.aeval (R := k) v).toRingHom.Etale) :
    ∃ w : Fin n → Γ(X, (Fr) ⁻¹ᵁ (Y).basicOpen a),
      letI := CanonicalGeometry.cotangentOpenAlgebra f ((Fr) ⁻¹ᵁ (Y).basicOpen a);
      (MvPolynomial.aeval (R := k) w).toRingHom.Etale := by
  erw [basicOpen_preimage f p U a]
  let b : Γ(X, U) :=
    (Fr).appLE (twistedOpen f p U) U (relative_preimage f p U).symm.le a
  exact ⟨fun j => X.presheaf.map (homOfLE (X.basicOpen_le b)).op (v j),
    SmoothEtaleAffineBasis.etale_coordinates_basicOpen f hU b v hv⟩

/-- ALL actual principal opens inside the genuine twisted coordinate-open cover. -/
def basicOpens (n : ℕ) : Set (Y).Opens :=
  {W | ∃ U ∈ SmoothEtaleAffineBasis.coordinateOpens f n,
    ∃ a : Γ(Y, twistedOpen f p U), W = (Y).basicOpen a}

/-- Every member of the actual refined family is affine. -/
theorem basicOpens_isAffine (n : ℕ) (W : (Y).Opens) (hW : W ∈ basicOpens f p n) :
    IsAffineOpen W := by
  obtain ⟨U, hU, a, rfl⟩ := hW
  exact (twistedOpen_isAffine f p U hU.1).basicOpen a

variable (n : ℕ) [SmoothOfRelativeDimension n f]

/-- Every actual twist point belongs to an original twisted coordinate affine open. -/
theorem coordinate_cover (y : Y) :
    ∃ U ∈ SmoothEtaleAffineBasis.coordinateOpens f n, y ∈ twistedOpen f p U := by
  obtain ⟨U, hU, hy, _⟩ := SmoothEtaleAffineBasis.exists_subchart f n ((π) y)
    (show (π) y ∈ (⊤ : X.Opens) from trivial)
  exact ⟨U, hU, hy⟩

/-- The original twisted coordinate opens form a genuine native covering family. -/
theorem coordinate_coversTop : (_root_.Opens.grothendieckTopology Y).CoversTop
    (fun U : {U : X.Opens // U ∈ SmoothEtaleAffineBasis.coordinateOpens f n} =>
      twistedOpen f p U.val) := by
  rw [_root_.Opens.coversTop_iff]
  apply top_unique
  intro y _
  obtain ⟨U, hU, hy⟩ := coordinate_cover f p n y
  exact Opens.mem_iSup.mpr ⟨⟨U, hU⟩, hy⟩

/-- GENUINE full topological basis from principal refinements of the actual affine cover. -/
theorem isBasis_basicOpens : Opens.IsBasis (basicOpens f p n) := by
  rw [Opens.isBasis_iff_nbhd]
  intro W y hy
  obtain ⟨U, hU, hyU⟩ := coordinate_cover f p n y
  obtain ⟨a, ha, hya⟩ := (twistedOpen_isAffine f p U hU.1).exists_basicOpen_le
    (⟨y, hy⟩ : W) hyU
  exact ⟨(Y).basicOpen a, ⟨U, hU, a, rfl⟩, hya, ha⟩

end EnvelopeProperty.Cartier.RelativeTwistedAffineBasis
