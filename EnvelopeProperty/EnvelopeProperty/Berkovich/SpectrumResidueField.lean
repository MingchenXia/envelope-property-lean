/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.Spectrum
import EnvelopeProperty.Berkovich.ValuationCompletion

/-!
# Completed residue fields of arbitrary real-valued seminorm points

For a seminorm point of any commutative ring, the support is prime. Its residue
field carries the induced absolute value, and the completion is an actual complete
nonarchimedean normed field. The map from the original ring preserves seminorms and
has kernel equal to the support; it need not be injective.

Arbitrary ring pullback induces isometric embeddings of residue fields and their
completions. Prescribed-base relative spectra retain the base seminorm and algebra
compatibility. No field, trivial valuation, boundedness, finite type, or completeness
hypothesis is imposed on the original or coefficient rings.
-/

open scoped NNReal ENNReal Topology nonZeroDivisors

noncomputable section

namespace EnvelopeProperty.Berkovich

namespace Spectrum

variable {B : Type*} [CommRing B]

/-! ### The residue field and its absolute value -/

/-- The residue field `κ(x)` of a seminorm point: the residue field of `B` at the prime
ideal `supp x = {b | |b|_x = 0}`, i.e. the fraction field of `B ⧸ supp x`. -/
abbrev ResidueField (x : Spectrum B) : Type _ := x.val.supp.ResidueField

theorem le_primeCompl_onQuot (x : Spectrum B) :
    (B ⧸ x.val.supp)⁰ ≤ (x.val.onQuot le_rfl).supp.primeCompl := by
  intro z hz
  rw [Ideal.mem_primeCompl_iff, Valuation.supp_quot_supp]
  exact nonZeroDivisors.ne_zero hz

/-- The valuation on `κ(x)` induced by `|·|_x`: the extension of the valuation induced on
`B ⧸ supp x` to its fraction field. -/
def residueValuation (x : Spectrum B) : Valuation x.ResidueField ℝ≥0 :=
  (x.val.onQuot le_rfl).extendToLocalization (le_primeCompl_onQuot x) x.ResidueField

@[simp]
theorem residueValuation_algebraMap (x : Spectrum B) (b : B) :
    x.residueValuation (algebraMap B x.ResidueField b) = x.val b := by
  rw [← Ideal.algebraMap_quotient_residueField_mk, residueValuation,
    Valuation.extendToLocalization_apply_map_apply]
  rfl

theorem residueValuation_eq_zero_iff (x : Spectrum B) {z : x.ResidueField} :
    x.residueValuation z = 0 ↔ z = 0 :=
  Valuation.zero_iff _

/-- The absolute value `κ(x) → ℝ` induced by `|·|_x`. -/
def residueAbs (x : Spectrum B) : AbsoluteValue x.ResidueField ℝ :=
  Valuation.toRealAbs x.residueValuation

@[simp]
theorem residueAbs_apply (x : Spectrum B) (z : x.ResidueField) :
    x.residueAbs z = x.residueValuation z := rfl

theorem residueAbs_algebraMap (x : Spectrum B) (b : B) :
    x.residueAbs (algebraMap B x.ResidueField b) = x.val b := by
  simp

theorem isNonarchimedean_residueAbs (x : Spectrum B) : IsNonarchimedean x.residueAbs :=
  Valuation.isNonarchimedean_toRealAbs _

/-! ### The completed residue field -/

/-- The **completed residue field** `H(x)` of a seminorm point (Berkovich, §1.2): the
completion of `κ(x)` with respect to the absolute value induced by `|·|_x`. It is a complete
nonarchimedean normed field (instances `NormedField`, `CompleteSpace`, `IsUltrametricDist`); its
norm may be trivial. -/
def H (x : Spectrum B) : Type _ := x.residueAbs.Completion

instance (x : Spectrum B) : NormedField (H x) :=
  inferInstanceAs (NormedField (UniformSpace.Completion (WithAbs x.residueAbs)))

instance (x : Spectrum B) : CompleteSpace (H x) :=
  inferInstanceAs (CompleteSpace (UniformSpace.Completion (WithAbs x.residueAbs)))

instance (x : Spectrum B) : Inhabited (H x) := ⟨0⟩

/-- The embedding `κ(x) → H(x)` preserves the induced absolute value, with dense image
(`Spectrum.denseRange_residueToH`). -/
def residueToH (x : Spectrum B) : x.ResidueField →+* H x :=
  UniformSpace.Completion.coeRingHom.comp (WithAbs.equiv x.residueAbs).symm.toRingHom

theorem norm_residueToH (x : Spectrum B) (z : x.ResidueField) :
    ‖x.residueToH z‖ = x.residueAbs z := by
  change ‖((WithAbs.toAbs x.residueAbs z : WithAbs x.residueAbs) :
    UniformSpace.Completion (WithAbs x.residueAbs))‖ = _
  rw [UniformSpace.Completion.norm_coe]
  rfl

theorem denseRange_residueToH (x : Spectrum B) : DenseRange x.residueToH := by
  have e : Set.range (((↑) : WithAbs x.residueAbs → UniformSpace.Completion
      (WithAbs x.residueAbs)) ∘ (WithAbs.equiv x.residueAbs).symm) =
      Set.range ((↑) : WithAbs x.residueAbs → UniformSpace.Completion (WithAbs x.residueAbs)) :=
    (WithAbs.equiv x.residueAbs).symm.surjective.range_comp _
  change Dense (Set.range (((↑) : WithAbs x.residueAbs → UniformSpace.Completion
      (WithAbs x.residueAbs)) ∘ (WithAbs.equiv x.residueAbs).symm))
  rw [e]
  exact UniformSpace.Completion.denseRange_coe

instance (x : Spectrum B) : IsUltrametricDist (WithAbs x.residueAbs) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun a b =>
    x.isNonarchimedean_residueAbs a.ofAbs b.ofAbs

instance (x : Spectrum B) : IsUltrametricDist (H x) :=
  inferInstanceAs (IsUltrametricDist (UniformSpace.Completion (WithAbs x.residueAbs)))

/-- The ring homomorphism `B → H(x)` preserves the original seminorm. -/
def toH (x : Spectrum B) : B →+* H x := x.residueToH.comp (algebraMap B x.ResidueField)

theorem toH_apply (x : Spectrum B) (b : B) :
    x.toH b = x.residueToH (algebraMap B x.ResidueField b) := rfl

@[simp]
theorem norm_toH (x : Spectrum B) (b : B) : ‖x.toH b‖ = x.val b := by
  rw [toH_apply, norm_residueToH, residueAbs_algebraMap]

@[simp]
theorem nnnorm_toH (x : Spectrum B) (b : B) : ‖x.toH b‖₊ = x.val b :=
  NNReal.eq (norm_toH x b)

theorem toH_eq_zero_iff (x : Spectrum B) {b : B} : x.toH b = 0 ↔ x.val b = 0 := by
  rw [← norm_eq_zero, norm_toH, NNReal.coe_eq_zero]

theorem ker_toH (x : Spectrum B) : RingHom.ker x.toH = x.val.supp :=
  Ideal.ext fun _ => by rw [RingHom.mem_ker, toH_eq_zero_iff, Valuation.mem_supp_iff]

instance (x : Spectrum B) : Algebra x.ResidueField (H x) := x.residueToH.toAlgebra

instance (x : Spectrum B) : Algebra B (H x) := x.toH.toAlgebra

theorem algebraMap_residueField_H (x : Spectrum B) :
    algebraMap x.ResidueField (H x) = x.residueToH := rfl

theorem algebraMap_H (x : Spectrum B) : algebraMap B (H x) = x.toH := rfl

instance (x : Spectrum B) : IsScalarTower B x.ResidueField (H x) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem norm_algebraMap_H (x : Spectrum B) (b : B) : ‖algebraMap B (H x) b‖ = x.val b :=
  norm_toH x b

/-! ### Functoriality -/

section map

variable {A : Type*} [CommRing A]

/-- The support of `φ^an(y)` is the preimage of the support of `y`. -/
theorem supp_comap (φ : B →+* A) (y : Spectrum A) :
    (comap φ y).val.supp = y.val.supp.comap (φ : B →+* A) :=
  Valuation.comap_supp _ _

/-- For `x = φ^an(y)`, the embedding of residue fields `κ(x) → κ(y)` induced by `φ`. -/
def ResidueField.map (φ : B →+* A) {x : Spectrum B} {y : Spectrum A} (h : comap φ y = x) :
    x.ResidueField →+* y.ResidueField :=
  Ideal.ResidueField.map x.val.supp y.val.supp (φ : B →+* A) (h ▸ supp_comap φ y)

@[simp]
theorem ResidueField.map_algebraMap (φ : B →+* A) {x : Spectrum B} {y : Spectrum A}
    (h : comap φ y = x) (b : B) :
    ResidueField.map φ h (algebraMap B x.ResidueField b) = algebraMap A y.ResidueField (φ b) :=
  Ideal.ResidueField.map_algebraMap _ _ _ _ b

/-- The embedding `κ(x) → κ(y)` preserves the induced valuations. -/
@[simp]
theorem residueValuation_map (φ : B →+* A) {x : Spectrum B} {y : Spectrum A}
    (h : comap φ y = x) (z : x.ResidueField) :
    y.residueValuation (ResidueField.map φ h z) = x.residueValuation z := by
  have e : y.residueValuation.comap (ResidueField.map φ h) = x.residueValuation := by
    refine Valuation.ext_of_residueField _ fun b => ?_
    rw [Valuation.comap_apply, ResidueField.map_algebraMap, residueValuation_algebraMap,
      residueValuation_algebraMap, ← h, comap_val_apply]
  exact congrArg (fun v : Valuation x.ResidueField ℝ≥0 => v z) e

theorem residueAbs_map (φ : B →+* A) {x : Spectrum B} {y : Spectrum A}
    (h : comap φ y = x) (z : x.ResidueField) :
    y.residueAbs (ResidueField.map φ h z) = x.residueAbs z := by
  simp

/-- The isometric embedding `κ(x) → κ(y)` on the normed fields `WithAbs`. -/
def ResidueField.withAbsMap (φ : B →+* A) {x : Spectrum B} {y : Spectrum A} (h : comap φ y = x) :
    WithAbs x.residueAbs →+* WithAbs y.residueAbs :=
  WithAbs.map x.residueAbs y.residueAbs (ResidueField.map φ h)

theorem ResidueField.norm_withAbsMap (φ : B →+* A) {x : Spectrum B} {y : Spectrum A}
    (h : comap φ y = x) (z : WithAbs x.residueAbs) : ‖ResidueField.withAbsMap φ h z‖ = ‖z‖ :=
  residueAbs_map φ h z.ofAbs

/-- For `x = φ^an(y)`, the isometric embedding of completed residue fields `H(x) → H(y)`
induced by `φ` (the completion of `Spectrum.ResidueField.map`). For `x = comap φ y` itself, use
`H.map φ rfl : H (comap φ y) →+* H y`. -/
def H.map (φ : B →+* A) {x : Spectrum B} {y : Spectrum A} (h : comap φ y = x) : H x →+* H y :=
  UniformSpace.Completion.mapRingHom (ResidueField.withAbsMap φ h)
    (AddMonoidHomClass.isometry_of_norm _ (ResidueField.norm_withAbsMap φ h)).continuous

/-- The embedding `H(x) → H(y)` is isometric. -/
@[simp]
theorem H.norm_map (φ : B →+* A) {x : Spectrum B} {y : Spectrum A} (h : comap φ y = x)
    (z : H x) : ‖H.map φ h z‖ = ‖z‖ :=
  UniformSpace.Completion.norm_mapRingHom (ResidueField.withAbsMap φ h)
    (ResidueField.norm_withAbsMap φ h) z

/-- The completed residue-field pullback is an isometry. -/
theorem H.isometry_map (φ : B →+* A) {x : Spectrum B} {y : Spectrum A}
    (h : comap φ y = x) : Isometry (H.map φ h) :=
  AddMonoidHomClass.isometry_of_norm _ (H.norm_map φ h)

/-- In particular the completed residue-field pullback is injective. -/
theorem H.map_injective (φ : B →+* A) {x : Spectrum B} {y : Spectrum A}
    (h : comap φ y = x) : Function.Injective (H.map φ h) :=
  (H.isometry_map φ h).injective

theorem H.map_residueToH (φ : B →+* A) {x : Spectrum B} {y : Spectrum A} (h : comap φ y = x)
    (z : x.ResidueField) : H.map φ h (x.residueToH z) = y.residueToH (ResidueField.map φ h z) :=
  UniformSpace.Completion.mapRingHom_coe _ _

/-- The square `B → H(x) → H(y)`, `B → A → H(y)` commutes. -/
@[simp]
theorem H.map_toH (φ : B →+* A) {x : Spectrum B} {y : Spectrum A} (h : comap φ y = x) (b : B) :
    H.map φ h (x.toH b) = y.toH (φ b) := by
  rw [toH_apply, H.map_residueToH, ResidueField.map_algebraMap, toH_apply]

theorem H.map_comp_toH (φ : B →+* A) {x : Spectrum B} {y : Spectrum A} (h : comap φ y = x) :
    (H.map φ h).comp x.toH = y.toH.comp (φ : B →+* A) :=
  RingHom.ext (H.map_toH φ h)

end map

/-- Identity ring pullback induces the identity residue-field map. -/
@[simp]
theorem ResidueField.map_id (x : Spectrum B) :
    ResidueField.map (RingHom.id B) (comap_id x) = RingHom.id x.ResidueField := by
  apply Ideal.ResidueField.ringHom_ext
  ext b
  simp only [RingHom.comp_apply, ResidueField.map_algebraMap, RingHom.id_apply]

/-- Residue-field embeddings respect composition of arbitrary ring homomorphisms. -/
theorem ResidueField.map_comp {A C : Type*} [CommRing A] [CommRing C]
    (φ : B →+* A) (ψ : A →+* C) {x : Spectrum B} {y : Spectrum A} {z : Spectrum C}
    (hφ : comap φ y = x) (hψ : comap ψ z = y) :
    (ResidueField.map ψ hψ).comp (ResidueField.map φ hφ) =
      ResidueField.map (ψ.comp φ) (by rw [comap_comp, hψ, hφ]) := by
  apply Ideal.ResidueField.ringHom_ext
  ext b
  simp only [RingHom.comp_apply, ResidueField.map_algebraMap]

/-- Continuous maps from the completed field are determined on its dense residue-field image. -/
theorem H.ringHom_ext {x : Spectrum B} {C : Type*} [CommRing C]
    [TopologicalSpace C] [T2Space C] {f g : H x →+* C}
    (hf : Continuous f) (hg : Continuous g)
    (h : ∀ z : x.ResidueField, f (x.residueToH z) = g (x.residueToH z)) : f = g := by
  have he := (denseRange_residueToH x).equalizer hf hg (funext h)
  exact RingHom.ext fun z => congrFun he z

/-- Identity ring pullback induces the identity completed-field map. -/
@[simp]
theorem H.map_id (x : Spectrum B) :
    H.map (RingHom.id B) (comap_id x) = RingHom.id (H x) := by
  apply H.ringHom_ext (H.isometry_map _ _).continuous continuous_id
  intro z
  rw [H.map_residueToH, ResidueField.map_id]
  rfl

/-- Completed-field embeddings respect composition of arbitrary ring homomorphisms. -/
theorem H.map_comp {A C : Type*} [CommRing A] [CommRing C]
    (φ : B →+* A) (ψ : A →+* C) {x : Spectrum B} {y : Spectrum A} {z : Spectrum C}
    (hφ : comap φ y = x) (hψ : comap ψ z = y) :
    (H.map ψ hψ).comp (H.map φ hφ) =
      H.map (ψ.comp φ) (by rw [comap_comp, hψ, hφ]) := by
  have hc : Continuous (((H.map ψ hψ).comp (H.map φ hφ)) : H x → H z) :=
    (H.isometry_map ψ hψ).continuous.comp (H.isometry_map φ hφ).continuous
  apply H.ringHom_ext hc (H.isometry_map _ _).continuous
  intro a
  simp only [RingHom.comp_apply, H.map_residueToH]
  exact congrArg z.residueToH (congrArg (fun f : x.ResidueField →+* z.ResidueField => f a)
    (ResidueField.map_comp φ ψ hφ hψ))

end Spectrum

namespace RelativeSpectrum

variable {R : Type*} [CommRing R] {v : Valuation R ℝ≥0}
  {A : Type*} [CommRing A] [Algebra R A]

/-- The completed residue field of a relative point is that of its underlying seminorm. -/
abbrev H (x : RelativeSpectrum v A) := Spectrum.H x.1

/-- The coefficient-ring action on the completed residue field. -/
instance (x : RelativeSpectrum v A) : Algebra R (H x) :=
  ((Spectrum.toH x.1).comp (algebraMap R A)).toAlgebra

instance (x : RelativeSpectrum v A) : IsScalarTower R A (H x) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The completed residue-field base map realizes the actual prescribed seminorm. -/
theorem norm_algebraMap_H (x : RelativeSpectrum v A) (r : R) :
    ‖algebraMap R (H x) r‖ = v r := by
  change ‖Spectrum.toH x.1 (algebraMap R A r)‖ = (v r : ℝ)
  rw [Spectrum.norm_toH, x.2 r]

@[simp]
theorem nnnorm_algebraMap_H (x : RelativeSpectrum v A) (r : R) :
    ‖algebraMap R (H x) r‖₊ = v r :=
  NNReal.eq (norm_algebraMap_H x r)

/-- Pullback along a base-algebra homomorphism gives a genuine completed-field algebra map. -/
def H.map {B : Type*} [CommRing B] [Algebra R B] (φ : A →ₐ[R] B)
    {x : RelativeSpectrum v A} {y : RelativeSpectrum v B} (h : comap φ y = x) :
    H x →ₐ[R] H y where
  __ := Spectrum.H.map φ.toRingHom (congrArg Subtype.val h)
  commutes' r := by
    have h' : Spectrum.comap φ.toRingHom y.1 = x.1 := congrArg Subtype.val h
    change Spectrum.H.map φ.toRingHom h'
      (Spectrum.toH x.1 (algebraMap R A r)) = Spectrum.toH y.1 (algebraMap R B r)
    rw [Spectrum.H.map_toH φ.toRingHom h']
    exact congrArg (Spectrum.toH y.1) (φ.commutes r)

/-- Relative completed-field algebra maps preserve norms. -/
@[simp]
theorem H.norm_map {B : Type*} [CommRing B] [Algebra R B] (φ : A →ₐ[R] B)
    {x : RelativeSpectrum v A} {y : RelativeSpectrum v B} (h : comap φ y = x) (z : H x) :
    ‖H.map φ h z‖ = ‖z‖ :=
  Spectrum.H.norm_map φ.toRingHom (congrArg Subtype.val h) z

/-- Relative completed-field algebra maps are isometric embeddings. -/
theorem H.isometry_map {B : Type*} [CommRing B] [Algebra R B] (φ : A →ₐ[R] B)
    {x : RelativeSpectrum v A} {y : RelativeSpectrum v B} (h : comap φ y = x) :
    Isometry (H.map φ h) :=
  AddMonoidHomClass.isometry_of_norm _ (H.norm_map φ h)

end RelativeSpectrum

end EnvelopeProperty.Berkovich
