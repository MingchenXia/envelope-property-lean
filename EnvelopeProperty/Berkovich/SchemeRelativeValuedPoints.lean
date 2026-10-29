/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SchemeOpenImmersion

/-!
# Native scheme points over an arbitrary prescribed base seminorm

An actual structure morphism to Spec(R) maps native valued points to the
independently defined native affine base space. Fixing the whole base point
corresponding to v is a closed condition. Commuting morphisms induce a true
continuous functor on schemes over Spec(R), and the actual Spec(A) fibre is
homeomorphic to the prescribed-base relative seminorm spectrum.

The actual structure morphism, global section identification and restriction
derive the R-action on each genuine section ring. Native local evaluations
therefore give actual relative-spectrum points for this derived action.
No field, triviality, completeness or finite-type assumption is used, and no
Hausdorff property of an arbitrary total scheme or nonaffine section-spectrum
point equivalence is asserted.
-/

open scoped NNReal Topology
open Topology CategoryTheory AlgebraicGeometry Opposite

universe u
noncomputable section

namespace EnvelopeProperty.Berkovich

namespace SchemeValuedPoint

variable {R : Type u} [CommRing R] {X : Scheme.{u}}

/-- The genuine native affine point corresponding to an arbitrary prescribed coefficient seminorm. -/
def basePoint (v : Valuation R ℝ≥0) : SchemeValuedPoint (Spec (CommRingCat.of R)) :=
  spectrumHomeomorph.symm (Spectrum.ofValuation v)

/-- Original-ring evaluation agrees with evaluation of the actual global section under the affine homeomorphism. -/
theorem spectrumHomeomorph_val_apply {A : Type u} [CommRing A]
    (y : SchemeValuedPoint (Spec (CommRingCat.of A))) (a : A) :
    (spectrumHomeomorph y).val a =
      eval y ⊤ trivial ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) :=
  toValuedPoint_eval y a

@[simp]
theorem basePoint_eval (v : Valuation R ℝ≥0) (r : R) :
    eval (basePoint v) ⊤ trivial ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) = v r := by
  rw [← spectrumHomeomorph_val_apply, basePoint, Homeomorph.apply_symm_apply]
  rfl

/-- The native point locus over an exact prescribed whole base seminorm point. -/
def relativeLocus (v : Valuation R ℝ≥0) (f : X ⟶ Spec (CommRingCat.of R)) : Set (SchemeValuedPoint X) :=
  map f ⁻¹' {basePoint v}

@[simp]
theorem mem_relativeLocus (v : Valuation R ℝ≥0) (f : X ⟶ Spec (CommRingCat.of R))
    (y : SchemeValuedPoint X) : y ∈ relativeLocus v f ↔ map f y = basePoint v := Iff.rfl

/-- The native affine base is Hausdorff by its actual homeomorphism; the total scheme need not be. -/
theorem isClosed_relativeLocus (v : Valuation R ℝ≥0) (f : X ⟶ Spec (CommRingCat.of R)) :
    IsClosed (relativeLocus v f) := by
  let : T2Space (SchemeValuedPoint (Spec (CommRingCat.of R))) :=
    (spectrumHomeomorph (A := R)).isEmbedding.t2Space
  exact isClosed_singleton.preimage (continuous_map f)

end SchemeValuedPoint

/-- Native valued points of an actual scheme structure map extending a prescribed base seminorm. -/
abbrev RelativeSchemeValuedPoint {R : Type u} [CommRing R] (v : Valuation R ℝ≥0)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) := SchemeValuedPoint.relativeLocus v f

namespace RelativeSchemeValuedPoint

variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
variable {X Y Z : Scheme.{u}}
variable {fX : X ⟶ Spec (CommRingCat.of R)} {fY : Y ⟶ Spec (CommRingCat.of R)}
variable {fZ : Z ⟶ Spec (CommRingCat.of R)}

/-- The exact prescribed-base native point space is a closed subspace. -/
theorem isClosedEmbedding_subtypeVal :
    IsClosedEmbedding ((↑) : RelativeSchemeValuedPoint v fX → SchemeValuedPoint X) :=
  (SchemeValuedPoint.isClosed_relativeLocus v fX).isClosedEmbedding_subtypeVal

/-- A genuine commuting scheme morphism preserves the exact whole prescribed base point. -/
def map (g : X ⟶ Y) (hg : g ≫ fY = fX) (y : RelativeSchemeValuedPoint v fX) :
    RelativeSchemeValuedPoint v fY :=
  ⟨SchemeValuedPoint.map g y.1, by
    change SchemeValuedPoint.map fY (SchemeValuedPoint.map g y.1) = SchemeValuedPoint.basePoint v
    rw [← SchemeValuedPoint.map_comp, hg]
    exact y.2⟩

@[simp]
theorem map_coe (g : X ⟶ Y) (hg : g ≫ fY = fX) (y : RelativeSchemeValuedPoint v fX) :
    (map g hg y : SchemeValuedPoint Y) = SchemeValuedPoint.map g y.1 := rfl

@[fun_prop]
theorem continuous_map (g : X ⟶ Y) (hg : g ≫ fY = fX) : Continuous (map (v := v) g hg) :=
  ((SchemeValuedPoint.continuous_map g).comp continuous_subtype_val).subtype_mk _

@[simp]
theorem map_id (y : RelativeSchemeValuedPoint v fX) : map (𝟙 X) (Category.id_comp fX) y = y :=
  Subtype.ext (SchemeValuedPoint.map_id y.1)

theorem map_comp (g : X ⟶ Y) (h : Y ⟶ Z) (hg : g ≫ fY = fX) (hh : h ≫ fZ = fY)
    (y : RelativeSchemeValuedPoint v fX) :
    map (g ≫ h) (by rw [Category.assoc, hh, hg]) y = map h hh (map g hg y) :=
  Subtype.ext (SchemeValuedPoint.map_comp g h y.1)

section Affine

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- Native fixed-base membership on Spec(A) is exactly the original coefficient restriction. -/
theorem mem_affine_relativeLocus_iff (y : SchemeValuedPoint (Spec (CommRingCat.of A))) :
    y ∈ SchemeValuedPoint.relativeLocus v (Spec.map (CommRingCat.ofHom (algebraMap R A))) ↔
      SchemeValuedPoint.spectrumHomeomorph y ∈ relativeLocus v A := by
  change (SchemeValuedPoint.map (Spec.map (CommRingCat.ofHom (algebraMap R A))) y =
    SchemeValuedPoint.basePoint v) ↔ ∀ r : R,
      (SchemeValuedPoint.spectrumHomeomorph y).val (algebraMap R A r) = v r
  constructor
  · intro h r
    have he := congrArg (SchemeValuedPoint.spectrumHomeomorph (A := R)) h
    rw [SchemeValuedPoint.spectrumHomeomorph_map, SchemeValuedPoint.basePoint,
      Homeomorph.apply_symm_apply] at he
    exact congrArg (fun x : Spectrum R => x.val r) he
  · intro h
    apply (SchemeValuedPoint.spectrumHomeomorph (A := R)).injective
    rw [SchemeValuedPoint.spectrumHomeomorph_map, SchemeValuedPoint.basePoint,
      Homeomorph.apply_symm_apply]
    exact Spectrum.ext_val h

/-- The actual native fixed-base affine locus is homeomorphic to the exact relative spectrum. -/
def affineSpectrumHomeomorph :
    RelativeSchemeValuedPoint v (Spec.map (CommRingCat.ofHom (algebraMap R A))) ≃ₜ
      RelativeSpectrum v A :=
  SchemeValuedPoint.spectrumHomeomorph.subtype (fun y => mem_affine_relativeLocus_iff y)

@[simp]
theorem affineSpectrumHomeomorph_apply_coe
    (y : RelativeSchemeValuedPoint v (Spec.map (CommRingCat.ofHom (algebraMap R A)))) :
    (affineSpectrumHomeomorph y : Spectrum A) = SchemeValuedPoint.spectrumHomeomorph y.1 := rfl

@[simp]
theorem affineSpectrumHomeomorph_symm_apply_coe (x : RelativeSpectrum v A) :
    (affineSpectrumHomeomorph.symm x : SchemeValuedPoint (Spec (CommRingCat.of A))) =
      SchemeValuedPoint.spectrumHomeomorph.symm x.1 := rfl

/-- An algebra homomorphism gives the actual commuting diagram of affine scheme structure maps. -/
theorem affineStructureMap_commutes (φ : A →ₐ[R] B) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R A)) =
        Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
  rw [← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext φ.commutes)

/-- The genuine native affine prescribed-base comparison is natural on whole algebra-map points. -/
@[simp]
theorem affineSpectrumHomeomorph_map (φ : A →ₐ[R] B)
    (y : RelativeSchemeValuedPoint v (Spec.map (CommRingCat.ofHom (algebraMap R B)))) :
    affineSpectrumHomeomorph (map (Spec.map (CommRingCat.ofHom φ.toRingHom))
      (affineStructureMap_commutes φ) y) = RelativeSpectrum.comap φ (affineSpectrumHomeomorph y) := by
  apply Subtype.ext
  exact SchemeValuedPoint.spectrumHomeomorph_map φ.toRingHom y.1

end Affine

end RelativeSchemeValuedPoint

/-- Actual native fixed-base point maps form a topological functor on schemes over Spec(R). -/
def relativeSchemeValuedPointFunctor {R : Type u} [CommRing R] (v : Valuation R ℝ≥0) :
    Over (Spec (CommRingCat.of R)) ⥤ TopCat where
  obj X := TopCat.of (RelativeSchemeValuedPoint v X.hom)
  map g := TopCat.ofHom ⟨RelativeSchemeValuedPoint.map g.left g.w,
    RelativeSchemeValuedPoint.continuous_map g.left g.w⟩
  map_id X := by
    apply TopCat.ext
    intro y
    exact Subtype.ext (SchemeValuedPoint.map_id y.1)
  map_comp g h := by
    apply TopCat.ext
    intro y
    exact Subtype.ext (SchemeValuedPoint.map_comp g.left h.left y.1)

namespace SchemeValuedPoint

variable {R : Type u} [CommRing R] {X : Scheme.{u}}

/-- The actual coefficient ring map on local sections, from the structure morphism and genuine restriction. -/
def sectionBaseMap (f : X ⟶ Spec (CommRingCat.of R)) (U : X.Opens) : R →+* Γ(X, U) :=
  (X.presheaf.map (homOfLE le_top).op).hom.comp
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

/-- The named section algebra action induced by the actual coefficient ring map. -/
@[instance_reducible]
def sectionBaseAlgebra (f : X ⟶ Spec (CommRingCat.of R)) (U : X.Opens) : Algebra R Γ(X, U) :=
  (sectionBaseMap f U).toAlgebra

@[simp]
theorem sectionBaseMap_apply (f : X ⟶ Spec (CommRingCat.of R)) (U : X.Opens) (r : R) :
    sectionBaseMap f U r = X.presheaf.map (homOfLE le_top).op
      (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) := rfl

end SchemeValuedPoint

namespace RelativeSchemeValuedPoint

variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}

/-- Every genuine local-section coefficient has exactly its prescribed value at a relative native point. -/
theorem eval_sectionBaseMap (y : RelativeSchemeValuedPoint v f) (U : X.Opens)
    (hy : y.1.point ∈ U) (r : R) :
    SchemeValuedPoint.eval y.1 U hy (SchemeValuedPoint.sectionBaseMap f U r) = v r := by
  have h := congrArg (fun z : SchemeValuedPoint (Spec (CommRingCat.of R)) =>
    SchemeValuedPoint.eval z ⊤ trivial ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) y.2
  rw [SchemeValuedPoint.evalTop_map, SchemeValuedPoint.basePoint_eval] at h
  exact (SchemeValuedPoint.eval_restrict y.1 ⊤ U le_top hy
    (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r))).trans h

/-- Actual local-section evaluation is a genuine relative spectrum point for the derived coefficient action. -/
def sectionSpectrum (y : RelativeSchemeValuedPoint v f) (U : X.Opens) (hy : y.1.point ∈ U) :
    letI := SchemeValuedPoint.sectionBaseAlgebra f U
    RelativeSpectrum v Γ(X, U) := by
  letI := SchemeValuedPoint.sectionBaseAlgebra f U
  refine ⟨Spectrum.ofValuation (y.1.residueVal.comap (X.evaluation U y.1.point hy).hom), ?_⟩
  intro r
  exact eval_sectionBaseMap y U hy r

@[simp]
theorem sectionSpectrum_val_apply (y : RelativeSchemeValuedPoint v f) (U : X.Opens)
    (hy : y.1.point ∈ U) (s : Γ(X, U)) :
    (sectionSpectrum y U hy).1.val s = SchemeValuedPoint.eval y.1 U hy s := rfl

/-- The actual section-spectrum evaluation map is continuous on its genuine local domain. -/
@[fun_prop]
theorem continuous_sectionSpectrum (U : X.Opens) :
    Continuous (fun y : {y : RelativeSchemeValuedPoint v f // y.1.point ∈ U} =>
      sectionSpectrum y.1 U y.2) := by
  let := SchemeValuedPoint.sectionBaseAlgebra f U
  rw [RelativeSpectrum.continuous_iff]
  intro s
  exact (SchemeValuedPoint.continuous_eval U s).comp
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk fun y => y.2)

end RelativeSchemeValuedPoint

end EnvelopeProperty.Berkovich
