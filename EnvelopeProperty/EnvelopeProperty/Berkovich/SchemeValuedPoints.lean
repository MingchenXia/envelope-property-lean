/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SpectrumValuedPoints
import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Valued points of actual Mathlib schemes

A native valued point is an actual scheme point with a real ultrametric valuation
on its stalk residue field. Genuine local sections give evaluations, and genuine
scheme residue-field maps give functorial point maps.

The topology is generated independently by support opens and actual local-section
evaluation opens. Scheme morphisms induce a topological functor with a natural
continuous support projection. On Spec(A), the actual residue-field isomorphism
gives a homeomorphism with valued prime points and the general seminorm spectrum;
reverse continuity uses genuine local fraction presentations of sections.

These are point-space results. No analytic structure sheaf, coherent-sheaf gluing,
or universal scheme analytification property is asserted. Arbitrary schemes,
including nonseparated schemes, are allowed; no general Hausdorff claim is made.
-/

open scoped NNReal Topology
open Topology CategoryTheory AlgebraicGeometry Opposite

universe u

noncomputable section

namespace EnvelopeProperty.Berkovich

structure SchemeValuedPoint (X : Scheme) where
  point : X
  residueVal : Valuation (X.residueField point) ℝ≥0

namespace SchemeValuedPoint

variable {X Y Z : Scheme}

/-- Evaluation of an actual scheme section in the valued stalk residue field. -/
def eval (y : SchemeValuedPoint X) (U : X.Opens) (hy : y.point ∈ U) (s : Γ(X, U)) : ℝ≥0 :=
  y.residueVal (X.evaluation U y.point hy s)

/-- Genuine section evaluation respects products. -/
@[simp]
theorem eval_mul (y : SchemeValuedPoint X) (U : X.Opens) (hy : y.point ∈ U)
    (s t : Γ(X, U)) : eval y U hy (s * t) = eval y U hy s * eval y U hy t :=
  (y.residueVal.comap (X.evaluation U y.point hy).hom).map_mul s t

@[simp]
theorem eval_eq_zero_iff (y : SchemeValuedPoint X) (U : X.Opens) (hy : y.point ∈ U)
    (s : Γ(X, U)) : eval y U hy s = 0 ↔ y.point ∉ X.basicOpen s := by
  rw [eval, Valuation.zero_iff, Scheme.evaluation_eq_zero_iff_notMem_basicOpen]

/-- Genuine restriction of a section does not change its residue-field value. -/
theorem eval_restrict (y : SchemeValuedPoint X) (U V : X.Opens) (i : V ≤ U)
    (hy : y.point ∈ V) (s : Γ(X, U)) :
    eval y V hy (X.presheaf.map (homOfLE i).op s) = eval y U (i hy) s := by
  exact congrArg (fun a => y.residueVal (X.residue y.point a))
    (X.presheaf.germ_res_apply (homOfLE i) y.point hy s)

/-- Native pullback uses the actual residue-field homomorphism of a scheme morphism. -/
def map (f : X ⟶ Y) (y : SchemeValuedPoint X) : SchemeValuedPoint Y :=
  ⟨f y.point, y.residueVal.comap (f.residueFieldMap y.point).hom⟩

@[simp]
theorem map_point (f : X ⟶ Y) (y : SchemeValuedPoint X) : (map f y).point = f y.point := rfl

@[simp]
theorem eval_map (f : X ⟶ Y) (y : SchemeValuedPoint X) (U : Y.Opens)
    (hy : f y.point ∈ U) (s : Γ(Y, U)) :
    eval (map f y) U hy s = eval y (f ⁻¹ᵁ U) hy (f.app U s) := by
  change y.residueVal (f.residueFieldMap y.point (Y.evaluation U (f y.point) hy s)) = _
  exact congrArg y.residueVal (Scheme.evaluation_naturality_apply f y.point hy s)

/-- Global section evaluation also obeys the actual scheme evaluation naturality law. -/
@[simp]
theorem evalTop_map (f : X ⟶ Y) (y : SchemeValuedPoint X) (s : Γ(Y, ⊤)) :
    eval (map f y) ⊤ trivial s = eval y ⊤ trivial (f.appTop s) :=
  congrArg y.residueVal (Scheme.Γevaluation_naturality_apply f y.point s)

@[simp]
theorem map_id (y : SchemeValuedPoint X) : map (𝟙 X) y = y := by
  rcases y with ⟨x, v⟩
  dsimp [map]
  rw [Scheme.residueFieldMap_id]
  apply congrArg (SchemeValuedPoint.mk x)
  exact _root_.Valuation.ext fun _ => rfl

theorem map_comp (f : X ⟶ Y) (g : Y ⟶ Z) (y : SchemeValuedPoint X) :
    map (f ≫ g) y = map g (map f y) := by
  rcases y with ⟨x, v⟩
  dsimp [map]
  rw [Scheme.residueFieldMap_comp]
  apply congrArg (SchemeValuedPoint.mk (g (f x)))
  exact _root_.Valuation.ext fun _ => rfl

/-- A local section evaluation inverse image, restricted to its genuine section domain. -/
def sectionOpen (U : X.Opens) (s : Γ(X, U)) (V : Set ℝ≥0) : Set (SchemeValuedPoint X) :=
  {y | ∃ hy : y.point ∈ U, eval y U hy s ∈ V}

/-- Support opens and actual local-section evaluation opens generate the native point topology. -/
def topologyGenerators (X : Scheme) : Set (Set (SchemeValuedPoint X)) :=
  {W | (∃ U : X.Opens, W = (fun y => y.point) ⁻¹' U) ∨
    ∃ (U : X.Opens) (s : Γ(X, U)) (V : Set ℝ≥0), IsOpen V ∧ W = sectionOpen U s V}

instance : TopologicalSpace (SchemeValuedPoint X) :=
  TopologicalSpace.generateFrom (topologyGenerators X)

theorem isOpen_point_preimage (U : X.Opens) :
    IsOpen ((fun y : SchemeValuedPoint X => y.point) ⁻¹' U) :=
  TopologicalSpace.isOpen_generateFrom_of_mem (Or.inl ⟨U, rfl⟩)

theorem isOpen_sectionOpen (U : X.Opens) (s : Γ(X, U)) (V : Set ℝ≥0) (hV : IsOpen V) :
    IsOpen (sectionOpen U s V) :=
  TopologicalSpace.isOpen_generateFrom_of_mem (Or.inr ⟨U, s, V, hV, rfl⟩)

@[fun_prop]
theorem continuous_point : Continuous (fun y : SchemeValuedPoint X => y.point) := by
  apply continuous_def.2
  intro U hU
  exact isOpen_point_preimage ⟨U, hU⟩

/-- Genuine section evaluation is continuous on the open domain where the section is defined. -/
@[fun_prop]
theorem continuous_eval (U : X.Opens) (s : Γ(X, U)) :
    Continuous (fun y : {y : SchemeValuedPoint X // y.point ∈ U} => eval y.1 U y.2 s) := by
  apply continuous_def.2
  intro V hV
  have h : (fun y : {y : SchemeValuedPoint X // y.point ∈ U} => eval y.1 U y.2 s) ⁻¹' V =
      Subtype.val ⁻¹' sectionOpen U s V := by
    ext y
    simp only [Set.mem_preimage, sectionOpen, Set.mem_ofPred_eq]
    exact ⟨fun hy => ⟨y.2, hy⟩, fun ⟨_, hy⟩ => hy⟩
  rw [h]
  exact (isOpen_sectionOpen U s V hV).preimage continuous_subtype_val

/-- Every scheme morphism induces a continuous native valued-point map. -/
@[fun_prop]
theorem continuous_map (f : X ⟶ Y) : Continuous (map f) := by
  apply continuous_generateFrom_iff.2
  intro W hW
  rcases hW with ⟨U, rfl⟩ | ⟨U, s, V, hV, rfl⟩
  · exact isOpen_point_preimage (f ⁻¹ᵁ U)
  · have h : map f ⁻¹' sectionOpen U s V = sectionOpen (f ⁻¹ᵁ U) (f.app U s) V := by
      ext y
      simp only [Set.mem_preimage, sectionOpen, Set.mem_ofPred_eq, map_point, eval_map]
      rfl
    rw [h]
    exact isOpen_sectionOpen _ _ _ hV

section Affine

set_option backward.isDefEq.respectTransparency.types false

variable {A : Type u} [CommRing A]

local instance (U : (Spec (CommRingCat.of A)).Opens) :
    Algebra A Γ(Spec (CommRingCat.of A), U) :=
  inferInstanceAs (Algebra A (StructureSheaf.sectionsSubalgebra A U))

/-- Convert the native residue field of Spec(A) through its genuine residue-field isomorphism. -/
def toValuedPoint (y : SchemeValuedPoint (Spec (CommRingCat.of A))) : ValuedPoint A :=
  ⟨y.point, y.residueVal.comap (Scheme.Spec.residueFieldIso (CommRingCat.of A) y.point).inv.hom⟩

/-- The inverse uses the forward genuine residue-field isomorphism of Spec(A). -/
def ofValuedPoint (y : ValuedPoint A) : SchemeValuedPoint (Spec (CommRingCat.of A)) :=
  ⟨y.prime, y.residueVal.comap (Scheme.Spec.residueFieldIso (CommRingCat.of A) y.prime).hom.hom⟩

@[simp]
theorem toValuedPoint_prime (y : SchemeValuedPoint (Spec (CommRingCat.of A))) :
    (toValuedPoint y).prime = y.point := rfl

@[simp]
theorem ofValuedPoint_point (y : ValuedPoint A) : (ofValuedPoint y).point = y.prime := rfl

@[simp]
theorem toValuedPoint_ofValuedPoint (y : ValuedPoint A) : toValuedPoint (ofValuedPoint y) = y := by
  rcases y with ⟨p, v⟩
  dsimp [toValuedPoint, ofValuedPoint]
  apply congrArg (ValuedPoint.mk p)
  apply _root_.Valuation.ext
  intro a
  change v ((Scheme.Spec.residueFieldIso (CommRingCat.of A) p).hom ((Scheme.Spec.residueFieldIso (CommRingCat.of A) p).inv a)) = v a
  simp

@[simp]
theorem ofValuedPoint_toValuedPoint (y : SchemeValuedPoint (Spec (CommRingCat.of A))) :
    ofValuedPoint (toValuedPoint y) = y := by
  rcases y with ⟨p, v⟩
  dsimp [toValuedPoint, ofValuedPoint]
  apply congrArg (SchemeValuedPoint.mk p)
  apply _root_.Valuation.ext
  intro a
  change v ((Scheme.Spec.residueFieldIso (CommRingCat.of A) p).inv ((Scheme.Spec.residueFieldIso (CommRingCat.of A) p).hom a)) = v a
  simp

/-- Native affine valued points are actually equivalent to algebraic residue-field points. -/
def valuedPointEquiv : SchemeValuedPoint (Spec (CommRingCat.of A)) ≃ ValuedPoint A where
  toFun := toValuedPoint
  invFun := ofValuedPoint
  left_inv := ofValuedPoint_toValuedPoint
  right_inv := toValuedPoint_ofValuedPoint

/-- The value of an original-ring element equals the value of its genuine global section. -/
theorem toValuedPoint_eval (y : SchemeValuedPoint (Spec (CommRingCat.of A))) (a : A) :
    ValuedPoint.eval (toValuedPoint y) a =
      eval y ⊤ trivial ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) := by
  have h := Scheme.Spec.algebraMap_residueFieldIso_inv (CommRingCat.of A) y.point
  exact congrArg y.residueVal (congrArg (fun f => f a) h)

/-- Original-ring evaluation is continuous on native affine valued points. -/
@[fun_prop]
theorem continuous_toValuedPoint :
    Continuous (toValuedPoint : SchemeValuedPoint (Spec (CommRingCat.of A)) → ValuedPoint A) := by
  rw [ValuedPoint.continuous_iff]
  intro a
  have h := (continuous_eval ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)).comp
    (continuous_id.subtype_mk fun _ => trivial)
  simpa only [toValuedPoint_eval, Function.comp_def, id_eq] using h

/-- Ring elements interpreted as genuine sections preserve their original values. -/
theorem ofValuedPoint_eval_algebraMap (y : ValuedPoint A)
    (U : (Spec (CommRingCat.of A)).Opens) (hy : y.prime ∈ U) (a : A) :
    eval (ofValuedPoint y) U hy (algebraMap A Γ(Spec (CommRingCat.of A), U) a) =
      ValuedPoint.eval y a := by
  have h := congrArg (fun f => f a) (Scheme.toOpen_eq (CommRingCat.of A) U)
  change algebraMap A Γ(Spec (CommRingCat.of A), U) a = _ at h
  rw [h]
  exact (eval_restrict (ofValuedPoint y) ⊤ U le_top hy
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)).trans (by
      simpa only [toValuedPoint_ofValuedPoint] using (toValuedPoint_eval (ofValuedPoint y) a).symm)

/-- On a genuine affine basic open, a constant fraction has the actual ratio value. -/
theorem ofValuedPoint_eval_const (y : ValuedPoint A) (a f : A)
    (hy : y.prime ∈ PrimeSpectrum.basicOpen f) :
    eval (ofValuedPoint y) (PrimeSpectrum.basicOpen f) hy
      (StructureSheaf.const a f _ le_rfl) = ValuedPoint.eval y a / ValuedPoint.eval y f := by
  have hf : ValuedPoint.eval y f ≠ 0 := fun h => hy ((ValuedPoint.eval_eq_zero_iff y f).1 h)
  apply (eq_div_iff hf).2
  have h := StructureSheaf.const_mul_cancel' a f 1 (PrimeSpectrum.basicOpen f) le_rfl
    (by rw [PrimeSpectrum.basicOpen_one]; exact le_top)
  have hn := (eval_mul (ofValuedPoint y) (PrimeSpectrum.basicOpen f) hy
    (StructureSheaf.const f 1 _ (by rw [PrimeSpectrum.basicOpen_one]; exact le_top))
    (StructureSheaf.const a f _ le_rfl)).symm.trans
      (congrArg (eval (ofValuedPoint y) (PrimeSpectrum.basicOpen f) hy) h)
  change eval (ofValuedPoint y) _ hy (algebraMap A _ f) *
    eval (ofValuedPoint y) _ hy (StructureSheaf.const a f _ le_rfl) =
    eval (ofValuedPoint y) _ hy (algebraMap A _ a) at hn
  rw [ofValuedPoint_eval_algebraMap, ofValuedPoint_eval_algebraMap, mul_comm] at hn
  exact hn

/-- A genuine local fraction presentation determines evaluation on the original open. -/
theorem ofValuedPoint_eval_of_const (y : ValuedPoint A)
    (U : (Spec (CommRingCat.of A)).Opens) (s : Γ(Spec (CommRingCat.of A), U)) (a f : A)
    (i : PrimeSpectrum.basicOpen f ≤ U)
    (hs : (StructureSheaf.const a f _ le_rfl : Γ(Spec (CommRingCat.of A), PrimeSpectrum.basicOpen f)) =
      (Spec (CommRingCat.of A)).presheaf.map (homOfLE i).op s)
    (hy : y.prime ∈ PrimeSpectrum.basicOpen f) :
    eval (ofValuedPoint y) U (i hy) s = ValuedPoint.eval y a / ValuedPoint.eval y f := by
  calc
    _ = eval (ofValuedPoint y) (PrimeSpectrum.basicOpen f) hy
        ((Spec (CommRingCat.of A)).presheaf.map (homOfLE i).op s) :=
      (eval_restrict (ofValuedPoint y) U _ i hy s).symm
    _ = eval (ofValuedPoint y) (PrimeSpectrum.basicOpen f) hy (StructureSheaf.const a f _ le_rfl) :=
      congrArg (eval (ofValuedPoint y) (PrimeSpectrum.basicOpen f) hy) hs.symm
    _ = _ := ofValuedPoint_eval_const y a f hy

/-- Actual affine local fraction presentations prove continuity of the inverse point comparison. -/
@[fun_prop]
theorem continuous_ofValuedPoint :
    Continuous (ofValuedPoint : ValuedPoint A → SchemeValuedPoint (Spec (CommRingCat.of A))) := by
  apply continuous_generateFrom_iff.2
  intro W hW
  rcases hW with ⟨U, rfl⟩ | ⟨U, s, V, hV, rfl⟩
  · exact U.isOpen.preimage ValuedPoint.continuous_prime
  · apply isOpen_iff_mem_nhds.2
    intro y hy
    change ∃ hy : y.prime ∈ U, eval (ofValuedPoint y) U hy s ∈ V at hy
    obtain ⟨hyU, hyV⟩ := hy
    obtain ⟨f, hyf, i, a, hs⟩ := StructureSheaf.exists_const U s y.prime hyU
    have hs' : (StructureSheaf.const a f _ le_rfl :
        Γ(Spec (CommRingCat.of A), PrimeSpectrum.basicOpen f)) =
        (Spec (CommRingCat.of A)).presheaf.map (homOfLE i).op s := hs
    have hf : ValuedPoint.eval y f ≠ 0 := fun h => hyf ((ValuedPoint.eval_eq_zero_iff y f).1 h)
    have hcont : ContinuousAt (fun z : ValuedPoint A => ValuedPoint.eval z a / ValuedPoint.eval z f) y :=
      (ValuedPoint.continuous_eval a).continuousAt.div
        (ValuedPoint.continuous_eval f).continuousAt hf
    have hyRatio : ValuedPoint.eval y a / ValuedPoint.eval y f ∈ V := by
      rwa [ofValuedPoint_eval_of_const y U s a f i hs' hyf] at hyV
    have hN₁ : (fun z : ValuedPoint A => z.prime) ⁻¹' PrimeSpectrum.basicOpen f ∈ 𝓝 y :=
      ((PrimeSpectrum.basicOpen f).isOpen.preimage ValuedPoint.continuous_prime).mem_nhds hyf
    have hN₂ : (fun z : ValuedPoint A => ValuedPoint.eval z a / ValuedPoint.eval z f) ⁻¹' V ∈ 𝓝 y :=
      hcont (hV.mem_nhds hyRatio)
    apply Filter.mem_of_superset (Filter.inter_mem hN₁ hN₂)
    intro z hz
    change ∃ hz : z.prime ∈ U, eval (ofValuedPoint z) U hz s ∈ V
    refine ⟨i hz.1, ?_⟩
    rw [ofValuedPoint_eval_of_const z U s a f i hs' hz.1]
    exact hz.2

/-- Native affine points with actual local-section topology are homeomorphic to valued residue fields. -/
def valuedPointHomeomorph : SchemeValuedPoint (Spec (CommRingCat.of A)) ≃ₜ ValuedPoint A where
  __ := valuedPointEquiv
  continuous_toFun := continuous_toValuedPoint
  continuous_invFun := continuous_ofValuedPoint

/-- The native affine point space is genuinely homeomorphic to the original-ring seminorm spectrum. -/
def spectrumHomeomorph : SchemeValuedPoint (Spec (CommRingCat.of A)) ≃ₜ Spectrum A :=
  valuedPointHomeomorph.trans ValuedPoint.spectrumHomeomorph

/-- The affine equivalence is natural for actual Spec maps of ring homomorphisms. -/
@[simp]
theorem toValuedPoint_map {B : Type u} [CommRing B] (φ : A →+* B)
    (y : SchemeValuedPoint (Spec (CommRingCat.of B))) :
    toValuedPoint (map (Spec.map (CommRingCat.ofHom φ)) y) =
      ValuedPoint.comap φ (toValuedPoint y) := by
  apply ValuedPoint.toSpectrum_injective
  apply Spectrum.ext_val
  intro a
  change ValuedPoint.eval (toValuedPoint (map (Spec.map (CommRingCat.ofHom φ)) y)) a =
    ValuedPoint.eval (ValuedPoint.comap φ (toValuedPoint y)) a
  rw [toValuedPoint_eval, ValuedPoint.eval_comap, toValuedPoint_eval, evalTop_map]
  have h := congrArg (fun f => f a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  exact congrArg (eval y ⊤ trivial) h.symm

/-- The native affine homeomorphism preserves whole-point RingHom pullback. -/
@[simp]
theorem spectrumHomeomorph_map {B : Type u} [CommRing B] (φ : A →+* B)
    (y : SchemeValuedPoint (Spec (CommRingCat.of B))) :
    spectrumHomeomorph (map (Spec.map (CommRingCat.ofHom φ)) y) =
      Spectrum.comap φ (spectrumHomeomorph y) :=
  congrArg ValuedPoint.toSpectrum (toValuedPoint_map φ y) |>.trans
    (ValuedPoint.toSpectrum_comap φ (toValuedPoint y))

end Affine

end SchemeValuedPoint

/-- Native valued scheme points with genuine section topology form an actual topological functor. -/
def schemeValuedPointFunctor : Scheme ⥤ TopCat where
  obj X := TopCat.of (SchemeValuedPoint X)
  map f := TopCat.ofHom ⟨SchemeValuedPoint.map f, SchemeValuedPoint.continuous_map f⟩
  map_id X := by
    ext y
    exact SchemeValuedPoint.map_id y
  map_comp f g := by
    ext y
    exact SchemeValuedPoint.map_comp f g y

/-- The point support projection is a natural continuous map to the underlying scheme topology. -/
def schemeValuedPointProjection : schemeValuedPointFunctor ⟶ Scheme.forgetToTop where
  app X := TopCat.ofHom ⟨SchemeValuedPoint.point, SchemeValuedPoint.continuous_point⟩
  naturality := by
    intro X Y f
    ext y
    rfl

end EnvelopeProperty.Berkovich
