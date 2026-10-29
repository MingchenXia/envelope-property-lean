import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-!
# Actual zero-fiber restriction of an ambient chart

An ambient open partial homeomorphism into a product induces a local chart of
its literal zero fiber. This is a topological restriction lemma; the actual
smooth presentation constructs the ambient chart independently.
-/

open Topology

set_option backward.isDefEq.respectTransparency false

namespace ComplexSchemes

noncomputable section

variable {E F G : Type*} [TopologicalSpace E] [TopologicalSpace F]
  [TopologicalSpace G] [Zero F]

/-- Restrict the actual ambient chart and its inverse to their literal zero slices. -/
def zeroFiberHomeomorph (e : OpenPartialHomeomorph E (F × G)) :
    {z : {x : E // (e x).1 = 0} // z.val ∈ e.source} ≃ₜ
      {t : G // (0, t) ∈ e.target} where
  toFun z := ⟨(e z.val.val).2, by
    have hz := e.map_source z.property
    have he : e z.val.val = (0, (e z.val.val).2) := Prod.ext z.val.property rfl
    rwa [he] at hz⟩
  invFun t := ⟨⟨e.symm (0, t.val), by
    exact congrArg Prod.fst (e.right_inv t.property)⟩, e.map_target t.property⟩
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    change e.symm (0, (e z.val.val).2) = z.val.val
    have he : e z.val.val = (0, (e z.val.val).2) := Prod.ext z.val.property rfl
    rw [← he]
    exact e.left_inv z.property
  right_inv t := by
    apply Subtype.ext
    exact congrArg Prod.snd (e.right_inv t.property)
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_iff_continuousAt.mpr
    intro z
    have hv : ContinuousAt
        (fun w : {z : {x : E // (e x).1 = 0} // z.val ∈ e.source} => w.val.val) z :=
      (continuous_subtype_val.comp continuous_subtype_val).continuousAt
    exact ContinuousAt.comp
      (f := fun w : {z : {x : E // (e x).1 = 0} // z.val ∈ e.source} => w.val.val)
      (x := z) (e.continuousAt z.property).snd hv
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply continuous_iff_continuousAt.mpr
    intro t
    have hv : ContinuousAt
        (fun w : {t : G // (0, t) ∈ e.target} => ((0 : F), w.val)) t :=
      (continuous_const.prodMk continuous_subtype_val).continuousAt
    exact ContinuousAt.comp
      (f := fun w : {t : G // (0, t) ∈ e.target} => ((0 : F), w.val))
      (x := t) (e.continuousAt_symm t.property) hv

/-- The source is open in the literal zero fiber, even when that fiber is not ambient-open. -/
def zeroFiberSource (e : OpenPartialHomeomorph E (F × G)) :
    TopologicalSpace.Opens {x : E // (e x).1 = 0} :=
  ⟨Subtype.val ⁻¹' e.source, e.open_source.preimage continuous_subtype_val⟩

/-- The actual zero slice of the ambient target is open in the free-coordinate space. -/
def zeroFiberTarget (e : OpenPartialHomeomorph E (F × G)) : TopologicalSpace.Opens G :=
  ⟨(fun t : G => ((0 : F), t)) ⁻¹' e.target,
    e.open_target.preimage (continuous_const.prodMk continuous_id)⟩

/-- A genuine point in the fiber supplies the native nonempty chart inclusions. -/
def zeroFiberOpenPartialHomeomorph (e : OpenPartialHomeomorph E (F × G)) (a : E)
    (ha : a ∈ e.source) (h0 : (e a).1 = 0) :
    OpenPartialHomeomorph {x : E // (e x).1 = 0} G := by
  have hU : Nonempty (zeroFiberSource e) := ⟨⟨⟨a, h0⟩, ha⟩⟩
  have hV : Nonempty (zeroFiberTarget e) := by
    refine ⟨⟨(e a).2, ?_⟩⟩
    have hm := e.map_source ha
    have he : e a = (0, (e a).2) := Prod.ext h0 rfl
    change ((0 : F), (e a).2) ∈ e.target
    rw [← he]
    exact hm
  let H : zeroFiberSource e ≃ₜ zeroFiberTarget e := zeroFiberHomeomorph e
  exact ((zeroFiberSource e).openPartialHomeomorphSubtypeCoe hU).symm.trans
    (H.toOpenPartialHomeomorph.trans
      ((zeroFiberTarget e).openPartialHomeomorphSubtypeCoe hV))

@[simp]
theorem zeroFiberOpenPartialHomeomorph_source (e : OpenPartialHomeomorph E (F × G)) (a : E)
    (ha : a ∈ e.source) (h0 : (e a).1 = 0) :
    (zeroFiberOpenPartialHomeomorph e a ha h0).source = Subtype.val ⁻¹' e.source := by
  simp [zeroFiberOpenPartialHomeomorph, zeroFiberSource]

@[simp]
theorem zeroFiberOpenPartialHomeomorph_target (e : OpenPartialHomeomorph E (F × G)) (a : E)
    (ha : a ∈ e.source) (h0 : (e a).1 = 0) :
    (zeroFiberOpenPartialHomeomorph e a ha h0).target =
      (fun t : G => ((0 : F), t)) ⁻¹' e.target := by
  simp [zeroFiberOpenPartialHomeomorph, zeroFiberTarget]

/-- On its genuine source the zero-fiber chart reads exactly the free coordinate. -/
theorem zeroFiberOpenPartialHomeomorph_apply (e : OpenPartialHomeomorph E (F × G)) (a : E)
    (ha : a ∈ e.source) (h0 : (e a).1 = 0)
    (z : {x : E // (e x).1 = 0}) (hz : z.val ∈ e.source) :
    zeroFiberOpenPartialHomeomorph e a ha h0 z = (e z.val).2 := by
  let U := zeroFiberSource e
  have hU : Nonempty U := ⟨⟨⟨a, h0⟩, ha⟩⟩
  change (e (((U.openPartialHomeomorphSubtypeCoe hU).symm z).val).val).2 = (e z.val).2
  have hu : ((U.openPartialHomeomorphSubtypeCoe hU).symm z).val = z := by
    apply (U.openPartialHomeomorphSubtypeCoe hU).right_inv
    simpa [U, zeroFiberSource] using hz
  rw [hu]

/-- On its genuine target the inverse is the actual ambient inverse at the zero slice. -/
theorem zeroFiberOpenPartialHomeomorph_symm_apply (e : OpenPartialHomeomorph E (F × G)) (a : E)
    (ha : a ∈ e.source) (h0 : (e a).1 = 0) (t : G) (ht : (0, t) ∈ e.target) :
    ((zeroFiberOpenPartialHomeomorph e a ha h0).symm t).val = e.symm (0, t) := by
  let V := zeroFiberTarget e
  have hV : Nonempty V := by
    refine ⟨⟨(e a).2, ?_⟩⟩
    have he : e a = (0, (e a).2) := Prod.ext h0 rfl
    change (0, (e a).2) ∈ e.target
    rw [← he]
    exact e.map_source ha
  change e.symm (0, ((V.openPartialHomeomorphSubtypeCoe hV).symm t).val) = e.symm (0, t)
  have hv : ((V.openPartialHomeomorphSubtypeCoe hV).symm t).val = t := by
    apply (V.openPartialHomeomorphSubtypeCoe hV).right_inv
    simpa [V, zeroFiberTarget] using ht
  rw [hv]

end

end ComplexSchemes
