import EnvelopeProperty.AlgGeom.DominantFunctionFieldMaps
import EnvelopeProperty.Alterations.Geometry.SegreGluingCoordinates
import Mathlib.RingTheory.KrullDimension.Zero

/-! # Actual open coordinate algebras and the SAME native generic point -/
open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section
universe u
namespace EnvelopeProperty.OpenImmersionGenericCoordinates
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : Spec (.of A) ⟶ X) [IsOpenImmersion f]

private theorem range_appLE_isIso :
    IsIso (f.appLE f.opensRange ⊤ (by intro x _; exact ⟨x, rfl⟩)) := by
  let : IsIso (f.app f.opensRange) := f.isIso_app _ le_rfl
  let h : (⊤ : (Spec (.of A)).Opens) ≤ f ⁻¹ᵁ f.opensRange := by
    intro x _; exact ⟨x, rfl⟩
  have he : homOfLE h = eqToHom (Scheme.Hom.preimage_opensRange f).symm :=
    Subsingleton.elim _ _
  let : IsIso (homOfLE h) := by rw [he]; infer_instance
  change IsIso (f.app f.opensRange ≫ (Spec (.of A)).presheaf.map (homOfLE h).op)
  infer_instance

/-- The WHOLE original open-coordinate algebra, with literal original range. -/
def sectionRingEquiv : A ≃+* Γ(X, f.opensRange) := by
  let h : (⊤ : (Spec (.of A)).Opens) ≤ f ⁻¹ᵁ f.opensRange := by
    intro x _; exact ⟨x, rfl⟩
  let : IsIso (f.appLE f.opensRange ⊤ h) := range_appLE_isIso f
  exact (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv.symm.trans
    (asIso (f.appLE f.opensRange ⊤ h)).commRingCatIsoToRingEquiv.symm

/-- The whole original coordinate map is inverted, with no comparison input. -/
theorem appLE_sectionRingEquiv (a : A) :
    f.appLE f.opensRange ⊤ (by intro x _; exact ⟨x, rfl⟩) (sectionRingEquiv f a) =
      (Scheme.ΓSpecIso (.of A)).inv a := by
  let h : (⊤ : (Spec (.of A)).Opens) ≤ f ⁻¹ᵁ f.opensRange := by
    intro x _; exact ⟨x, rfl⟩
  let : IsIso (f.appLE f.opensRange ⊤ h) := range_appLE_isIso f
  change (asIso (f.appLE f.opensRange ⊤ h)).hom
    ((asIso (f.appLE f.opensRange ⊤ h)).inv ((Scheme.ΓSpecIso (.of A)).inv a)) = _
  exact Iso.inv_hom_id_apply _ _

variable [Nontrivial A] [IsIntegral X]

/-- Every actual nonempty affine chart has a genuinely nonempty whole range. -/
instance range_nonempty : Nonempty f.opensRange := by
  obtain ⟨x⟩ : Nonempty (Spec (.of A)) := inferInstance
  exact ⟨⟨f x, ⟨x, rfl⟩⟩⟩

/-- The SAME original generic point lies in the actual nonempty chart range. -/
theorem genericPoint_mem : genericPoint X ∈ f.opensRange :=
  ((genericPoint_spec X).mem_open_set_iff f.opensRange.isOpen).mpr (by
    obtain ⟨x⟩ : Nonempty f.opensRange := inferInstance
    exact ⟨x.1, trivial, x.property⟩)

private theorem range_genericPointMap :
    Set.range (X.fromSpecStalk (genericPoint X)) ⊆ Set.range f := by
  intro y hy
  have hs : y ⤳ genericPoint X := Scheme.range_fromSpecStalk.le hy
  exact hs.mem_open f.opensRange.isOpen (genericPoint_mem f)

/-- The TRUE generic point morphism factors through the SAME original chart. -/
def genericFactor : Spec X.functionField ⟶ Spec (.of A) :=
  IsOpenImmersion.lift f (X.fromSpecStalk (genericPoint X)) (range_genericPointMap f)

/-- The entire actual generic-point triangle. -/
theorem genericFactor_fac : genericFactor f ≫ f = X.fromSpecStalk (genericPoint X) :=
  IsOpenImmersion.lift_fac f (X.fromSpecStalk (genericPoint X)) (range_genericPointMap f)

/-- The SAME original coordinate as an actual generic germ in the native function field. -/
def genericValue (a : A) : X.functionField :=
  X.germToFunctionField f.opensRange (sectionRingEquiv f a)

private theorem appLE_eq_of_eq {T Z : Scheme.{u}} {q q' : T ⟶ Z}
    (w : q = q') (U : Z.Opens) (V : T.Opens)
    (h : V ≤ q ⁻¹ᵁ U) (h' : V ≤ q' ⁻¹ᵁ U) :
    q.appLE U V h = q'.appLE U V h' := by
  cases w
  rfl

/-- Actual pullback by the TRUE generic factor equals the original generic
germ of the SAME coordinate; no parameter or field comparison certificate. -/
theorem genericFactor_pullRingHom (a : A) :
    (Scheme.ΓSpecIso X.functionField).hom
      (Alterations.Geometry.Segre.pullRingHom (genericFactor f) a) = genericValue f a := by
  let l := genericFactor f
  let g := X.fromSpecStalk (genericPoint X)
  let h : (⊤ : (Spec (.of A)).Opens) ≤ f ⁻¹ᵁ f.opensRange := by
    intro x _; exact ⟨x, rfl⟩
  have hcomp := Scheme.Hom.appLE_comp_appLE l f f.opensRange ⊤ ⊤ h le_top
  have heq : f.appLE f.opensRange ⊤ h ≫ l.appTop =
      g.appLE f.opensRange ⊤ (by
        intro z _
        change g z ∈ f.opensRange
        exact range_genericPointMap f ⟨z, rfl⟩) := by
    change f.appLE f.opensRange ⊤ h ≫ l.appLE ⊤ ⊤ le_top = _
    exact hcomp.trans (appLE_eq_of_eq (genericFactor_fac f) _ _ _ _)
  have ha := ConcreteCategory.congr_hom heq (sectionRingEquiv f a)
  change l.appTop (f.appLE f.opensRange ⊤ h (sectionRingEquiv f a)) = _ at ha
  rw [appLE_sectionRingEquiv] at ha
  have hg : g.appLE f.opensRange ⊤ (by
        intro z _
        exact range_genericPointMap f ⟨z, rfl⟩) =
      X.presheaf.germ f.opensRange (genericPoint X) (genericPoint_mem f) ≫
        (Scheme.ΓSpecIso X.functionField).inv := by
    let W : (Spec X.functionField).Opens := g ⁻¹ᵁ f.opensRange
    have hW : (⊤ : (Spec X.functionField).Opens) ≤ W := by
      intro z _
      exact range_genericPointMap f ⟨z, rfl⟩
    unfold Scheme.Hom.appLE
    rw [Scheme.fromSpecStalk_app (genericPoint_mem f)]
    simp only [Category.assoc, ← Functor.map_comp]
    rw [← Category.assoc]
    suffices (Spec X.functionField).presheaf.map
        ((homOfLE (show W ≤ ⊤ from le_top)).op ≫ (homOfLE hW).op) =
          𝟙 Γ(Spec X.functionField, ⊤) by
      rw [this, Category.comp_id]
    convert (Spec X.functionField).presheaf.map_id (Opposite.op ⊤) using 1
    congr 1
  rw [hg] at ha
  have hv := congrArg (fun s : Γ(Spec X.functionField, ⊤) =>
    (Scheme.ΓSpecIso X.functionField).hom s) ha
  simpa only [genericValue, Scheme.germToFunctionField,
    Alterations.Geometry.Segre.pullRingHom, CommRingCat.hom_comp,
    RingHom.comp_apply, Iso.inv_hom_id_apply] using hv

end EnvelopeProperty.OpenImmersionGenericCoordinates
