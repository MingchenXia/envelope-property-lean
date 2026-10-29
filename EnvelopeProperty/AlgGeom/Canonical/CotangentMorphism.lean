import EnvelopeProperty.AlgGeom.Canonical.CotangentSheaf

/-!
# Relative differentials of arbitrary actual scheme morphisms

The map on cotangent sheaves is constructed from the literal structure
presheaf map, relative universal derivations, and sheafification.
-/

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

namespace EnvelopeProperty.CanonicalGeometry

universe u
noncomputable section

variable {K : Type u} [Field K] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (g : Y ⟶ X)

/-- Actual structural constants commute with the ring maps of every morphism. -/
theorem schemeMorphism_constantSquare (U : X.Opens) :
    (schemeConstantPresheafMap f).app (.op U) ≫ g.app U =
      (schemeConstantPresheafMap (g ≫ f)).app (.op (g ⁻¹ᵁ U)) := by
  have htop : g.appLE ⊤ ⊤ (by simp) = g.appTop := by
    unfold Scheme.Hom.appLE
    change g.appTop ≫ Y.presheaf.map (𝟙 (op ⊤)) = g.appTop
    simp
  have hu : g.appLE U (g ⁻¹ᵁ U) le_rfl = g.app U := by
    unfold Scheme.Hom.appLE
    simp
  have hm : X.presheaf.map U.leTop.op ≫ g.app U =
      g.appTop ≫ Y.presheaf.map (g ⁻¹ᵁ U).leTop.op := by
    rw [← hu]
    exact ((g.map_appLE le_rfl U.leTop.op).trans
      (g.appLE_map (U := ⊤) (V := ⊤) (by simp)
        (g ⁻¹ᵁ U).leTop.op).symm).trans
      (congrArg (fun h ↦ h ≫ Y.presheaf.map (g ⁻¹ᵁ U).leTop.op) htop)
  change ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫
    X.presheaf.map U.leTop.op) ≫ g.app U =
      (Scheme.ΓSpecIso (.of K)).inv ≫ (g ≫ f).appTop ≫
        Y.presheaf.map (g ⁻¹ᵁ U).leTop.op
  rw [Scheme.Hom.comp_appTop]
  simp only [Category.assoc]
  rw [hm]

set_option backward.isDefEq.respectTransparency false in
/-- Differentiating actual pullbacks of regular functions gives a relative
presheaf derivation into the actual pushed cotangent presheaf. -/
def cotangentMorphismDerivation :
    ((PresheafOfModules.pushforward
      g.toRingCatSheafHom.hom).obj
        (cotangentPresheaf (g ≫ f))).Derivation' (schemeConstantPresheafMap f) where
  d {U} := (cotangentPresheafDerivation (g ≫ f)).d.comp (g.app U.unop).hom.toAddMonoidHom
  d_mul {U} a b := by
    change (cotangentPresheafDerivation (g ≫ f)).d (g.app U.unop (a * b)) = _
    rw [map_mul, (cotangentPresheafDerivation (g ≫ f)).d_mul]
    rfl
  d_map {U V} i a := by
    change (cotangentPresheafDerivation (g ≫ f)).d
      (g.app V.unop (X.presheaf.map i a)) = _
    have h : g.app V.unop (X.presheaf.map i a) =
        Y.presheaf.map ((Opens.map g.base).op.map i) (g.app U.unop a) :=
      congr($(g.c.naturality i).hom a)
    exact (congrArg (cotangentPresheafDerivation (g ≫ f)).d h).trans
      ((cotangentPresheafDerivation (g ≫ f)).d_map
        ((Opens.map g.base).op.map i) (g.app U.unop a))
  d_app {U} a := by
    change (cotangentPresheafDerivation (g ≫ f)).d
      (g.app U.unop ((schemeConstantPresheafMap f).app U a)) = 0
    have h : g.app U.unop ((schemeConstantPresheafMap f).app U a) =
        (schemeConstantPresheafMap (g ≫ f)).app (.op (g ⁻¹ᵁ U.unop)) a :=
      congr($(schemeMorphism_constantSquare f g U.unop).hom a)
    exact (congrArg (cotangentPresheafDerivation (g ≫ f)).d h).trans
      ((cotangentPresheafDerivation (g ≫ f)).d_app a)

/-- The actual raw cotangent morphism for an arbitrary scheme morphism. -/
def cotangentPresheafMorphism : cotangentPresheaf f ⟶
    (PresheafOfModules.pushforward
      g.toRingCatSheafHom.hom).obj
        (cotangentPresheaf (g ≫ f)) :=
  (cotangentPresheafHomEquiv f _).symm (cotangentMorphismDerivation f g)

set_option backward.isDefEq.respectTransparency false in
/-- The raw morphism carries each actual differential to the differential
of its actual regular-function pullback. -/
theorem cotangentPresheafMorphism_d (U : X.Opens) (a : Γ(X, U)) :
    (cotangentPresheafMorphism f g).app (.op U) ((cotangentPresheafDerivation f).d a) =
      (cotangentPresheafDerivation (g ≫ f)).d (g.app U a) := by
  have h := (cotangentPresheafUniversal f).fac (cotangentMorphismDerivation f g)
  exact PresheafOfModules.Derivation.congr_d h a

set_option backward.isDefEq.respectTransparency false in
/-- The actual cotangent sheaf map into the actual pushed sheaf, obtained
from the genuine raw differential map and the target sheafification unit. -/
def cotangentSheafMorphism : cotangentSheaf f ⟶
    (Scheme.Modules.pushforward g).obj (cotangentSheaf (g ≫ f)) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)
    (P := cotangentPresheaf f)
    (F := (Scheme.Modules.pushforward g).obj (cotangentSheaf (g ≫ f)))).symm
    (cotangentPresheafMorphism f g ≫
      (PresheafOfModules.pushforward
        g.toRingCatSheafHom.hom).map
          (X := cotangentPresheaf (g ≫ f))
          (Y := (cotangentSheaf (g ≫ f)).val)
          (cotangentSheafificationMap (g ≫ f)))

set_option backward.isDefEq.respectTransparency false in
/-- The actual sheaf map retains precisely the raw differential map through
both actual sheafification units. -/
theorem cotangentSheafMorphism_unit :
    cotangentSheafificationMap f ≫ (cotangentSheafMorphism f g).val =
      cotangentPresheafMorphism f g ≫
        (PresheafOfModules.pushforward
          g.toRingCatSheafHom.hom).map
            (X := cotangentPresheaf (g ≫ f))
            (Y := (cotangentSheaf (g ≫ f)).val)
            (cotangentSheafificationMap (g ≫ f)) := by
  exact (PresheafOfModules.sheafificationHomEquiv
    (𝟙 X.ringCatSheaf.obj)).apply_symm_apply _

set_option backward.isDefEq.respectTransparency.types false in
/-- The relative differential map on genuine sheaf pullbacks, adjoint to
the genuine map into the pushed cotangent sheaf. -/
def cotangentSheafPullbackMap :
    (Scheme.Modules.pullback g).obj (cotangentSheaf f) ⟶ cotangentSheaf (g ≫ f) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).symm
    (cotangentSheafMorphism f g)

end
end EnvelopeProperty.CanonicalGeometry
