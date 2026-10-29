import EnvelopeProperty.AlgGeom.Canonical.CotangentMorphism
import EnvelopeProperty.AlgGeom.Canonical.ExteriorSheaf

/-!
# Exterior differentials of arbitrary actual scheme morphisms

Every component is induced by the actual cotangent semilinear map, and
naturality is proved on the genuine spanning exterior products.
-/

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

namespace EnvelopeProperty.CanonicalGeometry

universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {K : Type u} [Field K] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (g : Y ⟶ X)

@[instance_reducible]
private def exteriorMorphismSourceModule (U : X.Opensᵒᵖ) : Module (X.presheaf.obj U)
    ((cotangentPresheaf f).obj U) := ((cotangentPresheaf f).obj U).isModule

@[instance_reducible]
private def exteriorMorphismTargetModule (U : Y.Opensᵒᵖ) : Module (Y.presheaf.obj U)
    ((cotangentPresheaf (g ≫ f)).obj U) := ((cotangentPresheaf (g ≫ f)).obj U).isModule

attribute [local instance] exteriorMorphismSourceModule exteriorMorphismTargetModule

/-- The genuine arbitrary-morphism cotangent component, with its actual
coefficient-changing semilinearity. -/
def cotangentMorphismSemilinear (U : X.Opensᵒᵖ) :
    (cotangentPresheaf f).obj U →ₛₗ[(g.app U.unop).hom]
      (cotangentPresheaf (g ≫ f)).obj ((Opens.map g.base).op.obj U) where
  toFun := (cotangentPresheafMorphism f g).app U
  map_add' := ((cotangentPresheafMorphism f g).app U).hom.map_add
  map_smul' a x := ((cotangentPresheafMorphism f g).app U).hom.map_smul a x

/-- The literal exterior component over the actual structure ring map. -/
def exteriorCotangentMorphismComponent (n : ℕ) (U : X.Opensᵒᵖ) :
    (exteriorCotangentPresheaf f n).obj U ⟶
      ((PresheafOfModules.pushforward
        g.toRingCatSheafHom.hom).obj
          (exteriorCotangentPresheaf (g ≫ f) n)).obj U := by
  let E := exteriorSemilinearMap (g.app U.unop).hom
    (cotangentMorphismSemilinear f g U) n
  exact ModuleCat.ofHom
    (X := (exteriorCotangentPresheaf f n).obj U)
    (Y := ((PresheafOfModules.pushforward
      g.toRingCatSheafHom.hom).obj
        (exteriorCotangentPresheaf (g ≫ f) n)).obj U)
    { toFun := E, map_add' := E.map_add, map_smul' := E.map_smulₛₗ }

/-- The actual exterior component carries pure products to pure products
of their actual cotangent images. -/
theorem exteriorCotangentMorphismComponent_wedge (n : ℕ) (U : X.Opensᵒᵖ)
    (m : Fin n → (cotangentPresheaf f).obj U) :
    exteriorCotangentMorphismComponent f g n U
        (exteriorPower.ιMulti (X.presheaf.obj U) n m) =
      exteriorPower.ιMulti (Y.presheaf.obj ((Opens.map g.base).op.obj U)) n
        (M := (cotangentPresheaf (g ≫ f)).obj ((Opens.map g.base).op.obj U))
        (fun j ↦ cotangentMorphismSemilinear f g U (m j)) :=
  exteriorSemilinearMap_ιMulti (g.app U.unop).hom
    (cotangentMorphismSemilinear f g U) n m

set_option backward.isDefEq.respectTransparency true in
/-- The actual exterior components are natural, by equality on the genuine
spanning pure exterior products. -/
def exteriorCotangentPresheafMorphism (n : ℕ) :
    exteriorCotangentPresheaf f n ⟶
      (PresheafOfModules.pushforward
        g.toRingCatSheafHom.hom).obj
          (exteriorCotangentPresheaf (g ≫ f) n) where
  app U := exteriorCotangentMorphismComponent f g n U
  naturality {U V} i := by
    apply ModuleCat.Hom.ext
    apply LinearMap.ext_on (exteriorPower.ιMulti_span
      (X.presheaf.obj U) n ((cotangentPresheaf f).obj U))
    rintro _ ⟨m, rfl⟩
    change exteriorCotangentMorphismComponent f g n V
        ((exteriorCotangentPresheaf f n).map i
          (exteriorPower.ιMulti (X.presheaf.obj U) n m)) =
      (exteriorCotangentPresheaf (g ≫ f) n).map ((Opens.map g.base).op.map i)
        (exteriorCotangentMorphismComponent f g n U
          (exteriorPower.ιMulti (X.presheaf.obj U) n m))
    refine (congrArg (exteriorCotangentMorphismComponent f g n V)
      (exteriorPresheaf_map_mk (cotangentPresheaf f) n i m)).trans ?_
    refine (exteriorCotangentMorphismComponent_wedge f g n V _).trans ?_
    refine Eq.trans ?_ ((congrArg ((exteriorCotangentPresheaf (g ≫ f) n).map
      ((Opens.map g.base).op.map i))
      (exteriorCotangentMorphismComponent_wedge f g n U m)).symm)
    refine Eq.trans ?_ (exteriorPresheaf_map_mk (cotangentPresheaf (g ≫ f)) n
      ((Opens.map g.base).op.map i) _).symm
    congr 1
    funext j
    exact PresheafOfModules.naturality_apply (cotangentPresheafMorphism f g) i (m j)

/-- The actual sheaf morphism on exterior cotangent forms. -/
def exteriorCotangentSheafMorphism (n : ℕ) : exteriorCotangentSheaf f n ⟶
    (Scheme.Modules.pushforward g).obj (exteriorCotangentSheaf (g ≫ f) n) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)).symm
    (exteriorCotangentPresheafMorphism f g n ≫
      (PresheafOfModules.pushforward
        g.toRingCatSheafHom.hom).map
          (exteriorSheafificationMap (cotangentPresheaf (g ≫ f)) n))

/-- Both actual sheafification units retain exactly the raw exterior map. -/
theorem exteriorCotangentSheafMorphism_unit (n : ℕ) :
    exteriorSheafificationMap (cotangentPresheaf f) n ≫
        (exteriorCotangentSheafMorphism f g n).val =
      exteriorCotangentPresheafMorphism f g n ≫
        (PresheafOfModules.pushforward
          g.toRingCatSheafHom.hom).map
            (exteriorSheafificationMap (cotangentPresheaf (g ≫ f)) n) := by
  exact (PresheafOfModules.sheafificationHomEquiv
    (𝟙 X.ringCatSheaf.obj)).apply_symm_apply _

/-- Pure exterior sections have their actual coefficient-changing image
under the genuine sheaf morphism. -/
theorem exteriorCotangentSheafMorphism_wedge (n : ℕ) (U : X.Opens)
    (m : Fin n → (cotangentPresheaf f).obj (.op U)) :
    (exteriorCotangentSheafMorphism f g n).val.app (.op U)
        (exteriorSheafSection (cotangentPresheaf f) n U m) =
      exteriorSheafSection (cotangentPresheaf (g ≫ f)) n (g ⁻¹ᵁ U)
        (fun j ↦ cotangentMorphismSemilinear f g (.op U) (m j)) := by
  have h := congr($(exteriorCotangentSheafMorphism_unit f g n).app (.op U) |>.hom
    (exteriorPower.ιMulti Γ(X, U) n m))
  exact h.trans (congrArg
    ((exteriorSheafificationMap (cotangentPresheaf (g ≫ f)) n).app (.op (g ⁻¹ᵁ U)))
      (exteriorCotangentMorphismComponent_wedge f g n (.op U) m))

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual exterior differential map on genuine sheaf pullbacks. -/
def exteriorCotangentSheafPullbackMap (n : ℕ) :
    (Scheme.Modules.pullback g).obj (exteriorCotangentSheaf f n) ⟶
      exteriorCotangentSheaf (g ≫ f) n :=
  ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).symm
    (exteriorCotangentSheafMorphism f g n)

end
end EnvelopeProperty.CanonicalGeometry
