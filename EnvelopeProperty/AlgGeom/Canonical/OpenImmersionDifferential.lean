import EnvelopeProperty.AlgGeom.Canonical.CotangentMorphismFunctoriality
import EnvelopeProperty.AlgGeom.Canonical.OpenImmersionSheafUnits

/-! # The original differential of an actual open immersion -/

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

namespace EnvelopeProperty.CanonicalGeometry

universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {K : Type u} [Field K] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (g : Y ⟶ X) [IsOpenImmersion g]

/-- The inverse ORIGINAL cotangent coefficient map after the actual
forward differential is exactly the ORIGINAL restriction to the image open. -/
theorem cotangentOpenImmersionSemilinear_morphism (U : X.Opens)
    (z : (cotangentPresheaf f).obj (.op U)) :
    cotangentOpenImmersionSemilinear f g (.op (g ⁻¹ᵁ U))
        (cotangentMorphismSemilinear f g (.op U) z) =
      (cotangentPresheaf f).map (homOfLE (g.image_preimage_le U)).op z := by
  let := cotangentOpenAlgebra f U
  have hz : z ∈ Submodule.span Γ(X, U) (Set.range (KaehlerDifferential.D K Γ(X, U))) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    change (cotangentPresheafOpenImmersionMap f g).app (.op (g ⁻¹ᵁ U))
        ((cotangentPresheafMorphism f g).app (.op U)
          ((cotangentPresheafDerivation f).d a)) = _
    rw [cotangentPresheafMorphism_d]
    change CommRingCat.KaehlerDifferential.map
      ((Category.id_comp _).trans (openImmersion_constantSquare_inv f g (.op (g ⁻¹ᵁ U))).symm)
      (CommRingCat.KaehlerDifferential.d _) = _
    rw [CommRingCat.KaehlerDifferential.map_d]
    exact (congrArg (cotangentPresheafDerivation f).d
      (congr($(g.app_appIso_inv U).hom a))).trans
      ((cotangentPresheafDerivation f).d_map (homOfLE (g.image_preimage_le U)).op a)
  | zero =>
    rw [(cotangentMorphismSemilinear f g (.op U)).map_zero,
      (cotangentOpenImmersionSemilinear f g (.op (g ⁻¹ᵁ U))).map_zero,
      map_zero]
  | add x y hx hy hxe hye => simp only [map_add, hxe, hye]
  | smul a x hx hxe =>
    rw [(cotangentMorphismSemilinear f g (.op U)).map_smulₛₗ,
      (cotangentOpenImmersionSemilinear f g (.op (g ⁻¹ᵁ U))).map_smulₛₗ,
      (cotangentPresheaf f).map_smul, hxe]
    exact congrArg (fun b ↦ b • ((cotangentPresheaf f).map
      (homOfLE (g.image_preimage_le U)).op x)) (congr($(g.app_appIso_inv U).hom a))

/-- In EVERY exterior degree, the actual inverse coefficient map after
the SAME forward differential is the ORIGINAL restriction on EVERY vector. -/
theorem exteriorCotangentOpenImmersionComponent_morphism (n : ℕ) (U : X.Opens)
    (z : (exteriorCotangentPresheaf f n).obj (.op U)) :
    exteriorCotangentOpenImmersionComponent f g n (.op (g ⁻¹ᵁ U))
        (exteriorCotangentMorphismComponent f g n (.op U) z) =
      (exteriorCotangentPresheaf f n).map (homOfLE (g.image_preimage_le U)).op z := by
  have hz : z ∈ Submodule.span Γ(X, U)
      (Set.range (exteriorPower.ιMulti Γ(X, U) n
        (M := (cotangentPresheaf f).obj (.op U)))) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, rfl⟩ := hx
    have hf := exteriorCotangentMorphismComponent_wedge f g n (.op U) m
    have hi := exteriorCotangentOpenImmersionComponent_wedge f g n (.op (g ⁻¹ᵁ U))
      (fun j ↦ cotangentMorphismSemilinear f g (.op U) (m j))
    have hr := exteriorPresheaf_map_mk (cotangentPresheaf f) n
      (homOfLE (g.image_preimage_le U)).op m
    refine (congrArg (exteriorCotangentOpenImmersionComponent f g n (.op (g ⁻¹ᵁ U))) hf).trans
      (hi.trans ((Eq.trans ?_ hr.symm)))
    congr 1
    funext j
    exact cotangentOpenImmersionSemilinear_morphism f g U (m j)
  | zero => simp only [map_zero]
  | add x y hx hy hxe hye => simp only [map_add, hxe, hye]
  | smul a x hx hxe =>
    have hf : exteriorCotangentMorphismComponent f g n (.op U) (a • x) =
        g.app U a • (show (exteriorCotangentPresheaf (g ≫ f) n).obj (.op (g ⁻¹ᵁ U))
          from exteriorCotangentMorphismComponent f g n (.op U) x) :=
      (exteriorCotangentMorphismComponent f g n (.op U)).hom.map_smul a x
    have hi : exteriorCotangentOpenImmersionComponent f g n (.op (g ⁻¹ᵁ U))
        (g.app U a • (show (exteriorCotangentPresheaf (g ≫ f) n).obj (.op (g ⁻¹ᵁ U))
          from exteriorCotangentMorphismComponent f g n (.op U) x)) =
        (g.appIso (g ⁻¹ᵁ U)).inv (g.app U a) •
          (show (exteriorCotangentPresheaf f n).obj (.op (g ''ᵁ (g ⁻¹ᵁ U)))
            from exteriorCotangentOpenImmersionComponent f g n (.op (g ⁻¹ᵁ U))
              (exteriorCotangentMorphismComponent f g n (.op U) x)) :=
      (exteriorCotangentOpenImmersionComponent f g n (.op (g ⁻¹ᵁ U))).hom.map_smul _ _
    rw [hf, hi, (exteriorCotangentPresheaf f n).map_smul, hxe]
    exact congrArg (fun b ↦ b • ((exteriorCotangentPresheaf f n).map
      (homOfLE (g.image_preimage_le U)).op x)) (congr($(g.app_appIso_inv U).hom a))

/-- The ENTIRE actual exterior sheaf differential, followed by the
inverse ORIGINAL open-immersion isomorphism, is exactly the native
restriction-adjunction unit. -/
theorem exteriorCotangentSheafMorphism_openImmersion_inv (n : ℕ) :
    exteriorCotangentSheafMorphism f g n ≫
        (Scheme.Modules.pushforward g).map (exteriorCotangentSheafOpenImmersionIso f g n).inv =
      (Scheme.Modules.restrictAdjunction g).unit.app (exteriorCotangentSheaf f n) := by
  apply (PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)
    (P := exteriorCotangentPresheaf f n)
    (F := (Scheme.Modules.pushforward g).obj
      ((Scheme.Modules.restrictFunctor g).obj (exteriorCotangentSheaf f n)))).injective
  ext U z
  change (exteriorCotangentSheafOpenImmersionIso f g n).inv.val.app (.op (g ⁻¹ᵁ U.unop))
      ((exteriorCotangentSheafMorphism f g n).val.app U
        ((exteriorSheafificationMap (cotangentPresheaf f) n).app U z)) =
    (exteriorCotangentSheaf f n).val.map
      (homOfLE (g.image_preimage_le U.unop)).op
      ((exteriorSheafificationMap (cotangentPresheaf f) n).app U z)
  rw [exteriorCotangentSheafMorphism_raw]
  have hi := congr($(exteriorCotangentSheafOpenImmersionIso_inv_unit g f n).app
    (.op (g ⁻¹ᵁ U.unop)) |>.hom (exteriorCotangentMorphismComponent f g n U z))
  change (exteriorCotangentSheafOpenImmersionIso f g n).inv.val.app (.op (g ⁻¹ᵁ U.unop))
      ((exteriorSheafificationMap (cotangentPresheaf (g ≫ f)) n).app (.op (g ⁻¹ᵁ U.unop))
        (exteriorCotangentMorphismComponent f g n U z)) =
    (exteriorSheafificationMap (cotangentPresheaf f) n).app
      (.op (g ''ᵁ (g ⁻¹ᵁ U.unop)))
      (exteriorCotangentOpenImmersionComponent f g n (.op (g ⁻¹ᵁ U.unop))
        (exteriorCotangentMorphismComponent f g n U z)) at hi
  refine hi.trans ?_
  rw [exteriorCotangentOpenImmersionComponent_morphism]
  exact congr($((exteriorSheafificationMap (cotangentPresheaf f) n).naturality
    (homOfLE (g.image_preimage_le U.unop)).op) |>.hom z)

/-- The SAME original pullback differential equals the ORIGINAL
open-immersion isomorphism, with the genuine native restriction/pullback
comparison. This is an equality of ENTIRE sheaf maps. -/
theorem exteriorCotangentSheafPullbackMap_openImmersion (n : ℕ) :
    exteriorCotangentSheafPullbackMap f g n =
      (Scheme.Modules.restrictFunctorIsoPullback g).inv.app (exteriorCotangentSheaf f n) ≫
        (exteriorCotangentSheafOpenImmersionIso f g n).hom := by
  let A := Scheme.Modules.pullbackPushforwardAdjunction g
  let B := Scheme.Modules.restrictAdjunction g
  let E := exteriorCotangentSheafOpenImmersionIso f g n
  let C := Scheme.Modules.restrictFunctorIsoPullback g
  have hu : A.unit.app (exteriorCotangentSheaf f n) ≫
      (Scheme.Modules.pushforward g).map (C.inv.app (exteriorCotangentSheaf f n)) =
      B.unit.app (exteriorCotangentSheaf f n) :=
    Adjunction.unit_leftAdjointUniq_hom_app A B _
  apply (A.homEquiv _ _).injective
  change (A.homEquiv _ _) ((A.homEquiv _ _).symm
      (exteriorCotangentSheafMorphism f g n)) = _
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  change exteriorCotangentSheafMorphism f g n =
    A.unit.app (exteriorCotangentSheaf f n) ≫
      (Scheme.Modules.pushforward g).map (C.inv.app (exteriorCotangentSheaf f n) ≫ E.hom)
  rw [Functor.map_comp, ← Category.assoc, hu]
  have he := exteriorCotangentSheafMorphism_openImmersion_inv f g n
  exact (Iso.comp_inv_eq ((Scheme.Modules.pushforward g).mapIso E)).mp he

/-- The ORIGINAL exterior differential of every actual open immersion
is an isomorphism in EVERY degree; no smoothness or frame assumption. -/
theorem isIso_exteriorCotangentSheafPullbackMap_openImmersion (n : ℕ) :
    IsIso (exteriorCotangentSheafPullbackMap f g n) := by
  rw [exteriorCotangentSheafPullbackMap_openImmersion]
  infer_instance

end
end EnvelopeProperty.CanonicalGeometry
