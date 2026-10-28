import EnvelopeProperty.AlgGeom.Canonical.CotangentMorphism
import EnvelopeProperty.AlgGeom.Canonical.ExteriorCotangentMorphism

/-! # Genuine whole-map functoriality of the SAME original cotangent morphisms -/

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

namespace EnvelopeProperty.CanonicalGeometry

universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {K : Type u} [Field K] {X Y Z : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (g : Y ⟶ X)

/-- The actual original cotangent sheaf morphism retains the differential
of EVERY original regular function under the SAME original ring map. -/
theorem cotangentSheafMorphism_d (U : X.Opens) (a : Γ(X, U)) :
    (cotangentSheafMorphism f g).val.app (.op U) ((cotangentDerivation f).d a) =
      (cotangentDerivation (g ≫ f)).d (g.app U a) := by
  have hu := congr($(cotangentSheafMorphism_unit f g).app (.op U) |>.hom
    ((cotangentPresheafDerivation f).d a))
  exact hu.trans (congrArg ((cotangentSheafificationMap (g ≫ f)).app (.op (g ⁻¹ᵁ U)))
    (cotangentPresheafMorphism_d f g U a))

private theorem canonicalCotangentTransportDifferential
    {W : Scheme.{u}} {f₁ f₂ : W ⟶ Spec (.of K)} (he : f₁ = f₂)
    (U : W.Opens) (a : Γ(W, U)) :
    (eqToHom (congrArg cotangentSheaf he)).val.app (.op U) ((cotangentDerivation f₁).d a) =
      (cotangentDerivation f₂).d a := by
  subst f₂
  rfl

private theorem canonicalCotangentPresheafTransportDifferential
    {W : Scheme.{u}} {f₁ f₂ : W ⟶ Spec (.of K)} (he : f₁ = f₂)
    (U : W.Opens) (a : Γ(W, U)) :
    (eqToHom (congrArg cotangentPresheaf he)).app (.op U)
        ((cotangentPresheafDerivation f₁).d a) =
      (cotangentPresheafDerivation f₂).d a := by
  subst f₂
  rfl

/-- Every original raw cotangent vector is preserved under genuine actual
composition, retaining SAME ring maps and the canonical structural transport. -/
theorem cotangentMorphismSemilinear_comp (h : Z ⟶ Y) (U : X.Opens)
    (m : (cotangentPresheaf f).obj (.op U)) :
    (eqToHom (congrArg cotangentPresheaf (Category.assoc h g f).symm)).app
        (.op (h ⁻¹ᵁ g ⁻¹ᵁ U))
        (cotangentMorphismSemilinear (g ≫ f) h (.op (g ⁻¹ᵁ U))
          (cotangentMorphismSemilinear f g (.op U) m)) =
      cotangentMorphismSemilinear f (h ≫ g) (.op U) m := by
  let T := (eqToHom (congrArg cotangentPresheaf (Category.assoc h g f).symm)).app
    (.op (h ⁻¹ᵁ g ⁻¹ᵁ U))
  let L : (cotangentPresheaf f).obj (.op U) →ₗ[Γ(X, U)]
      ((PresheafOfModules.pushforward (h ≫ g).toRingCatSheafHom.hom).obj
        (cotangentPresheaf ((h ≫ g) ≫ f))).obj (.op U) :=
    { toFun := fun z ↦ T (cotangentMorphismSemilinear (g ≫ f) h (.op (g ⁻¹ᵁ U))
        (cotangentMorphismSemilinear f g (.op U) z))
      map_add' := fun x y ↦ by simp only [map_add]
      map_smul' := fun a z ↦ by
        change T (cotangentMorphismSemilinear (g ≫ f) h (.op (g ⁻¹ᵁ U))
          (cotangentMorphismSemilinear f g (.op U) (a • z))) =
          ((h ≫ g).app U a) • T (cotangentMorphismSemilinear (g ≫ f) h (.op (g ⁻¹ᵁ U))
            (cotangentMorphismSemilinear f g (.op U) z))
        rw [(cotangentMorphismSemilinear f g (.op U)).map_smulₛₗ,
          (cotangentMorphismSemilinear (g ≫ f) h (.op (g ⁻¹ᵁ U))).map_smulₛₗ,
          T.hom.map_smul]
        rfl }
  have hL : L = ((cotangentPresheafMorphism f (h ≫ g)).app (.op U)).hom := by
    let := cotangentOpenAlgebra f U
    apply LinearMap.ext_on (KaehlerDifferential.span_range_derivation K Γ(X, U))
    rintro _ ⟨a, rfl⟩
    change T ((cotangentPresheafMorphism (g ≫ f) h).app (.op (g ⁻¹ᵁ U))
        ((cotangentPresheafMorphism f g).app (.op U) ((cotangentPresheafDerivation f).d a))) =
      (cotangentPresheafMorphism f (h ≫ g)).app (.op U) ((cotangentPresheafDerivation f).d a)
    rw [cotangentPresheafMorphism_d, cotangentPresheafMorphism_d, cotangentPresheafMorphism_d]
    exact canonicalCotangentPresheafTransportDifferential (Category.assoc h g f).symm
      (h ⁻¹ᵁ g ⁻¹ᵁ U) (h.app (g ⁻¹ᵁ U) (g.app U a))
  exact LinearMap.congr_fun hL m

/-- The ENTIRE original cotangent morphism is functorial for arbitrary
actual composition, with actual native pushforward comparison and canonical
structural-map associativity transport. No comparison certificate is assumed. -/
theorem cotangentSheafMorphism_comp (h : Z ⟶ Y) :
    cotangentSheafMorphism f (h ≫ g) =
      cotangentSheafMorphism f g ≫
        (Scheme.Modules.pushforward g).map (cotangentSheafMorphism (g ≫ f) h) ≫
        (Scheme.Modules.pushforward g).map ((Scheme.Modules.pushforward h).map
          (eqToHom (congrArg cotangentSheaf (Category.assoc h g f).symm))) ≫
        (Scheme.Modules.pushforwardComp h g).hom.app (cotangentSheaf ((h ≫ g) ≫ f)) := by
  apply (cotangentSheafHomEquiv f
    ((Scheme.Modules.pushforward (h ≫ g)).obj (cotangentSheaf ((h ≫ g) ≫ f)))).injective
  ext U a
  change (cotangentSheafMorphism f (h ≫ g)).val.app U ((cotangentDerivation f).d a) =
    (eqToHom (congrArg cotangentSheaf (Category.assoc h g f).symm)).val.app
      (.op (h ⁻¹ᵁ g ⁻¹ᵁ U.unop))
      ((cotangentSheafMorphism (g ≫ f) h).val.app (.op (g ⁻¹ᵁ U.unop))
        ((cotangentSheafMorphism f g).val.app U ((cotangentDerivation f).d a)))
  rw [cotangentSheafMorphism_d, cotangentSheafMorphism_d, cotangentSheafMorphism_d]
  exact (canonicalCotangentTransportDifferential (Category.assoc h g f).symm
    (h ⁻¹ᵁ g ⁻¹ᵁ U.unop) (h.app (g ⁻¹ᵁ U.unop) (g.app U.unop a))).symm

private theorem canonicalExteriorPresheafTransportWedge
    {W : Scheme.{u}} {f₁ f₂ : W ⟶ Spec (.of K)} (he : f₁ = f₂)
    (U : W.Opens) (n : ℕ) (m : Fin n → (cotangentPresheaf f₁).obj (.op U)) :
    (eqToHom (congrArg (fun q ↦ exteriorCotangentPresheaf q n) he)).app (.op U)
        (exteriorPower.ιMulti Γ(W, U) n m) =
      exteriorPower.ιMulti Γ(W, U) n
        (fun j ↦ (eqToHom (congrArg cotangentPresheaf he)).app (.op U) (m j)) := by
  subst f₂
  rfl

/-- The WHOLE actual raw exterior component preserves genuine arbitrary
composition, on EVERY original exterior vector and every exterior degree. -/
theorem exteriorCotangentMorphismComponent_comp (h : Z ⟶ Y) (n : ℕ) (U : X.Opens)
    (z : (exteriorCotangentPresheaf f n).obj (.op U)) :
    (eqToHom (congrArg (fun q ↦ exteriorCotangentPresheaf q n)
        (Category.assoc h g f).symm)).app (.op (h ⁻¹ᵁ g ⁻¹ᵁ U))
        (exteriorCotangentMorphismComponent (g ≫ f) h n (.op (g ⁻¹ᵁ U))
          (exteriorCotangentMorphismComponent f g n (.op U) z)) =
      exteriorCotangentMorphismComponent f (h ≫ g) n (.op U) z := by
  let T := (eqToHom (congrArg (fun q ↦ exteriorCotangentPresheaf q n)
    (Category.assoc h g f).symm)).app (.op (h ⁻¹ᵁ g ⁻¹ᵁ U))
  let L : (exteriorCotangentPresheaf f n).obj (.op U) →ₗ[Γ(X, U)]
      ((PresheafOfModules.pushforward (h ≫ g).toRingCatSheafHom.hom).obj
        (exteriorCotangentPresheaf ((h ≫ g) ≫ f) n)).obj (.op U) :=
    { toFun := fun w ↦ T (exteriorCotangentMorphismComponent (g ≫ f) h n (.op (g ⁻¹ᵁ U))
        (exteriorCotangentMorphismComponent f g n (.op U) w))
      map_add' := fun x y ↦ by simp only [map_add]
      map_smul' := fun a w ↦ by
        change T (exteriorCotangentMorphismComponent (g ≫ f) h n (.op (g ⁻¹ᵁ U))
          (exteriorCotangentMorphismComponent f g n (.op U) (a • w))) =
          ((h ≫ g).app U a) • T (exteriorCotangentMorphismComponent (g ≫ f) h n (.op (g ⁻¹ᵁ U))
            (exteriorCotangentMorphismComponent f g n (.op U) w))
        have hg : exteriorCotangentMorphismComponent f g n (.op U) (a • w) =
            g.app U a • (show (exteriorCotangentPresheaf (g ≫ f) n).obj (.op (g ⁻¹ᵁ U))
              from exteriorCotangentMorphismComponent f g n (.op U) w) :=
          (exteriorCotangentMorphismComponent f g n (.op U)).hom.map_smul a w
        rw [hg]
        have hh : exteriorCotangentMorphismComponent (g ≫ f) h n (.op (g ⁻¹ᵁ U))
              (g.app U a • (show (exteriorCotangentPresheaf (g ≫ f) n).obj (.op (g ⁻¹ᵁ U))
                from exteriorCotangentMorphismComponent f g n (.op U) w)) =
            h.app (g ⁻¹ᵁ U) (g.app U a) •
              (show (exteriorCotangentPresheaf (h ≫ (g ≫ f)) n).obj (.op (h ⁻¹ᵁ g ⁻¹ᵁ U))
                from exteriorCotangentMorphismComponent (g ≫ f) h n (.op (g ⁻¹ᵁ U))
                  (exteriorCotangentMorphismComponent f g n (.op U) w)) :=
          (exteriorCotangentMorphismComponent (g ≫ f) h n (.op (g ⁻¹ᵁ U))).hom.map_smul _ _
        rw [hh, T.hom.map_smul]
        rfl }
  have hL : L = ((exteriorCotangentMorphismComponent f (h ≫ g) n (.op U))).hom := by
    apply LinearMap.ext_on (exteriorPower.ιMulti_span Γ(X, U) n
      ((cotangentPresheaf f).obj (.op U)))
    rintro _ ⟨m, rfl⟩
    change T (exteriorCotangentMorphismComponent (g ≫ f) h n (.op (g ⁻¹ᵁ U))
        (exteriorCotangentMorphismComponent f g n (.op U)
          (exteriorPower.ιMulti Γ(X, U) n m))) =
      exteriorCotangentMorphismComponent f (h ≫ g) n (.op U)
        (exteriorPower.ιMulti Γ(X, U) n m)
    have hg := exteriorCotangentMorphismComponent_wedge f g n (.op U) m
    have hh := exteriorCotangentMorphismComponent_wedge (g ≫ f) h n (.op (g ⁻¹ᵁ U))
      (fun j ↦ cotangentMorphismSemilinear f g (.op U) (m j))
    have hc := exteriorCotangentMorphismComponent_wedge f (h ≫ g) n (.op U) m
    have ht := canonicalExteriorPresheafTransportWedge (Category.assoc h g f).symm
      (h ⁻¹ᵁ g ⁻¹ᵁ U) n
      (fun j ↦ cotangentMorphismSemilinear (g ≫ f) h (.op (g ⁻¹ᵁ U))
        (cotangentMorphismSemilinear f g (.op U) (m j)))
    have hw : exteriorPower.ιMulti Γ(Z, h ⁻¹ᵁ g ⁻¹ᵁ U) n
        (fun j ↦ (eqToHom (congrArg cotangentPresheaf (Category.assoc h g f).symm)).app
          (.op (h ⁻¹ᵁ g ⁻¹ᵁ U))
          (cotangentMorphismSemilinear (g ≫ f) h (.op (g ⁻¹ᵁ U))
            (cotangentMorphismSemilinear f g (.op U) (m j)))) =
        exteriorPower.ιMulti Γ(Z, h ⁻¹ᵁ g ⁻¹ᵁ U) n
          (fun j ↦ cotangentMorphismSemilinear f (h ≫ g) (.op U) (m j)) := by
      congr 1
      funext j
      exact cotangentMorphismSemilinear_comp f g h U (m j)
    exact (congrArg (fun w ↦ T (exteriorCotangentMorphismComponent (g ≫ f) h n
      (.op (g ⁻¹ᵁ U)) w)) hg).trans ((congrArg T hh).trans (ht.trans (hw.trans hc.symm)))
  exact LinearMap.congr_fun hL z

/-- BOTH SAME original units retain the ENTIRE raw exterior component,
on EVERY original raw exterior section, without a chosen-coordinate restriction. -/
theorem exteriorCotangentSheafMorphism_raw (n : ℕ) (U : X.Opens)
    (z : (exteriorCotangentPresheaf f n).obj (.op U)) :
    (exteriorCotangentSheafMorphism f g n).val.app (.op U)
        ((exteriorSheafificationMap (cotangentPresheaf f) n).app (.op U) z) =
      (exteriorSheafificationMap (cotangentPresheaf (g ≫ f)) n).app (.op (g ⁻¹ᵁ U))
        (exteriorCotangentMorphismComponent f g n (.op U) z) :=
  congr($(exteriorCotangentSheafMorphism_unit f g n).app (.op U) |>.hom z)

private theorem canonicalExteriorSheafTransportUnit
    {W : Scheme.{u}} {f₁ f₂ : W ⟶ Spec (.of K)} (he : f₁ = f₂)
    (U : W.Opens) (n : ℕ) (z : (exteriorCotangentPresheaf f₁ n).obj (.op U)) :
    (eqToHom (congrArg (fun q ↦ exteriorCotangentSheaf q n) he)).val.app (.op U)
        ((exteriorSheafificationMap (cotangentPresheaf f₁) n).app (.op U) z) =
      (exteriorSheafificationMap (cotangentPresheaf f₂) n).app (.op U)
        ((eqToHom (congrArg (fun q ↦ exteriorCotangentPresheaf q n) he)).app (.op U) z) := by
  subst f₂
  rfl

/-- The ENTIRE original exterior cotangent SHEAF morphism is genuinely
functorial for arbitrary original scheme composition, in EVERY degree. -/
theorem exteriorCotangentSheafMorphism_comp (h : Z ⟶ Y) (n : ℕ) :
    exteriorCotangentSheafMorphism f (h ≫ g) n =
      exteriorCotangentSheafMorphism f g n ≫
        (Scheme.Modules.pushforward g).map (exteriorCotangentSheafMorphism (g ≫ f) h n) ≫
        (Scheme.Modules.pushforward g).map ((Scheme.Modules.pushforward h).map
          (eqToHom (congrArg (fun q ↦ exteriorCotangentSheaf q n) (Category.assoc h g f).symm))) ≫
        (Scheme.Modules.pushforwardComp h g).hom.app (exteriorCotangentSheaf ((h ≫ g) ≫ f) n) := by
  apply (PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)
    (P := exteriorCotangentPresheaf f n)
    (F := (Scheme.Modules.pushforward (h ≫ g)).obj
      (exteriorCotangentSheaf ((h ≫ g) ≫ f) n))).injective
  ext U z
  change (exteriorCotangentSheafMorphism f (h ≫ g) n).val.app U
      ((exteriorSheafificationMap (cotangentPresheaf f) n).app U z) =
    (eqToHom (congrArg (fun q ↦ exteriorCotangentSheaf q n)
      (Category.assoc h g f).symm)).val.app (.op (h ⁻¹ᵁ g ⁻¹ᵁ U.unop))
      ((exteriorCotangentSheafMorphism (g ≫ f) h n).val.app (.op (g ⁻¹ᵁ U.unop))
        ((exteriorCotangentSheafMorphism f g n).val.app U
          ((exteriorSheafificationMap (cotangentPresheaf f) n).app U z)))
  rw [exteriorCotangentSheafMorphism_raw, exteriorCotangentSheafMorphism_raw,
    exteriorCotangentSheafMorphism_raw]
  have ht := canonicalExteriorSheafTransportUnit (Category.assoc h g f).symm
    (h ⁻¹ᵁ g ⁻¹ᵁ U.unop) n
    (exteriorCotangentMorphismComponent (g ≫ f) h n (.op (g ⁻¹ᵁ U.unop))
      (exteriorCotangentMorphismComponent f g n U z))
  exact ((congrArg ((exteriorSheafificationMap (cotangentPresheaf ((h ≫ g) ≫ f)) n).app
    (.op (h ⁻¹ᵁ g ⁻¹ᵁ U.unop)))
      (exteriorCotangentMorphismComponent_comp f g h n U.unop z)).symm).trans ht.symm

end
end EnvelopeProperty.CanonicalGeometry
