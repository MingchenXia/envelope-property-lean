import EnvelopeProperty.Vanishing.ArithmeticCanonicalPushoutDifferential

/-! # Composition of the actual arithmetic universal differential maps -/

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.ArithmeticCanonicalPushoutDifferential

open CanonicalGeometry ArithmeticCanonicalGlobal

set_option backward.isDefEq.respectTransparency false

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    {X Y Z : Scheme.{u}} (φ : CommRingCat.of R ⟶ CommRingCat.of S)
    (ψ : CommRingCat.of S ⟶ CommRingCat.of T)
    (f : X ⟶ Spec (.of R)) (h : Y ⟶ Spec (.of S)) (j : Z ⟶ Spec (.of T))
    (g : Y ⟶ X) (k : Z ⟶ Y)
    (w : CoefficientSquare φ f h g) (v : CoefficientSquare ψ h j k)

include w v

theorem coefficientSquare_comp : CoefficientSquare (φ ≫ ψ) f j (k ≫ g) := by
  intro U
  change (relativeConstants f).app (.op U) ≫ (g.app U ≫ k.app (g ⁻¹ᵁ U)) = _
  rw [← Category.assoc, w U, Category.assoc, v (g ⁻¹ᵁ U)]
  exact (Category.assoc _ _ _).symm

/-- Actual cotangent vectors retain both original coefficient maps under composition. -/
theorem cotangentSemilinear_comp (U : X.Opens)
    (m : (relativeCotangentPresheaf f).obj (.op U)) :
    cotangentSemilinear ψ h j k v (.op (g ⁻¹ᵁ U))
        (cotangentSemilinear φ f h g w (.op U) m) =
      cotangentSemilinear (φ ≫ ψ) f j (k ≫ g)
        (coefficientSquare_comp φ ψ f h j g k w v) (.op U) m := by
  let : Algebra R Γ(X, U) := ((relativeConstants f).app (.op U)).hom.toAlgebra
  have hm : m ∈ Submodule.span Γ(X, U)
      (Set.range (KaehlerDifferential.D R Γ(X, U))) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    change (cotangentPresheafMap ψ h j k v).app (.op (g ⁻¹ᵁ U))
        ((cotangentPresheafMap φ f h g w).app (.op U) ((relativeDerivation f).d a)) =
      (cotangentPresheafMap (φ ≫ ψ) f j (k ≫ g)
        (coefficientSquare_comp φ ψ f h j g k w v)).app (.op U)
          ((relativeDerivation f).d a)
    rw [cotangentPresheafMap_d, cotangentPresheafMap_d, cotangentPresheafMap_d]
    rfl
  | zero => simp only [map_zero]
  | add x y hx hy hxe hye => simp only [map_add, hxe, hye]
  | smul a x hx hxe =>
    rw [(cotangentSemilinear φ f h g w (.op U)).map_smulₛₗ,
      (cotangentSemilinear ψ h j k v (.op (g ⁻¹ᵁ U))).map_smulₛₗ,
      (cotangentSemilinear (φ ≫ ψ) f j (k ≫ g)
        (coefficientSquare_comp φ ψ f h j g k w v) (.op U)).map_smulₛₗ, hxe]
    rfl

/-- The whole raw exterior map, in every degree, retains genuine composition. -/
theorem exteriorComponent_comp (q : ℕ) (U : X.Opens)
    (z : (relativeExteriorPresheaf f q).obj (.op U)) :
    exteriorComponent ψ h j k v q (.op (g ⁻¹ᵁ U))
        (exteriorComponent φ f h g w q (.op U) z) =
      exteriorComponent (φ ≫ ψ) f j (k ≫ g)
        (coefficientSquare_comp φ ψ f h j g k w v) q (.op U) z := by
  have hz : z ∈ Submodule.span Γ(X, U)
      (Set.range (exteriorPower.ιMulti Γ(X, U) q
        (M := (relativeCotangentPresheaf f).obj (.op U)))) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, rfl⟩ := hx
    have hg := exteriorComponent_wedge φ f h g w q (.op U) m
    have hk := exteriorComponent_wedge ψ h j k v q (.op (g ⁻¹ᵁ U))
      (fun a => cotangentSemilinear φ f h g w (.op U) (m a))
    have hc := exteriorComponent_wedge (φ ≫ ψ) f j (k ≫ g)
      (coefficientSquare_comp φ ψ f h j g k w v) q (.op U) m
    refine (congrArg (exteriorComponent ψ h j k v q (.op (g ⁻¹ᵁ U))) hg).trans
      (hk.trans (Eq.trans ?_ hc.symm))
    congr 1
    funext a
    exact cotangentSemilinear_comp φ ψ f h j g k w v U (m a)
  | zero => simp only [map_zero]
  | add x y hx hy hxe hye => simp only [map_add, hxe, hye]
  | smul a x hx hxe =>
    have hg : exteriorComponent φ f h g w q (.op U) (a • x) =
        g.app U a • (show (relativeExteriorPresheaf h q).obj (.op (g ⁻¹ᵁ U))
          from exteriorComponent φ f h g w q (.op U) x) :=
      (exteriorComponent φ f h g w q (.op U)).hom.map_smul a x
    have hk : exteriorComponent ψ h j k v q (.op (g ⁻¹ᵁ U))
        (g.app U a • (show (relativeExteriorPresheaf h q).obj (.op (g ⁻¹ᵁ U))
          from exteriorComponent φ f h g w q (.op U) x)) =
        k.app (g ⁻¹ᵁ U) (g.app U a) •
          (show (relativeExteriorPresheaf j q).obj (.op (k ⁻¹ᵁ g ⁻¹ᵁ U))
            from exteriorComponent ψ h j k v q (.op (g ⁻¹ᵁ U))
              (exteriorComponent φ f h g w q (.op U) x)) :=
      (exteriorComponent ψ h j k v q (.op (g ⁻¹ᵁ U))).hom.map_smul _ _
    have hc : exteriorComponent (φ ≫ ψ) f j (k ≫ g)
        (coefficientSquare_comp φ ψ f h j g k w v) q (.op U) (a • x) =
        (k ≫ g).app U a •
          (show (relativeExteriorPresheaf j q).obj (.op ((k ≫ g) ⁻¹ᵁ U))
            from exteriorComponent (φ ≫ ψ) f j (k ≫ g)
              (coefficientSquare_comp φ ψ f h j g k w v) q (.op U) x) :=
      (exteriorComponent (φ ≫ ψ) f j (k ≫ g)
        (coefficientSquare_comp φ ψ f h j g k w v) q (.op U)).hom.map_smul _ _
    rw [hg, hk, hc, hxe]
    rfl

omit [CommRing T] v in
theorem exteriorSheafPushMap_raw (q : ℕ) (U : X.Opens)
    (z : (relativeExteriorPresheaf f q).obj (.op U)) :
    (exteriorSheafPushMap φ f h g w q).val.app (.op U)
        ((exteriorSheafificationMap (relativeCotangentPresheaf f) q).app (.op U) z) =
      (exteriorSheafificationMap (relativeCotangentPresheaf h) q).app (.op (g ⁻¹ᵁ U))
        (exteriorComponent φ f h g w q (.op U) z) :=
  congr($(exteriorSheafPushMap_unit φ f h g w q).app (.op U) |>.hom z)

/-- Equality of whole sheaf maps follows from the original two units. -/
theorem exteriorSheafPushMap_comp (q : ℕ) :
    exteriorSheafPushMap (φ ≫ ψ) f j (k ≫ g)
        (coefficientSquare_comp φ ψ f h j g k w v) q =
      exteriorSheafPushMap φ f h g w q ≫
        (Scheme.Modules.pushforward g).map (exteriorSheafPushMap ψ h j k v q) ≫
        (Scheme.Modules.pushforwardComp k g).hom.app (relativeExteriorSheaf j q) := by
  apply (PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)
    (P := relativeExteriorPresheaf f q)
    (F := (Scheme.Modules.pushforward (k ≫ g)).obj (relativeExteriorSheaf j q))).injective
  ext U z
  change (exteriorSheafPushMap (φ ≫ ψ) f j (k ≫ g)
      (coefficientSquare_comp φ ψ f h j g k w v) q).val.app U
        ((exteriorSheafificationMap (relativeCotangentPresheaf f) q).app U z) =
    (exteriorSheafPushMap ψ h j k v q).val.app (.op (g ⁻¹ᵁ U.unop))
      ((exteriorSheafPushMap φ f h g w q).val.app U
        ((exteriorSheafificationMap (relativeCotangentPresheaf f) q).app U z))
  rw [exteriorSheafPushMap_raw, exteriorSheafPushMap_raw, exteriorSheafPushMap_raw]
  exact congrArg ((exteriorSheafificationMap (relativeCotangentPresheaf j) q).app
    (.op (k ⁻¹ᵁ g ⁻¹ᵁ U.unop)))
      (exteriorComponent_comp φ ψ f h j g k w v q U.unop z).symm

omit [CommRing R] [CommRing S] [CommRing T] w v in
private theorem pullbackComp_homEquiv (A : X.Modules) (C : Z.Modules)
    (b : (Scheme.Modules.pullback (k ≫ g)).obj A ⟶ C) :
    (((Scheme.Modules.pullbackPushforwardAdjunction g).comp
        (Scheme.Modules.pullbackPushforwardAdjunction k)).homEquiv A C)
        ((Scheme.Modules.pullbackComp k g).hom.app A ≫ b) ≫
      (Scheme.Modules.pushforwardComp k g).hom.app C =
        ((Scheme.Modules.pullbackPushforwardAdjunction (k ≫ g)).homEquiv A C) b := by
  let Ac := (Scheme.Modules.pullbackPushforwardAdjunction g).comp
    (Scheme.Modules.pullbackPushforwardAdjunction k)
  let At := Scheme.Modules.pullbackPushforwardAdjunction (k ≫ g)
  let α := Scheme.Modules.pullbackComp k g
  let ε := Scheme.Modules.pushforwardComp k g
  have hu : Ac.unit.app A ≫ ε.hom.app
      ((Scheme.Modules.pullback k).obj ((Scheme.Modules.pullback g).obj A)) =
      At.unit.app A ≫ (Scheme.Modules.pushforward (k ≫ g)).map (α.inv.app A) := by
    have H := unit_conjugateEquiv Ac At α.inv A
    rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at H
    exact H
  change Ac.homEquiv A C (α.hom.app A ≫ b) ≫ ε.hom.app C = At.homEquiv A C b
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  calc
    _ = Ac.unit.app A ≫ (ε.hom.app _ ≫
        (Scheme.Modules.pushforward (k ≫ g)).map (α.hom.app A ≫ b)) := by
      rw [Category.assoc, ε.hom.naturality]
    _ = (At.unit.app A ≫ (Scheme.Modules.pushforward (k ≫ g)).map (α.inv.app A)) ≫
        (Scheme.Modules.pushforward (k ≫ g)).map (α.hom.app A ≫ b) := by
      exact (Category.assoc _ _ _).symm.trans
        (congrArg (fun z => z ≫
          (Scheme.Modules.pushforward (k ≫ g)).map (α.hom.app A ≫ b)) hu)
    _ = _ := by
      rw [Category.assoc, ← Functor.map_comp, α.inv_hom_id_app_assoc]

omit [CommRing R] [CommRing S] [CommRing T] w v in
private theorem pullback_compAdj_homEquiv (A : X.Modules) (B : Y.Modules) (C : Z.Modules)
    (a : (Scheme.Modules.pullback g).obj A ⟶ B)
    (b : (Scheme.Modules.pullback k).obj B ⟶ C) :
    (((Scheme.Modules.pullbackPushforwardAdjunction g).comp
        (Scheme.Modules.pullbackPushforwardAdjunction k)).homEquiv A C)
        ((Scheme.Modules.pullback k).map a ≫ b) =
      ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv A B) a ≫
        (Scheme.Modules.pushforward g).map
          (((Scheme.Modules.pullbackPushforwardAdjunction k).homEquiv B C) b) := by
  rw [Adjunction.comp_homEquiv]
  change ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv A _)
    (((Scheme.Modules.pullbackPushforwardAdjunction k).homEquiv _ C)
      ((Scheme.Modules.pullback k).map a ≫ b)) = _
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]

omit [CommRing T] v in
theorem exteriorPullbackMap_homEquiv (q : ℕ) :
    ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _)
        (exteriorPullbackMap φ f h g w q) = exteriorSheafPushMap φ f h g w q :=
  ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).apply_symm_apply _

/-- The whole actual pullback differential respects native composition. -/
theorem exteriorPullbackMap_comp (q : ℕ) :
    (Scheme.Modules.pullbackComp k g).hom.app (relativeExteriorSheaf f q) ≫
        exteriorPullbackMap (φ ≫ ψ) f j (k ≫ g)
          (coefficientSquare_comp φ ψ f h j g k w v) q =
      (Scheme.Modules.pullback k).map (exteriorPullbackMap φ f h g w q) ≫
        exteriorPullbackMap ψ h j k v q := by
  let Ac := (Scheme.Modules.pullbackPushforwardAdjunction g).comp
    (Scheme.Modules.pullbackPushforwardAdjunction k)
  apply (Ac.homEquiv _ _).injective
  apply (cancel_mono ((Scheme.Modules.pushforwardComp k g).hom.app
    (relativeExteriorSheaf j q))).mp
  change _ = (((Scheme.Modules.pullbackPushforwardAdjunction g).comp
    (Scheme.Modules.pullbackPushforwardAdjunction k)).homEquiv _ _) _ ≫ _
  rw [pullbackComp_homEquiv, pullback_compAdj_homEquiv,
    exteriorPullbackMap_homEquiv, exteriorPullbackMap_homEquiv,
    exteriorPullbackMap_homEquiv]
  exact exteriorSheafPushMap_comp φ ψ f h j g k w v q

end EnvelopeProperty.Vanishing.ArithmeticCanonicalPushoutDifferential
