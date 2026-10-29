import EnvelopeProperty.Vanishing.ArithmeticCanonicalPushoutFunctoriality

/-! # The same arithmetic differential is the actual open pullback isomorphism -/

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.ArithmeticCanonicalPushoutDifferential

open CanonicalGeometry ArithmeticCanonicalGlobal

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) (g : Y ⟶ X) [IsOpenImmersion g]

omit [IsOpenImmersion g] in
theorem openCoefficientSquare : CoefficientSquare (𝟙 (CommRingCat.of R)) f (g ≫ f) g := by
  intro U
  simpa only [Category.id_comp] using
    ArithmeticCanonicalGlobalBaseChange.morphismConstantsSquare f g U

theorem cotangentOpenImmersionSemilinear_morphism (U : X.Opens)
    (z : (relativeCotangentPresheaf f).obj (.op U)) :
    ArithmeticCanonicalGlobalRestriction.cotangentSemilinear f g (.op (g ⁻¹ᵁ U))
        (cotangentSemilinear (𝟙 _) f (g ≫ f) g (openCoefficientSquare f g) (.op U) z) =
      (relativeCotangentPresheaf f).map (homOfLE (g.image_preimage_le U)).op z := by
  let : Algebra R Γ(X, U) := ((relativeConstants f).app (.op U)).hom.toAlgebra
  have hz : z ∈ Submodule.span Γ(X, U) (Set.range (KaehlerDifferential.D R Γ(X, U))) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    change (ArithmeticCanonicalGlobalRestriction.cotangentPresheafMap f g).app
        (.op (g ⁻¹ᵁ U))
        ((cotangentPresheafMap (𝟙 _) f (g ≫ f) g (openCoefficientSquare f g)).app
          (.op U) ((relativeDerivation f).d a)) = _
    rw [cotangentPresheafMap_d]
    change CommRingCat.KaehlerDifferential.map
      ((Category.id_comp _).trans
        (ArithmeticCanonicalGlobalRestriction.constantsSquare_inv f g (.op (g ⁻¹ᵁ U))).symm)
      (CommRingCat.KaehlerDifferential.d _) = _
    rw [CommRingCat.KaehlerDifferential.map_d]
    exact (congrArg (relativeDerivation f).d (congr($(g.app_appIso_inv U).hom a))).trans
      ((relativeDerivation f).d_map (homOfLE (g.image_preimage_le U)).op a)
  | zero => simp only [map_zero]
  | add x y hx hy hxe hye => simp only [map_add, hxe, hye]
  | smul a x hx hxe =>
    rw [(cotangentSemilinear (𝟙 _) f (g ≫ f) g
        (openCoefficientSquare f g) (.op U)).map_smulₛₗ,
      (ArithmeticCanonicalGlobalRestriction.cotangentSemilinear f g
        (.op (g ⁻¹ᵁ U))).map_smulₛₗ,
      (relativeCotangentPresheaf f).map_smul, hxe]
    exact congrArg (fun b => b • ((relativeCotangentPresheaf f).map
      (homOfLE (g.image_preimage_le U)).op x)) (congr($(g.app_appIso_inv U).hom a))

theorem exteriorOpenImmersionComponent_morphism (q : ℕ) (U : X.Opens)
    (z : (relativeExteriorPresheaf f q).obj (.op U)) :
    ArithmeticCanonicalGlobalRestriction.exteriorComponent f g q (.op (g ⁻¹ᵁ U))
        (exteriorComponent (𝟙 _) f (g ≫ f) g (openCoefficientSquare f g) q (.op U) z) =
      (relativeExteriorPresheaf f q).map (homOfLE (g.image_preimage_le U)).op z := by
  have hz : z ∈ Submodule.span Γ(X, U)
      (Set.range (exteriorPower.ιMulti Γ(X, U) q
        (M := (relativeCotangentPresheaf f).obj (.op U)))) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, rfl⟩ := hx
    have hf := exteriorComponent_wedge (𝟙 _) f (g ≫ f) g
      (openCoefficientSquare f g) q (.op U) m
    have hi := ArithmeticCanonicalGlobalRestriction.exteriorComponent_wedge f g q
      (.op (g ⁻¹ᵁ U))
      (fun a => cotangentSemilinear (𝟙 _) f (g ≫ f) g
        (openCoefficientSquare f g) (.op U) (m a))
    have hr := exteriorPresheaf_map_mk (relativeCotangentPresheaf f) q
      (homOfLE (g.image_preimage_le U)).op m
    refine (congrArg
      (ArithmeticCanonicalGlobalRestriction.exteriorComponent f g q (.op (g ⁻¹ᵁ U)))
      hf).trans (hi.trans (Eq.trans ?_ hr.symm))
    congr 1
    funext a
    exact cotangentOpenImmersionSemilinear_morphism f g U (m a)
  | zero => simp only [map_zero]
  | add x y hx hy hxe hye => simp only [map_add, hxe, hye]
  | smul a x hx hxe =>
    have hf : exteriorComponent (𝟙 _) f (g ≫ f) g
        (openCoefficientSquare f g) q (.op U) (a • x) =
        g.app U a • (show (relativeExteriorPresheaf (g ≫ f) q).obj (.op (g ⁻¹ᵁ U))
          from exteriorComponent (𝟙 _) f (g ≫ f) g
            (openCoefficientSquare f g) q (.op U) x) :=
      (exteriorComponent (𝟙 _) f (g ≫ f) g
        (openCoefficientSquare f g) q (.op U)).hom.map_smul a x
    have hi : ArithmeticCanonicalGlobalRestriction.exteriorComponent f g q (.op (g ⁻¹ᵁ U))
        (g.app U a • (show (relativeExteriorPresheaf (g ≫ f) q).obj (.op (g ⁻¹ᵁ U))
          from exteriorComponent (𝟙 _) f (g ≫ f) g
            (openCoefficientSquare f g) q (.op U) x)) =
        (g.appIso (g ⁻¹ᵁ U)).inv (g.app U a) •
          (show (relativeExteriorPresheaf f q).obj (.op (g ''ᵁ (g ⁻¹ᵁ U)))
            from ArithmeticCanonicalGlobalRestriction.exteriorComponent f g q
              (.op (g ⁻¹ᵁ U)) (exteriorComponent (𝟙 _) f (g ≫ f) g
                (openCoefficientSquare f g) q (.op U) x)) :=
      (ArithmeticCanonicalGlobalRestriction.exteriorComponent f g q
        (.op (g ⁻¹ᵁ U))).hom.map_smul _ _
    rw [hf, hi, (relativeExteriorPresheaf f q).map_smul, hxe]
    exact congrArg (fun b => b • ((relativeExteriorPresheaf f q).map
      (homOfLE (g.image_preimage_le U)).op x)) (congr($(g.app_appIso_inv U).hom a))

theorem exteriorSheafPushMap_openImmersion_inv (q : ℕ) :
    exteriorSheafPushMap (𝟙 _) f (g ≫ f) g (openCoefficientSquare f g) q ≫
        (Scheme.Modules.pushforward g).map
          (ArithmeticCanonicalGlobalRestriction.exteriorRestrictIso f g q).inv =
      (Scheme.Modules.restrictAdjunction g).unit.app (relativeExteriorSheaf f q) := by
  apply (PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)
    (P := relativeExteriorPresheaf f q)
    (F := (Scheme.Modules.pushforward g).obj
      ((Scheme.Modules.restrictFunctor g).obj (relativeExteriorSheaf f q)))).injective
  ext U z
  change (ArithmeticCanonicalGlobalRestriction.exteriorRestrictIso f g q).inv.val.app
      (.op (g ⁻¹ᵁ U.unop))
      ((exteriorSheafPushMap (𝟙 _) f (g ≫ f) g (openCoefficientSquare f g) q).val.app U
        ((exteriorSheafificationMap (relativeCotangentPresheaf f) q).app U z)) =
    (relativeExteriorSheaf f q).val.map (homOfLE (g.image_preimage_le U.unop)).op
      ((exteriorSheafificationMap (relativeCotangentPresheaf f) q).app U z)
  rw [exteriorSheafPushMap_raw]
  have hi := congr($(ArithmeticCanonicalGlobalUnits.restrictIso_inv_unit f g q).app
    (.op (g ⁻¹ᵁ U.unop)) |>.hom
      (exteriorComponent (𝟙 _) f (g ≫ f) g (openCoefficientSquare f g) q U z))
  change (ArithmeticCanonicalGlobalRestriction.exteriorRestrictIso f g q).inv.val.app
      (.op (g ⁻¹ᵁ U.unop))
      ((exteriorSheafificationMap (relativeCotangentPresheaf (g ≫ f)) q).app
        (.op (g ⁻¹ᵁ U.unop))
        (exteriorComponent (𝟙 _) f (g ≫ f) g (openCoefficientSquare f g) q U z)) =
    (exteriorSheafificationMap (relativeCotangentPresheaf f) q).app
      (.op (g ''ᵁ (g ⁻¹ᵁ U.unop)))
      (ArithmeticCanonicalGlobalRestriction.exteriorComponent f g q (.op (g ⁻¹ᵁ U.unop))
        (exteriorComponent (𝟙 _) f (g ≫ f) g (openCoefficientSquare f g) q U z)) at hi
  refine hi.trans ?_
  rw [exteriorOpenImmersionComponent_morphism]
  exact congr($((exteriorSheafificationMap (relativeCotangentPresheaf f) q).naturality
    (homOfLE (g.image_preimage_le U.unop)).op) |>.hom z)

/-- The whole identity-base differential equals the original open pullback isomorphism. -/
theorem exteriorPullbackMap_openImmersion (q : ℕ) :
    exteriorPullbackMap (𝟙 _) f (g ≫ f) g (openCoefficientSquare f g) q =
      (ArithmeticCanonicalGlobalRestriction.exteriorPullbackIso f g q).hom := by
  let A := Scheme.Modules.pullbackPushforwardAdjunction g
  let B := Scheme.Modules.restrictAdjunction g
  let E := ArithmeticCanonicalGlobalRestriction.exteriorRestrictIso f g q
  let C := Scheme.Modules.restrictFunctorIsoPullback g
  have hu : A.unit.app (relativeExteriorSheaf f q) ≫
      (Scheme.Modules.pushforward g).map (C.inv.app (relativeExteriorSheaf f q)) =
      B.unit.app (relativeExteriorSheaf f q) :=
    Adjunction.unit_leftAdjointUniq_hom_app A B _
  apply (A.homEquiv _ _).injective
  change (A.homEquiv _ _) ((A.homEquiv _ _).symm
    (exteriorSheafPushMap (𝟙 _) f (g ≫ f) g (openCoefficientSquare f g) q)) = _
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  change exteriorSheafPushMap (𝟙 _) f (g ≫ f) g (openCoefficientSquare f g) q =
    A.unit.app (relativeExteriorSheaf f q) ≫
      (Scheme.Modules.pushforward g).map (C.inv.app (relativeExteriorSheaf f q) ≫ E.hom)
  rw [Functor.map_comp, ← Category.assoc, hu]
  exact (Iso.comp_inv_eq ((Scheme.Modules.pushforward g).mapIso E)).mp
    (exteriorSheafPushMap_openImmersion_inv f g q)

end EnvelopeProperty.Vanishing.ArithmeticCanonicalPushoutDifferential
