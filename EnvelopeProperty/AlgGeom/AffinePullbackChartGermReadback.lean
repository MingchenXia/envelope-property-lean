import EnvelopeProperty.AlgGeom.AffinePullbackStalkTensorReadback
import ModularCurves.ForMathlib.SchemeModulePushforwardBaseChange
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Actual categorical base-change charts and original module-unit germ transport -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TensorProduct
noncomputable section
universe u

namespace EnvelopeProperty.AffinePullbackChartGermReadback

variable {R B S : Type u} [CommRing R] [CommRing B] [CommRing S] [Algebra R S]
  {Y : Scheme.{u}} (π : Y ⟶ Spec (.of R)) (c : Spec (.of B) ⟶ Y)

/-- The original affine chart coefficient action comes from its actual original scheme composite. -/
@[instance_reducible] def chartCoefficientAlgebra : Algebra R B :=
  (Spec.preimage (c ≫ π)).hom.toAlgebra

/-- The actual original coefficient action recovers precisely the given scheme composite. -/
theorem chartCoefficientAlgebra_spec :
    letI := chartCoefficientAlgebra π c
    Spec.map (CommRingCat.ofHom (algebraMap R B)) = c ≫ π :=
  Spec.map_preimage (c ≫ π)

/-- The literal tensor spectrum is an actual chart of the categorical pullback of the ORIGINAL scheme. -/
def tensorChartMap :
    letI := chartCoefficientAlgebra π c
    Spec (.of (B ⊗[R] S)) ⟶
      pullback π (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  letI := chartCoefficientAlgebra π c
  exact (pullbackSpecIso R B S).inv ≫
    pullback.map _ _ π _ c (𝟙 _) (𝟙 _)
      (by simpa only [Category.comp_id] using chartCoefficientAlgebra_spec π c)
      (by simp)

/-- The original source projection is exactly the original left tensor-factor spectrum map and chart. -/
theorem tensorChartMap_fst :
    letI := chartCoefficientAlgebra π c
    tensorChartMap (S := S) π c ≫ pullback.fst π
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[R] S)) ≫ c := by
  let := chartCoefficientAlgebra π c
  simp only [tensorChartMap, Category.assoc, pullback.lift_fst, pullbackSpecIso_inv_fst_assoc]

/-- The original base projection is exactly the original right tensor-factor spectrum map. -/
theorem tensorChartMap_snd :
    letI := chartCoefficientAlgebra π c
    tensorChartMap (S := S) π c ≫ pullback.snd π
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : S →ₐ[R] B ⊗[R] S)) := by
  let := chartCoefficientAlgebra π c
  simp only [tensorChartMap, Category.assoc, pullback.lift_snd, Category.comp_id,
    pullbackSpecIso_inv_snd]

/-- Base change of the actual original affine open chart is again an actual open chart. -/
instance tensorChartMap_isOpenImmersion [IsOpenImmersion c] :
    IsOpenImmersion (tensorChartMap (S := S) π c) := by
  unfold tensorChartMap
  infer_instance

section ModuleTransport

variable {X U V W : Scheme.{u}} (a : U ⟶ V) (b : V ⟶ X) (M : X.Modules)

/-- The actual canonical pullback composition retains the ENTIRE original adjunction-unit morphism. -/
theorem pullbackComp_unit :
    ((Scheme.Modules.pullbackPushforwardAdjunction b).comp
      (Scheme.Modules.pullbackPushforwardAdjunction a)).unit.app M ≫
        (Scheme.Modules.pushforwardComp a b).hom.app
          ((Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback b).obj M)) =
    (Scheme.Modules.pullbackPushforwardAdjunction (a ≫ b)).unit.app M ≫
      (Scheme.Modules.pushforward (a ≫ b)).map ((Scheme.Modules.pullbackComp a b).inv.app M) := by
  have h := unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction b).comp
      (Scheme.Modules.pullbackPushforwardAdjunction a))
    (Scheme.Modules.pullbackPushforwardAdjunction (a ≫ b))
    (Scheme.Modules.pullbackComp a b).inv M
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at h
  exact h

private theorem unitTop_eq_appTop {P Q : Scheme.{u}} (f : P ⟶ Q) (N : Q.Modules)
    (m : Γ(N, ⊤)) : Scheme.Modules.affinePullbackUnitTop f N m =
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N).app ⊤ m := by
  simp [Scheme.Modules.affinePullbackUnitTop, Scheme.Modules.Hom.app]
  rfl

/-- The original top-section unit along a composite is the actual twice-pulled original unit. -/
theorem pullbackComp_unitTop (m : Γ(M, ⊤)) :
    ((Scheme.Modules.pullbackComp a b).inv.app M).app ⊤
      (Scheme.Modules.affinePullbackUnitTop (a ≫ b) M m) =
    Scheme.Modules.affinePullbackUnitTop a ((Scheme.Modules.pullback b).obj M)
      (Scheme.Modules.affinePullbackUnitTop b M m) := by
  have h := ConcreteCategory.congr_hom
    (congrArg (fun k => k.app (⊤ : X.Opens)) (pullbackComp_unit a b M)) m
  rw [unitTop_eq_appTop, unitTop_eq_appTop, unitTop_eq_appTop]
  simpa [Adjunction.comp_unit_app, Scheme.Modules.Hom.comp_app,
    ConcreteCategory.comp_apply, Scheme.Modules.pushforward_map_app,
    Scheme.Modules.pushforwardComp_hom_app_app, Scheme.Modules.pushforward_obj_obj,
    Scheme.Hom.preimage_top, CategoryTheory.id_apply, ModuleCat.id_apply, AddCommGrpCat.id_apply] using h.symm

/-- The actual commuting square gives the canonical isomorphism of the SAME original iterated pullbacks. -/
def squarePullbackIso (c : U ⟶ X) (π : V ⟶ X) (g : W ⟶ U) (j : W ⟶ V)
    (h : j ≫ π = g ≫ c) (M : X.Modules) :
    (Scheme.Modules.pullback j).obj ((Scheme.Modules.pullback π).obj M) ≅
      (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback c).obj M) :=
  (Scheme.Modules.pullbackComp j π).app M ≪≫
    (Scheme.Modules.pullbackCongr h).app M ≪≫
      ((Scheme.Modules.pullbackComp g c).app M).symm

/-- Equality of actual original scheme maps preserves the original top-level pullback unit. -/
theorem pullbackCongr_unitTop {P Q : Scheme.{u}} {f g : P ⟶ Q} (h : f = g)
    (N : Q.Modules) (m : Γ(N, ⊤)) :
    ((Scheme.Modules.pullbackCongr h).hom.app N).app ⊤
      (Scheme.Modules.affinePullbackUnitTop f N m) =
        Scheme.Modules.affinePullbackUnitTop g N m := by
  subst g
  simp [Scheme.Modules.pullbackCongr]

private theorem moduleIso_hom_inv_top_apply {P : Scheme.{u}} {N N' : P.Modules}
    (e : N ≅ N') (s : Γ(N', ⊤)) : e.hom.app ⊤ (e.inv.app ⊤ s) = s := by
  have h := ConcreteCategory.congr_hom (congrArg (fun k => k.app (⊤ : P.Opens)) e.inv_hom_id) s
  simpa only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app,
    ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using h

/-- The actual chart-square isomorphism preserves the original twice-pulled unit section. -/
theorem squarePullbackIso_unitTop {P Q A C : Scheme.{u}} (c : A ⟶ Q) (π : P ⟶ Q)
    (g : C ⟶ A) (j : C ⟶ P) (h : j ≫ π = g ≫ c) (N : Q.Modules) (s : Γ(N, ⊤)) :
    (squarePullbackIso c π g j h N).hom.app ⊤
      (Scheme.Modules.affinePullbackUnitTop j ((Scheme.Modules.pullback π).obj N)
        (Scheme.Modules.affinePullbackUnitTop π N s)) =
    Scheme.Modules.affinePullbackUnitTop g ((Scheme.Modules.pullback c).obj N)
      (Scheme.Modules.affinePullbackUnitTop c N s) := by
  rw [← pullbackComp_unitTop j π N s]
  change ((Scheme.Modules.pullbackComp g c).inv.app N).app ⊤
    (((Scheme.Modules.pullbackCongr h).hom.app N).app ⊤
      (((Scheme.Modules.pullbackComp j π).hom.app N).app ⊤
        (((Scheme.Modules.pullbackComp j π).inv.app N).app ⊤
          (Scheme.Modules.affinePullbackUnitTop (j ≫ π) N s)))) = _
  have hc := moduleIso_hom_inv_top_apply ((Scheme.Modules.pullbackComp j π).app N)
    (Scheme.Modules.affinePullbackUnitTop (j ≫ π) N s)
  change ((Scheme.Modules.pullbackComp j π).hom.app N).app ⊤
    (((Scheme.Modules.pullbackComp j π).inv.app N).app ⊤
      (Scheme.Modules.affinePullbackUnitTop (j ≫ π) N s)) = _ at hc
  rw [hc, pullbackCongr_unitTop h N s, pullbackComp_unitTop g c N s]

/-- EVERY actual chart scalar is retained on the SAME twice-pulled original unit. -/
theorem squarePullbackIso_unitTop_smul {P Q A C : Scheme.{u}} (c : A ⟶ Q) (π : P ⟶ Q)
    (g : C ⟶ A) (j : C ⟶ P) (h : j ≫ π = g ≫ c) (N : Q.Modules)
    (r : Γ(C, ⊤)) (s : Γ(N, ⊤)) :
    (squarePullbackIso c π g j h N).hom.app ⊤
      (r • Scheme.Modules.affinePullbackUnitTop j ((Scheme.Modules.pullback π).obj N)
        (Scheme.Modules.affinePullbackUnitTop π N s)) =
    r • Scheme.Modules.affinePullbackUnitTop g ((Scheme.Modules.pullback c).obj N)
      (Scheme.Modules.affinePullbackUnitTop c N s) := by
  rw [Scheme.Modules.Hom.app_smul, squarePullbackIso_unitTop]

/-- Genuine original module isomorphisms preserve vanishing of actual point germs. -/
theorem moduleIso_germ_eq_zero_iff {P : Scheme.{u}} {N N' : P.Modules}
    (e : N ≅ N') (x : P) (s : Γ(N, ⊤)) :
    N'.presheaf.germ ⊤ x trivial (e.hom.app ⊤ s) = 0 ↔
      N.presheaf.germ ⊤ x trivial s = 0 := by
  let eP := (Scheme.Modules.toPresheaf P).mapIso e
  let eS := (TopCat.Presheaf.stalkFunctor Ab x).mapIso eP
  have he := TopCat.Presheaf.stalkFunctor_map_germ_apply ⊤ x trivial e.hom.mapPresheaf s
  have hi : Function.Injective eS.hom :=
    (AddCommGrpCat.mono_iff_injective eS.hom).mp inferInstance
  change eS.hom (N.presheaf.germ ⊤ x trivial s) =
    N'.presheaf.germ ⊤ x trivial (e.hom.app ⊤ s) at he
  rw [← he]
  constructor
  · intro h
    apply hi
    simpa only [map_zero] using h
  · intro h
    rw [h, map_zero]

section Restriction

variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f] (N : Q.Modules)

/-- The literal original global section restricted to the image of the actual open chart. -/
def restrictedTopSection (s : Γ(N, ⊤)) : Γ(N.restrict f, ⊤) :=
  (N.restrictAppIso f ⊤).inv (N.presheaf.map
    (homOfLE (show f ''ᵁ (⊤ : P.Opens) ≤ ⊤ from le_top)).op s)

private theorem restrictedTopSection_eq_map (s : Γ(N, ⊤)) :
    restrictedTopSection f N s = N.presheaf.map
      (homOfLE (show f ''ᵁ (⊤ : P.Opens) ≤ ⊤ from le_top)).op s := rfl

/-- Actual open-chart restriction preserves vanishing of the SAME original point germ. -/
theorem restrictedGerm_eq_zero_iff (x : P) (s : Γ(N, ⊤)) :
    (N.restrict f).presheaf.germ ⊤ x trivial (restrictedTopSection f N s) = 0 ↔
      N.presheaf.germ ⊤ (f x) trivial s = 0 := by
  constructor
  · intro h
    obtain ⟨V, hxV, i, j, he⟩ := (N.restrict f).presheaf.germ_eq (U := ⊤) (V := ⊤) x trivial trivial
      (restrictedTopSection f N s) 0 (by simpa only [map_zero] using h)
    have hr : (N.restrict f).presheaf.map i.op (restrictedTopSection f N s) = 0 := by
      simpa only [map_zero] using he
    have hz : N.presheaf.map (homOfLE (show f ''ᵁ V ≤ ⊤ from le_top)).op s = 0 := by
      change N.presheaf.map (f.opensFunctor.map i).op
        (N.presheaf.map (homOfLE le_top).op s) = 0 at hr
      rw [← N.presheaf.map_comp_apply] at hr
      exact hr
    have hx : f x ∈ f ''ᵁ V := ⟨x, hxV, rfl⟩
    have hg := N.presheaf.germ_res_apply (homOfLE (show f ''ᵁ V ≤ ⊤ from le_top)) (f x) hx s
    rw [hz, map_zero] at hg
    exact hg.symm
  · intro h
    obtain ⟨V, hxV, i, j, he⟩ := N.presheaf.germ_eq (U := ⊤) (V := ⊤) (f x) trivial trivial s 0
      (by simpa only [map_zero] using h)
    have hr : N.presheaf.map i.op s = 0 := by simpa only [map_zero] using he
    let U := f ⁻¹ᵁ V
    have hxU : x ∈ U := hxV
    have hz : (N.restrict f).presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
        (restrictedTopSection f N s) = 0 := by
      have he := congrArg (N.presheaf.map (homOfLE (f.image_preimage_le V)).op) hr
      rw [map_zero, ← N.presheaf.map_comp_apply] at he
      change N.presheaf.map (f.opensFunctor.map (homOfLE le_top)).op
        (N.presheaf.map (homOfLE le_top).op s) = 0
      rw [← N.presheaf.map_comp_apply]
      exact he
    have hg := (N.restrict f).presheaf.germ_res_apply
      (homOfLE (show U ≤ ⊤ from le_top)) x hxU (restrictedTopSection f N s)
    rw [hz, map_zero] at hg
    exact hg.symm

/-- The ACTUAL restriction/pullback isomorphism retains the original pullback-unit section. -/
theorem restrictPullbackIso_unitTop (s : Γ(N, ⊤)) :
    ((Scheme.Modules.restrictFunctorIsoPullback f).hom.app N).app ⊤
      (restrictedTopSection f N s) = Scheme.Modules.affinePullbackUnitTop f N s := by
  rw [unitTop_eq_appTop, restrictedTopSection_eq_map]
  have h := ConcreteCategory.congr_hom
    (congrArg (fun k => k.app (⊤ : Q.Opens))
      (Adjunction.unit_leftAdjointUniq_hom_app (Scheme.Modules.restrictAdjunction f)
        (Scheme.Modules.pullbackPushforwardAdjunction f) N)) s
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    Scheme.Modules.pushforward_map_app, Scheme.Modules.restrictAdjunction_unit_app_app,
    Scheme.Modules.restrictFunctorIsoPullback, Scheme.Modules.pushforward_obj_obj,
    Scheme.Hom.preimage_top] at h ⊢
  convert h using 1 <;> rfl

/-- Original actual chart pullback-unit germs vanish exactly with the SAME original scheme germ. -/
theorem openPullbackUnitGerm_eq_zero_iff (x : P) (s : Γ(N, ⊤)) :
    ((Scheme.Modules.pullback f).obj N).presheaf.germ ⊤ x trivial
      (Scheme.Modules.affinePullbackUnitTop f N s) = 0 ↔
        N.presheaf.germ ⊤ (f x) trivial s = 0 := by
  rw [← restrictPullbackIso_unitTop f N s]
  exact (moduleIso_germ_eq_zero_iff ((Scheme.Modules.restrictFunctorIsoPullback f).app N)
    x (restrictedTopSection f N s)).trans (restrictedGerm_eq_zero_iff f N x s)

/-- The original actual global scalar is retained by the original top pullback-unit map. -/
theorem pullbackUnitTop_smul {P Q : Scheme.{u}} (f : P ⟶ Q) (N : Q.Modules)
    (r : Γ(Q, ⊤)) (s : Γ(N, ⊤)) :
    Scheme.Modules.affinePullbackUnitTop f N (r • s) =
      f.appTop r • Scheme.Modules.affinePullbackUnitTop f N s := by
  rw [unitTop_eq_appTop, unitTop_eq_appTop]
  exact (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N).val.app (.op ⊤)).hom.map_smul r s

/-- The SAME original global pulled section is read on the actual commuting open chart, without a stalk certificate. -/
theorem squareChartGerm_eq_zero_iff {P Q A C : Scheme.{u}} (c : A ⟶ Q) (π : P ⟶ Q)
    (g : C ⟶ A) (j : C ⟶ P) [IsOpenImmersion j] (h : j ≫ π = g ≫ c)
    (N : Q.Modules) (x : C) (r : Γ(P, ⊤)) (s : Γ(N, ⊤)) :
    ((Scheme.Modules.pullback π).obj N).presheaf.germ ⊤ (j x) trivial
      (r • Scheme.Modules.affinePullbackUnitTop π N s) = 0 ↔
    ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback c).obj N)).presheaf.germ ⊤ x trivial
      (j.appTop r • Scheme.Modules.affinePullbackUnitTop g ((Scheme.Modules.pullback c).obj N)
        (Scheme.Modules.affinePullbackUnitTop c N s)) = 0 := by
  have ho := (openPullbackUnitGerm_eq_zero_iff j ((Scheme.Modules.pullback π).obj N) x
    (r • Scheme.Modules.affinePullbackUnitTop π N s)).symm
  rw [pullbackUnitTop_smul] at ho
  have hi := moduleIso_germ_eq_zero_iff (squarePullbackIso c π g j h N) x
    (j.appTop r • Scheme.Modules.affinePullbackUnitTop j ((Scheme.Modules.pullback π).obj N)
      (Scheme.Modules.affinePullbackUnitTop π N s))
  rw [squarePullbackIso_unitTop_smul] at hi
  exact ho.trans hi.symm

end Restriction

end ModuleTransport

/-- EVERY actual base coefficient retains its literal right-tensor image on the actual categorical chart. -/
theorem tensorChartMap_baseCoefficient (s : S) :
    letI := chartCoefficientAlgebra π c
    (tensorChartMap (S := S) π c).appTop.hom
      (ProperBirationalSections.coefficientMap
        (pullback.snd π (Spec.map (CommRingCat.ofHom (algebraMap R S)))) s) =
    (Scheme.ΓSpecIso (.of (B ⊗[R] S))).inv.hom
      ((Algebra.TensorProduct.includeRight : S →ₐ[R] B ⊗[R] S) s) := by
  let := chartCoefficientAlgebra π c
  change (((Scheme.ΓSpecIso (.of S)).inv ≫
    (pullback.snd π (Spec.map (CommRingCat.ofHom (algebraMap R S)))).appTop ≫
      (tensorChartMap (S := S) π c).appTop).hom s) = _
  rw [← Scheme.Hom.comp_appTop, tensorChartMap_snd, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

/-- The SAME original categorical pulled module germ is read on its actual tensor chart. -/
theorem tensorChartGerm_eq_zero_iff [IsOpenImmersion c] (N : Y.Modules) :
    letI := chartCoefficientAlgebra π c
    ∀ (x : Spec (.of (B ⊗[R] S)))
      (r : Γ(pullback π (Spec.map (CommRingCat.ofHom (algebraMap R S))), ⊤)) (s : Γ(N, ⊤)),
    ((Scheme.Modules.pullback (pullback.fst π
      (Spec.map (CommRingCat.ofHom (algebraMap R S))))).obj N).presheaf.germ ⊤
        (tensorChartMap (S := S) π c x) trivial
      (r • Scheme.Modules.affinePullbackUnitTop (pullback.fst π
        (Spec.map (CommRingCat.ofHom (algebraMap R S)))) N s) = 0 ↔
    ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[R] S)))).obj
          ((Scheme.Modules.pullback c).obj N)).presheaf.germ ⊤ x trivial
      ((tensorChartMap (S := S) π c).appTop r •
        Scheme.Modules.affinePullbackUnitTop (Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[R] S)))
            ((Scheme.Modules.pullback c).obj N) (Scheme.Modules.affinePullbackUnitTop c N s)) = 0 := by
  let := chartCoefficientAlgebra π c
  intro x r s
  exact squareChartGerm_eq_zero_iff c (pullback.fst π
    (Spec.map (CommRingCat.ofHom (algebraMap R S))))
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[R] S)))
          (tensorChartMap (S := S) π c) (tensorChartMap_fst π c) N x r s

/-- ALL original base scalars, including entire formal series, retain their literal tensor-chart germ test. -/
theorem tensorChartBaseScalarGerm_eq_zero_iff [IsOpenImmersion c] (N : Y.Modules) :
    letI := chartCoefficientAlgebra π c
    ∀ (x : Spec (.of (B ⊗[R] S))) (a : S) (s : Γ(N, ⊤)),
    ((Scheme.Modules.pullback (pullback.fst π
      (Spec.map (CommRingCat.ofHom (algebraMap R S))))).obj N).presheaf.germ ⊤
        (tensorChartMap (S := S) π c x) trivial
      ((ProperBirationalSections.coefficientMap
        (pullback.snd π (Spec.map (CommRingCat.ofHom (algebraMap R S)))) a) •
          Scheme.Modules.affinePullbackUnitTop (pullback.fst π
            (Spec.map (CommRingCat.ofHom (algebraMap R S)))) N s) = 0 ↔
    ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[R] S)))).obj
          ((Scheme.Modules.pullback c).obj N)).presheaf.germ ⊤ x trivial
      (((Algebra.TensorProduct.includeRight : S →ₐ[R] B ⊗[R] S) a) •
        (show (moduleSpecΓFunctor (R := CommRingCat.of (B ⊗[R] S))).obj
          ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[R] S)))).obj
              ((Scheme.Modules.pullback c).obj N)) from
          Scheme.Modules.affinePullbackUnitTop (Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[R] S)))
              ((Scheme.Modules.pullback c).obj N) (Scheme.Modules.affinePullbackUnitTop c N s))) = 0 := by
  let := chartCoefficientAlgebra π c
  intro x a s
  have h := tensorChartGerm_eq_zero_iff π c N x
    (ProperBirationalSections.coefficientMap
      (pullback.snd π (Spec.map (CommRingCat.ofHom (algebraMap R S)))) a) s
  rw [tensorChartMap_baseCoefficient] at h
  exact h

/-- The SAME actual categorical pulled section is read by the literal original localization tensor,
with quasicoherence of the actual original affine chart module as its only module hypothesis. -/
theorem tensorChartBaseScalarGerm_eq_zero_iff_localizedTensor [IsOpenImmersion c]
    (N : Y.Modules) [((Scheme.Modules.pullback c).obj N).IsQuasicoherent] :
    letI := chartCoefficientAlgebra π c
    ∀ (x : Spec (.of (B ⊗[R] S))) (a : S) (s : Γ(N, ⊤)),
    let T := B ⊗[R] S
    let D := Localization.AtPrime x.asIdeal
    letI : Algebra B D := ((algebraMap T D).comp
      (Algebra.TensorProduct.includeLeftRingHom : B →+* T)).toAlgebra
    letI : Module B D := Algebra.toModule
    ((Scheme.Modules.pullback (pullback.fst π
      (Spec.map (CommRingCat.ofHom (algebraMap R S))))).obj N).presheaf.germ ⊤
        (tensorChartMap (S := S) π c x) trivial
      ((ProperBirationalSections.coefficientMap
        (pullback.snd π (Spec.map (CommRingCat.ofHom (algebraMap R S)))) a) •
          Scheme.Modules.affinePullbackUnitTop (pullback.fst π
            (Spec.map (CommRingCat.ofHom (algebraMap R S)))) N s) = 0 ↔
    (algebraMap T D ((Algebra.TensorProduct.includeRight : S →ₐ[R] T) a)) ⊗ₜ[B]
      (show AffineModuleFlatBaseChange.sections (𝟙 (Spec (.of B)))
        ((Scheme.Modules.pullback c).obj N) from Scheme.Modules.affinePullbackUnitTop c N s) = 0 := by
  let := chartCoefficientAlgebra π c
  intro x a s
  let T := B ⊗[R] S
  let D := Localization.AtPrime x.asIdeal
  let : Algebra B D := ((algebraMap T D).comp
    (Algebra.TensorProduct.includeLeftRingHom : B →+* T)).toAlgebra
  let : Module B D := Algebra.toModule
  let M := (Scheme.Modules.pullback c).obj N
  let m : AffineModuleFlatBaseChange.sections (𝟙 (Spec (.of B))) M :=
    Scheme.Modules.affinePullbackUnitTop c N s
  have hg := tensorChartBaseScalarGerm_eq_zero_iff π c N x a s
  have ht := AffinePullbackStalkTensorReadback.pullbackGerm_eq_zero_iff_identitySectionsTensor
    (B := CommRingCat.of B) (T := CommRingCat.of T) M
      (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : B →+* T)) x
        ((Algebra.TensorProduct.includeRight : S →ₐ[R] T) a) m
  exact hg.trans ht

end EnvelopeProperty.AffinePullbackChartGermReadback
