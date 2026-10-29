import EnvelopeProperty.AlgGeom.SeshadriAmplenessCriterionPrimePiece
import EnvelopeProperty.AlgGeom.SeshadriAmplenessCriterionCoherentACC
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Order.OrderIsoNat

/-! # Actual finite coherent prime filtrations on general projective schemes

The target is a finite sequence of actual original short exact extensions.
Termination is derived only for the internal coherent subobject family by
the already proved original finite-affine ACC theorem.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Scheme.Modules
universe u
namespace EnvelopeProperty.SeshadriAmplenessCriterion

/-- An explicit finite length of actual coherent short exact prime extensions.
This is an output notion; no filtration is an assumption of the existence goal. -/
inductive ActualCoherentPrimeFiltration {X : Scheme.{u}} : ℕ → X.Modules → Prop where
  | zero (M : X.Modules) (hM : IsZero M) : ActualCoherentPrimeFiltration 0 M
  | iso {n : ℕ} {M N : X.Modules} (e : M ≅ N)
      (hM : ActualCoherentPrimeFiltration n M) : ActualCoherentPrimeFiltration n N
  | extension {n : ℕ} (S : ShortComplex X.Modules) (hS : S.ShortExact)
      (hQ₁ : S.X₁.IsQuasicoherent) (hQ₂ : S.X₂.IsQuasicoherent)
      (hQ₃ : S.X₃.IsQuasicoherent) (hF₁ : S.X₁.IsFiniteType)
      (hF₂ : S.X₂.IsFiniteType) (hF₃ : S.X₃.IsFiniteType)
      (eta : X)
      (T : (Scheme.IdealSheafData.vanishingIdeal
        (⟨closure ({eta} : Set X), isClosed_closure⟩ : Closeds X)).subscheme.Modules)
      (hT : IsInvertible T)
      (e : S.X₃ ≅ (Scheme.Modules.pushforward
        (Scheme.IdealSheafData.vanishingIdeal
          (⟨closure ({eta} : Set X), isClosed_closure⟩ : Closeds X)).subschemeι).obj T)
      (hM : ActualCoherentPrimeFiltration n S.X₁) :
      ActualCoherentPrimeFiltration (n + 1) S.X₂

private abbrev coherentSubobjects {X : Scheme.{u}} (F : X.Modules) :=
  { A : Subobject F // (A : X.Modules).IsQuasicoherent ∧ (A : X.Modules).IsFiniteType }

private theorem coherentSubobjects_wellFoundedGT
    {X : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    WellFoundedGT (coherentSubobjects F) := by
  apply wellFoundedGT_iff_monotone_chain_condition.mpr
  intro c
  let d : ℕ →o Subobject F :=
    ⟨fun n => (c n).val, fun _ _ h => c.monotone h⟩
  obtain ⟨N, hN⟩ := coherent_subobject_chain_stabilizes F d (fun n => (c n).property.1)
  exact ⟨N, fun n hn => Subtype.ext (hN n hn)⟩

private theorem finiteType_of_original_iso {X : Scheme.{u}} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] [N.IsFiniteType] (e : M ≅ N) :
    M.IsFiniteType := by
  apply isFiniteType_of_sections_module_finite M
  intro U
  let : Module.Finite Γ(X, U.1) Γ(N, U.1) :=
    sections_module_finite_of_isFiniteType_of_isAffineOpen N U
  let E : X.Modules ⥤ ModuleCat.{u} Γ(X, U.1) :=
    SheafOfModules.evaluation X.ringCatSheaf (op U.1)
  let eU : Γ(M, U.1) ≃ₗ[Γ(X, U.1)] Γ(N, U.1) := (E.mapIso e).toLinearEquiv
  exact Module.Finite.equiv eU.symm

private theorem finiteType_of_original_cokernel {X : Scheme.{u}}
    {A F : X.Modules} [A.IsQuasicoherent] [F.IsQuasicoherent] [F.IsFiniteType]
    (a : A ⟶ F) : (cokernel a).IsFiniteType := by
  let Q := cokernel a
  let : Q.IsQuasicoherent := isQuasicoherent_cokernel a
  apply isFiniteType_of_sections_module_finite Q
  intro U
  let : Module.Finite Γ(X, U.1) Γ(F, U.1) :=
    sections_module_finite_of_isFiniteType_of_isAffineOpen F U
  let q : Γ(F, U.1) →ₗ[Γ(X, U.1)] Γ(Q, U.1) :=
    ((cokernel.π a).val.app (op U.1)).hom
  have hq : Function.Surjective q :=
    isQuasicoherent_app_surjective_of_epi U.1 U.2 (cokernel.π a)
  exact Module.Finite.of_surjective q hq

private theorem original_stalk_subsingleton_of_isZero {X : Scheme.{u}}
    (M : X.Modules) (hM : IsZero M) (x : X) :
    Subsingleton (M.presheaf.stalk x) := by
  have hid : (𝟙 M : M ⟶ M) = 0 := (IsZero.iff_id_eq_zero M).mp hM
  have hz (m : M.presheaf.stalk x) : m = 0 := by
    obtain ⟨U, hxU, s, hs⟩ := M.presheaf.exists_germ_eq m
    have hs0 : s = 0 := by
      have h := congrArg (fun v : M ⟶ M => v.val.app (op U) s) hid
      exact h
    exact hs.symm.trans ((congrArg (M.presheaf.germ U x hxU) hs0).trans
      (M.presheaf.germ U x hxU).hom.map_zero)
  exact ⟨fun m n => (hz m).trans (hz n).symm⟩

private def kernelPullback_projection
    {C : Type*} [Category C] [Abelian C] {F P Q : C}
    (q : F ⟶ Q) (v : P ⟶ Q) [Mono v] :
    kernel (q ≫ cokernel.π v) ⟶ P :=
  Abelian.monoLift v (kernel.ι (q ≫ cokernel.π v) ≫ q)
    (by simpa only [Category.assoc] using kernel.condition (q ≫ cokernel.π v))

private theorem kernelPullback_isPullback
    {C : Type*} [Category C] [Abelian C] {F P Q : C}
    (q : F ⟶ Q) (v : P ⟶ Q) [Mono v] :
    IsPullback (kernel.ι (q ≫ cokernel.π v)) (kernelPullback_projection q v) q v := by
  let d := kernel.ι (q ≫ cokernel.π v)
  let pi := kernelPullback_projection q v
  have hcomm : d ≫ q = pi ≫ v :=
    (Abelian.monoLift_comp v _ _).symm
  let lift (s : PullbackCone q v) : s.pt ⟶ kernel (q ≫ cokernel.π v) :=
    kernel.lift _ s.fst (by
      rw [← Category.assoc, s.condition, Category.assoc, cokernel.condition, comp_zero])
  have hleft (s : PullbackCone q v) : lift s ≫ d = s.fst := kernel.lift_ι _ _ _
  refine { w := hcomm, isLimit' := ⟨?_⟩ }
  refine PullbackCone.IsLimit.mk hcomm lift hleft ?_ ?_
  · intro s
    apply (cancel_mono v).mp
    calc
      (lift s ≫ pi) ≫ v = lift s ≫ (pi ≫ v) := Category.assoc _ _ _
      _ = lift s ≫ (d ≫ q) := congrArg (fun r => lift s ≫ r) hcomm.symm
      _ = (lift s ≫ d) ≫ q := (Category.assoc _ _ _).symm
      _ = s.fst ≫ q := congrArg (fun r => r ≫ q) (hleft s)
      _ = s.snd ≫ v := s.condition
  · intro s m hm _
    apply (cancel_mono d).mp
    exact hm.trans (hleft s).symm

private theorem kernelPullback_shortExact
    {C : Type*} [Category C] [Abelian C] {A F P : C}
    (a : A ⟶ F) [Mono a] (v : P ⟶ cokernel a) [Mono v] :
    let q := cokernel.π a
    let pi := kernelPullback_projection q v
    let hzero : a ≫ (q ≫ cokernel.π v) = 0 := by
      rw [← Category.assoc, cokernel.condition, zero_comp]
    let k := kernel.lift _ a hzero
    ∃ hk : k ≫ pi = 0, (ShortComplex.mk k pi hk).ShortExact := by
  let q := cokernel.π a
  let d := kernel.ι (q ≫ cokernel.π v)
  let pi := kernelPullback_projection q v
  have hzero : a ≫ (q ≫ cokernel.π v) = 0 := by
    rw [← Category.assoc, cokernel.condition, zero_comp]
  let k := kernel.lift _ a hzero
  have hkd : k ≫ d = a := kernel.lift_ι _ _ _
  have sq : IsPullback d pi q v := kernelPullback_isPullback q v
  have hcomm : d ≫ q = pi ≫ v := sq.w
  have hkpi : k ≫ pi = 0 := by
    apply (cancel_mono v).mp
    rw [Category.assoc, ← hcomm, ← Category.assoc, hkd, cokernel.condition, zero_comp]
  let S := ShortComplex.mk k pi hkpi
  have hf : IsLimit (KernelFork.ofι k hkpi) := by
    let lift (s : KernelFork pi) : s.pt ⟶ A :=
      Abelian.monoLift a (s.ι ≫ d) (by
        rw [Category.assoc, hcomm, ← Category.assoc, s.condition, zero_comp])
    refine Fork.IsLimit.mk _ lift ?_ ?_
    · intro s
      apply (cancel_mono d).mp
      change (lift s ≫ k) ≫ d = s.ι ≫ d
      rw [Category.assoc, hkd]
      exact Abelian.monoLift_comp a _ _
    · intro s m hm
      apply (cancel_mono a).mp
      calc
        m ≫ a = m ≫ (k ≫ d) := congrArg (fun r => m ≫ r) hkd.symm
        _ = (m ≫ k) ≫ d := (Category.assoc _ _ _).symm
        _ = s.ι ≫ d := congrArg (fun r => r ≫ d) hm
        _ = lift s ≫ a := (Abelian.monoLift_comp a _ _).symm
  have hpi : Epi pi := by
    let e := sq.isoPullback
    have he : e.hom ≫ pullback.snd q v = pi := sq.isoPullback_hom_snd
    have hc : Epi (e.hom ≫ pullback.snd q v) := by infer_instance
    exact he ▸ hc
  refine ⟨hkpi, ShortComplex.ShortExact.mk' (S.exact_of_f_is_kernel hf) ?_ hpi⟩
  exact mono_of_isLimit_fork hf

private theorem kernelPullback_coherent {X : Scheme.{u}} [IsLocallyNoetherian X]
    {A F P : X.Modules} [A.IsQuasicoherent] [F.IsQuasicoherent] [F.IsFiniteType]
    [P.IsQuasicoherent] (a : A ⟶ F) (v : P ⟶ cokernel a) :
    (kernel (cokernel.π a ≫ cokernel.π v)).IsQuasicoherent ∧
      (kernel (cokernel.π a ≫ cokernel.π v)).IsFiniteType := by
  let : (cokernel a).IsQuasicoherent := isQuasicoherent_cokernel a
  let : (cokernel v).IsQuasicoherent := isQuasicoherent_cokernel v
  exact ⟨isQuasicoherent_kernel _, isFiniteType_kernel _⟩

private theorem coherentFiltered_nonempty
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    { A : coherentSubobjects F |
      ∃ n, ActualCoherentPrimeFiltration n (A.val : X.Modules) }.Nonempty := by
  let K := kernel (𝟙 F)
  let : K.IsQuasicoherent := isQuasicoherent_kernel (𝟙 F)
  let : K.IsFiniteType := isFiniteType_kernel (𝟙 F)
  let i : K ⟶ F := kernel.ι (𝟙 F)
  have hi : i = 0 := by simpa only [Category.comp_id] using kernel.condition (𝟙 F)
  have hK : IsZero K := by
    apply (IsZero.iff_id_eq_zero K).mpr
    apply (cancel_mono i).mp
    simp only [hi, comp_zero]
  let A : Subobject F := Subobject.mk i
  let e : (A : X.Modules) ≅ K := Subobject.underlyingIso i
  have hAQC : (A : X.Modules).IsQuasicoherent :=
    (isQuasicoherent X).prop_of_iso e.symm (inferInstance : K.IsQuasicoherent)
  let : (A : X.Modules).IsQuasicoherent := hAQC
  have hAFT : (A : X.Modules).IsFiniteType := finiteType_of_original_iso e
  refine ⟨⟨A, hAQC, hAFT⟩, 0, ?_⟩
  exact ActualCoherentPrimeFiltration.iso e.symm (ActualCoherentPrimeFiltration.zero K hK)

private theorem exists_maximal_coherentFiltered
    {X : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ A : coherentSubobjects F,
      (∃ n, ActualCoherentPrimeFiltration n (A.val : X.Modules)) ∧
      ∀ B : coherentSubobjects F,
        (∃ n, ActualCoherentPrimeFiltration n (B.val : X.Modules)) → ¬ A < B := by
  let S : Set (coherentSubobjects F) :=
    { A | ∃ n, ActualCoherentPrimeFiltration n (A.val : X.Modules) }
  have hWF : WellFoundedGT (coherentSubobjects F) := coherentSubobjects_wellFoundedGT F
  obtain ⟨A, hA, hmax⟩ := hWF.wf.has_min S (coherentFiltered_nonempty F)
  exact ⟨A, hA, fun B hB => hmax B hB⟩

private theorem isIso_of_equal_mono_subobjects
    {C : Type*} [Category C] {A B F : C} (a : A ⟶ F) (d : B ⟶ F)
    [Mono a] [Mono d] (k : A ⟶ B) (hk : k ≫ d = a)
    (h : Subobject.mk a = Subobject.mk d) : IsIso k := by
  let f : MonoOver.mk a ⟶ MonoOver.mk d := MonoOver.homMk k hk
  exact (MonoOver.isIso_hom_left_iff_subobjectMk_eq f).mpr h

/-- Every original coherent module on the actual projective scheme has a
genuine finite prime filtration. All strata, lines, short exact sequences
and the finite termination witness are constructed internally. -/
theorem exists_finite_coherent_primeFiltration
    {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsProjective p]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ n : ℕ, ActualCoherentPrimeFiltration n F := by
  classical
  let hp : IsProjectiveFactorization p := ProjectiveFactorizationRingIso.of_isProjective p
  let : IsProper p := hp.isProper
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  obtain ⟨A, hAfil, hmax⟩ := exists_maximal_coherentFiltered F
  obtain ⟨n, hAfil⟩ := hAfil
  let M : X.Modules := (A.val : X.Modules)
  let a : M ⟶ F := A.val.arrow
  let : M.IsQuasicoherent := A.property.1
  let : M.IsFiniteType := A.property.2
  let : Mono a := Subobject.arrow_mono A.val
  let Q := cokernel a
  let : Q.IsQuasicoherent := isQuasicoherent_cokernel a
  let : Q.IsFiniteType := finiteType_of_original_cokernel a
  by_cases hQ : IsZero Q
  · let S := ShortComplex.mk a (cokernel.π a) (cokernel.condition a)
    have hf : IsLimit (KernelFork.ofι a (cokernel.condition a)) :=
      Abelian.monoIsKernelOfCokernel
        (CokernelCofork.ofπ (cokernel.π a) (cokernel.condition a)) (cokernelIsCokernel a)
    have hS : S.ShortExact :=
      ShortComplex.ShortExact.mk' (S.exact_of_f_is_kernel hf) inferInstance inferInstance
    have ha : IsIso a := hS.isIso_f_iff.mpr hQ
    let e : M ≅ F := @asIso X.Modules inferInstance _ _ a ha
    exact ⟨n, ActualCoherentPrimeFiltration.iso e hAfil⟩
  · obtain ⟨eta, T, hT, hPQC, hPFT, hPnz, v, hv⟩ :=
      exists_nonzero_coherent_line_primePiece p Q hQ
    let I := Scheme.IdealSheafData.vanishingIdeal
      (⟨closure ({eta} : Set X), isClosed_closure⟩ : Closeds X)
    let P : X.Modules := (Scheme.Modules.pushforward I.subschemeι).obj T
    let : P.IsQuasicoherent := hPQC
    let : P.IsFiniteType := hPFT
    let : Mono v := hv
    have hPnotzero : ¬ IsZero P := fun h =>
      hPnz (original_stalk_subsingleton_of_isZero P h eta)
    let q : F ⟶ Q := cokernel.π a
    let B := kernel (q ≫ cokernel.π v)
    let d : B ⟶ F := kernel.ι (q ≫ cokernel.π v)
    let pi : B ⟶ P := kernelPullback_projection q v
    have hzero : a ≫ (q ≫ cokernel.π v) = 0 := by
      rw [← Category.assoc, cokernel.condition, zero_comp]
    let j : M ⟶ B := kernel.lift _ a hzero
    have hjd : j ≫ d = a := kernel.lift_ι _ _ _
    have hseq := kernelPullback_shortExact a v
    change ∃ hj : j ≫ pi = 0, (ShortComplex.mk j pi hj).ShortExact at hseq
    obtain ⟨hjpi, hseq⟩ := hseq
    let S := ShortComplex.mk j pi hjpi
    obtain ⟨hBQC, hBFT⟩ := kernelPullback_coherent a v
    let : B.IsQuasicoherent := hBQC
    let : B.IsFiniteType := hBFT
    have hBfil : ActualCoherentPrimeFiltration (n + 1) B :=
      ActualCoherentPrimeFiltration.extension S hseq
        A.property.1 hBQC hPQC A.property.2 hBFT hPFT eta T hT (Iso.refl P) hAfil
    let BS : Subobject F := Subobject.mk d
    let eB : (BS : X.Modules) ≅ B := Subobject.underlyingIso d
    have hBSQC : (BS : X.Modules).IsQuasicoherent :=
      (isQuasicoherent X).prop_of_iso eB.symm hBQC
    let : (BS : X.Modules).IsQuasicoherent := hBSQC
    have hBSFT : (BS : X.Modules).IsFiniteType := finiteType_of_original_iso eB
    let BC : coherentSubobjects F := ⟨BS, hBSQC, hBSFT⟩
    have hBCfil : ActualCoherentPrimeFiltration (n + 1) (BC.val : X.Modules) :=
      ActualCoherentPrimeFiltration.iso eB.symm hBfil
    have hAB : A.val ≤ BS := Subobject.le_mk_of_comm (X := A.val) (f := d) j hjd
    have hneq : A ≠ BC := by
      intro heq
      have hval : A.val = BS := congrArg Subtype.val heq
      have hmk : Subobject.mk a = Subobject.mk d :=
        (Subobject.mk_arrow A.val).trans hval
      have hj : IsIso j := isIso_of_equal_mono_subobjects a d j hjd hmk
      have hPzero : IsZero P := hseq.isIso_f_iff.mp hj
      exact hPnotzero hPzero
    have hstrict : A < BC := lt_iff_le_and_ne.mpr ⟨hAB, hneq⟩
    exact False.elim (hmax BC ⟨n + 1, hBCfil⟩ hstrict)

#check @coherentSubobjects_wellFoundedGT
#print axioms coherentSubobjects_wellFoundedGT
#check @finiteType_of_original_cokernel
#print axioms finiteType_of_original_cokernel
#check @original_stalk_subsingleton_of_isZero
#print axioms original_stalk_subsingleton_of_isZero
#check @kernelPullback_shortExact
#print axioms kernelPullback_shortExact
#check @exists_maximal_coherentFiltered
#print axioms exists_maximal_coherentFiltered
#check @exists_finite_coherent_primeFiltration
#print axioms exists_finite_coherent_primeFiltration

end EnvelopeProperty.SeshadriAmplenessCriterion
