/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Global.ModelPSH

/-!
# The scaling action and homogeneous functions on a model

Let `𝒳 = (K, S, z)` be an integral multiprojective model (`EnvelopeProperty.MultiModel`,
`def:gl-model`) with analytification `𝒳^an` (`MultiModel.an`). This file implements the blueprint
nodes `def:gl-scaling` and `lem:gl-scaling` of the global chapter `global.tex` of the
formalization of Fang–Han–Xia, *The envelope property for unibranch projective varieties*
(FHX, §2.1, `eq:scaling-action`, `prop:BJ-package`(6)), following
Boucksom–Jonsson, *Global pluripotential theory over a trivially valued field* (BJ22), §1.1
(equation (1.3)) and §6.2 (Lemmas 6.13 and 6.14), together with the part
`PSH_hom(𝒳, θ)` of `def:gl-psh` (`MultiModel.IsPSHHom`). The rank-one template is
`EnvelopeProperty.Projective.Order` (`ProjBerk.rpow`, `ProjBerk.scaleFun`).

## The scaling action (`def:gl-scaling`)

* `MultiModel.rpow t ht v` (`t > 0`): `|p|_{t·v} = |p|_v ^ t`. It preserves multigradedness and
  the normalization `max_j |z^{(c)}_j| = 1`, so it acts on `𝒳^an`; `MultiModel.rpowHomeomorph`.
* `MultiModel.scaleFun t ht u`: `(t · u)(v) = t u(t⁻¹ · v)` on functions `𝒳^an → [-∞, +∞]`.
* `MultiModel.IsScaleHomogeneous u`: `u(t · v) = t u(v)` for all `t > 0`, equivalently
  `t · u = u` for all `t > 0` (`MultiModel.isScaleHomogeneous_iff_scaleFun_eq`).
* `MultiModel.homogenization u = û = inf_{t > 0} t · u` and the **Legendre slices**
  `MultiModel.legendreSlice u λ = û_λ = (u - λ)^`.
* `MultiModel.IsPSHHom θ u`: `u ∈ PSH_hom(𝒳, θ)`, i.e. `u` is `θ`-psh and homogeneous
  (`def:gl-psh`).

## Properties (`lem:gl-scaling`)

1. `MultiModel.continuous_rpow`, `MultiModel.continuous_rpow_prod` (joint continuity in
   `(t, v)`), `MultiModel.rpow_triv` (`⋆` is fixed) and `MultiModel.logSecAbs_rpow`
   (`log |f|(t · v) = t log |f|(v)`).
2. `MultiModel.FSData.scaleFun_eval`: `t · (m⁻¹ max_j (log |f_j| + λ_j)) =
   m⁻¹ max_j (log |f_j| + t λ_j)`; hence `MultiModel.IsFS.scaleFun`, `MultiModel.IsPSH.scaleFun`,
   `MultiModel.isPSH_scaleFun_iff` (`t · PSH(θ) = PSH(θ)`), and `MultiModel.isHomFS_iff`: the
   homogeneous Fubini–Study functions are exactly those of `𝓗_hom` (a homogeneous `φ ∈ 𝓗(a)`
   equals the limit `m⁻¹ max_j log |f_j|` of `t · φ` as `t → 0`).
3. `MultiModel.IsPSH.apply_triv_eq_zero`, `MultiModel.IsPSH.nonpos`: homogeneous psh functions
   vanish at `⋆` and are `≤ 0`.
4. `MultiModel.homogenization_le`, `MultiModel.isScaleHomogeneous_homogenization` and
   `MultiModel.IsScaleHomogeneous.le_homogenization`: `û ≤ u` is the largest homogeneous function
   below `u`; `MultiModel.homogenization_iInf`: homogenization commutes with **arbitrary** infima
   (this gives BJ22 Lemma 6.13, `û_i ↓ û` for `u_i ↓ u`, without the extremal argument), and
   `MultiModel.homogenization_mono`. At `⋆`: `MultiModel.homogenization_triv_of_nonneg`
   (`û(⋆) = 0` if `u(⋆) ∈ [0, ∞)`) and `MultiModel.homogenization_eq_bot` (`û ≡ -∞` if
   `u ≤ u(⋆) < 0`), BJ22 Example 6.12, Lemma 6.14.
5. `MultiModel.scaleFun_iSup`, `MultiModel.scaleFun_uscReg`: scaling commutes with pointwise
   suprema and usc regularization (via `MultiModel.uscReg_comp_rpow` and
   `EnvelopeProperty.uscReg_coe_mul`); `MultiModel.IsScaleHomogeneous.iSup`,
   `MultiModel.IsScaleHomogeneous.uscReg`, `MultiModel.IsScaleHomogeneous.uscReg_iSup`.

Also: `MultiModel.legendreSlice_le`, `MultiModel.legendreSlice_add_le` (`û_λ + λ ≤ u`),
`MultiModel.legendreSlice_antitone` (`λ ↦ û_λ` is decreasing) and `MultiModel.legendreSlice_mono`
(`u ↦ û_λ` is increasing), used in `thm:gl-homog-decomposition`.
-/

open scoped NNReal ENNReal Topology

open Set Topology Filter

noncomputable section

namespace EnvelopeProperty

universe u

namespace MultiModel

variable {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K] {r : ℕ}
  (X : MultiModel k K r)

/-! ### The scaling action on points (`def:gl-scaling`) -/

variable {X} in
/-- The scaling action preserves multigradedness. -/
theorem IsMultigraded.rpow {v : Berk k X.S} (hv : X.IsMultigraded v) (t : ℝ) (ht : 0 < t) :
    X.IsMultigraded (Berk.rpow t ht v) := fun p a => by
  simp only [Berk.rpow_val_apply]
  exact NNReal.rpow_le_rpow (hv p a) ht.le

variable {X} in
/-- The scaling action preserves the normalization `max_j |z^{(c)}_j| = 1`. -/
theorem IsNormalized.rpow {v : Berk k X.S} (hv : X.IsNormalized v) (t : ℝ) (ht : 0 < t) :
    X.IsNormalized (Berk.rpow t ht v) := fun c => by
  simp only [Berk.rpow_val_apply]
  have h := Finset.apply_sup_eq_sup_comp_of_linearOrder (s := Finset.univ)
    (f := fun j : Fin (X.M c + 1) => v.val (X.coordElem ⟨c, j⟩)) (fun x : ℝ≥0 => x ^ t)
    (NNReal.monotone_rpow_of_nonneg ht.le) (by simp [NNReal.zero_rpow ht.ne'])
  rw [hv c, NNReal.one_rpow] at h
  exact h.symm

/-- The **scaling action** of `t > 0` on `𝒳^an` (`def:gl-scaling`, FHX `eq:scaling-action`,
BJ22 §1.1): `|p|_{t·v} = |p|_v ^ t`, i.e. `(t v)(p) = t v(p)` in additive notation. -/
def rpow (t : ℝ) (ht : 0 < t) (v : X.an) : X.an :=
  ⟨Berk.rpow t ht v.1, v.2.1.rpow t ht, v.2.2.rpow t ht⟩

variable {X}

@[simp]
theorem coe_rpow (t : ℝ) (ht : 0 < t) (v : X.an) :
    (X.rpow t ht v : Berk k X.S) = Berk.rpow t ht v.1 :=
  rfl

theorem rpow_val_apply (t : ℝ) (ht : 0 < t) (v : X.an) (p : X.S) :
    (X.rpow t ht v).1.val p = v.1.val p ^ t :=
  rfl

variable (X) in
/-- **`lem:gl-scaling`(1)**: `v ↦ t · v` is continuous. -/
@[fun_prop]
theorem continuous_rpow (t : ℝ) (ht : 0 < t) : Continuous (X.rpow t ht) :=
  X.continuous_iff_an.2 fun p =>
    (NNReal.continuous_rpow_const ht.le).comp
      ((Berk.continuous_val_apply p).comp continuous_subtype_val)

variable (X) in
/-- **`lem:gl-scaling`(1)**: `(t, v) ↦ t · v` is jointly continuous on `ℝ_{>0} × 𝒳^an`. -/
theorem continuous_rpow_prod :
    Continuous fun q : Set.Ioi (0 : ℝ) × X.an => X.rpow q.1 q.1.2 q.2 := by
  refine X.continuous_iff_an.2 fun p => continuous_iff_continuousAt.2 fun q => ?_
  have hc : Continuous fun q : Set.Ioi (0 : ℝ) × X.an => (q.2.1.val p, (q.1 : ℝ)) :=
    (((Berk.continuous_val_apply p).comp continuous_subtype_val).comp continuous_snd).prodMk
      (continuous_subtype_val.comp continuous_fst)
  have hg : ContinuousAt (fun x : ℝ≥0 × ℝ => x.1 ^ x.2) (q.2.1.val p, (q.1 : ℝ)) :=
    NNReal.continuousAt_rpow (Or.inr q.1.2)
  exact hg.comp (f := fun q : Set.Ioi (0 : ℝ) × X.an => (q.2.1.val p, (q.1 : ℝ)))
    hc.continuousAt

@[simp]
theorem rpow_one (v : X.an) : X.rpow 1 one_pos v = v :=
  Subtype.ext (Berk.rpow_one v.1)

/-- The scaling action only depends on the value of `t`. -/
theorem rpow_congr {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (h : s = t) (v : X.an) :
    X.rpow s hs v = X.rpow t ht v := by
  subst h
  rfl

theorem rpow_rpow (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (v : X.an) :
    X.rpow s hs (X.rpow t ht v) = X.rpow (t * s) (mul_pos ht hs) v :=
  Subtype.ext (Berk.rpow_rpow s t hs ht v.1)

theorem rpow_inv_rpow (t : ℝ) (ht : 0 < t) (v : X.an) :
    X.rpow t⁻¹ (inv_pos.2 ht) (X.rpow t ht v) = v := by
  rw [rpow_rpow, X.rpow_congr _ one_pos (mul_inv_cancel₀ ht.ne'), rpow_one]

theorem rpow_rpow_inv (t : ℝ) (ht : 0 < t) (v : X.an) :
    X.rpow t ht (X.rpow t⁻¹ (inv_pos.2 ht) v) = v := by
  rw [rpow_rpow, X.rpow_congr _ one_pos (inv_mul_cancel₀ ht.ne'), rpow_one]

variable (X) in
/-- The scaling action is by homeomorphisms of `𝒳^an`. -/
def rpowHomeomorph (t : ℝ) (ht : 0 < t) : X.an ≃ₜ X.an where
  toFun := X.rpow t ht
  invFun := X.rpow t⁻¹ (inv_pos.2 ht)
  left_inv := rpow_inv_rpow t ht
  right_inv := rpow_rpow_inv t ht
  continuous_toFun := X.continuous_rpow t ht
  continuous_invFun := X.continuous_rpow t⁻¹ (inv_pos.2 ht)

@[simp]
theorem rpowHomeomorph_apply (t : ℝ) (ht : 0 < t) (v : X.an) :
    X.rpowHomeomorph t ht v = X.rpow t ht v :=
  rfl

variable (X) in
/-- **`lem:gl-scaling`(1)**: the trivial point `⋆` is fixed by the scaling action. -/
@[simp]
theorem rpow_triv (t : ℝ) (ht : 0 < t) : X.rpow t ht X.triv = X.triv :=
  Subtype.ext (by rw [coe_rpow, coe_triv, Berk.rpow_triv])

/-! ### Sections under scaling -/

theorem homNorm_rpow (t : ℝ) (ht : 0 < t) (v : X.an) (a : Fin r →₀ ℕ) (f : K) :
    X.homNorm (X.rpow t ht v).1 a f = X.homNorm v.1 a f ^ t := by
  by_cases hf : f ∈ X.piece a
  · rw [X.homNorm_of_mem _ hf, X.homNorm_of_mem _ hf]
    rfl
  · rw [homNorm_of_notMem _ hf, homNorm_of_notMem _ hf, NNReal.zero_rpow ht.ne']

theorem secAbsAt_rpow (t : ℝ) (ht : 0 < t) (v : X.an) (a : Fin r → ℤ) (b : Fin r →₀ ℕ)
    (f : K) : X.secAbsAt (X.rpow t ht v).1 a b f = X.secAbsAt v.1 a b f ^ t := by
  simp only [secAbsAt, homNorm_rpow]
  exact (Finset.apply_sup_eq_sup_comp_of_linearOrder (fun x : ℝ≥0 => x ^ t)
    (NNReal.monotone_rpow_of_nonneg ht.le) (by simp [NNReal.zero_rpow ht.ne'])).symm

/-- `|f|_{t·v} = |f|_v ^ t` for sections `f ∈ R_a`. -/
theorem secAbs_rpow (t : ℝ) (ht : 0 < t) (v : X.an) (a : Fin r → ℤ) (f : K) :
    X.secAbs (X.rpow t ht v).1 a f = X.secAbs v.1 a f ^ t := by
  by_cases h : f ∈ X.sections a
  · simp only [secAbs, dif_pos h]
    exact secAbsAt_rpow t ht v a _ f
  · rw [secAbs_of_notMem _ h, secAbs_of_notMem _ h, NNReal.zero_rpow ht.ne']

/-- **`lem:gl-scaling`(1)**: `log |f|(t · v) = t log |f|(v)`. -/
theorem logSecAbs_rpow (t : ℝ) (ht : 0 < t) (v : X.an) (a : Fin r → ℤ) (f : K) :
    X.logSecAbs (X.rpow t ht v).1 a f = (t : EReal) * X.logSecAbs v.1 a f := by
  simp only [logSecAbs, secAbs_rpow, ENNReal.coe_rpow_of_nonneg _ ht.le, ENNReal.log_rpow]

theorem termVal_rpow (d : Fin r → ℤ) (p : K × ℝ) (t : ℝ) (ht : 0 < t) (v : X.an) :
    X.termVal d p (X.rpow t ht v) = (t : EReal) * X.logSecAbs v.1 d p.1 + (p.2 : EReal) := by
  rw [termVal_def, logSecAbs_rpow]

/-! ### The scaling action on functions, homogeneous functions -/

variable (X) in
/-- The **scaling action on functions** (`def:gl-scaling`, BJ22 (1.3)):
`(t · u)(v) = t u(t⁻¹ · v)`. -/
def scaleFun (t : ℝ) (ht : 0 < t) (u : X.an → EReal) (v : X.an) : EReal :=
  (t : EReal) * u (X.rpow t⁻¹ (inv_pos.2 ht) v)

variable (X) in
/-- `u` is **homogeneous** (`def:gl-scaling`, BJ22 §1.1): `u(t · v) = t u(v)` for all `t > 0`;
equivalently `t · u = u` for all `t > 0` (`isScaleHomogeneous_iff_scaleFun_eq`). -/
def IsScaleHomogeneous (u : X.an → EReal) : Prop :=
  ∀ (t : ℝ) (ht : 0 < t) (v : X.an), u (X.rpow t ht v) = (t : EReal) * u v

theorem scaleFun_apply (t : ℝ) (ht : 0 < t) (u : X.an → EReal) (v : X.an) :
    X.scaleFun t ht u v = (t : EReal) * u (X.rpow t⁻¹ (inv_pos.2 ht) v) :=
  rfl

/-- `(t · u)(t · v) = t u(v)`. -/
theorem scaleFun_apply_rpow (t : ℝ) (ht : 0 < t) (u : X.an → EReal) (v : X.an) :
    X.scaleFun t ht u (X.rpow t ht v) = (t : EReal) * u v := by
  rw [scaleFun_apply, rpow_inv_rpow]

@[simp]
theorem scaleFun_one (u : X.an → EReal) : X.scaleFun 1 one_pos u = u := by
  funext v
  rw [scaleFun_apply, X.rpow_congr _ one_pos inv_one, rpow_one, EReal.coe_one, one_mul]

theorem scaleFun_mono {t : ℝ} (ht : 0 < t) {u u' : X.an → EReal} (h : u ≤ u') :
    X.scaleFun t ht u ≤ X.scaleFun t ht u' := fun _ =>
  ProjBerk.ereal_coe_mul_monotone ht.le (h _)

/-- Homogeneous functions are the fixed points of the scaling action (BJ22 §1.1). -/
theorem isScaleHomogeneous_iff_scaleFun_eq {u : X.an → EReal} :
    X.IsScaleHomogeneous u ↔ ∀ (t : ℝ) (ht : 0 < t), X.scaleFun t ht u = u := by
  constructor
  · intro h t ht
    funext v
    rw [scaleFun_apply, h t⁻¹ (inv_pos.2 ht), ProjBerk.ereal_coe_mul_inv_mul ht.ne']
  · intro h t ht v
    have := congrFun (h t ht) (X.rpow t ht v)
    rw [scaleFun_apply_rpow] at this
    exact this.symm

theorem IsScaleHomogeneous.scaleFun_eq {u : X.an → EReal} (h : X.IsScaleHomogeneous u) (t : ℝ)
    (ht : 0 < t) : X.scaleFun t ht u = u :=
  isScaleHomogeneous_iff_scaleFun_eq.1 h t ht

/-- **`lem:gl-scaling`(5)**: scaling commutes with pointwise suprema. -/
theorem scaleFun_iSup {ι : Sort*} (t : ℝ) (ht : 0 < t) (u : ι → X.an → EReal) :
    X.scaleFun t ht (fun v => ⨆ i, u i v) = fun v => ⨆ i, X.scaleFun t ht (u i) v := by
  funext v
  exact ereal_coe_mul_iSup ht _

/-- Scaling commutes with pointwise infima. -/
theorem scaleFun_iInf {ι : Sort*} (t : ℝ) (ht : 0 < t) (u : ι → X.an → EReal) :
    X.scaleFun t ht (fun v => ⨅ i, u i v) = fun v => ⨅ i, X.scaleFun t ht (u i) v := by
  funext v
  exact ereal_coe_mul_iInf ht _

/-- The usc regularization commutes with the scaling homeomorphisms:
`(u ∘ (t ·))^⋆ = u^⋆ ∘ (t ·)`, since `uscReg` is a `limsup` along `𝓝` and `v ↦ t · v` maps
neighbourhood filters onto neighbourhood filters. -/
theorem uscReg_comp_rpow (t : ℝ) (ht : 0 < t) (u : X.an → EReal) :
    uscReg (fun v => u (X.rpow t ht v)) = fun v => uscReg u (X.rpow t ht v) := by
  funext v
  change Filter.limsup (u ∘ X.rpowHomeomorph t ht) (𝓝 v) = _
  rw [Filter.limsup_comp, Homeomorph.map_nhds_eq]
  rfl

/-- **`lem:gl-scaling`(5)**: scaling commutes with usc regularization,
`t · u^⋆ = (t · u)^⋆`. -/
theorem scaleFun_uscReg (t : ℝ) (ht : 0 < t) (u : X.an → EReal) :
    X.scaleFun t ht (uscReg u) = uscReg (X.scaleFun t ht u) := by
  have h' := uscReg_coe_mul ht (fun v => u (X.rpow t⁻¹ (inv_pos.2 ht) v))
  rw [uscReg_comp_rpow] at h'
  funext v
  exact (congrFun h' v).symm

/-- **`lem:gl-scaling`(5)**: a pointwise supremum of homogeneous functions is homogeneous. -/
theorem IsScaleHomogeneous.iSup {ι : Sort*} {u : ι → X.an → EReal}
    (h : ∀ i, X.IsScaleHomogeneous (u i)) : X.IsScaleHomogeneous fun v => ⨆ i, u i v := by
  refine isScaleHomogeneous_iff_scaleFun_eq.2 fun t ht => ?_
  rw [scaleFun_iSup]
  simp only [(h _).scaleFun_eq t ht]

/-- **`lem:gl-scaling`(5)**: the usc regularization of a homogeneous function is homogeneous. -/
theorem IsScaleHomogeneous.uscReg {u : X.an → EReal} (h : X.IsScaleHomogeneous u) :
    X.IsScaleHomogeneous (uscReg u) :=
  isScaleHomogeneous_iff_scaleFun_eq.2 fun t ht => by rw [scaleFun_uscReg, h.scaleFun_eq t ht]

/-- **`lem:gl-scaling`(5)**: `(sup_i u_i)^⋆` is homogeneous if all `u_i` are. -/
theorem IsScaleHomogeneous.uscReg_iSup {ι : Sort*} {u : ι → X.an → EReal}
    (h : ∀ i, X.IsScaleHomogeneous (u i)) :
    X.IsScaleHomogeneous (EnvelopeProperty.uscReg fun v => ⨆ i, u i v) :=
  (IsScaleHomogeneous.iSup h).uscReg

/-! ### Homogenization and Legendre slices -/

variable (X) in
/-- The **homogenization** `û = inf_{t > 0} t · u` (`def:gl-scaling`, BJ22 §6.2): the largest
homogeneous function below `u` (`homogenization_le`, `isScaleHomogeneous_homogenization`,
`IsScaleHomogeneous.le_homogenization`). -/
def homogenization (u : X.an → EReal) (v : X.an) : EReal :=
  ⨅ (t : ℝ) (ht : 0 < t), X.scaleFun t ht u v

variable (X) in
/-- The **Legendre slice** `û_λ = (u - λ)^` at `λ ∈ ℝ` (`def:gl-scaling`, BJ22 (6.2)). -/
def legendreSlice (u : X.an → EReal) (lam : ℝ) : X.an → EReal :=
  X.homogenization fun v => u v - (lam : EReal)

theorem legendreSlice_def (u : X.an → EReal) (lam : ℝ) :
    X.legendreSlice u lam = X.homogenization fun v => u v - (lam : EReal) :=
  rfl

theorem homogenization_le_scaleFun (u : X.an → EReal) (t : ℝ) (ht : 0 < t) (v : X.an) :
    X.homogenization u v ≤ X.scaleFun t ht u v :=
  iInf₂_le t ht

/-- **`lem:gl-scaling`(4)**: `û ≤ u`. -/
theorem homogenization_le (u : X.an → EReal) : X.homogenization u ≤ u := fun v =>
  (homogenization_le_scaleFun u 1 one_pos v).trans_eq (by rw [scaleFun_one])

theorem homogenization_mono {u u' : X.an → EReal} (h : u ≤ u') :
    X.homogenization u ≤ X.homogenization u' := fun v =>
  iInf₂_mono fun _ ht => scaleFun_mono ht h v

/-- **`lem:gl-scaling`(4)**: homogenization commutes with arbitrary pointwise infima; in
particular `û_i ↓ û` for every decreasing net `u_i ↓ u` (BJ22 Lemma 6.13). -/
theorem homogenization_iInf {ι : Sort*} (u : ι → X.an → EReal) :
    X.homogenization (fun v => ⨅ i, u i v) = fun v => ⨅ i, X.homogenization (u i) v := by
  funext v
  refine le_antisymm (le_iInf fun i => le_iInf₂ fun t ht => ?_) (le_iInf₂ fun t ht => ?_)
  · exact (homogenization_le_scaleFun _ t ht v).trans
      (ProjBerk.ereal_coe_mul_monotone ht.le (iInf_le _ i))
  · rw [scaleFun_apply, ereal_coe_mul_iInf ht]
    exact le_iInf fun i => (iInf_le _ i).trans (homogenization_le_scaleFun _ t ht v)

/-- **`lem:gl-scaling`(4)**: `û` is homogeneous. -/
theorem isScaleHomogeneous_homogenization (u : X.an → EReal) :
    X.IsScaleHomogeneous (X.homogenization u) := by
  intro s hs v
  have hmul : (s : EReal) * X.homogenization u v =
      ⨅ (t : ℝ) (ht : 0 < t), (s : EReal) * X.scaleFun t ht u v := by
    rw [homogenization, ereal_coe_mul_iInf hs]
    exact iInf_congr fun t => ereal_coe_mul_iInf hs _
  rw [hmul]
  refine le_antisymm (le_iInf₂ fun t ht => ?_) (le_iInf₂ fun t ht => ?_)
  · have hst : 0 < s * t := mul_pos hs ht
    refine (homogenization_le_scaleFun u (s * t) hst _).trans_eq ?_
    have hr : X.rpow (s * (s * t)⁻¹) (mul_pos hs (inv_pos.2 hst)) v =
        X.rpow t⁻¹ (inv_pos.2 ht) v :=
      X.rpow_congr _ _ (by field_simp) v
    rw [scaleFun_apply, scaleFun_apply, rpow_rpow, hr, ProjBerk.ereal_coe_mul_coe_mul]
  · have hts : 0 < t / s := div_pos ht hs
    refine (iInf₂_le (t / s) hts).trans_eq ?_
    have hr : X.rpow (s * t⁻¹) (mul_pos hs (inv_pos.2 ht)) v =
        X.rpow (t / s)⁻¹ (inv_pos.2 hts) v :=
      X.rpow_congr _ _ (by field_simp) v
    rw [scaleFun_apply, scaleFun_apply, rpow_rpow, hr, ProjBerk.ereal_coe_mul_coe_mul,
      mul_div_cancel₀ t hs.ne']

/-- **`lem:gl-scaling`(4)**: every homogeneous function `w ≤ u` satisfies `w ≤ û`. -/
theorem IsScaleHomogeneous.le_homogenization {w u : X.an → EReal} (hw : X.IsScaleHomogeneous w)
    (h : w ≤ u) : w ≤ X.homogenization u := fun v =>
  le_iInf₂ fun t ht => by
    calc w v = (t : EReal) * w (X.rpow t⁻¹ (inv_pos.2 ht) v) := by
          rw [hw t⁻¹ (inv_pos.2 ht) v, ProjBerk.ereal_coe_mul_inv_mul ht.ne']
      _ ≤ X.scaleFun t ht u v := ProjBerk.ereal_coe_mul_monotone ht.le (h _)

/-- A homogeneous function is its own homogenization. -/
theorem IsScaleHomogeneous.homogenization_eq {u : X.an → EReal} (h : X.IsScaleHomogeneous u) :
    X.homogenization u = u :=
  le_antisymm (homogenization_le u) (h.le_homogenization le_rfl)

/-- The homogenization at the fixed point `⋆`: `û(⋆) = inf_{t > 0} t u(⋆)`. -/
theorem homogenization_triv (u : X.an → EReal) :
    X.homogenization u X.triv = ⨅ (t : ℝ) (_ : 0 < t), (t : EReal) * u X.triv := by
  simp only [homogenization, scaleFun_apply, rpow_triv]

/-- **`lem:gl-scaling`(4)** at `⋆` (BJ22 Example 6.12): `û(⋆) = 0` if `0 ≤ u(⋆) < ∞`. -/
theorem homogenization_triv_of_nonneg {u : X.an → EReal} (h0 : 0 ≤ u X.triv)
    (htop : u X.triv ≠ ⊤) : X.homogenization u X.triv = 0 := by
  rw [homogenization_triv]
  lift u X.triv to ℝ using ⟨htop, ne_bot_of_le_ne_bot (EReal.coe_ne_bot 0) h0⟩ with c hc
  have hc0 : 0 ≤ c := by exact_mod_cast h0
  refine le_antisymm (ProjBerk.ereal_le_of_forall_pos_le_add fun ε hε => ?_)
    (le_iInf₂ fun t ht => ?_)
  · have hpos : 0 < ε / (c + 1) := div_pos hε (by linarith)
    refine (iInf₂_le (ε / (c + 1)) hpos).trans ?_
    rw [zero_add, ← EReal.coe_mul, EReal.coe_le_coe_iff]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    nlinarith
  · rw [← EReal.coe_mul]
    exact EReal.coe_nonneg.2 (mul_nonneg ht.le hc0)

/-- **`lem:gl-scaling`(4)** (BJ22 Lemma 6.14): if `u ≤ u(⋆) < 0`, then `û ≡ -∞`. -/
theorem homogenization_eq_bot {u : X.an → EReal} (hle : ∀ v, u v ≤ u X.triv)
    (hneg : u X.triv < 0) (v : X.an) : X.homogenization u v = ⊥ := by
  have hbound : ∀ (t : ℝ) (ht : 0 < t), X.homogenization u v ≤ (t : EReal) * u X.triv :=
    fun t ht => (homogenization_le_scaleFun u t ht v).trans
      (ProjBerk.ereal_coe_mul_monotone ht.le (hle _))
  by_cases hbot : u X.triv = ⊥
  · have := hbound 1 one_pos
    rwa [hbot, EReal.coe_one, one_mul, le_bot_iff] at this
  lift u X.triv to ℝ using ⟨ne_top_of_lt hneg, hbot⟩ with c hc
  have hc0 : c < 0 := by exact_mod_cast hneg
  refine (EReal.eq_bot_iff_forall_lt _).2 fun M => ?_
  have ht : 0 < (|M| + 1) / (-c) := div_pos (by positivity) (by linarith)
  have heq : (|M| + 1) / (-c) * c = -(|M| + 1) := by
    field_simp [hc0.ne]
  refine (hbound _ ht).trans_lt ?_
  rw [← EReal.coe_mul, EReal.coe_lt_coe_iff, heq]
  linarith [neg_abs_le M]

/-- `û_λ ≤ u - λ`. -/
theorem legendreSlice_le (u : X.an → EReal) (lam : ℝ) (v : X.an) :
    X.legendreSlice u lam v ≤ u v - (lam : EReal) :=
  homogenization_le _ v

/-- `û_λ + λ ≤ u`. -/
theorem legendreSlice_add_le (u : X.an → EReal) (lam : ℝ) (v : X.an) :
    X.legendreSlice u lam v + (lam : EReal) ≤ u v := by
  refine (add_le_add_left (legendreSlice_le u lam v) _).trans_eq ?_
  induction u v using EReal.rec with
  | bot => rfl
  | coe x =>
    rw [← EReal.coe_sub, ← EReal.coe_add, sub_add_cancel]
  | top => rfl

/-- `λ ↦ û_λ` is decreasing (`thm:gl-homog-decomposition`). -/
theorem legendreSlice_antitone (u : X.an → EReal) {lam lam' : ℝ} (h : lam ≤ lam') :
    X.legendreSlice u lam' ≤ X.legendreSlice u lam :=
  homogenization_mono fun _ => EReal.sub_le_sub le_rfl (EReal.coe_le_coe_iff.2 h)

/-- `u ↦ û_λ` is increasing (`thm:gl-homog-decomposition`). -/
theorem legendreSlice_mono {u u' : X.an → EReal} (h : u ≤ u') (lam : ℝ) :
    X.legendreSlice u lam ≤ X.legendreSlice u' lam :=
  homogenization_mono fun v => EReal.sub_le_sub (h v) le_rfl

/-! ### Homogeneous psh functions (`def:gl-psh`, `lem:gl-scaling`(3)) -/

variable (X) in
/-- **Homogeneous `θ`-psh functions** `PSH_hom(𝒳, θ)` (`def:gl-psh`): `θ`-psh functions that are
homogeneous for the scaling action. -/
def IsPSHHom (θ : Fin r → ℝ) (u : X.an → EReal) : Prop :=
  X.IsPSH θ u ∧ X.IsScaleHomogeneous u

variable {θ : Fin r → ℝ} {u : X.an → EReal}

theorem IsPSHHom.isPSH (h : X.IsPSHHom θ u) : X.IsPSH θ u := h.1

theorem IsPSHHom.isScaleHomogeneous (h : X.IsPSHHom θ u) : X.IsScaleHomogeneous u := h.2

/-- **`lem:gl-scaling`(3)**: homogeneous psh functions vanish at the fixed point `⋆`. -/
theorem IsPSH.apply_triv_eq_zero (h : X.IsPSH θ u) (hu : X.IsScaleHomogeneous u) :
    u X.triv = 0 := by
  have h2 := hu 2 two_pos X.triv
  rw [rpow_triv] at h2
  have hreal : ((u X.triv).toReal : EReal) = u X.triv :=
    EReal.coe_toReal h.apply_triv_ne_top h.apply_triv_ne_bot
  rw [← hreal, ← EReal.coe_mul] at h2
  rw [← hreal]
  have : (u X.triv).toReal = 2 * (u X.triv).toReal := EReal.coe_injective h2
  exact_mod_cast (by linarith : (u X.triv).toReal = 0)

/-- **`lem:gl-scaling`(3)**: homogeneous psh functions are `≤ 0`. -/
theorem IsPSH.nonpos (h : X.IsPSH θ u) (hu : X.IsScaleHomogeneous u) (v : X.an) : u v ≤ 0 :=
  (h.le_apply_triv v).trans (h.apply_triv_eq_zero hu).le

theorem IsPSHHom.apply_triv_eq_zero (h : X.IsPSHHom θ u) : u X.triv = 0 :=
  h.1.apply_triv_eq_zero h.2

theorem IsPSHHom.nonpos (h : X.IsPSHHom θ u) (v : X.an) : u v ≤ 0 :=
  h.1.nonpos h.2 v

/-! ### Fubini–Study functions under scaling (`lem:gl-scaling`(2)) -/

namespace FSData

variable {a : Fin r → ℚ}

/-- **`lem:gl-scaling`(2)**: `t · (m⁻¹ max_j (log |f_j| + λ_j)) = m⁻¹ max_j (log |f_j| + t λ_j)`,
the data with weights `t λ_j` (BJ22 Proposition 2.19(ii)). -/
theorem scaleFun_eval (D : X.FSData a) (t : ℝ) (ht : 0 < t) :
    X.scaleFun t ht D.eval = (D.reweight fun x => t * x).eval := by
  funext v
  rw [scaleFun_apply, eval_reweight, eval_def, ← mul_assoc, ← EReal.coe_mul, mul_comm t,
    EReal.coe_mul, mul_assoc, ProjBerk.ereal_coe_mul_finset_sup ht]
  congr 1
  refine Finset.sup_congr rfl fun p _ => ?_
  rw [termVal_rpow, termVal_def, ProjBerk.ereal_coe_mul_add ht.le,
    ProjBerk.ereal_coe_mul_inv_mul ht.ne', EReal.coe_mul]

/-- Data with zero weights are invariant under scaling. -/
theorem scaleFun_eval_of_weights_zero (D : X.FSData a) (hD : ∀ p ∈ D.terms, p.2 = 0) (t : ℝ)
    (ht : 0 < t) : X.scaleFun t ht D.eval = D.eval := by
  rw [scaleFun_eval]
  funext v
  rw [eval_reweight, eval_def]
  congr 1
  refine Finset.sup_congr rfl fun p hp => ?_
  rw [termVal_def, termVal_def, hD p hp, mul_zero]

end FSData

variable {a : Fin r → ℚ} {φ : X.an → EReal}

/-- **`lem:gl-scaling`(2)**: `t · 𝓗(𝒳, a) ⊆ 𝓗(𝒳, a)`. -/
theorem IsFS.scaleFun (h : X.IsFS a φ) (t : ℝ) (ht : 0 < t) : X.IsFS a (X.scaleFun t ht φ) := by
  classical
  obtain ⟨D, ⟨p, hp, hp0⟩, hφ⟩ := h
  refine ⟨D.reweight fun x => t * x, ⟨(p.1, t * p.2), ?_, hp0⟩, fun v => ?_⟩
  · exact Finset.mem_image_of_mem (fun p => (p.1, t * p.2)) hp
  · rw [show φ = D.eval from funext hφ, FSData.scaleFun_eval]

/-- **`lem:gl-scaling`(2)**: homogeneous Fubini–Study functions are homogeneous. -/
theorem IsHomFS.isScaleHomogeneous (h : X.IsHomFS a φ) : X.IsScaleHomogeneous φ := by
  obtain ⟨D, hD, -, hφ⟩ := h
  rw [show φ = D.eval from funext hφ]
  exact isScaleHomogeneous_iff_scaleFun_eq.2 fun t ht => D.scaleFun_eval_of_weights_zero hD t ht

/-- Changing the weights `t λ_j` of an FS datum to `0` changes the function by at most
`t L / m`, where `L ≥ |λ_j|` for all `j`. -/
theorem FSData.eval_reweight_zero_sub_le (D : X.FSData a) (t : ℝ) (ht : 0 < t) (L : ℝ)
    (hL : ∀ p ∈ D.terms, |p.2| ≤ L) (v : X.an) :
    (D.reweight fun x => t * x).eval v ≤
      (D.reweight fun _ => 0).eval v + ((t * L / D.m : ℝ) : EReal) ∧
    (D.reweight fun _ => 0).eval v ≤
      (D.reweight fun x => t * x).eval v + ((t * L / D.m : ℝ) : EReal) := by
  have hm : (0 : ℝ) < D.m := by exact_mod_cast D.m_pos
  have key : ∀ (ρ ρ' : ℝ → ℝ), (∀ p ∈ D.terms, ρ p.2 ≤ ρ' p.2 + t * L) →
      (D.reweight ρ).eval v ≤ (D.reweight ρ').eval v + ((t * L / D.m : ℝ) : EReal) := by
    intro ρ ρ' hρ
    rw [FSData.eval_reweight, FSData.eval_reweight]
    have hsup : (D.terms.sup fun p => X.termVal D.deg (p.1, ρ p.2) v) ≤
        (D.terms.sup fun p => X.termVal D.deg (p.1, ρ' p.2) v) + ((t * L : ℝ) : EReal) := by
      rw [Finset.apply_sup_eq_sup_comp_of_linearOrder (s := D.terms)
        (fun x : EReal => x + ((t * L : ℝ) : EReal)) (fun _ _ h => add_le_add_left h _)
        (EReal.bot_add _)]
      refine Finset.sup_mono_fun fun p hp => ?_
      simp only [Function.comp_apply, termVal_def, add_assoc]
      have h' : ((ρ p.2 : ℝ) : EReal) ≤ ((ρ' p.2 : ℝ) : EReal) + ((t * L : ℝ) : EReal) := by
        rw [← EReal.coe_add, EReal.coe_le_coe_iff]
        exact hρ p hp
      exact add_le_add le_rfl h'
    refine (ProjBerk.ereal_coe_mul_monotone D.inv_m_pos.le hsup).trans_eq ?_
    dsimp only
    rw [ProjBerk.ereal_coe_mul_add D.inv_m_pos.le, ← EReal.coe_mul]
    congr 2
    field_simp
  refine ⟨key _ _ fun p hp => ?_, key _ _ fun p hp => ?_⟩
  · have := hL p hp
    have := le_abs_self p.2
    nlinarith
  · have := hL p hp
    have := neg_abs_le p.2
    nlinarith

/-- **`lem:gl-scaling`(2)**: the homogeneous Fubini–Study functions are exactly the
homogeneous elements of `𝓗(𝒳, a)`: if `φ = m⁻¹ max_j (log |f_j| + λ_j)` is homogeneous, then
`φ = t · φ → m⁻¹ max_j log |f_j|` as `t → 0`. -/
theorem isHomFS_iff : X.IsHomFS a φ ↔ X.IsFS a φ ∧ X.IsScaleHomogeneous φ := by
  classical
  refine ⟨fun h => ⟨h.isFS, h.isScaleHomogeneous⟩, fun ⟨h, hhom⟩ => ?_⟩
  obtain ⟨D, ⟨p, hp, hp0⟩, hφ⟩ := h
  have hφD : φ = D.eval := funext hφ
  refine ⟨D.reweight fun _ => 0, fun q hq => ?_, ⟨(p.1, 0), ?_, hp0⟩, fun v => ?_⟩
  · obtain ⟨q₀, -, rfl⟩ := Finset.mem_image.1 hq
    rfl
  · exact Finset.mem_image_of_mem (fun p => (p.1, (fun _ => (0 : ℝ)) p.2)) hp
  · set L : ℝ := ∑ q ∈ D.terms, |q.2|
    have hL : ∀ q ∈ D.terms, |q.2| ≤ L := fun q hq =>
      Finset.single_le_sum (f := fun q : K × ℝ => |q.2|) (fun _ _ => abs_nonneg _) hq
    have hm : (0 : ℝ) < D.m := by exact_mod_cast D.m_pos
    have hscale : ∀ (t : ℝ) (ht : 0 < t), φ v = (D.reweight fun x => t * x).eval v := by
      intro t ht
      rw [← FSData.scaleFun_eval D t ht, ← hφD, hhom.scaleFun_eq t ht]
    refine le_antisymm (ProjBerk.ereal_le_of_forall_pos_le_add fun ε hε => ?_)
      (ProjBerk.ereal_le_of_forall_pos_le_add fun ε hε => ?_)
    · have ht : 0 < ε * D.m / (L + 1) := by
        have : 0 ≤ L := (abs_nonneg _).trans (hL p hp)
        positivity
      have hbd := (D.eval_reweight_zero_sub_le _ ht L hL v).1
      rw [← hscale _ ht] at hbd
      refine hbd.trans (add_le_add le_rfl (EReal.coe_le_coe_iff.2 ?_))
      have hL0 : 0 ≤ L := (abs_nonneg _).trans (hL p hp)
      rw [div_le_iff₀ hm, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
      nlinarith [mul_pos hε hm]
    · have ht : 0 < ε * D.m / (L + 1) := by
        have : 0 ≤ L := (abs_nonneg _).trans (hL p hp)
        positivity
      have hbd := (D.eval_reweight_zero_sub_le _ ht L hL v).2
      rw [← hscale _ ht] at hbd
      refine hbd.trans (add_le_add le_rfl (EReal.coe_le_coe_iff.2 ?_))
      have hL0 : 0 ≤ L := (abs_nonneg _).trans (hL p hp)
      rw [div_le_iff₀ hm, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
      nlinarith [mul_pos hε hm]

/-! ### Psh functions under scaling (`lem:gl-scaling`(2)) -/

/-- **`lem:gl-scaling`(2)**: `t · PSH(𝒳, θ) ⊆ PSH(𝒳, θ)`: a decreasing net of FS functions for
`u` gives one for `t · u` with the same classes. -/
theorem IsPSH.scaleFun (h : X.IsPSH θ u) (t : ℝ) (ht : 0 < t) :
    X.IsPSH θ (X.scaleFun t ht u) := by
  obtain ⟨⟨v₀, hv₀⟩, -, ι, _, _, _, a, f, hf, ha, hanti, hu⟩ := h
  refine FSSystemC.isPSH_of_iInf (F := X.fsSystem) ⟨X.rpow t ht v₀, ?_⟩ a
    (fun i => X.scaleFun t ht (f i)) (fun i => IsFS.scaleFun (hf i) t ht) ha
    (fun v i j hij => ProjBerk.ereal_coe_mul_monotone ht.le (hanti _ hij)) (fun v => ?_)
  · rw [scaleFun_apply_rpow]
    exact ProjBerk.ereal_coe_mul_ne_bot ht.le hv₀
  · rw [scaleFun_apply, hu, ereal_coe_mul_iInf ht]
    rfl

/-- **`lem:gl-scaling`(2)**: `t · PSH(𝒳, θ) = PSH(𝒳, θ)`. -/
theorem isPSH_scaleFun_iff (t : ℝ) (ht : 0 < t) :
    X.IsPSH θ (X.scaleFun t ht u) ↔ X.IsPSH θ u := by
  refine ⟨fun h => ?_, fun h => h.scaleFun t ht⟩
  have h' := h.scaleFun t⁻¹ (inv_pos.2 ht)
  convert h' using 1
  funext v
  rw [scaleFun_apply, scaleFun_apply, rpow_rpow, X.rpow_congr _ one_pos (by field_simp) v,
    rpow_one, ProjBerk.ereal_inv_mul_mul ht.ne']

end MultiModel

end EnvelopeProperty
