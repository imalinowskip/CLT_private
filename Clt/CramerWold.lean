import Clt.CharFun
import Clt.Inversion

noncomputable section

open Mathlib MeasureTheory ProbabilityTheory Topology Filter Vector Complex Isometry BoundedContinuousFunction Finset RealInnerProductSpace

open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω] --[TopologicalSpace Ω]
variable {P : ProbabilityMeasure Ω}
variable {d : ℕ+}
variable {X : Ω → EuclideanSpace ℝ (Fin d)}
variable {Xn : ℕ → Ω → EuclideanSpace ℝ (Fin d)}

instance : MeasurableSpace (EuclideanSpace ℝ (Fin d)) := inferInstance

lemma measurable_dotProduct_shorter (hX : Measurable X) (t : EuclideanSpace ℝ (Fin d)):
  Measurable (fun ω : Ω => ⟪(X ω), t⟫) :=
  Measurable.inner_const hX

lemma aemeasurable_dotProduct {μ : Measure Ω} (hX : Measurable X) (t : EuclideanSpace ℝ (Fin d)):
  AEMeasurable (fun ω : Ω => ⟪(X ω), t⟫) μ :=
  (measurable_dotProduct_shorter hX t).aemeasurable

lemma continuous_exp_ofReal_mul_I : Continuous (fun u : ℝ => Complex.exp (u * Complex.I))
  := continuous_exp.comp (Continuous.mul continuous_ofReal continuous_const)

lemma complex_dist_zero_eq_abs (z : ℂ) : dist z 0 = ‖z‖ :=
calc
  dist z 0 = ‖z - 0‖ := rfl
  _ = ‖z‖ := by rw [sub_zero]

lemma complex_dist_zero_eq_abs' (z : ℂ) : dist 0 z = ‖z‖ :=
by rw [dist_comm, complex_dist_zero_eq_abs z]

lemma cexp_bound_exact : ∀ (u v : ℝ), dist (Complex.exp (↑u * I)) (Complex.exp (↑v * I)) ≤ 2 :=
  fun u v =>
    calc
      dist (Complex.exp (↑u * I)) (Complex.exp (↑v * I))
        ≤ dist (Complex.exp (↑u * I)) 0 + dist 0 (Complex.exp (↑v * I)) := dist_triangle _ _ _
      _ = ‖Complex.exp (↑u * I)‖ + ‖Complex.exp (↑v * I)‖ := by rw [complex_dist_zero_eq_abs, complex_dist_zero_eq_abs']
      _ = 1 + 1 := by rw [norm_exp_ofReal_mul_I, norm_exp_ofReal_mul_I]
      _ = 2 := by norm_num

def bounded_continuous_exp_ofReal_mul_I : ℝ →ᵇ ℂ :=
  BoundedContinuousFunction.mkOfBound ⟨fun u => Complex.exp (u * Complex.I), continuous_exp_ofReal_mul_I⟩ 2 cexp_bound_exact

def bounded_continuous_exp_inner_mul_I (t : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) →ᵇ ℂ :=
  BoundedContinuousFunction.compContinuous bounded_continuous_exp_ofReal_mul_I ⟨fun x => ⟪x, t⟫,
    continuous_id.inner continuous_const⟩

@[simp] lemma bounded_continuous_exp_ofReal_mul_I_eq_cexp (u : ℝ) :
  bounded_continuous_exp_ofReal_mul_I u = Complex.exp (u * Complex.I) :=
rfl

lemma charFun_tendsto_if_inner_tendsto (hX : Measurable X) (hXn : ∀ n, Measurable (Xn n)):
  (∀ t : EuclideanSpace ℝ (Fin d), Tendsto (fun n : ℕ => P.map (aemeasurable_dotProduct (hXn n) t)) atTop (𝓝 (P.map (aemeasurable_dotProduct hX t)))) → (∀ t : EuclideanSpace ℝ (Fin d), Tendsto (fun n ↦ charFun (P.map (hXn n).aemeasurable) t) atTop (𝓝 (charFun (P.map hX.aemeasurable) t))) :=
  by
    intros hconv t
    let φ := bounded_continuous_exp_inner_mul_I t

    have h_eq3 : charFun (P.map hX.aemeasurable) t = ∫ x, Complex.exp (⟪X x, t⟫ * Complex.I) ∂P :=
      by
        simp only [charFun]
        apply MeasureTheory.integral_map
        · exact hX.aemeasurable
        · exact φ.continuous.stronglyMeasurable.aestronglyMeasurable
    have h_eq_final : charFun (P.map hX.aemeasurable) t = ∫ x, Complex.exp (x * Complex.I) ∂(P.map (aemeasurable_dotProduct hX t)).toMeasure :=
      by
        rw [h_eq3]
        rw [eq_comm]
        apply MeasureTheory.integral_map
        · exact (aemeasurable_dotProduct hX t)
        · exact continuous_exp_ofReal_mul_I.stronglyMeasurable.aestronglyMeasurable

    have h_eq_n : ∀ n, charFun (P.map (hXn n).aemeasurable) t = ∫ x, φ (Xn n x) ∂P := by
      intro n
      simp only [charFun]
      apply MeasureTheory.integral_map
      · exact (hXn n).aemeasurable
      · exact φ.continuous.stronglyMeasurable.aestronglyMeasurable
    have h_eq_n_final : ∀ n, charFun (P.map (hXn n).aemeasurable) t = ∫ x, Complex.exp (x * Complex.I) ∂(P.map (aemeasurable_dotProduct (hXn n) t)).toMeasure :=
      by
        intro n
        rw [h_eq_n]
        rw [eq_comm]
        apply MeasureTheory.integral_map
        · exact (aemeasurable_dotProduct (hXn n) t)
        · exact continuous_exp_ofReal_mul_I.stronglyMeasurable.aestronglyMeasurable

    let ψ := bounded_continuous_exp_ofReal_mul_I
    let ψ_re := (fun u => (ψ u).re)
    let ψ_im := (fun u => (ψ u).im)

    let ψ_re_bcf_bound_exact : ∀ (u v : ℝ), dist (ψ_re u) (ψ_re v) ≤ 2 := fun u v =>
    calc
      dist (ψ_re u) (ψ_re v)
        ≤ dist (ψ_re u) 0 + dist 0 (ψ_re v) := dist_triangle _ _ _
      _ = |ψ_re u| + |ψ_re v| := by rw [Real.dist_0_eq_abs, dist_comm, Real.dist_0_eq_abs]
      _ = ‖ψ_re u‖ + ‖ψ_re v‖ := by rw [Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ ‖ψ u‖ + ‖ψ v‖ :=
      by
        simp [ψ_im]
        exact add_le_add (RCLike.norm_re_le_norm (ψ u)) (RCLike.norm_re_le_norm (ψ v))
      _ = ‖Complex.exp (u * Complex.I)‖ + ‖Complex.exp (v * Complex.I)‖ := by simp [ψ, ψ]
      _ = 1 + 1 := by rw [norm_exp_ofReal_mul_I, norm_exp_ofReal_mul_I]
      _ = 2 := by norm_num
    let ψ_im_bcf_bound_exact : ∀ (u v : ℝ), dist (ψ_im u) (ψ_im v) ≤ 2 := fun u v =>
    calc
      dist (ψ_im u) (ψ_im v)
        ≤ dist (ψ_im u) 0 + dist 0 (ψ_im v) := dist_triangle _ _ _
      _ = |ψ_im u| + |ψ_im v| := by rw [Real.dist_0_eq_abs, dist_comm, Real.dist_0_eq_abs]
      _ = ‖ψ_im u‖ + ‖ψ_im v‖ := by rw [Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ ‖ψ u‖ + ‖ψ v‖ :=
      by
        simp [ψ_im]
        exact add_le_add (RCLike.norm_im_le_norm (ψ u)) (RCLike.norm_im_le_norm (ψ v))
      _ = ‖Complex.exp (u * Complex.I)‖ + ‖Complex.exp (v * Complex.I)‖ := by simp [ψ, ψ]
      _ = 1 + 1 := by rw [norm_exp_ofReal_mul_I, norm_exp_ofReal_mul_I]
      _ = 2 := by norm_num

    let ψ_re_bcf : ℝ →ᵇ ℝ := BoundedContinuousFunction.mkOfBound ⟨ψ_re, Continuous.comp continuous_re ψ.continuous⟩ 2 ψ_re_bcf_bound_exact
    let ψ_im_bcf : ℝ →ᵇ ℝ := BoundedContinuousFunction.mkOfBound ⟨ψ_im, Continuous.comp continuous_im ψ.continuous⟩ 2 ψ_im_bcf_bound_exact

    let ψ_decomp (x : ℝ) : ψ x = ψ_re_bcf x + (ψ_im_bcf x) * Complex.I :=
      by
        simp [ψ_re_bcf, ψ_im_bcf]
        rw [Complex.re_add_im]

    let h_lim (f : ℝ →ᵇ ℝ) : 0 ≤ f → atTop.limsup (fun n => ∫ x, f x ∂ (↑(P.map (aemeasurable_dotProduct (hXn n) t)))) ≤ ∫ x, f x ∂ (↑(P.map (aemeasurable_dotProduct hX t))) :=
      by
        intro f_nn
        let μₙ : ℕ → ProbabilityMeasure ℝ :=
          fun n => (P.map (aemeasurable_dotProduct (hXn n) t) : ProbabilityMeasure ℝ)
        let μ : ProbabilityMeasure ℝ :=
          (P.map (aemeasurable_dotProduct hX t) : ProbabilityMeasure ℝ)
        let hconv_t : Tendsto μₙ atTop (𝓝 μ)
          := hconv t
        have hf : Tendsto (fun n => ∫ x, f x ∂ (↑(P.map (aemeasurable_dotProduct (hXn n) t)))) atTop
                        (𝓝 (∫ x, f x ∂ (↑(P.map (aemeasurable_dotProduct hX t))))) :=
          by
            have h_iff := @ProbabilityMeasure.tendsto_iff_forall_integral_tendsto ℝ _ _ _ ℕ atTop μₙ μ
            have h_rhs := Iff.mp h_iff hconv_t
            exact h_rhs f

        exact le_of_eq (Tendsto.limsup_eq hf)

    have integralConv_re :
      Tendsto (fun n => ∫ (x : ℝ), ψ_re_bcf x ∂ (↑(P.map (aemeasurable_dotProduct (hXn n) t)))) atTop (𝓝 (∫ (x : ℝ), ψ_re_bcf x ∂ (↑(P.map (aemeasurable_dotProduct hX t))))) := BoundedContinuousFunction.tendsto_integral_of_forall_limsup_integral_le_integral h_lim ψ_re_bcf

    have integralConv_im :
      Tendsto (fun n => ∫ (x : ℝ), ψ_im_bcf x ∂ (↑(P.map (aemeasurable_dotProduct (hXn n) t)))) atTop (𝓝 (∫ (x : ℝ), ψ_im_bcf x ∂ (↑(P.map (aemeasurable_dotProduct hX t)))) ) :=
      BoundedContinuousFunction.tendsto_integral_of_forall_limsup_integral_le_integral h_lim ψ_im_bcf

    have h_mul_one : ∀ x, x * Complex.ofReal 1 = x := by simp

    have h_integral_smul_const_ψ_re_bcf : ∀ (ν : Measure ℝ), ∫ x, ψ_re_bcf x * Complex.ofReal 1 ∂ ν = (∫ x, ψ_re_bcf x ∂ ν) * Complex.ofReal 1 :=
    by
      intro ν
      exact integral_smul_const ψ_re_bcf (Complex.ofReal 1)
    have h_integral_smul_const_ψ_im_bcf : ∀ (ν : Measure ℝ), ∫ x, ψ_im_bcf x * Complex.I ∂ ν = (∫ x, ψ_im_bcf x ∂ ν) * Complex.I :=
    by
      intro ν
      exact integral_smul_const ψ_im_bcf (Complex.I)

    have h_ψ : ∀ (ν : ProbabilityMeasure ℝ), ∫ x, ψ x ∂ ν = ∫ x, ψ_re_bcf x ∂ ν + (∫ x, ψ_im_bcf x ∂ ν) * Complex.I :=
      by
        intro ν
        have h : ∀ x, ψ x = (ψ_re_bcf x) * Complex.ofReal 1 + (ψ_im_bcf x) * Complex.I := by
          intro x
          rw [h_mul_one]
          exact ψ_decomp x
        rw [integral_congr_ae (Eventually.of_forall h), integral_add]

        rw [h_integral_smul_const_ψ_re_bcf ν]
        rw [h_integral_smul_const_ψ_im_bcf ν]
        rw [h_mul_one]

        simp [h_mul_one]

        have h_ψ_re_bcf_integ : Integrable ψ_re_bcf ν := BoundedContinuousFunction.integrable ν ψ_re_bcf
        have h_c_ψ_re_bcf_integ : Integrable (fun a => (ψ_re_bcf a : ℂ)) ↑ν := by exact h_ψ_re_bcf_integ.ofReal
        exact h_c_ψ_re_bcf_integ

        have h_ψ_im_bcf_integ : Integrable ψ_im_bcf ν := BoundedContinuousFunction.integrable ν ψ_im_bcf
        have h_c_ψ_im_bcf_integ : Integrable (fun a => (ψ_im_bcf a : ℂ)) ↑ν := by exact h_ψ_im_bcf_integ.ofReal

        exact h_ψ_im_bcf_integ.ofReal.mul_const Complex.I

    have integralConv :
      Tendsto (fun n => ∫ (x : ℝ), ψ x ∂ (↑(P.map (aemeasurable_dotProduct (hXn n) t)))) atTop (𝓝 (∫ (x : ℝ), ψ x ∂ (↑(P.map (aemeasurable_dotProduct hX t))))) :=
        by
          rw [h_ψ]
          have h1 : Tendsto (fun n => Complex.ofReal (∫ (x : ℝ), ψ_re_bcf x ∂ (↑(P.map (aemeasurable_dotProduct (hXn n) t))))) atTop
            (𝓝 (↑(∫ (x : ℝ), ψ_re_bcf x ∂ (↑(P.map (aemeasurable_dotProduct hX t)))))) :=
            Tendsto.ofReal integralConv_re
          have h2 : Tendsto (fun n => Complex.ofReal (∫ (x : ℝ), ψ_im_bcf x ∂ (↑(P.map (aemeasurable_dotProduct (hXn n) t))))) atTop
            (𝓝 (↑(∫ (x : ℝ), ψ_im_bcf x ∂ (↑(P.map (aemeasurable_dotProduct hX t)))))) :=
            Tendsto.ofReal integralConv_im
          have h3 := Tendsto.mul h2 (tendsto_const_nhds : Tendsto (fun _ => Complex.I) atTop (𝓝 Complex.I))
          have h4 := Tendsto.add h1 h3

          have : ∀ n, ∫ x, ψ x ∂(↑(P.map (aemeasurable_dotProduct (hXn n) t))) =
                        ∫ x, ψ_re_bcf x ∂(↑(P.map (aemeasurable_dotProduct (hXn n) t))) +
                        (∫ x, ψ_im_bcf x ∂(↑(P.map (aemeasurable_dotProduct (hXn n) t)))) * Complex.I :=
            fun n => h_ψ _
          refine Tendsto.congr' ?_ h4
          simp_rw [this]
          simp [EventuallyEq.of_eq]

    rw [h_eq_final]

    have h_char_eq_n : ∀ n, charFun (P.map (hXn n).aemeasurable) t = ∫ x, ψ x ∂(↑(P.map (aemeasurable_dotProduct (hXn n) t))) :=
      fun n => h_eq_n_final n ▸ rfl

    have h_char_eq_lim : charFun (P.map hX.aemeasurable) t = ∫ x, ψ x ∂(↑(P.map (aemeasurable_dotProduct hX t))) :=
      h_eq_final

    simp_rw [h_char_eq_n]

    have hψ_eq_cexp : (fun x : ℝ => ψ x) = (fun x : ℝ => Complex.exp (x * Complex.I)) := by
      ext x
      rfl

    have h_lim_eq : ∫ x, Complex.exp (x * Complex.I) ∂((P.map (aemeasurable_dotProduct hX t)).toMeasure) =
                ∫ x, ψ x ∂(↑(P.map (aemeasurable_dotProduct hX t))) :=
      by rw [← hψ_eq_cexp]

    rw [h_lim_eq]
    exact integralConv

lemma rv_tendsto_if_charFun_tendsto (hX : Measurable X) (hXn : ∀ n, Measurable (Xn n)):
  (∀ t : EuclideanSpace ℝ (Fin d), Tendsto (fun n ↦ charFun (P.map (hXn n).aemeasurable) t) atTop (𝓝 (charFun (P.map hX.aemeasurable) t))) → Tendsto (fun n ↦ P.map (hXn n).aemeasurable) atTop (𝓝 (P.map hX.aemeasurable)) :=
  by
    intro h
    let μ := P.map hX.aemeasurable
    let μₙ := fun n => P.map (hXn n).aemeasurable
    exact MeasureTheory.ProbabilityMeasure.tendsto_iff_tendsto_charFun.mpr h

theorem cramerWold (hX : Measurable X) (hXn : ∀ n, Measurable (Xn n)) :
  (∀ t : EuclideanSpace ℝ (Fin d), Tendsto (fun n : ℕ => P.map (aemeasurable_dotProduct (hXn n) t)) atTop (𝓝 (P.map (aemeasurable_dotProduct hX t)))) → (Tendsto (fun n : ℕ => P.map (hXn n).aemeasurable) atTop (𝓝 (P.map hX.aemeasurable)))
  := by
  intro h
  exact (rv_tendsto_if_charFun_tendsto hX hXn) ((charFun_tendsto_if_inner_tendsto hX hXn) (h))

#min_imports
