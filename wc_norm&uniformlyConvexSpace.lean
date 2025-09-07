/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Filter Finset Real

variable {k : Type u} [rc : RCLike k] {B : Type v} [NormedAddCommGroup B] [NormedSpace k B]

-- If $y_n$ is a sequence weakly converging to $x$, then the norm of $x$ is at most the $liminf$ of the norms of $y_n$
theorem norm_le_liminf_norm_of_wc  (x : B) (y : ℕ → B) (wc_y : ∀ f : StrongDual k B,
    Tendsto (f ∘ y) atTop (nhds (f x))) : ‖x‖ ≤ liminf (fun i => ‖y i‖) atTop := by
-- Convert $y$ to its double dual by applying `NormedSpace.inclusionInDoubleDualLi`, then apply Banach-Steinhaus theorem to show that their norms are bounded
  have : Bornology.IsVonNBounded ℝ (Set.range (fun i => ‖y i‖)) := by
    simp only [← Set.image_univ, NormedSpace.image_isVonNBounded_iff, Set.mem_univ, norm_eq_abs,
      abs_norm, forall_const]
    let T := fun i => NormedSpace.inclusionInDoubleDualLi k (y i)
    have aux : ∀ f : StrongDual k B, ∃ C, ∀ (i : ℕ), ‖(T i) f‖ ≤ C := by
      intro f; have := Metric.isBounded_range_of_tendsto _ (wc_y f)
      simp only [← Set.image_univ, Function.comp_apply, ← NormedSpace.isVonNBounded_iff ℝ,
        NormedSpace.image_isVonNBounded_iff, Set.mem_univ, forall_const] at this
      rcases this with ⟨C, hC⟩; use C; convert hC
    apply banach_steinhaus at aux; rcases aux with ⟨C, hC⟩
    use C; convert hC with i; symm
    exact (NormedSpace.inclusionInDoubleDualLi k).norm_map (y i)
  simp only [← Set.image_univ, NormedSpace.image_isVonNBounded_iff, Set.mem_univ, norm_eq_abs,
    abs_norm, forall_const] at this
  rcases this with ⟨C, hC⟩
-- When $x$ is $0$, the goal is trivial since all norms are nonnegative
  by_cases h : x = 0
  · simp only [h, norm_zero, liminf_eq, eventually_atTop, ge_iff_le]
    apply le_csSup
    · simp only [BddAbove, Set.Nonempty, upperBounds, Set.mem_setOf_eq, forall_exists_index]
      use C; intro _ N h; specialize h N (by rfl)
      specialize hC N; linarith only [h, hC]
    · simp
-- When $x$ is nonzero, apply `exists_dual_vector`(a corollary of Hahn-Banach theorem) to $x$ to get some continuous linear map $f$
  rw [← ne_eq] at h; apply exists_dual_vector k at h
  rcases h with ⟨f, norm_f, hf⟩;-- simp? at hf
-- Specialize `wc_y` at $f$ and finish the goal by applying `liminf_le_liminf`
  specialize wc_y f; rw [hf] at wc_y
  replace wc_y := wc_y.norm; simp only [Function.comp_apply, norm_algebraMap', norm_norm] at wc_y
  have : IsCoboundedUnder (fun x1 x2 => x1 ≥ x2) atTop (fun i => ‖y i‖) := by
    simp only [IsCoboundedUnder, IsCobounded, ge_iff_le, eventually_map, eventually_atTop,
      forall_exists_index]
    use C; intro _ N h; specialize h N (by rfl)
    specialize hC N; linarith only [h, hC]
  have : IsBoundedUnder (fun x1 x2 => x1 ≥ x2) atTop (fun x => ‖f (y x)‖) := by
    simp only [IsBoundedUnder, IsBounded, ge_iff_le, eventually_map, eventually_atTop]
    use 0, 0; simp
  have : ∀ᶠ (i : ℕ) in atTop, (fun x => ‖f (y x)‖) i ≤ (fun i => ‖y i‖) i := by
    rw [eventually_atTop]; use 0; intro i _; simp only
    rw [← one_mul ‖y i‖, ← norm_f]; apply f.le_opNorm
  apply liminf_le_liminf at this; rw [wc_y.liminf_eq] at this; apply this
  all_goals rw [autoParam]; assumption

-- In a uniformly convex space, if the norm sequence of a weakly convergent sequence converges, then the sequence converges
theorem tendsto_of_wc_of_nc_of_ucs (ucs : UniformConvexSpace B) (x : ℕ → B)
    (y : B) (wc_x : ∀ f : StrongDual k B, Tendsto (f ∘ x) atTop (nhds (f y)))
    (nc_x : Tendsto (fun n => ‖x n‖) atTop (nhds ‖y‖)) : Tendsto x atTop (nhds y) := by
-- When $y=0$, the goal is trivial
  by_cases hy : y = 0
  · rw [hy, norm_zero, ← tendsto_zero_iff_norm_tendsto_zero] at nc_x
    rw [hy]; exact nc_x
  rw [← ne_eq, ← norm_pos_iff] at hy
-- By shifting the indexes of $x$, we can assume w. l. o. g. that all of the norms of $x_i$ are positive
  wlog hx : ∀ n, 0 < ‖x n‖
  · let h := nc_x; simp only [Metric.tendsto_atTop, gt_iff_lt, ge_iff_le, dist_eq_norm, norm_eq_abs] at h
    specialize h ‖y‖ hy; rcases h with ⟨N, hN⟩
    replace hN : ∀ n, 0 < ‖x (n + N)‖ := by
      intro n; specialize hN (n + N) (by simp); rw [abs_lt] at hN
      linarith only [hN.left]
    specialize @this k rc B _ _ ucs (fun n => x (n + N)) y
    have aux1 : ∀ (f : StrongDual k B), Tendsto (⇑f ∘ fun n => x (n + N)) atTop (nhds (f y)) := by
      intro f; simp only [tendsto_iff_eventually, eventually_atTop, ge_iff_le]
      intro p hp; specialize wc_x f
      simp only [Metric.tendsto_atTop, gt_iff_lt, ge_iff_le, Function.comp_apply] at wc_x
      simp only [Metric.eventually_nhds_iff, gt_iff_lt, dist_eq_norm] at hp
      rcases hp with ⟨ε, εpos, hε⟩; specialize wc_x ε εpos
      rcases wc_x with ⟨M, hM⟩; simp only [dist_eq_norm] at hM
      use M; intros; simp only [Function.comp_apply]
      apply hε; apply hM; omega
    have aux2 : Tendsto (fun n => ‖x (n + N)‖) atTop (nhds ‖y‖) := by
      simp only [tendsto_iff_eventually, eventually_atTop, ge_iff_le]
      intro p hp; simp only [Metric.tendsto_atTop, gt_iff_lt, ge_iff_le] at nc_x
      simp only [Metric.eventually_nhds_iff, gt_iff_lt, dist] at hp
      rcases hp with ⟨ε, εpos, hε⟩; specialize nc_x ε εpos
      rcases nc_x with ⟨M, hM⟩; simp only [dist] at hM
      use M; intros; apply hε; apply hM; omega
    specialize this aux1 aux2 hy hN
    simp only [tendsto_iff_eventually, eventually_atTop, ge_iff_le]
    intro _ h; simp only [Metric.eventually_nhds_iff, gt_iff_lt, dist_eq_norm] at h
    rcases h with ⟨ε, εpos, hε⟩
    simp only [Metric.tendsto_atTop, gt_iff_lt, ge_iff_le] at this
    specialize this ε εpos; rcases this with ⟨M, hM⟩
    simp only [dist_eq_norm] at hM; use M + N
    intro n nge; rw [show n = n - N + N by omega]; apply hε
    apply hM; omega
-- Assume the contrary, prove that there exists some $ε > 0$ such that for all natural numbers $k$, we can always find $m$, $n$ greater than $k$ such that $‖x_m - x_n‖$ is at least $ε$
  by_contra h; simp only [Metric.tendsto_atTop, gt_iff_lt, ge_iff_le, not_forall,
    not_exists, not_lt, dist_eq_norm] at h
  rcases h with ⟨ε, εpos, hε⟩; choose n hn using hε; simp only [exists_prop] at hn
  have lim_n : Tendsto n atTop atTop := by
    rw [tendsto_atTop_atTop]; intro b
    use b; intro a age; specialize hn a
    rcases hn with ⟨h, _⟩; omega
-- Prove that the difference of the normalized term $‖x (n i)‖⁻¹ • x (n i)$ and $‖y‖⁻¹ • y$ is greater than some constant for $i$ large
  obtain ⟨N, hN⟩ : ∃ N, ∀ i, N ≤ i → ε / (2 * ‖y‖) < ‖rc.ofReal ‖x (n i)‖⁻¹ • x (n i) - rc.ofReal ‖y‖⁻¹ • y‖ := by
    have : Tendsto (fun i => (ε - |‖x (n i)‖ - ‖y‖|) / (‖x (n i)‖)) atTop (nhds (ε / ‖y‖)) := by
      simp only [sub_div]; rw [← sub_zero (ε / ‖y‖)]; apply Tendsto.sub
      · apply Tendsto.div; simp
        apply nc_x.comp; exact lim_n; positivity
      · rw [show 0 = 0 / ‖y‖ by simp]
        apply Tendsto.div
        · simp only [← norm_eq_abs]; rw [← tendsto_iff_norm_sub_tendsto_zero]
          apply nc_x.comp; exact lim_n
        · apply nc_x.comp; exact lim_n
        positivity
    simp only [Metric.tendsto_atTop, gt_iff_lt, ge_iff_le, dist] at this
    specialize this (ε / (2 * ‖y‖)) (by positivity)
    rcases this with ⟨N, hN⟩; use N
    intro i ige; calc
      _ < (ε * ‖y‖ - |‖x (n i)‖ - ‖y‖| * ‖y‖) / (‖x (n i)‖ * ‖y‖) := by
        rw [← sub_mul, mul_div_mul_right]
        specialize hN i ige; rw [abs_lt, lt_sub_iff_add_lt] at hN
        ring_nf at hN; ring_nf; exact hN.left
        positivity
      _ ≤ (‖x (n i) - y‖ * ‖y‖ - |‖x (n i)‖ - ‖y‖| * ‖y‖) / (‖x (n i)‖ * ‖y‖) := by
        gcongr; exact (hn i).right
      _ ≤ _ := by
        rw [sub_div, ← mul_div, mul_comm, div_mul_cancel_right₀]
        nth_rw 1 [← abs_eq_self.mpr (show 0 ≤ ‖x (n i)‖⁻¹ by positivity)]
        rw [← rc.norm_ofReal, ← norm_smul, smul_sub, ← div_mul_eq_mul_div]
        rw [← abs_eq_self.mpr (show 0 ≤ ‖x (n i)‖ * ‖y‖ by positivity), ← abs_div]
        rw [← rc.norm_ofReal, ← norm_smul, sub_div, div_mul_cancel_right₀]
        rw [div_mul_cancel_left₀, RCLike.ofReal_sub, sub_smul]
        apply le_trans (norm_sub_norm_le _ _); rw [sub_sub_sub_cancel_right]
        · specialize hx (n i); positivity
        all_goals positivity
-- Specialize the uniform convexity of $B$ to the constant $ε / (2 * ‖y‖)$ and get some $δ > 0$, then revert `hδ` and simplify the goal
  obtain ⟨δ, δpos, hδ⟩ := ucs.uniform_convex (show 0 < ε / (2 * ‖y‖) by positivity)
  revert hδ; simp only [imp_false, not_forall, exists_prop, not_le]
-- Denote the sequence $‖x (n i)‖⁻¹ • x (n i) + ‖y‖⁻¹ • y$ by $x'$, prove that $x'$ weakly converges to $2 * ‖y‖⁻¹) • y$
  let x' := fun i => rc.ofReal ‖x (n i)‖⁻¹ • x (n i) + rc.ofReal ‖y‖⁻¹ • y
  have wc_x' : ∀ (f : StrongDual k B), Tendsto (f ∘ x') atTop (nhds (f (rc.ofReal (2 * ‖y‖⁻¹) • y))) := by
    intro f; simp only [Metric.tendsto_atTop, gt_iff_lt, ge_iff_le, dist_eq_norm, Function.comp_apply,
      map_add, map_smul, smul_eq_mul, x']
    push_cast; ring_nf
    suffices : Tendsto (fun i => ‖x (n i)‖⁻¹ * f (x (n i))) atTop (nhds (‖y‖⁻¹ * f y))
    · simp only [Metric.tendsto_atTop, gt_iff_lt, ge_iff_le, dist_eq_norm] at this
      push_cast at this; exact this
    apply Tendsto.mul
    · apply RCLike.continuous_ofReal.seqContinuous
      apply Tendsto.inv₀; exact nc_x.comp lim_n
      positivity
    · exact (wc_x f).comp lim_n
-- Apply the lemma `norm_le_liminf_norm_of_wc` to `wc_x'`
  apply norm_le_liminf_norm_of_wc at wc_x'
  simp only [map_mul, map_inv₀, norm_smul, norm_mul, norm_algebraMap', norm_ofNat, norm_inv,
    norm_norm] at wc_x'
  have : IsCoboundedUnder (fun x1 x2 => x1 ≥ x2) atTop (fun i => ‖x' i‖) := by
    simp only [IsCoboundedUnder, IsCobounded, ge_iff_le, eventually_map, eventually_atTop,
      forall_exists_index]
    use 2; intro _ i h; specialize h i (by rfl)
    apply le_trans h; dsimp [x']; rw [show (2:ℝ) = 1+1 by ring]
    convert norm_add_le _ _
    · simp only [map_inv₀, norm_smul, norm_inv, norm_algebraMap', norm_eq_abs, abs_norm]
      rw [inv_mul_cancel₀]; specialize hx (n i); positivity
    · simp only [map_inv₀, norm_smul, norm_inv, norm_algebraMap', norm_eq_abs, abs_norm]
      rw [inv_mul_cancel₀]; positivity
  have : IsBoundedUnder (fun x1 x2 => x1 ≥ x2) atTop (fun i => ‖x' i‖) := by
    simp only [IsBoundedUnder, IsBounded, ge_iff_le, eventually_map, eventually_atTop]
    use 0, 0; simp
-- Rewrite `wc_x` by `le_liminf_iff` and simplify, then specialize it to $2 - δ$ to get some large index $M$
  rw [mul_assoc, inv_mul_cancel₀, mul_one, le_liminf_iff] at wc_x'
  simp only [eventually_atTop, ge_iff_le] at wc_x'
  specialize wc_x' (2 - δ) (by linarith only [δpos])
-- Specialize `hM` to $M + N$, then fulfill the goal with $‖x (n (M + N))‖⁻¹ • x (n (M + N))$ and $‖y‖⁻¹ • y$ and finish the goal
  rcases wc_x' with ⟨M, hM⟩; specialize hM (M + N) (by simp); dsimp [x'] at hM
  use rc.ofReal ‖x (n (M + N))‖⁻¹ • x (n (M + N)); constructor
  · simp only [map_inv₀, norm_smul, norm_inv, norm_algebraMap', norm_eq_abs, abs_norm]
    rw [inv_mul_cancel₀]; specialize hx (n (M + N)); positivity
  use rc.ofReal ‖y‖⁻¹ • y; split_ands
  · simp only [map_inv₀, norm_smul, norm_inv, norm_algebraMap', norm_eq_abs, abs_norm]
    rw [inv_mul_cancel₀]; positivity
  · apply le_of_lt; apply hN; simp
  · exact hM
  positivity
