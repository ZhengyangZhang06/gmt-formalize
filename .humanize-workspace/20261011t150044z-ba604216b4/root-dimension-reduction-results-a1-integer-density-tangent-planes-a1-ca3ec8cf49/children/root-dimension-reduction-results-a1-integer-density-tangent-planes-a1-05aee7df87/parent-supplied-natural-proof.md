# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_point_tangent_plane-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_point_tangent_plane-a1.plane_subsequence_limit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 3 of the parent proof (convergence of the planes; Simon 7.3.3(2), proof, chapter-07.txt lines 512–530, where (3) measures flatness by q, the orthogonal projection onto L^⊥, and (13) at line 581), made self-contained. Notation: ℝ^P = Euclid P with inner product ⟨·,·⟩ and norm |·|; p_V = V.starProjection; δ_{ll'} = 1 if l = l' and 0 otherwise.
1. (Orthonormal frames of the Q_j.) Fix j. Q_j is a finite-dimensional real inner product space with dim Q_j = n, so it has an orthonormal basis b_j indexed by Fin n (Mathlib: stdOrthonormalBasis ℝ Q_j reindexed by finCongr along finrank ℝ Q_j = n). Let v_{j,l} ∈ ℝ^P (l ∈ Fin n) be the vectors b_j(l) regarded in ℝ^P. The inclusion Q_j → ℝ^P is a linear isometry, so (v_{j,l})_l is orthonormal in ℝ^P (Orthonormal.comp_linearIsometry with Q_j.subtypeₗᵢ): |v_{j,l}| = 1 and ⟨v_{j,l}, v_{j,l'}⟩ = δ_{ll'}. Expanding the orthogonal projection in the orthonormal basis b_j of Q_j (OrthonormalBasis.starProjection_eq_sum_rankOne) gives p_{Q_j}(u) = Σ_{l∈Fin n} ⟨v_{j,l}, u⟩ v_{j,l} for every u ∈ ℝ^P.
2. (A convergent subsequence of frames.) Let V_j := (v_{j,l})_{l∈Fin n}, an element of the finite product (ℝ^P)^{Fin n} with its sup norm. As |v_{j,l}| = 1 for all l, V_j lies in the closed unit ball of (ℝ^P)^{Fin n}, which is compact because (ℝ^P)^{Fin n} is a finite-dimensional normed space. By sequential compactness of compact subsets of a metric space (IsCompact.tendsto_subseq) there are τ = (τ_l)_{l∈Fin n} ∈ (ℝ^P)^{Fin n} and a strictly increasing js : ℕ → ℕ with V_{js(i)} → τ as i → ∞. Evaluation at a coordinate l is continuous, so v_{js(i),l} → τ_l for every l ∈ Fin n.
3. (τ is orthonormal.) For l, l' ∈ Fin n and every i, ⟨v_{js(i),l}, v_{js(i),l'}⟩ = δ_{ll'} by step 1. The inner product is jointly continuous, so letting i → ∞ and using uniqueness of limits, ⟨τ_l, τ_{l'}⟩ = δ_{ll'}. By orthonormal_iff_ite, τ is orthonormal (Orthonormal ℝ τ).
4. (Projection onto Q := span{τ_1, …, τ_n}.) Let u ∈ ℝ^P and w := Σ_l ⟨τ_l, u⟩ τ_l; then w ∈ Q. For each m ∈ Fin n, ⟨u − w, τ_m⟩ = ⟨u, τ_m⟩ − Σ_l ⟨τ_l, u⟩⟨τ_l, τ_m⟩ = ⟨u, τ_m⟩ − ⟨τ_m, u⟩|τ_m|² = 0 by step 3 and symmetry of the real inner product. The set of z with ⟨u − w, z⟩ = 0 is a linear subspace containing every τ_m, hence it contains Q (span induction). Since w ∈ Q and u − w is orthogonal to Q, the characterization of the orthogonal projection (Submodule.eq_starProjection_of_mem_of_inner_eq_zero) gives p_Q(u) = w = Σ_l ⟨τ_l, u⟩ τ_l.
5. (The rate.) Put κ_i := 2·Σ_{l∈Fin n} |v_{js(i),l} − τ_l|. By step 2 each |v_{js(i),l} − τ_l| → |τ_l − τ_l| = 0, and the sum is finite, so κ_i → 0.
6. (The estimate.) Fix i, u and l, and write a := v_{js(i),l}, t := τ_l, so |a| = |t| = 1 (steps 1 and 3). Then ⟨a, u⟩a − ⟨t, u⟩t = ⟨a − t, u⟩a + ⟨t, u⟩(a − t), so by the triangle and Cauchy–Schwarz inequalities |⟨a, u⟩a − ⟨t, u⟩t| ≤ |a − t||u||a| + |t||u||a − t| = 2|a − t||u|. By steps 1 and 4, p_{Q_{js(i)}}(u) − p_Q(u) = Σ_l (⟨v_{js(i),l}, u⟩v_{js(i),l} − ⟨τ_l, u⟩τ_l), hence by the triangle inequality |p_{Q_{js(i)}}(u) − p_Q(u)| ≤ Σ_l 2|v_{js(i),l} − τ_l||u| = κ_i|u|.
7. (Conclusion.) js is strictly increasing, τ is orthonormal, κ_i → 0, and |p_{Q_{js(i)}}(u) − p_{span τ}(u)| ≤ κ_i|u| for all i ∈ ℕ and u ∈ ℝ^P. (For n = 0 all sums are empty, τ is the empty family, span τ = 0 = Q_j, both projections vanish and κ ≡ 0; the argument covers this case unchanged.) ∎

## Key steps

1. Pick orthonormal frames (v_{j,l})_{l∈Fin n} of the Q_j; then p_{Q_j}(u) = Σ_l ⟨v_{j,l}, u⟩v_{j,l}.
2. The frames lie in the compact closed unit ball of (ℝ^P)^{Fin n}; extract a strictly increasing js with v_{js(i),l} → τ_l.
3. Orthonormality passes to the limit, so τ is orthonormal, and p_{span τ}(u) = Σ_l ⟨τ_l, u⟩τ_l by the orthogonality characterization.
4. Termwise |⟨a,u⟩a − ⟨t,u⟩t| ≤ 2|a − t||u| gives |p_{Q_{js(i)}}u − p_{span τ}u| ≤ κ_i|u| with κ_i = 2Σ_l|v_{js(i),l} − τ_l| → 0.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean && cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD (compared with manifest.json)`
- `python3 scan of dag.json lean_statements for IsConeCurrent | ConvergesWeakly[^→]*→[^∀]*BoundaryVanishes|BoundaryVanishes C | starProjection | ConvergesWeakly.*support | Orthonormal`
- `python3 scan of accepted dag.json lean_statements containing 'support' together with massOn|zeroRegion|VanishesOn|boundary`
- `dag.json lookup by lean_name: dtc_blowUp_algebra, dtc_vanish_off_support, dtc_blowUp_massOn_image, dimred_im_mass_measure, dimred_minimizing_monotonicity, density_and_tangent_cones, idtp_convergesWeakly_massOn_le, idtp_planar_cycle_eq_const_mul, dtc_blowUp_compactness, dimred_blowup_limit_moving_centres, dorag_ted_planes_limit, dorag_ted_pl_proj_limit_rank, cone_current_imrep_measure_smul_image, cone_current_apply_dilation_pullback, dor_ims_support_of_massOn_eq`
- `grep -n 'def GeometricCurrentOn.support|zeroRegion|VanishesOn|testFormOnInclusion' simongmt Chapter06/CurrentLocalEquality.lean; grep -n 'boundary_apply|exteriorDerivativeTestOn|GeometricCurrentOn.ext|zero_apply' Chapter06/Currents.lean; grep -n 'massOn|massAdmissibleOn|covectorEuclideanNorm' Chapter06/Mass.lean; grep -n 'Covector|DifferentialForm|IsTestForm' Chapter06/Forms.lean`
- `grep -rn in local-references/123e8435b4a2469b/mathlib/Mathlib: euclideanHausdorffMeasure, IsCompact.tendsto_subseq, Orthonormal.comp_linearIsometry, starProjection_eq_sum_rankOne, eq_starProjection_of_mem_of_inner_eq_zero, starProjection_orthogonal_val, norm_starProjection_apply_le, starProjection_apply_mem, orthonormal_iff_ite, finrank_span_eq_card, tendsto_pow_atTop_nhds_zero_of_lt_one, tendsto_one_div_add_atTop_nhds_zero_nat, StrictMono.id_le, squeeze_zero, 'class HasOrthogonalProjection'`
- `grep -rl idtp_tpf in dag.json, nodes/*/*.json and .swarm-worktrees/*/gmt-ch07/GMT/Ch07/*.lean (no match)`
- `grep -n 'Proof of 3.3(2)|h(spt|(13)' book/chapter-07.txt`
- `lake env lean /tmp/idtpf_check/Stmts.lean; lake env lean /tmp/idtpf_check/Assembly.lean; lake env lean /tmp/idtpf_check/Feas.lean; lake env lean /tmp/idtpf_check/Feas2.lean (#print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-ca3ec8cf49/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Orthonormal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Sequences.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Dimension/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecificLimits/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/tmp/idtpf_check/Stmts.lean`
- `/tmp/idtpf_check/Assembly.lean`
- `/tmp/idtpf_check/Feas.lean`
- `/tmp/idtpf_check/Feas2.lean`

Pins and contract.
- The snapshot pins project b4d606db (equal to workspace HEAD) and mathlib 25730c7c; SimonGMT is 2b366308.
- The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

Existing lemmas.
- Not available as accepted lemmas: dilation invariance of cone supports, ∂C = 0 for blow-up limits, support exclusion for weak limits, compactness of n-planes in projection form.
- dtc_blowUp_compactness and dimred_blowup_limit_moving_centres conclude BoundaryVanishes C but are not accepted and carry heavy hypotheses.
- dorag_ted_pl_proj_limit_rank (accepted) only identifies limits of projections of basis vectors, so it is not reused.

Accepted lemmas used by the children:
- dtc_blowUp_algebra: (i) linearity, (iii) spt(blowUp T x λ) = dilation x λ '' spt T, (iv) ∂ commutes with blow-up.
- dtc_vanish_off_support.
- dimred_im_mass_measure (optional route in planar_support_eq).

Other cited results.
- idtp_planar_cycle_eq_const_mul is the parent's prerequisite (status decomposing).
- The parent glue uses density_and_tangent_cones and dimred_minimizing_monotonicity.
- SimonGMT: support = U ∖ zeroRegion with relatively compact open sets (CurrentLocalEquality.lean); boundary_apply ∂S(ω) = S(dω) with tsupport_exteriorDerivative_subset (Currents.lean); massOn = sSup over massAdmissibleOn (Mass.lean); IsTestForm = smooth ∧ compact support (Forms.lean).
- Mathlib: the μHE Haar-measure instance and isometry invariance, plus all cited projection/orthonormal/compactness lemmas, exist under the cited names. HasOrthogonalProjection is a Prop class.

Book. chapter-07.txt lines 512–530 contain the proof of 3.3(2) and the flatness h(spt S, L, ρ, x) via q onto L^⊥; (13) is at line 581.

Names. idtp_tpf_* occurs nowhere in dag.json, in the node JSONs or in the ch07 worktrees.

Lean.
- All 7 child statements elaborate.
- The parent's frozen type is proved from the child stubs; axioms are propext, Classical.choice, Quot.sound and sorryAx from the stubs only.
- All 7 children are proved in Lean against stubs of the cited accepted lemmas only. plane_subsequence_limit and blowup_domain_eventually are fully proved with standard axioms.
