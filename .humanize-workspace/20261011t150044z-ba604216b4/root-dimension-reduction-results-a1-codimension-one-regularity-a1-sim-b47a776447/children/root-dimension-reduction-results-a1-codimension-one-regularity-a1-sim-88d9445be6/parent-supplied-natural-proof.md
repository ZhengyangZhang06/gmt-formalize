# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.density_one_local_rep-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.density_one_local_rep-a1.rep_density-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Parent step 4 ("|m_y| = 1") of the supplied proof of codim1_density_one_regular_local_rep, stated for an arbitrary integer k and computing the density instead of only bounding it. Book: Simon 7.4.1 (chapter-07.txt lines 590–600: T = m[[M]] in B_ρ(y) at a regular point), Ch. 6, 2.5 (M_W(T), chapter-06.txt line 231), Ch. 3, 1.8(2) (density of a set with a tangent plane, chapter-03.txt lines 306–316).
Departure from the parent text, stated explicitly. The parent proved only the lower bound M_{B_s(y)}(T) ≥ |m_y|(1 − ε)·H^m(M_y ∩ B_s(y)), by testing T with φ·sgn(m_y)·L(ξ_y(y)), and proved the density of M_y from scratch in its fact (F4). Both ingredients are now accepted declarations, which the parent's handoff explicitly allowed child sessions to reuse once accepted: mass_identity gives the exact local mass |k|·H^m(M ∩ B_s(y)), and density_one is (F4). locally_closed supplies the measurability of M (the parent's (F0)).

Dependencies used (sibling subproblems; accepted declarations reused with their identical frozen types):
- locally_closed (Submission.dimred_rpd_embedded_locally_closed): if IsEmbeddedSubmanifold r d M, then M is measurable and every y ∈ M has some ε > 0 with M ∩ closedBall(y, ε) compact.
- density_one (Submission.dimred_rpd_submanifold_density_one): if IsEmbeddedSubmanifold 1 n M and z ∈ M, then H^n(M ∩ B_s(z))/(ω_n·ofReal(s^n)) → 1 in [0, ∞] as s → 0 within (0, ∞).
- mass_identity (Submission.dimred_rpd_massOn_eq_mult_measure): let W be open with W ⊆ U, M measurable, ξ continuous on M with ξ(x) a unit orientation of some linear subspace for every x ∈ M (IsUnitOrientationOf), H^n(M ∩ W) < ∞, and T(ω) = m₀ ∫_M ⟨ω(x), ξ(x)⟩ dH^n(x) for every ω ∈ 𝒟^n(U) with tsupport ω ⊆ W (m₀ ∈ ℤ). Then M_W(T) = T.massOn W = |m₀|·H^n(M ∩ W) in [0, ∞], |m₀| = m₀.natAbs.

Notation. H^m := μHE[m]; B_s(x) := ball x s (open ball); ω_m := unitBallVolume m; ⟨ω(x), ξ(x)⟩ := ξ(x)(ω(x)); 𝒟^m(U) := TestFormOn U m (smooth compactly supported m-forms ω with tsupport ω ⊆ U). M_W(T) := T.massOn W = sup{ofReal(T(ω)) : ω ∈ 𝒟^m(U), tsupport ω ⊆ W, covectorEuclideanNorm(ω(x)) ≤ 1 for all x} (supremum in [0, ∞]). T vanishes on O (T.VanishesOn O) if T(ω) = 0 for every ω ∈ 𝒟^m(U) with tsupport ω ⊆ O; T.zeroRegion is the union of all open O with closure(O) compact, closure(O) ⊆ U and T vanishing on O; spt T := T.support = U ∖ T.zeroRegion. IsOrientation m M ξ means: ξ is continuous on M, and for every x ∈ M there is a linear subspace Q with (Q : Set) = tangentSpace(M, x) and IsUnitOrientationOf (ξ(x)) Q.

Proof. Fix the data and hypotheses of the statement: ρ > 0, B_ρ(y) ⊆ U, y ∈ M, IsEmbeddedSubmanifold 1 m M, IsOrientation m M ξ, H^m(M ∩ K) < ∞ for compact K ⊆ B_ρ(y), and (R) T(ω) = k ∫_M ⟨ω(x), ξ(x)⟩ dH^m(x) for every ω ∈ 𝒟^m(U) with tsupport ω ⊆ B_ρ(y).
1. (Radius-independent hypotheses of mass_identity.) By locally_closed (with r = 1, d = m), M is measurable. By IsOrientation m M ξ, ξ is continuous on M, and for every x ∈ M there is Q with IsUnitOrientationOf (ξ(x)) Q (forget the tangent-space equation).
2. (Exact mass of small balls.) Let 0 < s < ρ and put W := B_s(y).
 (2a) W is open, and W ⊆ B_ρ(y) ⊆ U because s ≤ ρ.
 (2b) closedBall(y, s) is compact (ℝ^P is a proper metric space) and closedBall(y, s) ⊆ B_ρ(y) because s < ρ. By hypothesis H^m(M ∩ closedBall(y, s)) < ∞, and by monotonicity H^m(M ∩ W) ≤ H^m(M ∩ closedBall(y, s)) < ∞.
 (2c) If ω ∈ 𝒟^m(U) and tsupport ω ⊆ W, then tsupport ω ⊆ B_ρ(y), so (R) gives T(ω) = k ∫_M ⟨ω, ξ⟩ dH^m.
 By mass_identity (n := m, m₀ := k), using step 1 and (2a)–(2c):
 (2.1) M_{B_s(y)}(T) = |k|·H^m(M ∩ B_s(y)) for every s ∈ (0, ρ).
3. (Density ratios.) For s ∈ (0, ρ), (2.1) and the identity a·b/c = a·(b/c) in [0, ∞] (mul_div_assoc) give
 M_{B_s(y)}(T)/(ω_m·ofReal(s^m)) = |k|·[H^m(M ∩ B_s(y))/(ω_m·ofReal(s^m))].
4. (Limit.) By density_one (n := m, z := y ∈ M), the bracket tends to 1 as s → 0 within (0, ∞). The constant |k| (a natural number) is finite, so multiplication by |k| is continuous in [0, ∞] at this limit (ENNReal.Tendsto.const_mul, using |k| ≠ ∞), and |k|·[…] → |k|·1 = |k|. The interval (0, ρ) belongs to the filter of s → 0 within (0, ∞) because ρ > 0, and by step 3 the two functions of s agree on it. Hence M_{B_s(y)}(T)/(ω_m·ofReal(s^m)) → |k| as s → 0 within (0, ∞).
5. (Conclusion.) HasMassDensity T y θ means 0 ≤ θ and M_{B_s(y)}(T)/(ω_m·ofReal(s^m)) → ofReal(θ) as s → 0 within (0, ∞). Take θ := (k.natAbs : ℝ). Then θ ≥ 0, and ofReal(θ) = |k| in [0, ∞] (ENNReal.ofReal_natCast). Step 4 is exactly the required limit, so HasMassDensity T y |k|. ∎

Lean reference proof (verified). The declaration below was compiled with Lean v4.35.0-rc3 (Mathlib 25730c7c) against the workspace build of GMT.Ch07.Submission at b4d606db, after `import GMT.Ch07.Submission` with the contract's namespace GMT.Ch07 and `open`s; the dependencies locally_closed, density_one and mass_identity were stated as axioms with their exact frozen types (in the child worktree they are the accepted theorems). It exits 0 with no `sorry`, and `#print axioms` lists propext, Classical.choice, Quot.sound, Submission.dimred_rpd_embedded_locally_closed, Submission.dimred_rpd_massOn_eq_mult_measure and Submission.dimred_rpd_submanifold_density_one. It follows the numbered proof above.

```lean
theorem Submission.codim1_dolr_rep_hasMassDensity : ∀ (P m : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U m) (y : Euclid P) (ρ : ℝ) (k : ℤ) (M : Set (Euclid P)) (ξ : Euclid P → MultiVector P m), 0 < ρ → ball y ρ ⊆ U → y ∈ M → IsEmbeddedSubmanifold 1 m M → IsOrientation m M ξ → (∀ K : Set (Euclid P), IsCompact K → K ⊆ ball y ρ → μHE[m] (M ∩ K) ≠ ∞) → (∀ ω : TestFormOn U m, tsupport (ω : DifferentialForm (Euclid P) m) ⊆ ball y ρ → T ω = k * ∫ x in M, ξ x ((ω : DifferentialForm (Euclid P) m) x) ∂μHE[m]) → HasMassDensity T y (k.natAbs : ℝ) := by
  intro P m U T y ρ k M ξ hρ hballU hyM hMemb hξ hfin hrep
  obtain ⟨hMmeas, -⟩ := Submission.dimred_rpd_embedded_locally_closed P 1 m M hMemb
  have hunit : ∀ x ∈ M, ∃ Q : Submodule ℝ (Euclid P), IsUnitOrientationOf (ξ x) Q := by
    intro x hx
    obtain ⟨Q, -, hQ⟩ := hξ.2 x hx
    exact ⟨Q, hQ⟩
  have hmass : ∀ s : ℝ, 0 < s → s < ρ →
      T.massOn (ball y s) = (k.natAbs : ℝ≥0∞) * μHE[m] (M ∩ ball y s) := by
    intro s _hs hsρ
    have hsub : ball y s ⊆ ball y ρ := ball_subset_ball hsρ.le
    refine Submission.dimred_rpd_massOn_eq_mult_measure P m U T M (ball y s) k ξ isOpen_ball
      (hsub.trans hballU) hMmeas hξ.1 hunit ?_ ?_
    · exact ne_top_of_le_ne_top (hfin _ (isCompact_closedBall y s) (closedBall_subset_ball hsρ))
        (measure_mono (inter_subset_inter_right _ ball_subset_closedBall))
    · intro ω hω
      exact hrep ω (hω.trans hsub)
  refine ⟨Nat.cast_nonneg _, ?_⟩
  rw [ENNReal.ofReal_natCast]
  have hlim := ENNReal.Tendsto.const_mul (a := (k.natAbs : ℝ≥0∞))
    (Submission.dimred_rpd_submanifold_density_one P m M y hMemb hyM)
    (Or.inr (ENNReal.natCast_ne_top _))
  rw [mul_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hρ] with s hs
  rw [hmass s hs.1 hs.2, mul_div_assoc]
```

## Key steps

1. locally_closed makes M measurable; IsOrientation gives continuity of ξ on M and a unit orientation at every point of M.
2. For 0 < s < ρ, mass_identity with W = B_s(y) (finiteness from the compact closedBall(y, s) ⊆ B_ρ(y)) gives M_{B_s(y)}(T) = |k|·H^m(M ∩ B_s(y)).
3. On (0, ρ) the density ratio of T equals |k| times the density ratio of M (mul_div_assoc in [0, ∞]).
4. density_one and continuity of multiplication by the finite constant |k| give the limit |k| = ofReal(k.natAbs), i.e. HasMassDensity T y |k|.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; sha256sum local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `sed -n 1,457p GMT/Ch07/Contract.lean (IsEmbeddedSubmanifold, tangentSpace, IsOrientation, IsUnitOrientationOf, regularSet, HasMassDensity, unitBallVolume, MultiVector)`
- `grep -n 'def support|def zeroRegion|isOpen_zeroRegion|VanishesOn|def massOn|massAdmissibleOn|structure GeometricCurrentOn|testFormOnSubmodule|abbrev Covector|def covectorEuclideanNorm' simongmt/Poincare/SimonGMT/Chapter06/{Currents,CurrentLocalEquality,Mass,Forms}.lean`
- `python3 scans of dag.json: lean_statement mentions IsEmbeddedSubmanifold, IsOrientation, regularSet, tangentSpace, support, massOn; children of regular_point_density-a1, simons_regular_cone-a1, imrep_mass_and_support-a1, cone_constant_density_planar-a1; status and candidate_commit of dimred_rpd_submanifold_density_one, dimred_rpd_massOn_eq_mult_measure, dimred_rpd_embedded_locally_closed, dimred_rpd_near_isometric_chart, dor_ims_unitOrientation_dual, chart_tangentSpace_eq_range_fderiv, dimred_rpd_bilipschitz_image_measure, dor_ims_support_of_massOn_eq, dimred_regular_point_density, idtp_ccd_regular_point_support, codim1_massOn_eq_lintegral_of_oriented_rep`
- `grep -rln IsEmbeddedSubmanifold local-references/123e8435b4a2469b/project; grep -rn 'theorem.*inter_open|theorem.*tangentSpace_inter|theorem.*support_inter' local-references/123e8435b4a2469b/project; grep -rn 'theorem .*support.*rep|theorem .*mem_support' simongmt/Poincare/SimonGMT/Chapter06/*.lean`
- `grep -rn 'setIntegral_eq_of_subset_of_forall_sdiff_eq_zero|setIntegral_eq_zero_of_forall_eq_zero|image_eq_zero_of_notMem_tsupport|IsOpen.closure_inter|ContinuousOn.isOpen_inter_preimage|HasDerivAt.scomp|ContDiffOn.comp|closure_ball|tendsto_nhds_unique|integral_const_mul' Mathlib`
- `runtime.py _existing_lean_name_problem, _accepted_checkpoint, _solve_children, _install_parent_supplied_child_handoff, _overlay_accepted_children, _wait_for_accepted_dependencies; store.py ensure; models.py Subproblem/Decomposition; lean_contract.py validate_lean_statement`
- `git for-each-ref --format='%(objectname)' | sort -u | xargs -n 100 sh -c 'git grep -l -E "codim1_dolr_(embedded_inter_open|rep_hasMassDensity|rep_support_inter)" "$@" -- GMT' _ (positive control: Submission.dimred_rpd_submanifold_density_one)`
- `lean -DautoImplicit=false /tmp/dolr-split/check/Types2.lean, Children2.lean, Assembly2.lean (LEAN_PATH = .lake/build/lib/lean plus every package's .lake/build/lib/lean)`
- `book: chapter-02.txt 850-871; chapter-03.txt 290-316; chapter-06.txt 225-233 and 290-305; chapter-07.txt 588-600`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Neighborhoods.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/Topology/ContinuousOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/RCLike/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/Topology/Separation/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-b47a776447/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-7577af74dd/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-regular-point-density-a1-density-one-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-regular-point-density-a1-mass-identity-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-regular-point-density-a1-locally-closed-a1/parent-child-handoff.json`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/store.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/models.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/tmp/dolr-split/check/Types2.lean`
- `/tmp/dolr-split/check/Children2.lean`
- `/tmp/dolr-split/check/Assembly2.lean`

Pins match. The snapshot manifest records project b4d606db and Mathlib 25730c7c, equal to workspace HEAD and the pinned Mathlib. The snapshot Contract.lean, the workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…). So the selected frozen type and the definitions it uses (regularSet, IsEmbeddedSubmanifold, tangentSpace, IsOrientation, HasMassDensity) are unchanged.
Library.
- SimonGMT Chapter06 defines T.support = U \ T.zeroRegion, where zeroRegion is the union of the open W with compact closure inside U on which T vanishes (CurrentLocalEquality.lean). It defines T.massOn W as a supremum of ofReal T(ω) over massAdmissibleOn (Mass.lean), and TestFormOn as the smooth compactly supported forms with tsupport in U (Currents.lean).
- SimonGMT has no lemma relating the support or the mass to a local representation m[[M]]. The snapshot project has no embedded-submanifold lemmas beyond the contract definitions (no match).
- The pinned Mathlib supplies every tool the child and glue proofs use (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero, setIntegral_eq_zero_of_forall_eq_zero, image_eq_zero_of_notMem_tsupport, IsOpen.closure_inter, ContinuousOn.isOpen_inter_preimage, HasDerivAt.scomp, ContDiffOn.comp, closure_ball, tendsto_nhds_unique, ENNReal.Tendsto.const_mul).
DAG.
- The parent handoff listed dimred_rpd_submanifold_density_one and dimred_rpd_massOn_eq_mult_measure as unaccepted, reusable by child sessions once accepted. Both are now accepted (candidate commits e8842d90b78f and 5fcaddaa05c1), as is dimred_rpd_embedded_locally_closed (6da66b1edf6f). Their frozen types are copied byte-for-byte, so they are reused with no new DAG node (runtime _existing_lean_name_problem / _accepted_checkpoint).
- idtp_ccd_regular_point_support and codim1_massOn_eq_lintegral_of_oriented_rep remain unaccepted in other branches and are not used.
- The 3 new codim1_dolr_ names are free in dag.json (974 nodes), GMT/, SimonGMT and all 1734 ref tips (corrected git grep, positive control 6 hits).
Lean.
- Types2.lean elaborates all 6 child types (exit 0).
- Assembly2.lean proves the selected frozen type from open_piece, rep_density, rep_support and locally_closed as axioms (exit 0; #print axioms: propext, Classical.choice, Quot.sound and those 4).
- Children2.lean proves the 3 new children from the 3 accepted declarations, with no sorry (exit 0).
