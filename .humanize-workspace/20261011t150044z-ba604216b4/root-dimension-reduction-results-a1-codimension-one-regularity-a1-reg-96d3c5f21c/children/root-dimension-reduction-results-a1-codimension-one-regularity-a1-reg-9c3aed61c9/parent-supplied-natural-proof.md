# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.rectifiable_density_one-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.rectifiable_density_one-a1.ae_approx_tangent-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Simon Ch. 3, Theorem 1.6 '⇒' (chapter-03.txt lines 109–144), with Lemma 1.2 and Remark 1.3 (lines 25–76); this is steps 2 and 4 of the parent proof. Simon writes M as the disjoint union of M_0 (null) and the sets M_j ⊆ N_j. He compares ∫_{η_{x,λ}(M)} f with ∫_{η_{x,λ}(N_j)} f, and kills the contributions of M ∖ M_j and N_j ∖ M_j at H^n-a.e. x ∈ M_j by the Upper Density Theorem. Below, the pieces are the sets M ∩ N_k. Their disjointness (Remark 1.3) is not needed, because the exceptional sets are combined by a countable union. Notation: H^n = μHE[n].

1. (C¹ cover; sibling c1_cover = Lemma 1.2.) There are C¹ maps g_k, points c_k, radii r_k and constants m_k > 0 with the following properties:
- N_k := g_k(B_{r_k}(c_k)) is Borel with H^n(N_k) < ∞;
- m_k|a − b| ≤ |g_k(a) − g_k(b)| for a, b ∈ B_{r_k}(c_k);
- H^n(M ∖ ⋃_k N_k) = 0.

2. (Tangent planes of the pieces; sibling c1_piece_tangent.) For each k and each z ∈ B_{r_k}(c_k), N_k has approximate tangent space Dg_k(z)(ℝ^n) at g_k(z). In particular N_k has some approximate tangent space at every point of N_k.

3. (Comparison of M with N_k; sibling tangent_transfer.) Apply the sibling with W := ℝ^P (open), A := M and B := N_k.
- Both sets are Borel. H^n(M ∩ K) < ∞ by hypothesis, and H^n(N_k ∩ K) ≤ H^n(N_k) < ∞.
- This gives an H^n-null set E_k such that, for every w ∉ E_k with w ∈ M ∩ N_k and every subspace Q, M has approximate tangent space Q at w iff N_k does.
- The sibling's proof is Simon's. The blow-up integrals of f over M and over N_k at w differ by at most sup|f|·R^n·(ρ^{-n}H^n((M∖N_k) ∩ closedBall(w, ρ)) + ρ^{-n}H^n((N_k∖M) ∩ closedBall(w, ρ))) with ρ = λR. These terms tend to 0 at a.e. w ∈ M ∩ N_k by the Upper Density Theorem.

4. (Countable union.) Let E := (M ∖ ⋃_k N_k) ∪ ⋃_k E_k. It is H^n-null, as a countable union of the null sets of steps 1 and 3. Let w ∈ M ∖ E.
- Then w ∈ N_k for some k, say w = g_k(z) with z ∈ B_{r_k}(c_k).
- By step 2, N_k has approximate tangent space Q := Dg_k(z)(ℝ^n) at w.
- Since w ∉ E_k and w ∈ M ∩ N_k, step 3 shows that M also has approximate tangent space Q at w.

5. (Restricted measure.) M is Borel. So for any property p, 'p(w) for μHE[n].restrict M-a.e. w' is equivalent to 'for H^n-a.e. w, w ∈ M → p(w)'. Step 4 gives the latter with the null set E. ∎

Appendix. The following Lean realization of steps 1–5 compiles with Lean v4.35.0-rc3 and Mathlib 25730c7c, after `import GMT.Ch07.Submission` in the frozen contract's scope (namespace GMT.Ch07 and its `open` commands). In the check, the sibling declarations Submission.codim1_rdo_rectifiable_c1_cover and Submission.codim1_rdo_c1_piece_approxTangent were stubs with the frozen types above. Submission.doraggt_ae_approxTangent_transfer was the accepted proof from candidate commit 422e346e.

```lean
theorem Submission.codim1_rdo_rectifiable_ae_approxTangent : ∀ (P n : ℕ) (M : Set (Euclid P)), MeasurableSet M → CountablyRectifiable n M → (∀ K : Set (Euclid P), IsCompact K → μHE[n] (M ∩ K) ≠ ∞) → ∀ᵐ w ∂(μHE[n].restrict M), ∃ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M w Q := by
  intro P n M hM hrect hloc
  obtain ⟨g, c, r, m, hg, hm, hlow, hmeas, hfin, hnull⟩ :=
    Submission.codim1_rdo_rectifiable_c1_cover P n M hrect
  have hpiece : ∀ k, ∀ᵐ w ∂(μHE[n] : Measure (Euclid P)), w ∈ (univ : Set (Euclid P)) → w ∈ M →
      w ∈ g k '' ball (c k) (r k) → ∀ Q : Submodule ℝ (Euclid P),
        HasApproximateTangentSpaceAt n M w Q ↔ HasApproximateTangentSpaceAt n (g k '' ball (c k) (r k)) w Q :=
    fun k => Submission.doraggt_ae_approxTangent_transfer P n univ M (g k '' ball (c k) (r k)) isOpen_univ hM
      (hmeas k) (fun K hK _ => hloc K hK)
      (fun K _ _ => ne_top_of_le_ne_top (hfin k) (measure_mono inter_subset_left))
  have hall := ae_all_iff.2 hpiece
  have hnull' : ∀ᵐ w ∂(μHE[n] : Measure (Euclid P)), w ∉ M \ ⋃ k, g k '' ball (c k) (r k) :=
    measure_eq_zero_iff_ae_notMem.1 hnull
  rw [ae_restrict_iff' hM]
  filter_upwards [hall, hnull'] with w hw hw' hwM
  have hU : w ∈ ⋃ k, g k '' ball (c k) (r k) := by
    by_contra h
    exact hw' ⟨hwM, h⟩
  obtain ⟨k, hk⟩ := mem_iUnion.1 hU
  obtain ⟨z, hz, rfl⟩ := hk
  exact ⟨_, (hw k (mem_univ _) hwM ⟨z, hz, rfl⟩ _).2
    (Submission.codim1_rdo_c1_piece_approxTangent P n (g k) (c k) (r k) (m k) (hg k) (hm k) (hlow k) z hz)⟩
```

## Key steps

1. Lemma 1.2 (sibling c1_cover): M is covered, up to an H^n-null set, by Borel C¹ pieces N_k = g_k(B_{r_k}(c_k)) of finite measure.
2. Each N_k has the approximate tangent space Dg_k(z)(ℝ^n) at every point g_k(z) (sibling c1_piece_tangent).
3. By the Upper Density Theorem (sibling tangent_transfer with A = M, B = N_k), M and N_k have the same approximate tangent spaces at H^n-a.e. point of M ∩ N_k.
4. A countable union of the exceptional null sets gives an approximate tangent space of M at H^n-a.e. point of M.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json; cat lean-toolchain lakefile.toml swarm-project.json; diff GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical)`
- `python3 scans of dag.json: lean_name/status/candidate_commit/lean_statement of rsd_tendsto_closedBall_density_of_approxTangent, rsd_tendsto_ball_density_of_closedBall, regcomp_atl_upper_density_zero, regcomp_approx_tangent_locality, rsdic_ae_tangent_iff_of_subset, doraggt_ae_approxTangent_transfer, dpf_rectifiable_bilipschitz_pieces, dpf_approxTangent_ae_bilipschitz_piece, ptd_piece_image_approxTangent_ae, cbr_rectifiable_of_approx_tangent; all accepted lean_statements containing HasApproximateTangentSpaceAt; collision check for codim1_rdo_c1_approximation, codim1_rdo_rectifiable_c1_cover, codim1_rdo_c1_piece_approxTangent, codim1_rdo_rectifiable_ae_approxTangent (0 matches); no existing children of the selected node`
- `sed -n /runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py: _existing_lean_name_problem, _install_parent_supplied_child_handoff, _solve_children, accepted-child overlay (merges candidate commits of node.children + node.depends_on only), _accepted_checkpoint`
- `grep -n '^theorem' simongmt Chapter02/{AreaCritical,AreaFormula,WeightedArea,WhitneyExtension,WhitneyJet,AreaLipschitz,Lipschitz}.lean, Chapter03/{Rectifiable,SubmanifoldCover,DisjointCover}.lean, Chapter01/Lusin.lean; module docstrings of all Chapter02/*.lean`
- `grep -rln 'Lusin|Whitney' and 'theorem .*exists.*continuousOn' in snapshot Mathlib (only Lusin–Souslin and the manifold Whitney embedding: no measure-theoretic Lusin, no C¹ Whitney extension); grep norm_fderiv_le_of_lipschitz in Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `lake env lean /tmp/rdo1-split-check/Avail.lean (#check of SimonGMT/Mathlib lemmas after import GMT.Ch07.Submission)`
- `lake env lean /tmp/rdo1-split-check/Imports.lean and /tmp/rdo1-split-check/Names.lean (#check and #print axioms with extra imports Poincare.SimonGMT.Chapter02.AreaCritical, Chapter02.WeightedArea, Chapter01.Lusin, Chapter03.SubmanifoldCover)`
- `olean survey of lake-packages-25730c7c/simongmt/.lake/build/lib/lean/Poincare/SimonGMT/Chapter0{1,2,3}; findmnt and touch on lake-packages-25730c7c (read-only); lake env lean /tmp/rdo1-split-check/vendor/WhitneyExtensionCopy.lean plus #print axioms exists_contDiff_one_extension_of_whitney`
- `git show <candidate_commit>:GMT/Ch07/Submission.lean over all accepted nodes (import headers; helper theorems in namespace Submission); git diff --stat of accepted commits; sed -n gmt-compare.py candidate_inputs/check_packages (new .lean files allowed under GMT/Ch07/)`
- `lake env lean -DautoImplicit=false /tmp/rdo1-split-check/Types.lean (seven child types plus comparator-style `theorem target : (T) := by exact Submission.X`)`
- `lake env lean -DautoImplicit=false /tmp/rdo1-split-check/Assembly.lean (parent and Theorem 1.6 '⇒' from child types; #print axioms parent_from_all)`
- `lake env lean -DautoImplicit=false /tmp/rdo1-split-check/Combined.lean (accepted proofs from commits 422e346e, dbef2c15, c3ca64f2 + stubs; #print axioms Submission.codim1_rdo_rectifiable_ae_density_one)`
- `sed -n book/chapter-02.txt 100–330, chapter-03.txt 1–160, chapter-01.txt 560–735; grep -n of the item headings (1.2 Lemma, 1.3 Remark, 1.4 Definition, 1.5 Remarks, 1.6 Theorem, Proof of Theorem 1.5, 3.6 Theorem)`
- `read accepted parent-supplied natural proofs of regcomp_approx_tangent_locality, rsd_tendsto_closedBall_density_of_approxTangent, rsd_tendsto_ball_density_of_closedBall, doraggt_ae_approxTangent_transfer, doraggt_local_density_zero`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-96d3c5f21c/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/swarm-project.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/lakefile.toml`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/DisjointCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaFormula.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WeightedArea.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaApproximation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyJet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/lakefile.toml`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/WhitneyEmbedding.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-components-are-minimizing-a1-approx-tangent-locality-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-density-eq-multiplicity-a1-unweighted-density-one-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-density-eq-multiplicity-a1-closed-to-open-b-2625a8c412/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-6e2110e6b7/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-cda4d660ba/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/tmp/rdo1-split-check/Avail.lean`
- `/tmp/rdo1-split-check/Imports.lean`
- `/tmp/rdo1-split-check/Names.lean`
- `/tmp/rdo1-split-check/Types.lean`
- `/tmp/rdo1-split-check/Assembly.lean`
- `/tmp/rdo1-split-check/Combined.lean`
- `/tmp/rdo1-split-check/vendor/WhitneyExtensionCopy.lean`
- `/tmp/rdo1-split-check/out/subproblems.json`

Pins and contract.
- The snapshot manifest (project b4d606db, Mathlib 25730c7c) matches the workspace.
- Submission.lean is byte-identical to Contract.lean.

Library: what exists.
- SimonGMT defines CountablyRectifiable, HasApproximateTangentSpaceAt and blowUpMap (Chapter03/Rectifiable).
- It proves Remark 1.3 (DisjointCover) and only the 'if' direction of Lemma 1.2. The SubmanifoldCover header states that 'only if' needs the C¹ approximation theorem and is not proved.
- It also proves: critical images are null (Chapter02/AreaCritical.area_image_criticalSet_eq_zero); the injective area formula in Bochner form (Chapter02/WeightedArea.integral_area_formula_of_injective_derivative); Whitney's C¹ extension (Chapter02/WhitneyExtension.exists_contDiff_one_extension_of_whitney); Lusin (Chapter01/Lusin.exists_isClosed_continuousOn_of_measurable); the Lipschitz image bound (euclideanHausdorffMeasure_image_le_of_lipschitzOn). All use only propext, Classical.choice and Quot.sound.
- Mathlib has Rademacher, Egoroff, closed inner regularity, strict differentiability, LinearMap.exists_antilipschitzWith, ContDiffOn.exists_lipschitzOnWith and μHE[n] = volume on Euclid n.

Library: what is missing.
- SimonGMT has neither Simon Ch. 2 Theorem 1.5 nor Ch. 3 Theorem 1.6.
- Mathlib has neither a measure-theoretic Lusin theorem nor a C¹ Whitney extension.

Imports.
- The SimonGMT area, Whitney and Lusin modules are not in the import closure of GMT.Ch07.Submission.
- Accepted nodes do add such imports (Chapter02.WeightedArea, Chapter02.AreaLipschitz, Chapter01.DensityComparison), and their Submission files contain helper theorems.
- WhitneyExtension.olean is absent from the read-only shared package tree. An unmodified copy compiles with 0 errors, so it must be vendored under GMT/Ch07/ (the verifier accepts new Lean files there) or inlined.

DAG.
- Three declarations are accepted with candidate commits and byte-identical types, and are reused as children: doraggt_ae_approxTangent_transfer (422e346e), rsd_tendsto_closedBall_density_of_approxTangent (dbef2c15) and rsd_tendsto_ball_density_of_closedBall (c3ca64f2).
- regcomp_atl_upper_density_zero, cited in the supplied step 4, is an ingredient of the doraggt proof chain.
- The four new names occur nowhere in dag.json.
- A parent worktree merges only the candidate commits of its children and depends_on, so the reused lemmas must be listed as children.

Lean.
- All seven child types elaborate after import GMT.Ch07.Submission in the contract scope.
- The parent type is proved from the child types with axioms propext, Classical.choice and Quot.sound only.
- With the actual accepted proofs and stubs for the three new lemma children, both Theorem 1.6 '⇒' and the parent compile. sorryAx comes only from those stubs.
