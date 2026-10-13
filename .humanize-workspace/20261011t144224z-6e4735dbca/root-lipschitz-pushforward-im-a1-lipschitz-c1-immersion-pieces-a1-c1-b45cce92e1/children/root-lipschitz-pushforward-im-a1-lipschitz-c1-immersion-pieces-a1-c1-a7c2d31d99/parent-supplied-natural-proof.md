# Parent-supplied natural-language proof

- Parent DAG node: `root.lipschitz_pushforward_im-a1.lipschitz_c1_immersion_pieces-a1.c1_approximation_real-a1`
- Child DAG node: `root.lipschitz_pushforward_im-a1.lipschitz_c1_immersion_pieces-a1.c1_approximation_real-a1.whitney_extension-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Statement. Let n ∈ ℕ, let A ⊆ ℝⁿ be closed, and let f : ℝⁿ → ℝ and τ : ℝⁿ → (ℝⁿ)* be continuous on A and satisfy the compact-uniform condition (‡) stated below. Then there is a C¹ function h : ℝⁿ → ℝ such that for every a ∈ A, h(a) = f(a) and h is Fréchet differentiable at a with derivative τ(a).

Source. This is Simon Ch. 2, Theorem 1.6 (Whitney Extension Theorem), with derivatives as continuous linear maps instead of gradients. It is the result applied in the last step of Simon's printed proof of Theorem 1.5 and in step 8 of the parent proof. Simon gives no proof (“For the proof see for example [EG92] or [Fed69]”). The proof below is the standard Whitney construction (Evans–Gariepy, Measure Theory and Fine Properties of Functions, §6.5; Federer 3.1.14). It is exactly the construction kernel-checked in the pinned SimonGMT files Poincare/SimonGMT/Chapter02/WhitneyJet.lean, WhitneyCover.lean, WhitneyPartition.lean and WhitneyExtension.lean, whose final theorem is Poincare.SimonGMT.Chapter02.exists_contDiff_one_extension_of_whitney. Its hypothesis HasWhitneyC1Compatibility A f τ consists exactly of: f continuous on A, τ continuous on A, and condition (‡) below.

Notation and hypotheses. ℝⁿ = EuclideanSpace ℝ (Fin n) with Euclidean norm |·|; B_r(x) is the open ball and B̄_r(x) the closed ball. (ℝⁿ)* = L(ℝⁿ, ℝ) carries the operator norm ‖·‖. A ⊆ ℝⁿ is closed. f : ℝⁿ → ℝ and τ : ℝⁿ → (ℝⁿ)* are continuous on A, and they satisfy
(‡) for every compact L ⊆ A and every δ > 0 there is ρ > 0 such that |f(y) − f(x) − τ(x)(y − x)| ≤ δ|y − x| for all x ∈ L and y ∈ A with |x − y| < ρ.
Values of f and τ off A play no role. For b ∈ ℝⁿ put P_b(y) := f(b) + τ(b)(y − b). This is an affine function of y with derivative DP_b ≡ τ(b), and P_b(b) = f(b).
(I) For all a, b, y ∈ ℝⁿ: P_b(y) − P_a(y) = [f(b) − f(a) − τ(a)(b − a)] + (τ(b) − τ(a))(y − b). Expand both sides, using τ(a)(y − a) = τ(a)(y − b) + τ(a)(b − a). Consequently |P_b(y) − P_a(y)| ≤ |f(b) − f(a) − τ(a)(b − a)| + ‖τ(b) − τ(a)‖ |y − b|.

0. (Trivial case and distance function.) If A = ∅, the function h :≡ 0 is C^∞, and the conditions at points of A hold vacuously. From now on A ≠ ∅.
- Let d(x) := dist(x, A) = inf_{a∈A} |x − a|. It is 1-Lipschitz, d(x) ≤ |x − a| for every a ∈ A, and d(x) > 0 iff x ∉ A, because A is closed.
- Since ℝⁿ is proper and A is closed and nonempty, every p ∈ ℝⁿ has a nearest point in A. Fix a choice π(p) ∈ A with |p − π(p)| = d(p). Then π(a) = a for a ∈ A, and |π(p) − a| ≤ |π(p) − p| + |p − a| ≤ 2|p − a| for every a ∈ A.
- If n = 0, then ℝ⁰ is a single point, so A = ℝ⁰. The constructions below then concern the empty set ℝ⁰ ∖ A, and h := f works.

1. (Local uniform estimate.) For every a ∈ A and η > 0 there is δ ∈ (0, 1] such that
(i) ‖τ(b) − τ(a)‖ ≤ η for all b ∈ A with |b − a| < δ, and
(ii) |f(c) − f(b) − τ(b)(c − b)| ≤ η|c − b| for all b, c ∈ A with |b − a| < δ and |c − a| < δ.
Proof.
- K := A ∩ B̄₁(a) is compact (closed and bounded). Apply (‡) to K with the constant η to get ρ > 0.
- By continuity of τ|A at a there is ρ′ > 0 with ‖τ(b) − τ(a)‖ < η for b ∈ A with |b − a| < ρ′.
- Put δ := min(1, ρ′, ρ/3). Then (i) holds.
- For (ii): b ∈ K because |b − a| < δ ≤ 1, and |b − c| ≤ |b − a| + |a − c| < 2δ < ρ. So (‡) with x := b and y := c gives the inequality.

2. (Whitney radius.) Let r(x) := min(1, d(x))/100.
- Then 0 ≤ r(x) ≤ 1/100; r(x) > 0 iff x ∉ A; and 100 r(x) ≤ d(x).
- |r(x) − r(y)| ≤ |x − y|/100, since t ↦ min(1, t) is 1-Lipschitz.
- If x ∉ A and |y − x| < 100 r(x), then y ∉ A, since |y − x| < d(x). In particular B_{r(x)}(x) ⊆ ℝⁿ ∖ A.
Comparability. If |x − c| ≤ r(x) + 10 r(c), then r(x)/2 ≤ r(c) ≤ 2 r(x) and |x − c| ≤ 21 r(x). Indeed:
- r(c) ≤ r(x) + |x − c|/100 ≤ r(x) + r(x)/100 + r(c)/10 gives (9/10) r(c) ≤ (101/100) r(x), hence r(c) ≤ 2 r(x);
- r(x) ≤ r(c) + |x − c|/100 ≤ r(c) + r(x)/100 + r(c)/10 gives (99/100) r(x) ≤ (11/10) r(c), hence r(c) ≥ (9/10) r(x) ≥ r(x)/2;
- finally |x − c| ≤ r(x) + 10 r(c) ≤ 21 r(x).

3. (Disjoint Whitney balls.) There is a set Z ⊆ ℝⁿ ∖ A of centres with two properties: the balls B_{r(c)}(c), c ∈ Z, are pairwise disjoint, and every x ∈ ℝⁿ ∖ A has some c ∈ Z with |x − c| < 4 r(c).
- Apply the Vitali covering lemma to the family of balls with centres x ∈ ℝⁿ ∖ A and radii r(x) ∈ (0, 1/100]; the radii are uniformly bounded. Use Simon Ch. 1, Lemma 3.4 (5-times covering lemma, property (*)) for the closed balls B̄_{r(x)}(x).
- It gives a pairwise disjoint subfamily {B̄_{r(c)}(c) : c ∈ Z}. As n ≥ 1 and r > 0, each closed ball determines its centre and radius, so the subfamily is indexed by its set Z of centres. Every B̄_{r(x)}(x) meets some B̄_{r(c)}(c), c ∈ Z, with diam B̄_{r(c)}(c) ≥ diam B̄_{r(x)}(x)/2, i.e. r(c) ≥ r(x)/2 (for n ≥ 1, diam B̄_r = 2r).
- Then |x − c| ≤ r(x) + r(c) ≤ 3 r(c) < 4 r(c), and disjointness of the closed balls implies disjointness of the open balls.
- Equivalently, apply Mathlib Vitali.exists_disjoint_subfamily_covering_enlargement_ball with enlargement factor 4 > 3. Every B_{r(x)}(x) is contained in some B_{4r(c)}(c), and x ∈ B_{r(x)}(x) since r(x) > 0.
Separation. For distinct c, c′ ∈ Z, |c − c′| ≥ r(c). Otherwise c′ ∈ B_{r(c)}(c) ∩ B_{r(c′)}(c′), using r(c′) > 0, which contradicts disjointness.

4. (Bounded overlap.) There is N ∈ ℕ, depending only on n, such that for every x ∈ ℝⁿ ∖ A the set
N(x) := {c ∈ Z : |x − c| ≤ r(x) + 10 r(c)}
is finite with at most N elements.
- The compact ball B̄₂₁(0) is covered by finitely many, say N, open balls of radius 1/4. Let x ∉ A and ρ := r(x) > 0.
- For c ∈ N(x) let p_c := (c − x)/ρ. By comparability |p_c| ≤ 21.
- For distinct c, c′ ∈ N(x), separation and comparability give |p_c − p_{c′}| = |c − c′|/ρ ≥ r(c)/ρ ≥ 1/2.
- Two points of one ball of radius 1/4 are at distance < 1/2. So each of the N small balls contains at most one p_c, and c ↦ p_c is injective. Hence #N(x) ≤ N.

5. (Rescaled bumps.)
- Fix a C^∞ function φ : ℝⁿ → [0, 1] with φ = 1 on B̄₄(0) and φ = 0 outside B₈(0) (Mathlib ContDiffBump with rIn = 4, rOut = 8).
- φ is C¹ with compact support, so it is Λ-Lipschitz for some Λ ≥ 0. Put B := Λ + 1 > 0.
- For c ∈ Z let φ_c(y) := φ((y − c)/r(c)). Then φ_c is C^∞ with 0 ≤ φ_c ≤ 1, φ_c(y) = 1 if |y − c| ≤ 4 r(c), and φ_c(y) = 0 if |y − c| ≥ 8 r(c).
- φ_c is (Λ/r(c))-Lipschitz, so ‖Dφ_c(y)‖ ≤ B/r(c) for all y (Mathlib norm_fderiv_le_of_lipschitz).

6. (Partition of unity on ℝⁿ ∖ A.) Let x ∉ A and y ∈ B_{r(x)}(x); then y ∉ A by step 2.
- If c ∈ Z ∖ N(x), then |y − c| ≥ |x − c| − |x − y| > (r(x) + 10 r(c)) − r(x) = 10 r(c) ≥ 8 r(c), so φ_c(y) = 0.
- So on B_{r(x)}(x) only the finitely many φ_c with c ∈ N(x) can be nonzero. Hence s(y) := Σ_{c∈Z} φ_c(y) (y ∉ A) is a well-defined finite sum, s = Σ_{c∈N(x)} φ_c on B_{r(x)}(x), and s is C^∞ on the open set ℝⁿ ∖ A.
- For y ∉ A, step 3 gives c ∈ Z with |y − c| < 4 r(c), so φ_c(y) = 1 and s(y) ≥ 1.
- Define w_c := φ_c/s on ℝⁿ ∖ A. Each w_c is C^∞ on ℝⁿ ∖ A, and 0 ≤ w_c ≤ 1.
- For x ∉ A and y ∈ B_{r(x)}(x): w_c(y) = 0 for c ∉ N(x), and Σ_{c∈N(x)} w_c(y) = 1. Differentiating this identity on the open ball B_{r(x)}(x) gives Σ_{c∈N(x)} Dw_c(x) = 0.

7. (Gradient bound.) With M := 2B(N + 1)², for every x ∉ A we have Σ_{c∈N(x)} ‖Dw_c(x)‖ ≤ M/r(x).
- For c ∈ N(x), comparability gives r(c) ≥ r(x)/2, so ‖Dφ_c(x)‖ ≤ B/r(c) ≤ 2B/r(x) =: T.
- Ds(x) = Σ_{c∈N(x)} Dφ_c(x), so ‖Ds(x)‖ ≤ N T.
- Dw_c = Dφ_c/s − φ_c Ds/s², with s ≥ 1 and 0 ≤ φ_c ≤ 1. Hence ‖Dw_c(x)‖ ≤ ‖Dφ_c(x)‖ + ‖Ds(x)‖ ≤ T + N T.
- Summing over at most N indices: Σ_{c∈N(x)} ‖Dw_c(x)‖ ≤ N(N + 1)T ≤ (N + 1)² · 2B/r(x) = M/r(x).

8. (Anchors.) Let x ∉ A and c ∈ N(x). Then
(a) |x − π(c)| ≤ 2 d(x), and
(b) |π(c) − a| ≤ 3|x − a| for every a ∈ A.
Proof.
- |x − π(c)| ≤ |x − c| + d(c) ≤ |x − c| + (d(x) + |x − c|) = d(x) + 2|x − c|.
- By comparability and step 2, |x − c| ≤ 21 r(x) ≤ 0.21 d(x). So |x − π(c)| ≤ 1.42 d(x) ≤ 2 d(x).
- For (b): |π(c) − a| ≤ |π(c) − x| + |x − a| ≤ 2 d(x) + |x − a| ≤ 3|x − a|.

9. (The extension.) Define h(y) := f(y) for y ∈ A, and h(y) := Σ_{c∈Z} w_c(y) P_{π(c)}(y) for y ∉ A.
- For y ∉ A this is a finite sum, by step 6 applied with x := y.
- For x ∉ A, step 6 gives h = Σ_{c∈N(x)} w_c P_{π(c)} on B_{r(x)}(x) ⊆ ℝⁿ ∖ A. So h is C^∞ on the open set ℝⁿ ∖ A, and
Dh(x) = Σ_{c∈N(x)} [ w_c(x) τ(π(c)) + P_{π(c)}(x) Dw_c(x) ].
- Since Σ_{c∈N(x)} w_c(x) = 1, also h(x) − P_a(x) = Σ_{c∈N(x)} w_c(x) (P_{π(c)}(x) − P_a(x)) for every a.

10. (h has derivative τ(a) at every a ∈ A.) Let a ∈ A and ε > 0. Take δ from step 1 with η := ε/5, and let |x − a| < δ/4.
- If x ∈ A: by step 1(ii) with b := a and c := x, |h(x) − h(a) − τ(a)(x − a)| = |f(x) − f(a) − τ(a)(x − a)| ≤ (ε/5)|x − a| ≤ ε|x − a|.
- If x ∉ A: h(a) = f(a), so h(a) + τ(a)(x − a) = P_a(x). By step 9, h(x) − P_a(x) = Σ_{c∈N(x)} w_c(x)(P_{π(c)}(x) − P_a(x)).
- For c ∈ N(x) put b := π(c) ∈ A. By step 8, |b − a| ≤ 3|x − a| < δ and |x − b| ≤ 2 d(x) ≤ 2|x − a|.
- By (I) and step 1, |P_b(x) − P_a(x)| ≤ (ε/5)|b − a| + (ε/5)|x − b| ≤ (ε/5)(3 + 2)|x − a| = ε|x − a|.
- The weights w_c(x), c ∈ N(x), are ≥ 0 with sum 1, so |h(x) − h(a) − τ(a)(x − a)| = |h(x) − P_a(x)| ≤ ε|x − a|.
Hence h(x) = h(a) + τ(a)(x − a) + o(|x − a|), i.e. h is differentiable at a with Dh(a) = τ(a). With step 9, h is differentiable at every point of ℝⁿ.

11. (Dh is continuous at every a ∈ A.) Let a ∈ A and ε > 0. Put η := ε/(2(1 + 700M)), take δ ∈ (0, 1] from step 1 with this η, and let |x − a| < δ/4. We show ‖Dh(x) − τ(a)‖ ≤ ε/2.
- If x ∈ A: by step 10, Dh(x) = τ(x), and by step 1(i), ‖τ(x) − τ(a)‖ ≤ η ≤ ε/2.
- If x ∉ A, let b := π(x) ∈ A. By steps 6 and 9 (Σ w_c(x) = 1 and Σ Dw_c(x) = 0),
Dh(x) − τ(a) = Σ_{c∈N(x)} w_c(x)(τ(π(c)) − τ(a)) + Σ_{c∈N(x)} (P_{π(c)}(x) − P_b(x)) Dw_c(x).
- First sum: for c ∈ N(x), |π(c) − a| ≤ 3|x − a| < δ, so ‖τ(π(c)) − τ(a)‖ ≤ η. The convex combination therefore has norm ≤ η.
- Second sum, setup: d(x) ≤ |x − a| < δ/4 < 1, so r(x) = d(x)/100. Also |b − a| ≤ 2|x − a| < δ, so ‖τ(b) − τ(a)‖ ≤ η.
- For c ∈ N(x) let e := π(c). Then |e − a| < δ and ‖τ(e) − τ(a)‖ ≤ η, so ‖τ(e) − τ(b)‖ ≤ 2η. Moreover |x − e| ≤ 2 d(x) and |e − b| ≤ |e − x| + |x − b| ≤ 3 d(x).
- By (I) with the pair (b, e) and step 1(ii) (both b and e lie within δ of a):
|P_e(x) − P_b(x)| ≤ |f(e) − f(b) − τ(b)(e − b)| + ‖τ(e) − τ(b)‖ |x − e| ≤ 3η d(x) + 4η d(x) = 7η d(x) = 700 η r(x).
- With step 7 the second sum has norm ≤ 700 η r(x) · M/r(x) = 700 η M.
- Altogether ‖Dh(x) − τ(a)‖ ≤ η(1 + 700M) = ε/2 < ε.
So Dh is continuous at every point of A. At points x ∉ A, Dh is continuous because h is C^∞ near x (step 9). Hence h is differentiable with continuous derivative, i.e. h ∈ C¹(ℝⁿ) (Mathlib contDiff_one_iff_fderiv).

12. (Conclusion.) h is C¹. For every a ∈ A, h(a) = f(a) by definition, and h is Fréchet differentiable at a with derivative τ(a) by step 10. ∎

Lean realization (checked during decomposition). The pinned SimonGMT source Poincare/SimonGMT/Chapter02/WhitneyExtension.lean (simongmt 2b36630) proves this construction. Its .olean is absent from the shared package tree, but it imports only the built modules Poincare.SimonGMT.Chapter02.WhitneyJet and Poincare.SimonGMT.Chapter02.WhitneyPartition. Copied verbatim to a new file GMT/Ch06/WhitneyExtension.lean (module GMT.Ch06.WhitneyExtension; new .lean files under GMT/Ch06/ are accepted by the comparator), it compiles. The child theorem is then
obtain ⟨h, hh, hEq, hD⟩ := Poincare.SimonGMT.Chapter02.exists_contDiff_one_extension_of_whitney (E := Eucl n) (h := f) (D := τ) hA ⟨hf, hτ, hrem⟩; exact ⟨h, hh, fun a ha => ⟨hEq ha, hD a ha⟩⟩.
The axioms are exactly propext, Classical.choice and Quot.sound. No other DAG branch vendors this file, so it must be added only once.

## Key steps

1. A = ∅ is trivial. Use the affine jets P_b(y) = f(b) + τ(b)(y − b) and the identity (I) for P_b − P_a. Condition (‡) on A ∩ B̄₁(a) and continuity of τ give a local uniform estimate.
2. Whitney radius r = min(1, d)/100 with comparability. Vitali (Simon 1.3.4 / Mathlib) gives disjoint balls B_{r(c)}(c), c ∈ Z, whose 4-fold enlargements cover ℝⁿ ∖ A, with overlap bounded by N(n).
3. Rescaled bumps φ_c and weights w_c = φ_c/Σφ form a locally finite partition of unity on ℝⁿ ∖ A with Σ_{N(x)} ‖Dw_c(x)‖ ≤ M/r(x).
4. Nearest anchors π(c) ∈ A satisfy |x − π(c)| ≤ 2d(x) and |π(c) − a| ≤ 3|x − a|.
5. h := f on A and h := Σ_c w_c P_{π(c)} off A; h is C^∞ on ℝⁿ ∖ A.
6. At a ∈ A, the convex combination of jet differences is ≤ ε|x − a|, so Dh(a) = τ(a).
7. Dh is continuous at a ∈ A because ‖Dh(x) − τ(a)‖ ≤ η(1 + 700M). Hence h ∈ C¹ with h = f and Dh = τ on A.
8. Lean: vendor SimonGMT WhitneyExtension.lean verbatim under GMT/Ch06/ and apply exists_contDiff_one_extension_of_whitney (standard axioms only).

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project, project_commit d8d46c9587747dee0751a1f780fcafdba16a3886, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); git rev-parse HEAD in workspace and lake-packages-25730c7c/{simongmt,mathlib} = d8d46c95…, 2b3663083f3fe399b6296fb8eaee52169170e197, 25730c7c…`
- `cmp snapshot project/GMT/Ch06/Contract.lean vs workspace GMT/Ch06/Contract.lean (identical); cmp workspace Contract.lean vs Submission.lean (identical)`
- `python3 -I over dag.json: id/lean_name/status of all 200 nodes; regex scan Whitney|Lusin|Luzin|Egoroff|Egorov|Rademacher|ContDiff ℝ 1|tendstoUniformly|IsClosed; assert the selected node's lean_statement is byte-equal to the frozen type; check lpf_c1r_lusin_closed, lpf_c1r_egoroff_closed, lpf_c1r_uniform_remainder, lpf_c1r_whitney_extension are unused`
- `grep -rl 'lpf_c1r' and 'exists_contDiff_one_extension_of_whitney|WhitneyExtension' over runs/…/nodes (no other branch vendors Whitney; names free)`
- `sed -n 150,275p book/chapter-02.txt (Simon Thm 1.5, Thm 1.6 (‡), Remark 1.7, printed proof of 1.5; no printed proof of 1.6)`
- `grep -n 'Vitali|Covering Lemma|Lusin|Egoroff' book/chapter-01.txt; sed -n 340,372p and 605,640p (Lusin 1.17, 5-times Covering Lemma 3.4 with property (*))`
- `sed SimonGMT Chapter02/{WhitneyJet,WhitneyCover,WhitneyPartition,WhitneyExtension}.lean and Chapter01/Lusin.lean; grep '^theorem|^def|^structure'; ls simongmt/.lake/build/lib/lean/Poincare/SimonGMT/Chapter0{1,2} (Lusin, WhitneyJet/Cover/Partition built; WhitneyExtension.olean absent)`
- `grep in snapshot mathlib: LipschitzWith.ae_differentiableAt (Analysis/Calculus/Rademacher.lean:385), measurableSet_of_differentiableAt and measurable_fderiv (Analysis/Calculus/FDeriv/Measurable.lean:372,378), MeasurableSet.exists_isClosed_sdiff_lt (MeasureTheory/Measure/Regular.lean:1036; exists_isClosed_diff_lt deprecated), tendstoUniformlyOn_of_ae_tendsto (MeasureTheory/Function/Egorov.lean:205, ε : ℝ≥0∞), addHaar_sphere_of_ne_zero (MeasureTheory/Measure/Lebesgue/EqHaar.lean:519), LocallyFinite.isClosed_iUnion (Topology/LocallyFinite.lean:128), continuousOn_clm_apply (Analysis/Normed/Module/FiniteDimension.lean:518), norm_fderiv_le_of_lipschitz (Analysis/Calculus/FDeriv/Basic.lean:947)`
- `python3 -I scope.py (verifier gmt-compare.contract_scope → opens MeasureTheory Filter Set Metric; scoped ENNReal NNReal Topology; namespace GMT.Ch06; Chapter06/03/01 opens; noncomputable section; end); python3 -I validate.py (lean_contract.validate_lean_statement on all 4 child statements: OK)`
- `sed gmt-compare.py child_modules/candidate_inputs (generated NodeChallenge imports GMT.Ch06.Submission; new .lean files allowed under GMT/Ch06/)`
- `lean src/Submission.lean -o build/GMT/Ch06/Submission.olean in scratch /tmp/c1real-decomp with LEAN_PATH to the shared package builds (shared tree untouched)`
- `lean tests/Stmts.lean, tests/Assembly.lean, tests/Interface.lean, tests/Api.lean, tests/Combined.lean, tests/WhitneyChild.lean, tests/Verbatim.lean with #check and #print axioms; lean vend2/WhitneyExtension.lean -o build/GMT/Ch06/WhitneyExtension.olean (verbatim SimonGMT source)`
- `Agent (independent adversarial review of the four child proofs, the Lean statements and the assembly): all OK; optional wording polish applied`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-lipschitz-c1-immersion-pieces-a1-c1-b45cce92e1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-lipschitz-c1-immersion-pieces-a1-c1-b45cce92e1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-lipschitz-c1-immersion-pieces-a1-c1-b45cce92e1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-lipschitz-c1-immersion-pieces-a1/decomposition-scope-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-lipschitz-c1-immersion-pieces-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyJet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyPartition.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/.lake/build/lib/lean/Poincare/SimonGMT/Chapter02`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/Egorov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/LocallyFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/tmp/c1real-tools/stmts.json`
- `/tmp/c1real-tools/scope.py`
- `/tmp/c1real-tools/validate.py`
- `/tmp/c1real-decomp/tests/Stmts.lean`
- `/tmp/c1real-decomp/tests/Assembly.lean`
- `/tmp/c1real-decomp/tests/Interface.lean`
- `/tmp/c1real-decomp/tests/Api.lean`
- `/tmp/c1real-decomp/tests/WhitneyChild.lean`
- `/tmp/c1real-decomp/tests/Verbatim.lean`
- `/tmp/c1real-decomp/tests/Combined.lean`
- `/tmp/c1real-decomp/vend/WhitneyVendored.lean`
- `/tmp/c1real-decomp/vend2/WhitneyExtension.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c, simongmt 2b36630) holds the frozen Ch06 Contract, byte-identical to the workspace Contract and Submission. Simon prints a proof of Thm 1.5 (p. 44) but none of Whitney's Thm 1.6.

Mathlib has no Lusin theorem for measurable functions, but provides Rademacher (LipschitzWith.ae_differentiableAt), measurableSet_of_differentiableAt, measurable_fderiv, closed inner regularity (MeasurableSet.exists_isClosed_sdiff_lt), Egorov (tendstoUniformlyOn_of_ae_tendsto, ε : ℝ≥0∞), addHaar_sphere_of_ne_zero, LocallyFinite.isClosed_iUnion, continuousOn_clm_apply and norm_fderiv_le_of_lipschitz.

SimonGMT provides:
- finite-measure Lusin, Chapter01.exists_isClosed_continuousOn_of_measurable (built; importable next to GMT.Ch06.Submission; standard axioms);
- the full Whitney C¹ extension, Chapter02.exists_contDiff_one_extension_of_whitney, whose hypothesis HasWhitneyC1Compatibility is exactly continuity of f and τ on A plus (‡). Its .olean is absent, but the source compiles verbatim as GMT/Ch06/WhitneyExtension.lean (it imports only the built WhitneyJet and WhitneyPartition), and the comparator accepts new .lean files under GMT/Ch06/.

All four child statements elaborate in the exact comparator child scope and pass validate_lean_statement. Combined.lean kernel-checks:
- the frozen parent type from the four children;
- uniform_remainder from egoroff_closed, with only the η_k facts stubbed;
- whitney_extension outright, with axioms propext, Classical.choice and Quot.sound.

The proposed lpf_c1r_* names are unused by all 200 DAG nodes and by every node artifact, and no other branch vendors Whitney.
