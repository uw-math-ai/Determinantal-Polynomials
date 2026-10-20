# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project

Lean 4 + Mathlib formalization of Theorem 4.1 from [arXiv:2309.00806](https://arxiv.org/abs/2309.00806)
(Al Ahmadieh '23, "The fiber of the principal minor map"). The theorem characterizes when two
matrices with the same principal minors must be diagonally equivalent. This is a UW Math AI Lab
project (Autumn 2026, mentors Shaoda Ji and Joe Rogge).

### Goals and philosophy

- Formalize Thm 4.1 and the lemmas it needs. The paper's new content is the ⇒ direction
  (constructing a second point in the fiber); results cited from other papers may stay `sorry`
  for a long time (see "External results" below).
- Code under `DetPoly/LEAN_Warmup/` is exploratory: drafts of definitions and statements that
  serve as references. Their names and design aren't fixed, and their contents will be
  reorganized into topic-based files of the library. Don't treat file locations as permanent.
- General-purpose material (Desnanot–Jacobi, multivariate Jacobi's formula, `setZero`,
  irreducible matrices over arbitrary rings, ...) may be upstreamed to Mathlib. Write it in
  Mathlib style and at Mathlib's level of generality (`CommRing` for identities, a field or UFD
  only when needed), independent of the paper's notation.
- Prefer phrasings that avoid bookkeeping the paper does by hand: arbitrary `Fintype` index
  types instead of `Fin n`, subsets instead of permutations, signs absorbed into factors, one
  ambient `MvPolynomial n R` with predicates like `MvPolynomial.supported` instead of subtypes.
- Comments and docstrings should contain only what helps formalization: the paper's statement
  and how ours deviates, Mathlib pointers, and proof hints. Avoid narration and design history.
- Externally cited results are stated as `sorry` theorems with a citation, never as `axiom`s.

## Commands

- `lake exe cache get` downloads prebuilt Mathlib oleans. Run it after a fresh clone or a Mathlib bump.
- `lake build` builds the `DetPoly` library (the default target).
- `lake env lean <file>` checks a single file. Prefer the Lean MCP tools below when iterating.
- `lake lint` runs the batteries linter (`lintDriver = "batteries/runLinter"`).
- `lake exe mk_all --check` verifies that `DetPoly.lean` imports every module. CI runs this check, so
  add each new file under `DetPoly/` as an `import` in `DetPoly.lean`.
- Blueprint (Python via `uv`): `uv run leanblueprint pdf`, `uv run leanblueprint web`, and
  `uv run leanblueprint checkdecls`. The `blueprint/print/` and `blueprint/web/` dirs are gitignored.

CI (`.github/workflows/blueprint.yml`, on push to `main`) builds, lints, runs the `mk_all` check, and
then compiles the blueprint, the docs (doc-gen4), and `home_page/` for GitHub Pages.

## Tooling for Claude

- **Lean LSP MCP (`mcp__lean-lsp__*`)** is available and works on this project. Use
  `lean_diagnostic_messages` (file-relative paths like `DetPoly/Basic.lean` work), `lean_goal`, and
  `lean_multi_attempt` instead of rebuilding. Run `lean_run_code` for scratch experiments (it needs
  `import Mathlib`). To find lemmas, use `lean_local_search`, then `lean_leansearch`, `lean_loogle`,
  or `lean_leanfinder`. The search tools are rate-limited. `lean_build` is slow, so use it only after
  adding new imports or files.
- **Skills**: use `lean:lean-proof` when proving things. `lean:lean-mwe` covers minimizing errors,
  and `lean:mathlib-review` covers Mathlib-style review.
- Mathlib source is in `.lake/packages/mathlib/`, so grep it directly when MCP search is slow.
- The paper's text, extracted with `pdftotext -layout` from `https://arxiv.org/pdf/2309.00806`, is
  readable. Re-download it if you need exact statements. The key cited paper is AV22,
  `https://arxiv.org/pdf/2205.05267`.

## Conventions

- Toolchain is pinned to `leanprover/lean4:v4.35.0`. Mathlib and doc-gen4 are pinned to the matching
  `v4.35.0` tag in `lakefile.toml`, so bump all three together.
- Files use the Lean module system: each starts with `module`, uses `public import Mathlib`, and wraps
  declarations in `public section` ... `end`. Use `@[expose] public section` when downstream files
  need to unfold definitions.
- `lakefile.toml` sets `relaxedAutoImplicit = false` and enables the Mathlib standard linter set, so
  follow Mathlib style: declare variables explicitly, add docstrings to definitions, and keep lines
  ≤ 100 chars.
- Each file starts with a copyright/authors header and a `/-! ... -/` module docstring.
- Blueprint: `blueprint/src/content.tex` holds the mathematical content (still empty), and shared
  macros go in `blueprint/src/macros/common.tex`. Use `\lean{...}` and `\leanok` to link statements
  to Lean declarations. `blueprint/lean_decls` lists the declarations that `checkdecls` verifies.
- Version control: the repo is a colocated `jj` (Jujutsu) + git repository.

## Mathematical notes (arXiv:2309.00806)

Notation: `F` is a field and `A ∈ F^{n×n}`. `A_S = det A[S,S]` is a principal minor (`A_∅ = 1`). The
principal minor map is `A ↦ (A_S)_{S⊆[n]}`, and the *fiber* of `A` is all `B` with the same principal
minors.
- **Diagonally equivalent**: `B = DAD⁻¹` or `B = DAᵀD⁻¹` for an invertible diagonal `D`. This always
  preserves principal minors. `𝒟(n)` is the set of `A` whose fiber is exactly its diagonal-equivalence
  class.
- **Reducible**: after a simultaneous row/column permutation, `A` is block upper triangular with ≥ 2
  diagonal blocks. Equivalently, the digraph (`i → j` iff `a_ij ≠ 0`) is not strongly connected,
  or some nonempty proper `S` has `a_ij = 0` for `i ∉ S`, `j ∈ S`. Mathlib's `Matrix.IsIrreducible`
  is the **nonnegative** (Perron–Frobenius) notion, so we mirror its quiver design with `≠ 0` in
  place of `> 0`. Use `Quiver.IsStronglyConnected`, not `IsSStronglyConnected`: they differ only
  for 1×1 matrices, which the paper treats as irreducible.
- **Cut**: `X ⊂ [n]` with `2 ≤ |X| ≤ n-2`, `rk A[X,Xᶜ] ≤ 1` and `rk A[Xᶜ,X] ≤ 1`. If `A` is
  irreducible, both ranks are exactly 1.
- **Determinantal polynomial**: `f_A = det(diag(x₁..xₙ) + A) ∈ F[x]`. It is multiaffine, and the
  coefficient of `∏_{i∉S} xᵢ` is `A_S`, so **same fiber ⟺ `f_A = f_B`**. This is the central reduction.
  `G = (diag(x) + A)^adj`. `∂f/∂xᵢ = G_ii`, and in general `∂_S f` is the principal minor of
  `diag(x)+A` with `S` deleted. For `i ≠ j`, `G_ij ∈ F[x_k : k ≠ i,j]` is multiaffine.
- **Rayleigh difference**: `Δᵢⱼ(f) = ∂ᵢf·∂ⱼf − f·∂ᵢ∂ⱼf`.
- **Resultant (degree-1 version)**: `res_{x_k}(g,h) = g|_{x_k=0}·∂_k h − h|_{x_k=0}·∂_k g`. This is
  **not** Mathlib's `Polynomial.resultant`.

### Main theorem (Thm 4.1)

For `n ≥ 4`, `A ∈ 𝒟(n)` ⟺ `A` is irreducible and either (a) `A` is diagonally equivalent to a
symmetric matrix, or (b) `A` has no cut.

### Dependency structure

- **Thm 2.3**: `Δᵢⱼ(f_A) = G_ij·G_ji`. The proof uses the Desnanot–Jacobi/Dodgson identity
  `det M(i,i)·det M(j,j) − det M·det M({i,j},{i,j}) = det M(i,j)·det M(j,i)` for `M = diag(x)+A`.
  Mathlib does **not** have Desnanot–Jacobi (only row/column Laplace expansion,
  `det_eq_sum_mul_adjugate_row`); it follows from Jacobi's complementary-minor theorem.
- **Thm 2.1** (= AV22 Thm 3.1, **external**): a multiaffine `f` with coefficient of `x₁⋯xₙ` equal to 1
  is `f_A` for some `A` iff each `Δᵢⱼ(f) = g_ij·g_ji` with (a) `g_ij ∈ F[x_k : k≠i,j]` multiaffine and
  (b) `res_{x_k}(g_ij, f) = g_ik·g_kj` for all `k ≠ i,j`. In that case `g_ij` can be taken to be `G_ij`.
  - The ⇒ direction is again Desnanot–Jacobi, with `res_{x_k}(G_ij, f) = G_kk·G_ij − f·q = G_ik·G_kj`.
  - ⇐ (needed by Lemma 4.5): the paper only applies it to **irreducible** `f`, so we only need that
    case. AV22's proof works as follows. Set `g_ii = ∂ᵢf`. Then all 2×2 minors of `G = (g_ij)` lie in
    `⟨f⟩`, using that `∂₁f` is a non-zero-divisor mod irreducible `f`. So `f^{k-1}` divides the k×k
    minors (cited from AV22 ref [50], Lemma 4.7, which is another external dependency). Then
    `M := G^adj / f^{n-2}` satisfies `det M = f`, and degree counting shows `M = diag(x) + A` with
    constant off-diagonal entries. Lemma 4.5 needs the **strong** conclusion that `adj(diag(x)+B)` has
    off-diagonal entries `g_ij`, not just `f_B = f`. AV22 Remark 3.4 states this
    (`G = (diag(x)+A)^adj`).
- **Lemma 2.2** (AV22 Prop 2.2): if `f` has degree 1 in both `xᵢ` and `xⱼ`, then `Δᵢⱼ f = 0` ⟺
  `f = g·h` with `g` free of `xᵢ` and `h` free of `xⱼ`. Writing `f = a xᵢxⱼ + b xᵢ + c xⱼ + d` gives
  `Δᵢⱼ f = bc − ad`, and the ⇒ direction needs a UFD (`bc = ad` ⇒ common-factor splitting).
- **Thm 3.1** (generalized Laplace expansion along a set of rows, with signs `(-1)^{ΣS+ΣT}`): Mathlib
  doesn't have it. It is used **only** in Lemma 4.3, so consider a direct argument instead: write
  `A[X,Xᶜ] = u vᵀ` and expand the cofactor by multilinearity in the rows of `X`.
- **Lemma 4.2** (Hartfiel–Loewy 1984 Thm 1, **external**, LAA 58:147–167, not on arXiv): if `A` is
  irreducible, every entry of `G` is a nonzero polynomial. Possible direct route: `G_ij` expands as a
  signed sum over paths `j → i` in the digraph of `A` times principal minors of `diag(x)+A` on the
  complement. A shortest path should give a monomial `∏_{k∉path} x_k` with a nonzero coefficient.
  This is unverified, so check it.
- **Lemma 4.3**: `A` is irreducible with a cut `X` (`n ≥ 4`) ⇒ for `i ∈ X`, `j ∈ Xᶜ`,
  `G_ij = ±aᵢ bⱼ` with `aᵢ ∈ F[x_k : k ∈ X∖{i}]` and `bⱼ ∈ F[x_k : k ∈ Xᶜ∖{j}]`, both nonzero. The
  `(-1)^i` sign can be absorbed into `aᵢ`. The same holds for `G[Xᶜ,X] = ±cᵢ dⱼ`.
- **Lemma 4.4**: with a cut `X`, if `G_ij = α_ij G_ji` (`α_ij ∈ F`) for all `i ∈ X`, `j ∈ Xᶜ`, then `A`
  is diagonally similar to a symmetric matrix. The proof uses Thm 2.1/2.3 and resultants to propagate
  the proportionality, then sets `D_jj = √α_jk`.
- **Lemma 4.5** (the key construction): with `X = [k]` a cut, `G = [[P, R], [T, Q]]`,
  `R_ij = ±aᵢbⱼ`, and `T_ij = ±cᵢdⱼ`, let `H = [[P, U], [V, Qᵀ]]` with `U_ij = ±aᵢcⱼ` and
  `V_ij = ±bᵢdⱼ` (swap the `b`/`c` factors and transpose one diagonal block). Then `H` satisfies the
  hypotheses of Thm 2.1, so `H = adj(diag(x)+B)` with `f_B = f_A`.
- **Proof of Thm 4.1 ⇒** (the new content): if `A` is reducible, replace the off-diagonal block `F`
  of `[[E,F],[0,G]]` by a block `H` whose zero pattern is complementary to `F`'s. This gives `B` in
  the fiber that is not equivalent to `A`. If `A` is irreducible with a cut and not symmetrizable,
  build `B` by Lemma 4.5. If `B ~ A`, the `bⱼ ∝ cⱼ`, so swap `aᵢ ↔ dᵢ` instead to get `C`. If `C ~ A`
  too, the `aᵢ ∝ dᵢ`, so Lemma 4.4 gives symmetrizability, a contradiction.
- **Proof of Thm 4.1 ⇐**: the "no cut" case is **Loewy 1986 Thm 1** (LAA 78:23–64, 40 pages,
  **external**, probably left as `sorry` at first). The symmetric case is Lemma 6.1.
- **Lemma 5.1**: `A` is irreducible ⟺ `f_A` is irreducible. ⇐ comes from block-triangular
  determinant factorization (`Matrix.BlockTriangular.det`). ⇒ follows from Lemma 4.2 + Thm 2.3
  (`Δᵢⱼ f ≠ 0`) + Lemma 2.2. Note that `n = 0` is an edge case (`f = 1`).
- **Lemma 6.1**: for symmetric `A` (`n ≥ 4`), `A ∈ 𝒟(n)` ⟺ `A` is irreducible. ⇐: `G` is symmetric,
  so `G_ij² = Δᵢⱼ f = H_ij H_ji`. Each irreducible factor of the multiaffine `G_ij` appears exactly
  once in each of the multiaffine `H_ij` and `H_ji`, so `H_ij = α_ij G_ij`. The resultant condition
  gives `α_ij = α_ik/α_jk`, and then `D = diag(1, α₁₂, …, α₁ₙ)` works.
- Sections 5–7 (structure theorem 5.2 via strongly connected components, symmetric/Hermitian fibers,
  real-stable matrices) are beyond Thm 4.1 and are lower priority.

### Known issues to keep in mind

1. **Square roots in Lemma 4.4 / Thm 4.1(a).** `D_jj = √α_jk` needs square roots in `F`. Over a
   non-quadratically-closed field, "diagonally equivalent to symmetric" is probably the wrong
   condition. The field-independent notion is **symmetrizable**: `∃` invertible diagonal `μ` with
   `μA` symmetric. We state Thm 4.1 with symmetrizable instead. Confirm with mentors.
2. **Transpose case in the ⇒ proof.** `𝒟(n)` allows `B ~ Aᵀ` as well as `B ~ A`, but the written
   proof only rules out `B = DAD⁻¹`. Also check that the constructed `B`/`C` is not `DAᵀD⁻¹`.
3. **Lemma 4.5 vs Example 4.6.** The lemma transposes `Q` but the example transposes `P`. Both
   conventions work, so pick one.
4. Example 4.6 (4×4 matrices `A`, `B` over `ℚ` with cut `X = {1,2}`) is a good computable sanity
   check: matrices over `ℚ` and their principal minors are computable (`#guard`/`#eval`).

### External results (likely to stay `sorry` initially)

These are Hartfiel–Loewy 1984 Thm 1 (Lemma 4.2), Loewy 1986 Thm 1 (no cut ⇒ trivial fiber), and
AV22 Thm 3.1 ⇐ (with AV22's ref [50] Lemma 4.7 on `f^{k-1} | k×k minors`).
