# Akopyan's PL Nash–Kuiper–Gromov Theorem

Let $P$ be a finite polyhedral space with compatible simplex charts of
constant curvature $\kappa \in \{-1,0,1\}$, let $d$ be the chart dimension, and let
$n \ge d$. Every short map from $P$ to the corresponding $n$-dimensional model
should admit a uniformly close PL-isometry. In the spherical case the
Challenge additionally assumes uniform strict shortness or that the image
lies in an open hemisphere.

This repository formalizes the PL analogue of the Nash–Kuiper–Gromov theorem
(Akopyan, 2010, Theorems 3.7, 3.17, and 3.18) in Lean 4, developed by
Arseniy Akopyan with the assistance of ChatGPT and Gemini, and released under
the [Apache-2.0](LICENSE) license.

---

## Challenge Theorem

The challenge is specified in [`Challenge.lean`](Challenge.lean) and verified against [`Solution.lean`](Solution.lean) using [`comparator.json`](comparator.json):

```lean
theorem akopyan_pl_nash_kuiper (κ : Geometry) {d m n : ℕ}
    (hdn : d ≤ n) (K : Polyhedron κ d m)
    (f : ↥K.K.space → Model κ n)
    (hf : Lipschitz K f 1)
    (hsphere : κ = .spherical →
      ((∃ L : ℝ≥0, L < 1 ∧ Lipschitz K f L) ∨
       ∃ o : Model κ n, ∀ x,
         modelDist κ n (f x) o < Real.pi / 2))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ↥K.K.space → Model κ n,
      PLIsometry K g ∧
      ∀ x, modelDist κ n (g x) (f x) < ε
```

---

## Verification

### Prerequisites
- Lean 4 toolchain `leanprover/lean4:v4.36.0-rc2` ([`lean-toolchain`](lean-toolchain))
- Mathlib `v4.36.0-rc2` ([`lake-manifest.json`](lake-manifest.json))

### Build & Check
```bash
lake exe cache get
lake build
./scripts/verify-comparator.sh
```

Submission portal: <https://submit.palomar-registry.org/>
