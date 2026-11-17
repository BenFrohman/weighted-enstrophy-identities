# TRUTH GATE — the GOD gate. Read this first.

Author: Benjamin Stanley Frohman. This file is the root instruction for every person and every
automated agent (every bot) that touches this repository. Load it before any other file.

**Only truth and honest, kernel-proved theorems pass this gate. Nothing from this repository is
published, released, deposited on Zenodo, cited or claimed unless the `truth-gate` check is green
on the exact commit being cited.** That is why it is the GOD gate: it sits above every other
check, and no other green check can stand in for it.

## The issue this gate fixes

A paper states its claim in English. Lean can only prove `formal_claim ↔ paper_claim` once
`paper_claim` is itself written in Lean. If `paper_claim` were simply *defined to be*
`formal_claim` (or an alias of it, or something that unfolds to it), the theorem
`intended_correspondence` would be `Iff.rfl`: it would be empty and prove nothing about the
paper. A green certificate could then "certify" a statement different from the one the paper
makes (drift), whether by accident or by an injected instruction.

## The fix rule (binding, permanent)

1. `paper_claim` is an **independent Lean transcription of the paper's exact claim**, written in
   the paper's own terms, with every hypothesis the paper states. The verbatim English quote,
   the paper path, its sha256 and the section are recorded in the doc comment of
   `Semantics.lean` **and** in this file (below).
2. `paper_claim` must **not** be defined as, reference, or trivially alias `formal_claim`.
3. `intended_correspondence : formal_claim ↔ paper_claim` must have a **substantive proof**. It
   may not be `Iff.rfl`, `rfl`, `exact Iff.rfl` or similar, and it may not use the main theorem
   (it is a statement-level equivalence, not "both sides happen to be provable").
4. `formal_claim` is exactly the statement of the repository's main theorem, and
   `paper_claim_holds` is the main theorem transported across the correspondence.
5. Only `propext`, `Classical.choice` and `Quot.sound`. No `sorry`, `admit`, `native_decide` or
   new `axiom` anywhere outside the draft directories in `TRUTH_GATE.lock`.
6. If the paper's English claim cannot be faithfully transcribed, or is not what Lean proves,
   the gate stays **red** and the mismatch is reported. Never patch over it: never weaken
   `paper_claim`, drop a hypothesis, or redefine it to match the formal side. If the
   formalization drifted, rewrite the formalization so it transports across the lock again.
7. Open problems stay hypotheses. No Millennium Prize problem is claimed solved; the gate only
   ensures the certificate proves precisely the locked claim and nothing else.
8. The locked region of `Semantics.lean`, the quote and `TRUTH_GATE.lock` change only with the
   author's explicit sign-off, as a PR that says "new lock" in its title.
9. Commits are authored by Benjamin Stanley Frohman only, with no AI co-author trailers. No
   force-push and no history rewriting.

## What `scripts/verify-lock.sh` checks mechanically

* `lake build` succeeds, with no `sorry` warning outside the draft directories;
* no `sorry` / `admit` / `native_decide` / `axiom` token outside the draft directories
  (comments and strings excluded);
* `Semantics.lean` has `PAPER_PATH`, `PAPER_SHA256`, `PAPER_SECTION` and a verbatim
  `PAPER_QUOTE`; the hash matches the paper file and the quote occurs in it; this file carries
  the same path, hash and quote;
* the lock region hash matches `TRUTH_GATE.lock`;
* `paper_claim`'s body does not mention `formal_claim`; the correspondence is not proved by
  `Iff.rfl`/`rfl`;
* in Lean: the bodies of `formal_claim` and `paper_claim` differ, the two are not
  definitionally equal, the correspondence proof does not reach the main theorem, the main
  theorem's statement is `formal_claim`, `paper_claim_holds` goes through the correspondence,
  and `#print axioms` shows only the three standard axioms.

What it cannot check: whether the transcription is the right reading of the English. That
reading is fixed once, in writing, below and in `Semantics.lean`, and is the author's sign-off.

## Running the gate locally

```
lake exe cache get
bash scripts/verify-lock.sh
```

Reports are written to `truth-gate-report/`.

## The locked claim of this repository

* Paper: `paper/main.tex`
* sha256: `725ff0ca81fd3ab1c843e4421665accf860369ee43cb44c2ba1e04679c6c5b2d`
* Section: The smooth-model theorem of Section "Smooth periodic fields" (`Smooth.enstrophy_identity_smooth`, `Smooth.weighted_identity_smooth`): identities (1) AND (2) for all u, ω, φ ∈ A satisfying (div)–(wt); Theorems "Identity (1)" and "Identity (2)"; Setting equations (div), (vort), (wt)
* Main theorem(s): `WeightedEnstrophy.Smooth.enstrophy_identity_smooth`, `WeightedEnstrophy.Smooth.weighted_identity_smooth`
* Lock file: `TRUTH_GATE.lock`; semantics: `WeightedEnstrophy/Semantics.lean`

Verbatim quote:

```
\begin{theorem}[Identity (1), \texttt{enstrophy\_identity}, \texttt{enstrophy\_identity\_T3}]
For the enstrophy $\|\omega\|_{L^2}^2=\int_{\mathbb{T}^3}|\omega|^2$,
\[\frac{d}{dt}\,\frac12\|\omega\|_{L^2}^2=\int_{\mathbb{T}^3}\omega_i\omega_j\partial_ju_i-\nu\int_{\mathbb{T}^3}|\nabla\omega|^2 .\]

\begin{theorem}[Identity (2), \texttt{weighted\_identity}, \texttt{weighted\_identity\_T3}]
\[\frac{d}{dt}\int_{\mathbb{T}^3}|\omega|^4\phi=4\int|\omega|^2\phi\,\omega\cdot(\omega\cdot\nabla)u+4\nu\int|\omega|^2\phi\,\omega\cdot\Delta\omega+\int|\omega|^6 .\]

\begin{theorem}[\texttt{Smooth.int\_d}, \texttt{Smooth.int\_dt}, \texttt{Smooth.enstrophy\_identity\_smooth}, \texttt{Smooth.weighted\_identity\_smooth}]
The smooth model is a periodic setting. Hence identities (1) and (2) hold for all
$u,\omega,\phi\in A$ satisfying (\ref{div})--(\ref{wt}).

Let $u,\omega:\mathbb{T}^3\to\mathbb{R}^3$ and $\phi:\mathbb{T}^3\to\mathbb{R}$ depend on $t$, with
\begin{align}
&\partial_k u_k=0, \label{div}\\
&\partial_t\omega_i=-u_k\partial_k\omega_i+\omega_k\partial_k u_i+\nu\,\partial_k\partial_k\omega_i,\label{vort}\\
&\partial_t\phi=-u_k\partial_k\phi+|\omega|^2,\label{wt}
\end{align}

summing over repeated indices. The relation $\omega=\nabla\times u$ is not needed for either identity.

$A$ is the algebra of $f\in C^\infty(\mathbb{R}\times\mathbb{R}^3,\mathbb{R})$, $f=f(t,a,b,c)$, with
$f(p+e_k)=f(p)$ for the unit spatial vectors $e_1,e_2,e_3$. $\partial_k f(p)=Df(p)e_k$,
$\partial_tf(p)=Df(p)e_t$, $I(f)(t)=\int_0^1\!\int_0^1\!\int_0^1 f(t,a,b,c)\,dc\,db\,da$, $D_t=\frac{d}{dt}$.
```

```lean
def formal_claim : Prop :=
  ∀ (ν : ℝ) (u w : Fin 3 → Smooth.A) (φ : Smooth.A),
    WeightedEnstrophy.div Smooth.setting u = 0 → VorticityEq Smooth.setting ν u w →
    WeightEq Smooth.setting u w φ →
    deriv (Smooth.I (vsq w)) =
        (2 : ℝ) • Smooth.I (stretch Smooth.setting u w) - (2 * ν) • Smooth.I (gradSq Smooth.setting w)
      ∧ deriv (Smooth.I (vsq w * vsq w * φ)) =
        (4 : ℝ) • Smooth.I (vsq w * φ * stretch Smooth.setting u w)
        + (4 * ν) • Smooth.I (vsq w * φ * wLapW Smooth.setting w)
        + Smooth.I (vsq w * vsq w * vsq w)

def paper_claim : Prop :=
  ∀ (ν : ℝ) (u w : Fin 3 → ℝ × ℝ × ℝ × ℝ → ℝ) (φ : ℝ × ℝ × ℝ × ℝ → ℝ),
    (∀ i, paperSmooth (u i)) → (∀ i, paperSmooth (w i)) → paperSmooth φ →
    (∀ p, ∑ k, fderiv ℝ (u k) p (paperE k) = 0) →
    (∀ i p, fderiv ℝ (w i) p (1, 0, 0, 0) =
      -(∑ k, u k p * fderiv ℝ (w i) p (paperE k)) + ∑ k, w k p * fderiv ℝ (u i) p (paperE k)
        + ν * ∑ k, fderiv ℝ (fun q => fderiv ℝ (w i) q (paperE k)) p (paperE k)) →
    (∀ p, fderiv ℝ φ p (1, 0, 0, 0) =
      -(∑ k, u k p * fderiv ℝ φ p (paperE k)) + ∑ i, w i p ^ 2) →
    ∀ t,
      deriv (fun s => (1 / 2 : ℝ) * paperInt (fun p => ∑ i, w i p ^ 2) s) t =
        paperInt (fun p => ∑ i, ∑ j, w i p * w j p * fderiv ℝ (u i) p (paperE j)) t
          - ν * paperInt (fun p => ∑ i, ∑ k, fderiv ℝ (w i) p (paperE k) ^ 2) t
      ∧ deriv (paperInt (fun p => (∑ i, w i p ^ 2) ^ 2 * φ p)) t =
        4 * paperInt (fun p => (∑ i, w i p ^ 2) * φ p *
              ∑ i, w i p * ∑ j, w j p * fderiv ℝ (u i) p (paperE j)) t
          + 4 * ν * paperInt (fun p => (∑ i, w i p ^ 2) * φ p *
              ∑ i, w i p * ∑ k, fderiv ℝ (fun q => fderiv ℝ (w i) q (paperE k)) p (paperE k)) t
          + paperInt (fun p => (∑ i, w i p ^ 2) ^ 3) t
```

See the doc comment of `WeightedEnstrophy/Semantics.lean` for the fixed reading of the paper's terms, the scope and the non-vacuity witness.

## Re-audit (2026-11-16): the earlier lock was NOT certifying (superseded by the re-lock below)

Status at the re-audit: **REOPENED. The gate was red on purpose.** `TRUTH_GATE.lock` carries `"certifying": false`, and
`scripts/truth_gate_check.py` fails while it does. Nothing was deleted: `Semantics.lean`, the quotes,
the hashes and the history are unchanged.

Rule applied (Benjamin Stanley Frohman, 2026-11-16):
* There are no partial locks. A lock certifies only a step on the correct path to the full theorem
  that is kernel-proved as the actual true answer, so that the next step can build on it.
* Drifted, dummy, placeholder or stand-in types, names or categories are rejected.
* Cross-ontology connections are not rejected for looking unrelated. The kernel check, and whether
  the piece genuinely helps reach the full structured proof, decide.
* `paper_claim` is an independent transcription of the verbatim paper quote, never an alias of
  `formal_claim`, and the correspondence is never `rfl`/`Iff.rfl`.

Locked claim under review: Smooth.enstrophy_identity_smooth (Identity (1) in the smooth model)

Why it is reopened:
* Partial lock. The paper's smooth-model theorem (`Smooth.int_d`, `Smooth.int_dt`, `Smooth.enstrophy_identity_smooth`, `Smooth.weighted_identity_smooth`) states "identities (1) and (2) hold for all u, ω, φ ∈ A". Only identity (1) is locked; identity (2), the weighted identity, is not.
* The locked identity itself is real, true and kernel-checked. It is about real objects (smooth ℤ³-periodic fields), and its `paper_claim` is an independent transcription.

What would re-certify it: Re-lock both identities (1) and (2) in the smooth model, independently transcribed.

## Re-lock (2026-11-16): full lock, certifying

With Benjamin Stanley Frohman's approval of 2026-11-16, the lock was replaced by a full lock:
the paper's full smooth-model theorem: identities (1) AND (2) for all u, ω, φ ∈ A satisfying (div), (vort), (wt) (`Smooth.enstrophy_identity_smooth` ∧ `Smooth.weighted_identity_smooth`).

Previous main theorem(s): `WeightedEnstrophy.Smooth.enstrophy_identity_smooth`. New main theorem(s): `WeightedEnstrophy.Smooth.enstrophy_identity_smooth`, `WeightedEnstrophy.Smooth.weighted_identity_smooth`. `TRUTH_GATE.lock` is back to `"certifying": true`; the reopen record is kept under `reaudit_history`.
All rules still apply: no `sorry`/`admit`/`native_decide`/new axioms; only `propext`, `Classical.choice`, `Quot.sound`;
`paper_claim` is an independent transcription of the verbatim quote; the correspondence is substantive (not `rfl`/`Iff.rfl`)
and does not use the main theorems; a non-vacuity witness is proved in `WeightedEnstrophy/Semantics.lean`.
