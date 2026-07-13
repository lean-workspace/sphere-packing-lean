---
title: 'Modular forms'
type: "blueprint-chapter"
tags:
  - "blueprint"
---

In this section, we recall and develop some theory of (quasi)modular forms.

**Modular forms and examples**

Let $\mathfrak{H}$ be the upper half-plane $\{z\in\mathbb{C}\mid\Im(z)>0\}$.

## Lemma: Gamma-1-Action {#def:Gamma-1-Action}

The modular group $\Gamma_1:=\mathrm{SL}_2(\mathbb{Z})$ acts on $\mathfrak{H}$ by linear fractional transformations

$$
\left(\begin{smallmatrix}a&b\\c&d\end{smallmatrix}\right)z:=\frac{az+b}{cz+d}.
$$

Let $N$ be a positive integer.

## Definition: level-N-princ-cong-subgp {#def:level-N-princ-cong-subgp}

The _level $N$ principal congruence subgroup_ of $\Gamma_1$ is

$$
\Gamma(N):=\left\{\left.\left(\begin{smallmatrix}a&b\\c&d\end{smallmatrix}\right)\in\Gamma_1\right|\left(\begin{smallmatrix}a&b\\c&d\end{smallmatrix}\right)\equiv\left(\begin{smallmatrix}1&0\\0&1\end{smallmatrix}\right)\;\mathrm{mod}\;N\right\}.
$$

## Definition: congruence-subgroup {#def:congruence-subgroup uses="def:level-N-princ-cong-subgp"}

A subgroup $\Gamma\subset\Gamma_1$ is called a _congruence subgroup_ if $\Gamma(N)\subset\Gamma$ for some $N\in\mathbb{N}$.

## Definition: Gamma-generators {#def:Gamma-generators lean="ModularGroup.S, ModularGroup.T, α, β" uses="def:level-N-princ-cong-subgp"}

Define the matrices

  
$$
S = \begin{pmatrix} 0 & -1 \\ 1 & 0 \end{pmatrix} \in \Gamma_1,
    T = \begin{pmatrix} 1 & 1 \\ 0 & 1 \end{pmatrix} \in \Gamma_1,
    \alpha = \begin{pmatrix} 1 & 2 \\ 0 & 1 \end{pmatrix} \in \Gamma_2 \subset \Gamma_1,
    \beta = \begin{pmatrix} 1 & 0 \\ 2 & 1 \end{pmatrix} \in \Gamma_2 \subset \Gamma_1.
$$

  It is easily verifiable that $\alpha = T^2$ and $\beta = -S\alpha^{-1}S = -ST^{-2}S$.

The following two lemmas tell us the group structure of $\Gamma(1) = \Gamma_1$ and $\Gamma(2)$, which we will use later on to define the theta forms.

## Lemma: Gamma-1-generators {#lemma:Gamma-1-generators lean="SL2Z_generate" uses="def:Gamma-generators"}

We have $\Gamma(1) = \langle S, T, -I \rangle$.

### Proof

See [@first-course, Exercise 1.1.1].

## Lemma: Gamma-2-generators {#lemma:Gamma-2-generators lean="Γ2_generate" uses="def:Gamma-generators"}

We have $\Gamma(2) = \langle \alpha, \beta, -I \rangle$.

### Proof

See [@first-course, Exercise 1.2.4].

Let $z\in\mathfrak{H}$, $k\in\mathbb{Z}$, and $\left(\begin{smallmatrix}a&b\\c&d\end{smallmatrix}\right)\in\mathrm{SL}_2(\mathbb{Z})$. We omit many of the proofs below when they exist in Mathlib already.

## Definition: automorphy-factor {#def:automorphy-factor lean="UpperHalfPlane.denom"}

The _automorphy factor_ of weight $k$ is defined as

$$
j_k(z,\left(\begin{smallmatrix}a&b\\c&d\end{smallmatrix}\right)):=(cz+d)^{-k}.
$$

## Lemma: automorphy-factor-chain-rule {#lemma:automorphy-factor-chain-rule lean="UpperHalfPlane.denom_cocycle" uses="def:automorphy-factor"}

The automorphy factor satisfies the _chain rule_

$$
j_k(z,\gamma_1\gamma_2)=j_k(z,\gamma_1)\,j_k(\gamma_2z,\gamma_1).
$$

## Definition: slash-operator {#def:slash-operator uses="def:automorphy-factor, def:Gamma-1-Action"}

Let $F$ be a function on $\mathfrak{H}$ and $\gamma\in\mathrm{SL}_2(\mathbb{Z})$. Then the _slash operator_ acts on $F$ by

$$
(F|_k\gamma)(z):=j_k(z,\gamma)\,F(\gamma z).
$$

## Lemma: slash-operator-chain-rule {#lemma:slash-operator-chain-rule lean="SlashAction.slash_mul" uses="lemma:automorphy-factor-chain-rule"}

The chain rule implies 
$$
F|_k\gamma_1\gamma_2=(F|_k\gamma_1)|_k\gamma_2.
$$

In particular, this lemma implies that if $\Gamma = \langle M_i \rangle_{i \in \mathcal{I}} \rangle$, then the slash action $F|\gamma$ is uniquely determined by the action of generators, i.e. $F|M_i$ and $F|M_i^{-1}$.

## Lemma: slash-negI-even-weight {#lemma:slash-negI-even-weight lean="modular_slash_negI_of_even" uses="def:slash-operator"}

For even $k$, $F|_{k}(-I) = F$.

### Proof

Follows from the definition of the slash operator:
$(F|_{k}(-I))(z) = (-1)^{-k}F((-I)z) = F(z)$.

## Definition: Mk {#def:Mk lean="ModularForm" uses="def:congruence-subgroup"}

Let  $\Gamma$ denote a subgroup of $\mathrm{SL}_2(\mathbb{Z})$, then a modular form  of level $\Gamma$ and weight $k \in \mathbb{Z}$ is a function $f : \mathbb{H} \to \mathbb{C}$ such that:
	
1. For all $\gamma \in \Gamma$ we have $f\mid_k \gamma = f$ (such functions are called slash invariant).
1. $f$ is holomorphic on $\mathbb{H}$.
1. For all $\gamma \in \mathrm{SL}_2(\mathbb{Z})$, there exist $A, B \in \mathbb{R}$ such that for all $z \in \mathbb{H}$, with $ A \le \mathrm{Im}(z)$, we have $|(f \mid_k \gamma) (z) |\le B$. Here $| - |$ denotes the standard complex absolute value.

    This defines a complex vector space which we denote by $M_{k}(\Gamma)$.

By replacing condition $(3)$ above with (4) below defines the subspace of cusp forms, which we denote by $S_k(\Gamma)$.

1. \setcounter{enumi}{3}
1. For all $\gamma \in \mathrm{SL}_2(\mathbb{Z})$, and all $0 < \epsilon$, there exists $A \in \mathbb{R}$ such that for all $z \in \mathbb{H}$, with $ A \le \mathrm{Im}(z)$, we have $|(f \mid_k \gamma) (z) |\le \epsilon$.

Let us consider several examples of modular forms.

## Definition: Ek {#def:Ek lean="ModularForm.eisensteinSeries_MF"}

For an even integer $k\geq 4$ we define the _weight $k$ Eisenstein series_ as

$$
\begin{equation*}
E_k(z):=\frac{1}{2}\sum_{(c,d)\in\mathbb{Z}^2, (c,d)=1}(cz+d)^{-k}.\end{equation*}
$$

## Lemma: Ek-is-modular-form {#lemma:Ek-is-modular-form lean="EisensteinSeries.eisensteinSeries_SIF" uses="def:Mk, def:Ek"}

For all $k$, $E_k\in M_k(\Gamma_1)$.
Especially, we have

$$
\begin{equation*}
    E_k \left(-\frac{1}{z}\right) = z^k E_k(z).
\end{equation*}
$$

### Proof

This follows from the fact that the sum converges absolutely.
Now apply slash operator with $\gamma = \left(\begin{smallmatrix} 0 & -1 \\ 1 & 0 \end{smallmatrix}\right)$ gives (eqn:Ek-trans-S).

Since modular forms are holomorphic and periodic they have a Fourier expansions. One thing that we
will need is the growth of the Fourier coefficients, which is given by the following lemma.

## Lemma: mod_form_poly_growth {#lemma:mod_form_poly_growth}

: Let $\Gamma$ be a finite index subgroup of $\mathrm{SL}_2(\mathbb{Z})$ and $f \in \mathcal{M}_k(\Gamma)$ be a modular form of weight $k$. Then the Fourier coefficients $a_n(f)$ has a polynomial growth, i.e. $|a_n(f)| = O(n^k)$.

### Proof

Note that the assumption on the polynomial growth holds when $f$ is a holomorphic modular form, where the proof can be found in [@Serre73, p. 94] for the case of level 1 modular forms. This has been done in Lean 4 by David Loeffler.

For Eisenstein series, we can see this directly from the following:

## Lemma: Ek-Fourier {#lemma:Ek-Fourier lean="E_k_q_expansion" uses="def:Ek"}

The Eisenstein series possesses the Fourier expansion

$$
\begin{equation*}E_k(z)=1+\frac{2}{\zeta(1-k)}\sum_{n=1}^\infty \sigma_{k-1}(n)\,e^{2\pi i z}, \end{equation*}
$$

where $\sigma_{k-1}(n)\,=\,\sum_{d|n} d^{k-1}$. In particular, we have

$$
\begin{align*}
  E_4(z)\,=\,& 1+240\sum_{n=1}^\infty \sigma_3(n)\,e^{2\pi i n z} \notag \\
  E_6(z)\,=\,& 1-504\sum_{n=1}^\infty \sigma_5(n)\,e^{2\pi i n z}. \notag
\end{align*}
$$

The infinite sum (eqn:Ek-definition) does not converge absolutely for $k=2$.
On the other hand, the expression (eqn:Ek-Fourier) converges to a holomorphic function on the upper half-plane and we will take it as a definition of $E_2$ (See Definition [E2](#def:E2) below).

The discriminant form is a unique normalized cusp form of weight 12, which can be defined as:

## Definition: disc-definition {#def:disc-definition lean="Δ" uses="def:dedekind_eta"}

The _discriminant form_ $\Delta(z)$ is given by

$$
\begin{equation*}
\Delta(z) = e^{2 \pi i z} \prod_{n \ge 1} (1 - e^{2 \pi i n z})^{24}.
\end{equation*}
$$

This product formula allows us to prove positivity of $\Delta(it)$ for $t > 0$ later. But we need to first check its a modular form. For this we first need some definitions/ results.

We define it as a $q$-series, which gives a holomorphic function on $\mathfrak{H}$.

## Definition: E2 {#def:E2 lean="E₂_eq"}

We set

$$
\begin{equation*}
    E_2(z):= 1-24\sum_{n=1}^\infty \sigma_1(n)\,e^{2\pi i n z}.
\end{equation*}
$$

## Lemma: E2-transform-S {#lemma:E2-transform-S lean="E₂_transform" uses="def:E2"}

This function is not modular, however it satisfies

$$
\begin{equation*}
    z^{-2}\,E_2\left(-\frac{1}{z}\right) = E_2(z) -\frac{6i}{\pi}\, \frac{1}{z}.
\end{equation*}
$$

### Proof

This is exercise 1.2.8 of [@first-course].

More generally, we have

## Lemma: E2-transform-general {#lemma:E2-transform-general lean="E₂_slash_transform" uses="lemma:E2-transform-S, def:E2"}

$$
\begin{equation*}
(cz + d)^{-2} E_2\left(\frac{az + b}{cx + d}\right) = E_2(z) - \frac{6ic}{\pi (cz + d)}, \quad \begin{pmatrix} a & b \\ c & d\end{pmatrix} \in \mathrm{SL}_{2}(\mathbb{Z}).
\end{equation*}
$$

### Proof

Use the fact that $\mathrm{SL}_2(\mathbb{Z})$ is generated by $S$ and $T$.
    Then (eqn:E2-transform-general) follows from (eqn:E2-S-transform) and $E_2|_T = E_2$.

## Definition: dedekind_eta {#def:dedekind_eta lean="ModularForm.eta"}

The Dedekind eta function is defined as

$$
\eta(z) = q^{1/24} \prod_{n \ge 1} (1 - q^n)
$$

where $q = e^{2\pi i z}$.

## Lemma: dedekind_eta_transformation {#lemma:dedekind_eta_transformation lean="ModularForm.eta_comp_eq_csqrt_I_inv" uses="def:dedekind_eta"}

The Dedekind eta function transforms as

$$
\eta\left(-\frac{1}{z}\right) = \sqrt{-iz} \eta(z).
$$

### Proof

Consider the logarithmic derivative of $\eta$, which one can easily see is equal to $\frac{\pi i}{12} E_2$.
    The result then follows from the transformation of $E_2$.

    See [@first-course, proposition 1.2.5].

## Lemma: disc-cuspform {#lemma:disc-cuspform lean="Delta" uses="def:disc-definition, lemma:dedekind_eta_transformation"}

$\Delta(z) \in M_{12}(\Gamma_1)$.
Especially, we have

$$
\begin{equation*}
    \Delta\left(-\frac{1}{z}\right) = z^{12} \Delta(z).
\end{equation*}
$$

Also, it vanishes at the unique cusp, i.e. it is a cusp form of level $\Gamma_1$ and weight $12$.

### Proof

The fact that it is invariant under translation is clear from the definition, so we only need to check transformation under $S$. Now, note that $\eta^{24} = \Delta$, and from [dedekind_eta_transformation](#lemma:dedekind_eta_transformation) we have $\eta(-1/z) = \sqrt{-iz} \eta(z)$, so $\Delta(-1/z) = z^{12} \Delta(z)$ as required.

## Lemma: disc-E4E6 {#lemma:disc-E4E6 lean="Delta_E4_eqn" uses="def:disc-definition"}

We have

$$
\begin{equation*}
\Delta(z) = (E_4^3-E_6^2)/1728.
\end{equation*}
$$

### Proof

We only need to show its a cuspform, since once we have this, dividing the rhs by $\Delta$ would give a modular form of weight $0$ which is a constant, and so we can determine the constant easily.

    To check its a cuspform, we just look at  the $q$-expansions of $E_4$ and $E_6$ and prove directly that the first term vanishes.

## Corollary: disc-pos {#cor:disc-pos lean="Delta_imag_axis_pos" uses="def:disc-definition"}

$\Delta(it) > 0$ for all $t > 0$.

### Proof

By [disc-definition](#def:disc-definition), we have

$$
\Delta(it) = e^{-2 \pi t} \prod_{n \ge 1} (1 - e^{-2 \pi n t})^{24} > 0.
$$

The following nonvanishing result, which directly follows from [disc-definition](#def:disc-definition), will be used in the construction of the magic function.

## Corollary: disc-nonvanishing {#cor:disc-nonvanishing lean="Δ_ne_zero" uses="def:disc-definition"}

$\Delta(z) \neq 0$ for all $z \in \mathfrak{H}$.

### Proof

This follows from the product formula.

A key fact in the theory of modular forms is that the spaces $M_k(\Gamma)$ are finite-dimensional.
To prove this we will do use the following non-standard proof. First we have the following result.

## Theorem: nonpos_wt {#thm:nonpos_wt lean="ModularFormClass.levelOne_neg_weight_eq_zero, ModularForm.levelOne_weight_zero_rank_one" uses="def:Mk"}

Let $k \in \mathbb{Z}$ with $k < 0$. Then $M_k(\Gamma_1) = \{0\}$ and moreover $\dim M_0(\Gamma(1)) = 1$.

### Proof

The proof makes use of the maximum modulus principle, as its already been formalised we skip the details here but see the lean proof for details.

## Theorem: lvl1_dims {#thm:lvl1_dims lean="ModularForm.dimension_level_one" uses="def:Mk, lemma:disc-E4E6, def:disc-definition"}

Let $k \in \mathbb{Z}$ with $k \ge 0$ and even. Then $\dim M_k(\Gamma_1) = \lfloor k / 12 \rfloor $ if $k \equiv 2 \mod 12$ and $\dim M_k(\Gamma_1) = \lfloor k / 12 \rfloor + 1$ if $k \not\equiv 2 \mod 12$.

### Proof

First we note that for $2 < k$ we have $\dim(M_k(\Gamma_1)) = 1 + \dim S_k(\Gamma_1)$. This follows since we know the $E_k$ are in $M_k$ so by scaling appropriately, any non-cuspform $f \in M_k$ we would have $f - a E_k \in S_k$ for some $a$.

Next, note that  $S_k(\Gamma_1)$ is isomorphic to $M_{k-12}(\Gamma_1)$, since if $f \in S_k$ then $f/ \Delta$ is now a modular form (using the product expansion of $\Delta$ and its non-vanishing on $\mathfrak{H}$) of weight $k-12$. Note its important that $f$ is a cuspform so that the quotient by $\Delta$ is a modular form.

So we only need to know the dimensions of $M_k(\Gamma_1)$ for $0 \le k \le 12$. For $k = 0$ we have $\dim M_0(\Gamma_1) = 1$ by [nonpos_wt](#thm:nonpos_wt).  For $k = 4$ we have $\dim M_4(\Gamma_1) = 1$ since if there was a cuspform $f$ of weight $4$ then $f/ \Delta$ would be a modular form of negative weight, i.e. zero, so $f=0$. Similarly for $k=6,8,10$. For $k=12$ we have $\dim S_{12}(\Gamma_1) = 1$ since the discriminant form is a cusp form of weight $12$ and any other cusp form of weight $12$ would be a scalar multiple of $\Delta$ (since their ratio would be a modular form of weight $0$). So we have $\dim M_{12}(\Gamma_1) = 2$.

Finally we need to check that $\dim M_2(\Gamma_1) = 0$. Firstly, there can't be any cuspforms here by the same argument as above. So we need to check that there are no modular forms of weight $2$. If we did have one, call it $f$ then $f^2$ would be a non-cuspform of weight $4$ and so $f^2 = a E_4$, where in fact $a=a_0(f)^2$ (since $(f^2-a_0(f)E_4)$ is now a cuspform of weight $4$ which means its zero). Similarly, $f^3 = a_0(f)^3 E_6$. But now taking powers to make them weight $12$ forms we see that $a_0(f)^6(E_4^3 - E_6^2) = 0 = 1728 a_0(f)^6 \Delta$
but $a_0(f) \ne 0$ (since its assumed to not be a cuspform), this would mean $\Delta =0$ which we know can't happen.

## Theorem: dim-mf-general-level {#thm:dim-mf-general-level lean="dim_gen_cong_levels" uses="def:Mk, thm:lvl1_dims"}

Let $\Gamma$ be a congruence subgroup. Then $M_k(\Gamma)$ is finite-dimensional.

### Proof

We know that $\dim(M_k(\Gamma_1))$ is finite dimensional from the above, now this means that there is some $r_k$ such that any element of $M_k(\Gamma_1)$ vanishing at infinity to degree $> r_k$ must be zero. Now take $f \in M_k(\Gamma)$ and vanishes to degree $n$ at infinity, then consider $F = \prod_\gamma f\mid_k \gamma$ where the product is over a set of representatives of $\Gamma_1 \backslash \Gamma$. Then $F$ is a modular form of weight $k d$ where $d = [\Gamma_1: \Gamma]$ and vanishes at infinity to degree at least $n$. So if $n > r_{kd}$ then $F=0$ meaning the $f=0$.

## Corollary: dim-mf {#cor:dim-mf uses="def:Mk, thm:lvl1_dims"}

We have

$$
\begin{align*}
    \dim M_2(\mathrm{SL}_{2}(\mathbb{Z})) &= 0,  \\
    \dim M_4(\mathrm{SL}_{2}(\mathbb{Z})) &= 1,  \\
    \dim M_6(\mathrm{SL}_{2}(\mathbb{Z})) &= 1,  \\
    \dim M_8(\mathrm{SL}_{2}(\mathbb{Z})) &= 1,  \\
    \dim S_4(\mathrm{SL}_{2}(\mathbb{Z})) &= 0,  \\
    \dim S_6(\mathrm{SL}_{2}(\mathbb{Z})) &= 0,  \\
    \dim S_8(\mathrm{SL}_{2}(\mathbb{Z})) &= 0. 
\end{align*}
$$

Another examples of modular forms we would like to consider are _theta functions_ [@1-2-3, Section 3.1].

## Definition: th00-th01-th10 {#def:th00-th01-th10 lean="Θ₂, Θ₃, Θ₄"}

We define three different theta functions (so called ``Thetanullwerte'') as

$$
\begin{align*}
  \Theta_{2}(z) = \theta_{10}(z)\,=\, & \sum_{n\in\mathbb{Z}}e^{\pi i (n+\frac12)^2 z}. \notag \\
  \Theta_{3}(z) = \theta_{00}(z)\,=\, & \sum_{n\in\mathbb{Z}}e^{\pi i n^2 z} \notag \\
  \Theta_{4}(z) = \theta_{01}(z)\,=\, & \sum_{n\in\mathbb{Z}}(-1)^n\,e^{\pi i n^2 z} \notag \\
\end{align*}
$$

For convenience, we use the following notations for the fourth powers of the theta functions.

## Definition: H2-H3-H4 {#def:H2-H3-H4 lean="H₂, H₃, H₄" uses="def:th00-th01-th10"}

Define

$$
\begin{equation*}
    H_2 = \Theta_2^4, \quad H_3 = \Theta_3^4, \quad H_4 = \Theta_4^4. 
\end{equation*}
$$

Note that we only need these fourth powers to define [b-definition](#def:b-definition).

The group $\Gamma_1$ is generated by the elements $T=\left(\begin{smallmatrix}1&1\\0&1\end{smallmatrix}\right)$, $S=\left(\begin{smallmatrix}0&1\\-1&0\end{smallmatrix}\right)$, and $-I = \left(\begin{smallmatrix}-1&0\\0&-1\end{smallmatrix}\right)$ ([Gamma-1-generators](#lemma:Gamma-1-generators)), and the transformation of functions under $\Gamma(2)$ is determined by that under $\Gamma_1$ (by [slash-operator-chain-rule](#lemma:slash-operator-chain-rule)).
The following lemma shows how the theta functions (and their powers) transform under the slash action of these matrices.

## Lemma: theta-transform-S-T {#lemma:theta-transform-S-T lean="H₂_T_action, H₃_T_action, H₄_T_action, H₂_S_action, H₃_S_action, H₄_S_action" uses="def:th00-th01-th10, def:H2-H3-H4"}

These elements act on the theta functions in the following way

$$
\begin{align*}
    H_2 | S &= -H_4  \\
    H_3 | S &= -H_3  \\
    H_4 | S &= -H_2 
\end{align*}
$$

and

$$
\begin{align*}
    H_2 | T &= -H_2  \\
    H_3 | T &= H_4  \\
    H_4 | T &= H_3 
\end{align*}
$$

### Proof

The last three identities easily follow from the definition.
For example, (eqn:H2-transform-T) follows from

$$
\begin{align*}
    \Theta_{2}(z + 1) &= \sum_{n\in\mathbb{Z}}e^{\pi i (n+\frac12)^2 (z + 1)}
    = \sum_{n \in \mathbb{Z}} e^{\pi i (n + \frac{1}{2})^{2}} e^{\pi i (n + \frac{1}{2})^{2} z} \\
    &= \sum_{n \in \mathbb{Z}} e^{\pi i (n^2 + n + \frac{1}{4})} e^{\pi i (n + \frac{1}{2})^{2} z} = \sum_{n \in \mathbb{Z}} (-1)^{n^2 + n}e^{\pi i / 4} e^{\pi i (n + \frac{1}{2})^{2} z} \\
    &= e^{\pi i / 4} \Theta_{2}(z)
\end{align*}
$$

and taking 4th power.
(eqn:H2-transform-S) and (eqn:H4-transform-S) are equivalent under $z \leftrightarrow -1/z$, so it is enough to show (eqn:H2-transform-S) and (eqn:H3-transform-S).
These identities follow from the identities of the _two-variable_ Jacobi theta function, which is defined as (be careful for the variables, where we use $\tau$ instead of $z$)

$$
\begin{equation*}
    \theta(z, \tau) = \sum_{n \in \mathbb{Z}} e^{2 \pi i n z + \pi i n^2 \tau} 
\end{equation*}
$$

and already formalized by David Loeffler.
This function specialize to the theta functions as

$$
\begin{align*}
    \Theta_{2}(\tau) &= e^{\pi i \tau / 4} \theta(-\tau / 2, \tau)  \\
    \Theta_{3}(\tau) &= \theta(0, \tau)  \\
    \Theta_{4}(\tau) &= \theta(1/2, \tau)  \\
\end{align*}
$$

Poisson summation formula gives

$$
\begin{equation*}
    \theta(z, \tau) = \frac{1}{\sqrt{-i \tau}} e^{-\frac{\pi i z^2}{\tau}} \theta\left(\frac{z}{\tau}, -\frac{1}{\tau}\right) 
\end{equation*}
$$

and applying the specializations above yield the identities.
For example, (eqn:H4-transform-S) follows from

$$
\begin{equation*}
    \Theta_{4}(\tau) = \theta\left(\frac{1}{2}, \tau\right) = \frac{1}{\sqrt{-i\tau}} e^{- \frac{\pi i }{4 \tau}} \theta\left(\frac{1}{2 \tau}, -\frac{1}{\tau}\right) = \frac{1}{\sqrt{-i\tau}} \Theta_{2}\left(-\frac{1}{\tau}\right)
\end{equation*}
$$

and taking 4th power.

Using the above identities, we can prove that these are modular forms.

## Lemma: theta-slash-invariant {#lemma:theta-slash-invariant lean="H₂_SIF, H₃_SIF, H₄_SIF" uses="lemma:slash-operator-chain-rule, lemma:slash-negI-even-weight, lemma:theta-transform-S-T, lemma:Gamma-2-generators"}

$H_{2}$, $H_{3}$, and $H_{4}$ are slash invariant under $\Gamma(2)$, i.e. for all $\gamma \in \Gamma(2)$ and $i \in \{2, 3, 4\}$, we have $H_i|\gamma = H_i|\gamma^{-1} = H_i$.

### Proof

By [Gamma-2-generators](#lemma:Gamma-2-generators) and [slash-operator-chain-rule](#lemma:slash-operator-chain-rule), it suffices to show that the $H_i$ are invariant under slash actions with respect to $\alpha$, $\beta$, and $-I$.
Invariance under $-I$ follows from Lemma [slash-negI-even-weight](#lemma:slash-negI-even-weight).
The rest follows from Lemma [slash-operator-chain-rule](#lemma:slash-operator-chain-rule), [theta-transform-S-T](#lemma:theta-transform-S-T), and the matrix identities

$$
\begin{equation*}
    \alpha = T^2, \quad \beta = -S\alpha^{-1}S = -ST^{-2}S. 
\end{equation*}
$$

For example, invariance for $H_2$ can be proved by

$$
\begin{align*}
    H_2|\alpha &= H_2 |T^{2} = -H_2 |T = H_2 \\
    H_2|\beta &= H_2 |(-S\alpha^{-1}S) = H_2 | (S\alpha^{-1}S) =-H_4 |(\alpha^{-1}S) = -H_4 |S  = H_2.
\end{align*}
$$

## Lemma: theta-bounded-im-infty {#lemma:theta-bounded-im-infty lean="isBoundedAtImInfty_H_slash" uses="lemma:theta-slash-invariant, lemma:Gamma-1-generators"}

For all $\gamma \in \Gamma_1$, $H_{2}|_2 \gamma$, $H_{3}|_2 \gamma$, and $H_{4}|_2 \gamma$ are holomorphic at $i\infty$.

### Proof

We want to show that for $\gamma \in \Gamma_1$, $\|H_2|_2\gamma(z)\|$ is bounded as $z \in \mathbb{H} \to i\infty$. Firstly, by [theta-transform-S-T](#lemma:theta-transform-S-T), [Gamma-2-generators](#lemma:Gamma-2-generators) and induction on group elements, we notice that $\{\pm H_2, \pm H_3, \pm H_4\}$ is closed under action by $\Gamma_1$. Hence, it suffices to prove that $H_2$, $H_3$ and $H_4$ are bounded at $i\infty$. Consider $z \in \mathbb{H}$ with $\Im(z) \geq A$. We proceed by direct algebraic manipulation:
    
$$
\begin{align*}
        \|H_2(z)\|
        &= \left\|\sum_{n \in \mathbb{Z}} \exp\left(\pi i \left(n + \frac{1}{2}\right)^2 z\right)\right\|^4
        \leq \left(\sum_{n \in \mathbb{Z}} \left\|\exp\left(\pi i \left(n + \frac{1}{2}\right)^2 z\right)\right)\right\|^4 \\
        &= \left(\sum_{n \in \mathbb{Z}} \left\|\exp\left(-\pi \left(n + \frac{1}{2}\right)^2 \Im(z)\right)\right)\right\|^4
        \leq \left(\sum_{n \in \mathbb{Z}} \left\|\exp\left(-\pi \left(n + \frac{1}{2}\right)^2 A\right)\right)\right\|^4
    \end{align*}
$$

    Where we prove the final term is convergent by noticing that it equals $\exp(-\pi A / 4)\theta(iA / 2, iA)$, which has been shown to converge in `Mathlib`. The proofs for $H_3$ and $H_4$ are similar (actually easier) and have been omitted.

    {\color{red}{**It seems the `MDifferentiable` requirement is missing.**}}

## Lemma: theta-modular {#lemma:theta-modular lean="H₂_MF, H₃_MF, H₄_MF" uses="lemma:theta-slash-invariant, lemma:theta-bounded-im-infty"}

$H_{2}$, $H_{3}$, and $H_{4}$ belong to $M_2(\Gamma(2))$.

### Proof

From [theta-slash-invariant](#lemma:theta-slash-invariant) and [theta-bounded-im-infty](#lemma:theta-bounded-im-infty), it remains ot prove that $H_2$, $H_3$ and $H_4$ are holomorphic on $\mathbb{H}$. {\color{red}{**fill in proof.**}}

They have Fourier expansions as follows.

## Proposition: H2-fourier {#prop:H2-fourier uses="def:H2-H3-H4"}

$H_2$ admits a Fourier series of the form

$$
\begin{equation*}
    H_2(z) = \sum_{n \ge 1} c_{H_2}(n) e^{\pi i n z}
\end{equation*}
$$

for some $c_{H_2}(n) \in \mathbb{R}_{\ge 0}$, with $c_{H_2}(1) = 16$ and $c_{H_2}(n) = O(n^k)$ for some $k \in \mathbb{N}$.

### Proof

We have

$$
\begin{align*}
    H_2(z) &= \Theta_2(z)^4 \\
    &= \left(\sum_{n \in \mathbb{Z}} e^{\pi i (n + \frac{1}{2})^{2} z}\right)^{4} \\
    &= \left(2\sum_{n \ge 0} e^{\pi i (n + \frac{1}{2})^{2} z}\right)^{4} \\
    &= \left(2 e^{\pi i z / 4} + 2 \sum_{n \ge 1} e^{\pi i (n^2 + n + \frac{1}{4}) z}\right)^{4} \\
    &= 16 e^{\pi i z}\left(1 + \sum_{n \ge 1} e^{\pi i (n^2 + n)z}\right)^{4} \\
    &= 16 e^{\pi i z} + \sum_{n \ge 2} c_{H_2}(n) e^{\pi i n z} \\
    &= \sum_{n \ge 1} c_{H_2}(n) e^{\pi i n z}.
\end{align*}
$$

## Proposition: H3-fourier {#prop:H3-fourier uses="def:H2-H3-H4"}

$H_3$ admits a Fourier series of the form

$$
\begin{equation*}
    H_3(z) = \sum_{n \ge 0} c_{H_3}(n) e^{\pi i n z}
\end{equation*}
$$

for some $c_{H_3}(n) \in \mathbb{R}_{\ge 0}$ with $c_{H_3}(0) = 1$ and $c_{H_3}(n) = O(n^k)$ for some $k \in \mathbb{N}$.
Especially, $H_3$ is not cuspidal.

### Proof

We have

$$
\begin{equation*}
    H_3(z) = \Theta_3(z)^{4} = \left(\sum_{n \in \mathbb{Z}} e^{\pi i n^2 z}\right)^{4} = \left(1 + 2 \sum_{n \ge 1} e^{\pi i n^2 z}\right)^{4} = 1 + O(e^{\pi i z}).
\end{equation*}
$$

## Proposition: H4-fourier {#prop:H4-fourier uses="def:H2-H3-H4"}

$H_4$ admits a Fourier series of the form

$$
\begin{equation*}
    H_4(z) = \sum_{n \ge 0} c_{H_4}(n) e^{\pi i n z}
\end{equation*}
$$

for some $c_{H_4}(n) \in \mathbb{R}$ with $c_{H_4}(0) = 1$ and $c_{H_4}(n) = O(n^k)$ for some $k \in \mathbb{N}$.
Especially, $H_4$ is not cuspidal.

We also have a nontrivial relation between these theta functions.

## Lemma: jacobi-identity {#lemma:jacobi-identity lean="jacobi_identity" uses="lemma:theta-modular, cor:dim-mf"}

These three theta functions satisfy the _Jacobi identity_

$$
\begin{equation*}
H_{2} + H_{4} = H_{3} \Leftrightarrow \Theta_{2}^4 + \Theta_{4}^4 = \Theta_{3}^4.
\end{equation*}
$$

### Proof

Let $f = (H_2 + H_4 - H_3)^{2}$.
    Obviously, $f$ is a modular form of weight $4$ and level $\Gamma(2)$.
    However, by using the transformation rules of $H_2, H_3, H_4$, one have
    
$$
\begin{align*}
        f|_{S} &= (-H_4 - H_2 + H_3)^{2} = f\\
        f|_{T} &= (-H_2 + H_3 - H_4)^{2} = f
    \end{align*}
$$

    so $f$ is actually a modular form of level $1$.
    By considering the limit as $z \to i\infty$, $f$ is a cusp form, so we get $f = 0$ from (eqn:dimS4).

These are also related to $E_4$, $E_6$, and $\Delta$ as follows.

## Lemma: lv1-lv2-identities {#lemma:lv1-lv2-identities uses="lemma:theta-transform-S-T, lemma:theta-modular, lemma:disc-cuspform"}

We have

$$
\begin{align*}
    E_4 &= \frac{1}{2}(H_{2}^{2} + H_{3}^{2} + H_{4}^{2}) = H_{2}^{2} + H_{2}H_{4} + H_{4}^{2}  \\
    E_6 &= \frac{1}{2} (H_{2} + H_{3})(H_{3} + H_{4}) (H_{4} - H_{2}) = \frac{1}{2}(H_2 + 2H_4)(2H_2 + H_4)(H_4 - H_2)  \\
    \Delta &= \frac{1}{256} (H_{2}H_{3}H_{4})^2. 
\end{align*}
$$

### Proof

We can prove these similarly as Lemma [jacobi-identity](#lemma:jacobi-identity).
Right hand sides of (eqn:e4theta), (eqn:e6theta), and (eqn:disctheta) are all modular forms of level $\Gamma_1$ and desired weights, where (eqn:disctheta) is a cusp form since $H_2$ is.
Now the identities follow from the dimension calculations $\dim M_4(\Gamma_1) = \dim M_6(\Gamma_1) = \dim S_{12}(\Gamma_1) = 1$ and comparing the first nonzero $q$-coefficients.

The _strict_ positivity of Jacobi theta functions might needed later.

## Corollary: theta-pos {#cor:theta-pos lean="H₂_imag_axis_pos, H₄_imag_axis_pos" uses="lemma:theta-transform-S-T"}

$H_2(it)$ and $H_4(it)$ are positive for $t > 0$.

### Proof

By the transformation law (eqn:H2-transform-S), it is enough to prove the positivity for $\Theta_2(it)$, which is clear from its definition:

$$
\begin{equation*}
    \Theta_{2}(it) = \sum_{n \in \mathbb{Z}} e^{- \pi (n + \frac{1}{2})^{2} t} > 0.
\end{equation*}
$$

**Quasimodular forms and derivatives**

Morally, quasimodular forms can be thought as _modular forms with differentiations_.
It can be defined formally as follows:
Let $f: \mathfrak{H} \to \mathbb{C}$ be a holomorphic function, and let $k$ and $s \ge 0$ be integers.
The function $f$ is a _quasimodular form of weight $k$, level $\Gamma$, and depth $s$_ if there exist holomorphic functions $f_0, \dots, f_s : \mathfrak{H} \to \mathbb{C}$ such that

$$
\begin{equation*}
    (f|_{k}\gamma)(z) = (cz + d)^{-k} f\left(\frac{az + b}{cz + d}\right) = \sum_{j=0}^{s} f_j(z) \left(\frac{c}{cz + d}\right)^j
\end{equation*}
$$

for all $z \in \mathfrak{H}$ and $\gamma = \left(\begin{smallmatrix} a&b\\c&d \end{smallmatrix}\right) \in \Gamma$.

By taking $\gamma = \left(\begin{smallmatrix} 1 & 0 \\ 0 & 1 \end{smallmatrix}\right)$, one can check that we should have $f_0 = f$. Thus, a quasimodular form of depth $0$ is just a modular form of same weight and level.
Also, it is easy to see that the space of quasimodular forms is closed under the normalized derivative.

In this project, we are _not_ going to formalize the above definition of quasimodular forms.
Instead, we only use $E_2$ (defined in [E2](#def:E2)) and define the normalized derivative operator $D$ ([derivative](#def:derivative)) and the Serre derivative $\partial_k$ ([serre-der](#def:serre-der)) as the main tools to work with quasimodular forms.

## Definition: derivative {#def:derivative lean="D"}

Let $F$ be a quasimodular form.
We define the (normalized) derivative of $F$ as

$$
\begin{equation*}
    F' = DF := \frac{1}{2\pi i} \frac{\mathrm{d}}{\mathrm{d} z} F.
\end{equation*}
$$

Normalizing the derivative by $1/(2 \pi i)$ as in (eqn:derivative) is standard in the theory of modular forms, since it makes the $q$-expansion coefficients nicer.

## Lemma: der-q-series {#lemma:der-q-series lean="D_qexp_tsum_pnat" uses="def:derivative"}

We have an equality of operators $D = q \frac{\mathrm{d}}{\mathrm{d} q}$.
In particular, the $q$-series of the derivative of a quasimodular form $F(z) = \sum_{n \ge n_0} a_n q^n$ is $F'(z) = \sum_{n \ge n_0} n a_n q^n$.

### Proof

Directly follows from the definition [derivative](#def:derivative), where $\frac{1}{2 \pi i}\frac{\mathrm{d}}{\mathrm{d} z}e^{2\pi i n z} = n e^{2\pi i n z}$.

The most important example of quasimodular form is the weight 2 Eisenstein series $E_2$ ([E2](#def:E2)).
Using it, we can define the _Serre derivative_ of a quasimodular form.

## Definition: serre-der {#def:serre-der lean="serre_D" uses="def:derivative, def:E2"}

For $k \in \mathbb{R}$, define the weight $k$ Serre derivative $\partial_{k}$ of a modular form $F$ as

$$
\begin{equation*}
    \partial_{k}F := F' - \frac{k}{12} E_2 F.
\end{equation*}
$$

## Theorem: serre-der-equiv-action {#thm:serre-der-equiv-action lean="serre_D_slash_equivariant" uses="def:serre-der, def:E2, lemma:E2-transform-general"}

Serre derivative $\partial_{k}$ is equivariant with the slash action of $\mathrm{SL}_{2}(\mathbb{Z})$ in the following sense:

$$
\begin{equation*}
    \partial_{k} (F|_{k}\gamma) = (\partial_{k} F)|_{k+2}\gamma, \quad \forall \gamma \in \mathrm{SL}_{2}(\mathbb{Z}).
\end{equation*}
$$

### Proof

Let $G = \partial_{k}F = F' - \frac{k}{12}E_2 F$.
From $F \in M_k(\Gamma)$, we have

$$
\begin{equation*}
    (F|_{k}\gamma)(z) := (cz + d)^{-k} F\left(\frac{az + b}{cz + d}\right), \quad \gamma = \begin{pmatrix}a & b \\ c & d\end{pmatrix} \in \Gamma.
\end{equation*}
$$

By taking the derivative of the above equation, we get

$$
\begin{align*}
    \frac{\mathrm{d}}{\mathrm{d} z}(F|_{k} \gamma)(z) &= -kc (cz + d)^{-k - 1} F\left(\frac{az + b}{cz + d}\right) + (cz + d)^{-k} (cz + d)^{-2} \frac{\mathrm{d} F}{\mathrm{d} z}\left(\frac{az + b}{cz + d}\right) \\
    &= -kc (cz + d)^{-k - 1} F\left(\frac{az + b}{cz + d}\right) + (cz + d)^{-k - 2} \frac{\mathrm{d} F}{\mathrm{d} z}\left(\frac{az + b}{cz + d}\right) \\
    &= -kc (cz + d)^{-k - 1} F\left(\frac{az + b}{cz + d}\right) + 2 \pi i (cz + d)^{-k - 2} F'\left(\frac{az + b}{cz + d}\right) \\
    \Leftrightarrow (F|_{k} \gamma)'(z) &= -\frac{kc}{2 \pi i} (cz + d)^{-k - 1} F\left(\frac{az + b}{cz + d}\right) + (cz + d)^{-k - 2} F'\left(\frac{az + b}{cz + d}\right).
\end{align*}
$$

Combined with (eqn:E2-transform-general), we get

$$
\begin{align*}
    ((\partial_k F)|_{k+2}\gamma)(z) &= (cz + d)^{-k-2} \left(F'\left(\frac{az + b}{cz + d}\right) - \frac{k}{12}E_2\left(\frac{az + b}{cz + d}\right)F\left(\frac{az + b}{cz + d}\right)\right) \\
    &= (cz + d)^{-k-2} F'\left(\frac{az + b}{cz + d}\right) - \frac{k}{12} \left(E_2(z) - \frac{6ic}{\pi(cz + d)}\right) \cdot (cz + d)^{-k} F\left(\frac{az + b}{cz + d}\right) \\
    &= (F|_{k}\gamma)'(z) - \frac{k}{12} E_2(z) (F|_{k}\gamma)(z) \\
    &= \partial_{k} (F|_{k}\gamma)(z).
\end{align*}
$$

As a direct consequence of Theorem [serre-der-equiv-action](#thm:serre-der-equiv-action), we can check that the Serre derivative preserves the modularity of a modular form.

## Theorem: serre-der-modularity {#thm:serre-der-modularity lean="serre_D_slash_invariant" uses="def:serre-der, def:Mk, thm:serre-der-equiv-action"}

Let $F$ be a modular form of weight $k$ and level $\Gamma$.
Then, $\partial_{k}F$ is a modular form of weight $k + 2$ of the same level.

### Proof

Immediate from Theorem [serre-der-equiv-action](#thm:serre-der-equiv-action) since $F|_k\gamma = F$ for all $\gamma \in \Gamma$.

> **remark.** More generally, the following theorem holds: if $F$ is a quasimodular form of weight $k$ and depth $s$, then $\partial_{k-s}F$ is a quasimodular form of weight $k + 2$ _and depth $\le s$_ of the same level. We will not prove this here.

## Theorem: ramanujan-formula {#thm:ramanujan-formula lean="ramanujan_E₂, ramanujan_E₄, ramanujan_E₆, ramanujan_E₂', ramanujan_E₄', ramanujan_E₆'" uses="thm:serre-der-modularity, def:serre-der, lemma:E2-transform-general, cor:dim-mf"}

We have

$$
\begin{align*}
    E_2' &= \frac{E_2^2 - E_4}{12}  \\
    E_4' &= \frac{E_2 E_4 - E_6}{3}  \\
    E_6' &= \frac{E_2 E_6 - E_4^2}{2} 
\end{align*}
$$

### Proof

In terms of Serre derivatives, these are equivalent to

$$
\begin{align*}
    \partial_{1}E_2 &= -\frac{1}{12} E_4  \\
    \partial_{4}E_4 &= -\frac{1}{3} E_6  \\
    \partial_{6}E_6 &= -\frac{1}{2} E_4^2 
\end{align*}
$$

By Theorem [serre-der-modularity](#thm:serre-der-modularity), all the Serre derivatives are, in fact, modular.
To be precise, the modularity of $\partial_{4} E_4$ and $\partial_6 E_6$ directly follows from Theorem [serre-der-modularity](#thm:serre-der-modularity), and that of $\partial_{1}E_2$ follows from (eqn:E2-transform-general).
Differentiating and squaring then gives us the following:

$$
\begin{align*}
    E_2'|_{4}\gamma &= E_2' - \frac{ic}{\pi(cz + d)} E_2 - \frac{3c^2}{\pi^2 (cz + d)^2}  \\
    E_2^2|_{4}\gamma &= E_2^2 - \frac{12ic}{\pi(cz + d)} E_2 - \frac{36c^2}{\pi^2 (cz + d)^2} 
\end{align*}
$$

Hence, (eqn:DE2)$-\frac{1}{12}$(eqn:E2sq-transform) is a modular form of weight 4.
By [dim-mf](#cor:dim-mf), they should be multiples of $E_4, E_6, E_4^2$, and the proportionality constants can be determined by observing the constant terms of $q$-expansions.

## Corollary: logder-disc-E2 {#cor:logder-disc-E2 uses="thm:ramanujan-formula, def:disc-definition"}

$$
\begin{equation*}
    \Delta' = E_2 \Delta.
\end{equation*}
$$

### Proof

By Ramanujan's formula (eqn:DE4) and (eqn:DE6),

$$
\begin{equation*}
\Delta' = \frac{3 E_4^2 E_4' - 2 E_6 E_6'}{1728} = \frac{1}{1728} \left(3 E_4^2 \cdot \frac{E_2 E_4 - E_6}{3} - 2 E_6 \cdot \frac{E_2 E_6 - E_4^2}{2}\right) = \frac{E_2(E_4^3 - E_6^2)}{1728} = E_2\Delta.
\end{equation*}
$$

Similar argument allow us to compute (Serre) derivatives of $H_2, H_3, H_4$.

## Proposition: theta-der {#prop:theta-der uses="def:serre-der, lemma:theta-transform-S-T, lemma:jacobi-identity"}

We have

$$
\begin{align*}
    H_2' &= \frac{1}{6} (H_{2}^{2} + 2 H_{2} H_{4} + E_2 H_2) \\
    H_3' &= \frac{1}{6} (H_{2}^{2} - H_{4}^{2} + E_2 H_3) \\
    H_4' &= -\frac{1}{6} (2H_{2} H_{4} + H_{4}^{2} - E_2 H_4) 
\end{align*}
$$

or equivalently,

$$
\begin{align*}
    \partial_{2} H_{2} &= \frac{1}{6} (H_{2}^{2} + 2 H_{2} H_{4})  \\
    \partial_{2} H_{3} &= \frac{1}{6} (H_{2}^{2} - H_{4}^{2})  \\
    \partial_{2} H_{4} &= -\frac{1}{6} (2H_{2} H_{4} + H_{4}^{2}) 
\end{align*}
$$

### Proof

Equivalences are obvious from the definition of the Serre derivative.
Define $f_{2}, f_{3}, f_{4}$ be the differences of the left and right hand sides of (eqn:H2-serre-der), (eqn:H3-serre-der), (eqn:H4-serre-der).

$$
\begin{align*}
    f_{2} &:= \partial_{2} H_{2} - \frac{1}{6} H_{2}(H_{2} + 2H_{4}) \\
    f_{3} &:= \partial_{2} H_{3} - \frac{1}{6} (H_{2}^2 - H_{4}^2) \\
    f_{4} &:= \partial_{2} H_{4} + \frac{1}{6} H_{4}(2H_{2} + H_{4}).
\end{align*}
$$

Then these are a priori modular forms of weight $4$ and level $\Gamma(2)$, and our goal is to prove that they are actually zeros.
By Jacobi's identity (eqn:jacobi-identity), we have $f_{2} + f_{4} = f_{3}$.
Also, the transformation rules of $H_2, H_3, H_4$ give

$$
\begin{align*}
    f_{2}|_{S} &= -f_{4} \\
    f_{2}|_{T} &= -f_{2} \\
    f_{4}|_{S} &= -f_{2} \\
    f_{4}|_{T} &= f_{3} = f_{2} + f_{4}.
\end{align*}
$$

Now, define

$$
\begin{align*}
    g &:= (2 H_2 + H_4) f_2 + (H_2 + 2 H_4) f_4 \\
    h &:= f_{2}^{2} + f_{2}f_{4} + f_{4}^{2}.
\end{align*}
$$

Then one can check that both $g$ and $h$ are invariant under the actions of $S$ and $T$, hence they are modular forms of level $1$.
Also, by analyzing the limit of $g$ and $h$ as $z \to i \infty$, one can see that $g$ and $h$ are cusp forms, hence $g = h = 0$ by (eqn:dimS6) and (eqn:dimS8).
This implies

$$
\begin{align*}
    3 E_4 f_2^{2} &= 3 (H_2^2 + H_2 H_4 + H_4^2) f_2^{2} = ((2 H_2 + H_4)^{2} - (2H_2 + H_4)(H_2 + 2H_4) + (H_2 + 2H_4)^{2}) f_2^{2}\\
    &= (2 H_2 + H_4)^{2} (f_2^2 + f_2 f_4 + f_4^2) = 0
\end{align*}
$$

and by considering $q$-series ($E_4$ has an invertible $q$-series), we get $f_2 = 0$.

## Theorem: serre-der-prod-rule {#thm:serre-der-prod-rule lean="serre_D_mul" uses="def:serre-der"}

The Serre derivative satisfies the following product rule: for any quasimodular forms $F$ and $G$,

$$
\begin{equation*}
    \partial_{w_1 + w_2} (FG) = (\partial_{w_1}F)G + F (\partial_{w_2}G).
\end{equation*}
$$

### Proof

It follows from the definition:
    
$$
\begin{align*}
        \partial_{w_1 + w_2} (FG) &= (FG)' - \frac{w_1 + w_2}{12} E_2 (FG) \\
        &= F'G + FG' - \frac{w_1 + w_2}{12} E_2(FG) \\
        &= \left(F' - \frac{w_1}{12}E_2 F\right)G + F \left(G' - \frac{w_2}{12}E_2 G\right) \\
        &= (\partial_{w_1}F)G + F(\partial_{w_2}G).
    \end{align*}
$$

We also have the following useful theorem for proving positivity of quasimodular forms on the imaginary axis, which is [@Lee, Proposition 3.5, Corollary 3.6].

## Theorem: anti-serre-der-pos {#thm:anti-serre-der-pos uses="def:serre-der, cor:logder-disc-E2"}

Let $F$ be a holomorphic quasimodular cusp form with real Fourier coefficients.
Assume that there exists $k$ such that $(\partial_{k}F)(it) > 0$ for all $t > 0$.
If the first Fourier coefficient of $F$ is positive, then $F(it) > 0$ for all $t > 0$.

### Proof

By (eqn:logder-disc-E2), we have

$$
\begin{align*}
    \frac{\mathrm{d}}{\mathrm{d} t} \left( \frac{F(it)}{\Delta(it)^{\frac{k}{12}}}\right)
    &= (-2 \pi) \frac{F'(it) \Delta(it)^{\frac{k}{12}} - F(it) \frac{k}{12} E_{2}(it) \Delta(it)^{\frac{k}{12}}}{\Delta(it)^{\frac{k}{6}}} \\
    &= (-2 \pi) \frac{(\partial_{k} F)(it)}{\Delta(it)^{\frac{k}{12}}}  < 0,
\end{align*}
$$

hence

$$
t \mapsto \frac{F(it)}{\Delta(it)^{\frac{k}{12}}}
$$

is monotone decreasing.
Because of the assumption on the positivity of the first nonzero Fourier coefficient of $F$, $F(it) > 0$ for sufficiently large $t$ since

$$
F = \sum_{n \geq n_{0}} a_{n} q^{n} \Rightarrow e^{2 \pi n_{0} t} F(it) = a_{n_{0}} + e^{-2 \pi t}\sum_{n\geq n_{0} + 1} a_{n} e^{-2 \pi (n - n_{0} - 1)t}
$$

and $\lim_{t \to \infty} e^{2 \pi n_{0}t} F(it) = a_{n_0} > 0$, hence the result follows.

\pagebreak

