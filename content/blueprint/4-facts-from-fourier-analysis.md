---
title: 'Facts from Fourier analysis'
type: "blueprint-chapter"
tags:
  - "blueprint"
---

Recall the definition of a Fourier transform.

## Definition: Fourier-Transform {#def:Fourier-Transform lean="FourierTransform.fourier"}

The Fourier transform of an $L^1$-function $f:\mathbb{R}^d\to\mathbb{C}$ is defined as

  
$$
\mathcal{F}(f)(y) = \widehat{f}(y) := \int_{\mathbb{R}^d} f(x)e^{-2\pi i \langle x, y \rangle} \,\mathrm{d}x, \quad y \in \mathbb{R}^d
$$

  where $\langle x, y \rangle = \frac12\|x\|^2 + \frac12\|y\|^2 - \frac12\|x - y\|^2$ is the standard scalar product in $\mathbb{R}^d$.

The following computational result will be of use later on.

## Lemma: Gaussian-Fourier {#lemma:Gaussian-Fourier uses="def:Fourier-Transform"}

$$
\begin{equation*}
    \mathcal{F}(e^{\pi i \|x\|^2 z})(y) = z^{-4}\,e^{\pi i \|y\|^2 \,(\frac{-1}{z}) }.
  \end{equation*}
$$

### Proof

{\color{red}{**Fill in proof.**}}

Of great interest to us will be a specific family of functions, known as Schwartz Functions. The Fourier transform behaves particularly well when acting on Schwartz functions. We elaborate in the following subsections.

**On Schwartz Functions**

## Definition: Schwartz-Space {#def:Schwartz-Space lean="SchwartzMap"}

A $C^\infty$ function $f:\mathbb{R}^d\to\mathbb{C}$ is called a _Schwartz function_ if it decays to zero as $\|x\|\to\infty$ faster then any inverse power of $\|x\|$, and the same holds for all partial derivatives of $f$, ie, if for all $k, n \in \mathbb{N}$, there exists a constant $C \in \mathbb{R}$ such that for all $x \in \mathbb{R}^d$, $\left\lVert x \right\rVert^k \cdot \left\lVert f^{(n)}(x) \right\rVert \leq C$, where $f^{(n)}$ denotes the $n$-th derivative of $f$ considered along with the appropriate operator norm. The set of all Schwartz functions from $\mathbb{R}^d$ to $\mathbb{C}$ is called the _Schwartz space_. It is an $\mathbb{R}$-vector space.

## Lemma: Fourier-transform-is-automorphism {#lemma:Fourier-transform-is-automorphism lean="SchwartzMap.fourierTransformCLM" uses="def:Fourier-Transform, def:Schwartz-Space"}

The Fourier transform is a continuous, linear automorphism of the space of Schwartz functions.

### Proof

We do not elaborate here as the result already exists in Mathlib. We do, however, mention that the Lean implementation _defines_ a continuous linear equivalence on the Schwartz space _using_ the Fourier transform (see `SchwartzMap.fourierTransformCLM`). The `proof' that for any Schwartz function $f$, its Fourier transform and its image under this continuous linear equivalence are, indeed, the same $\mathbb{R}^d \to \mathbb{R}$ function, is stated in Mathlib solely for the purpose of `rw` and `simp` tactics, and is proven simply by `rfl`.

Another reason we are interested in Schwartz Functions is that they behave well under infinite sums. This will be useful to us when proving the Cohn-Elkies linear programming bound.

**On the Summability of Schwartz Functions**

We begin by stating a general summability result over specific subsets of $\mathbb{R}^d$.

## Lemma: inv-power-summable {#lemma:inv-power-summable}

Let $X \subset \mathbb{R}^d$ be a set of sphere packing centres of separation $1$ that is periodic with some lattice $\Lambda \subset \mathbb{R}^d$. Then, there exists $k \in \mathbb{N}$ sufficiently large such that
  
$$
\sum_{x \in X} \frac{1}{\left\lVert x \right\rVert^{k}} < \infty.
$$

### Proof

First, note that it does not matter how we number the (countably many) elements of the discrete set $X$: if we prove absolute convergence for one numbering, we prove absolute convergence for _any_ numbering. The idea will be to bound the sequence of partial sums by considering the volumes of concentric $d$-spheres of the appropriate radii (or scaled versions of a $0$-centred fundamental domain).

  {\color{red}{**Finish!**}}

The decaying property of Schwartz functions means that they can be compared to the absolutely convergent power series above.

## Lemma: Schwartz-summable {#lemma:Schwartz-summable uses="def:Schwartz-Space"}

Let $f : \mathbb{R}^d \to \mathbb{C}$ be a Schwartz function and let $X \subset \mathbb{R}^d$ be periodic with respect to some lattice $\Lambda \subset \mathbb{R}^d$. Then,
  
$$
\sum_{x \in X} |f(x)| < \infty.
$$

### Proof

Without loss of generality, assume that $0 \notin X$: if $0 \in X$, then we can add the $f(0)$ term to the sum over nonzero elements of $X$, which, if the sum over the nonzero elements converges absolutely, will be equal to the sum over all of $X$. Now, we know that for all $k \in \mathbb{N}$, there exists some constant $C$ such that $|f(x)| \leq C\left\lVert x \right\rVert^{-k}$ for all $x \in \mathbb{R}^d$. Choosing $k$ to be sufficiently large, we see that
  
$$
\sum_{x \in X} |f(x)| \leq \sum_{x \in X} \frac{C}{\left\lVert x \right\rVert^{k}} = C \sum_{x \in X} \frac{1}{\left\lVert x \right\rVert^k} < \infty.
$$

We end with a crucial result on Schwartz functions, the statement of which only makes sense because of the above result.

## Theorem: Poisson summation formula {#thm:Poisson-summation-formula lean="SchwartzMap.PoissonSummation_Lattices" uses="def:Fourier-Transform, def:Schwartz-Space, lemma:Schwartz-summable, lemma:inv-power-summable, def:dual-lattice"}

Let $\Lambda$ be a lattice in $\mathbb{R}^d$, and let $f:\mathbb{R}^d\to\mathbb{R}$ be a Schwartz function. Then, for all $v \in \mathbb{R}^d$,
  
$$
\sum_{\ell\in\Lambda}f(\ell + v) = \frac{1}{\operatorname{Vol}\!\left(\mathbb{R}^d/\Lambda\right)} \sum_{m\in\Lambda^*}\widehat{f}(m) e^{-2\pi i \left\langle v, m \right\rangle}.
$$

### Proof

One possible proof would be by induction on $d$. However, there are numerous nuances involved, particularly in manipulating nested infinite sums. Ideas would be appreciated.

While the Poisson Summation Formula over lattices can be stated in greater generality (and probably should be formalised as such in Mathlib due to the many applications it admits), we stick with Schwartz functions because that should be sufficient for our purposes.

Later, we will use Theorem [Poisson summation formula](#thm:Poisson-summation-formula) to prove that the certain functions $a(x)$ and $b(x)$ that will be defined later are eigenfunctions of the Fourier transform.
To apply the theorem, we need to show that these functions are Schwartz functions. We will do so by verifying the following sufficient condition.

## Theorem: smooth-fast-decay-schwartz {#thm:smooth-fast-decay-schwartz}

Assume $f : \mathbb{R} \to \mathbb{C}$ is smooth on $[0, \infty)$ and for all $k, n \in \mathbb{N}$, there exists $C \in \mathbb{R}$ such that
    
$$
x^{\frac{k}{2}} \cdot |f^{(n)}(x)| \leq C.
$$

    Then, for all $d \in \mathbb{N}$, the function
    
$$
f_d : \mathbb{R}^d \to \mathbb{C}, \quad f_d(x) := f(\|x\|^2)
$$

    is a Schwartz function.

\pagebreak

