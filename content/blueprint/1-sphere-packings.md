---
title: 'Sphere packings'
type: "blueprint-chapter"
tags:
  - "blueprint"
---

The Sphere Packing problem is a classic optimisation problem with widespread applications that go well beyond mathematics. The task is to determine the ``densest" possible arrangement of spheres in a given space. It remains unsolved in all but finitely many dimensions.

It was famously determined, in [@Via2017], that the optimal arrangement in $\mathbb{R}^8$ is given by the $E_8$ lattice. The result is strongly dependent on the Cohn-Elkies linear programming bound (Theorem 3.1 in [@ElkiesCohn]), which, if a $\mathbb{R}^d \to \mathbb{R}$ function satisfying certain conditions exists, bounds the optimal density of sphere packings in $\mathbb{R}^d$ in terms of it. The proof in [@Via2017] uses the theory of modular forms to construct a function that can be used to bound the density of all sphere packings in $\mathbb{R}^8$ above by the density of the $E_8$ lattice packing. This then allows us to conclude that no packing in $\mathbb{R}^8$ can be denser than the $E_8$ lattice packing.

**The Setup**

This subsection gives an overview for the setup of the problem, both informally and in Lean. Throughout this blueprint, $\mathbb{R}^d$ will denote the Euclidean vector space equipped with distance $\|\cdot\|$ and Lebesgue measure $\mathrm{Vol}(\cdot)$. For any $x\in\mathbb{R}^d$ and $r\in\mathbb{R}_{>0}$, we denote by $B_d(x,r)$ the open ball in $\mathbb{R}^d$ with center $x$ and radius $r$. While we will give a more formal definition of a sphere packing below (and in Lean), the underlying idea is that it is a union of balls of equal radius centred at points that are far enough from each other that the balls do not overlap.

Arguably the most important definition in this subsection is that of _packing density_, which measures which portion of $d$-dimensional Euclidean space is covered by a given sphere packing. Taking the supremum over all packings gives what we refer to as the _sphere packing constant_, which is the quantity we are interested in optimising.

## Definition: SpherePacking.balls {#SpherePacking.balls lean="SpherePacking.balls"}

Given a set $X \subset \mathbb{R}^d$ and a real number $r > 0$ (known as the _separation radius_) such that $\|x - y\| \geq r$ for all distinct $x, y \in X$, we define the _sphere packing_ $\mathcal{P}(X)$ with centres at $X$ to be the union of all open balls of radius $r$ centred at points in $X$:
  
$$
\mathcal{P}(X) := \bigcup_{x \in X} B_d(x, r)
$$

## Definition: SpherePacking {#SpherePacking lean="SpherePacking"}

_Stated as a remark in the original blueprint._

Note that a sphere packing is uniquely defined from a given set of centres (which, in order to be a valid set of centres, must admit a corresponding separation radius). Therefore, as a conscious choice during the formalisation process, we will define everything that depends on sphere packings in terms of `SpherePacking`, a `structure` that bundles all the identifying information of a packing, but not the actual balls themselves. For the purposes of this blueprint, however, we will refrain from making this distinction.

We now define a notion of density for bounded regions of space by considering the density inside balls of finite radius.

## Definition: SpherePacking.finiteDensity {#SpherePacking.finiteDensity lean="SpherePacking.finiteDensity" uses="SpherePacking, SpherePacking.balls"}

The _finite density_ of a packing $\mathcal{P}$ is defined as
  
$$
\Delta_{\mathcal{P}}(R):=\frac{\mathrm{Vol}(\mathcal{P}\cap B_d(0,R))}{\mathrm{Vol}(B_d(0,R))},\quad R>0.
$$

As intuitive as it seems to take the density of a packing to be the limit of the finite densities as the radius of the ball goes to infinity, it is not immediately clear that this limit exists. Therefore, we define the density of a sphere packing as a limit superior instead.

## Definition: SpherePacking.density {#SpherePacking.density lean="SpherePacking.density" uses="SpherePacking, SpherePacking.finiteDensity"}

We define the _density_ of a packing $\mathcal{P}$ as the limit superior
  
$$
\Delta_{\mathcal{P}}:=\limsup\limits_{R\to\infty}\Delta_{\mathcal{P}}(R).
$$

We may now define the sphere packing constant, the quantity that the sphere packing problem requires us to compute.

## Definition: SpherePackingConstant {#SpherePackingConstant lean="SpherePackingConstant" uses="SpherePacking.balls, SpherePacking.density"}

The _sphere packing constant_ is defined as supremum of packing densities over all possible packings:
  
$$
\Delta_d:=\sup\limits_{\substack{\mathcal{P}\subset\mathbb{R}^d\\ \scriptscriptstyle\mathrm{sphere}\;\mathrm{packing}}}\Delta_{\mathcal{P}}.
$$

**Scaling Sphere Packings**

Given that the problem involves the _arrangement_ of balls in space, it is intuitive not to worry about the radius of the balls (so long as they are all equal to each other). However, [SpherePacking.balls](#SpherePacking.balls) involves a choice of separation radius. In principle, we would want two sphere packing configurations that differ only in separation radii to `encode the same information'. In this brief subsection, we will describe how to change the separation radius of a sphere packing by _scaling_ the packing by a positive real number and prove that this does not affect its density. This will give us the freedom to choose any separation radius we like when attempting to define the optimal sphere packing in $\mathbb{R}^d$.

## Definition: SpherePacking.scale {#SpherePacking.scale lean="SpherePacking.scale" uses="SpherePacking"}

Given a sphere packing $\mathcal{P}(X)$ with separation radius $r$, we defined the _scaled packing_ with respect to a real number $c > 0$ to be the packing $\mathcal{P}(cX)$, where $cX = \left\{ cx \in V \; \middle| \; x \in X \right\}$ has separation radius $cr$.

## Lemma: SpherePacking.scale_finiteDensity {#SpherePacking.scale_finiteDensity lean="SpherePacking.scale_finiteDensity" uses="SpherePacking.finiteDensity, SpherePacking.scale"}

Let $\mathcal{P}(X)$ be a sphere packing and $c$ a positive real number. Then, for all $R > 0$,
  
$$
\Delta_{\mathcal{P}(cX)}(cR) = \Delta_{\mathcal{P}(X)}(R).
$$

### Proof

The proof follows by direct computation:
  
$$
\Delta_{\mathcal{P}(cX)}(cR) = \frac{\operatorname{Vol}\!\left(\mathcal{P}(cX) \cap B_d(0, cR)\right)}{\operatorname{Vol}\!\left(B_d(0, cR)\right)} = \frac{c^d \cdot \operatorname{Vol}\!\left(\mathcal{P}(X) \cap B_d(0, R)\right)}{c^d \cdot \operatorname{Vol}\!\left(B_d(0, R)\right)}
    
    = \Delta_{\mathcal{P}(X)}(R)
$$

  where the second equality follows from applying the fact that scaling a (measurable) set by a factor of $c$ scales its volume by a factor of $c^d$ to the fact that $\mathcal{P}(cX) \cap B_d(0, cR) = c \cdot (\mathcal{P}(X) \cap B_d(0, cR))$.

## Lemma: SpherePacking.scale_density {#SpherePacking.scale_density lean="SpherePacking.scale_density" uses="SpherePacking.scale"}

Let $\mathcal{P}(X)$ be a sphere packing and $c$ a positive real number. Then, the density of the scaled packing $\mathcal{P}(cX)$ is equal to the density of the original packing $\mathcal{P}(X)$.

### Proof {uses="SpherePacking.scale_finiteDensity"}

One can show, using relatively unsophisticated real analysis, that
  
$$
\limsup_{R \to \infty} \Delta_{\mathcal{P}(cX)}(R) = \limsup_{cR \to \infty} \Delta_{\mathcal{P}(cX)}(cR)
$$

  [SpherePacking.scale_finiteDensity](#SpherePacking.scale_finiteDensity) tells us that $\Delta_{\mathcal{P}(cX)}(cR) = \Delta_{\mathcal{P}(X)}(R)$ for every $R > 0$. Therefore,
  
$$
\limsup_{cR \to \infty} \Delta_{\mathcal{P}(cX)}(cR) = \limsup_{cR \to \infty} \Delta_{\mathcal{P}(X)}(R) = \limsup_{R \to \infty} \Delta_{\mathcal{P}(X)}(R)
$$

  where the second equality is the result of a similar change of variables to the one done above.

Therefore, as expected, we do not need to worry about the separation radius when constructing sphere packings. This will be useful when we attempt to construct the optimal sphere packing in $\mathbb{R}^8$---and even more so when attempting to _formalise_ this construction---because the underlying structure of the packing is given by a set known as the $E_8$ lattice, which has separation radius $\sqrt{2}$.

We can also use [SpherePacking.scale_density](#SpherePacking.scale_density) to simplify the computation of the sphere packing constant by taking the supremum not over _all_ sphere packings but only over those with density $1$.

## Lemma: SpherePacking.constant_eq_constant_normalized {#SpherePacking.constant_eq_constant_normalized lean="SpherePacking.constant_eq_constant_normalized" uses="SpherePackingConstant, SpherePacking.density"}

$$
\Delta_d = \sup\limits_{\substack{\mathcal{P} \subset \mathbb{R}^d \\ \text{sphere packing} \\ \text{sep. rad.} = 1}} \Delta_{\mathcal{P}}
$$

### Proof {uses="SpherePacking.scale_density"}

That the supremum over packings of unit density is at most the sphere packing constant is obvious. For the reverse inequality, let $\mathcal{P}(X)$ be any sphere packing with separation radius $r$. We know, from [SpherePacking.scale_density](#SpherePacking.scale_density), that the density of $\mathcal{P}(X)$ is equal to that of the scaled packing $\mathcal{P}\!\left(\frac{X}{r}\right)$. Since the scaled packing has separation radius $1$, its density is naturally at most the supremum over all packings of unit density, meaning that the same is true of $\mathcal{P}(X)$.

**Lattices and Periodic packings**

We begin by defining what a lattice is in Euclidean space.

## Definition: IsZLattice {#IsZLattice lean="IsZLattice"}

We say that an additive subgroup $\Lambda \leq \mathbb{R}^d$ is a _lattice_ if it is discrete and its $\mathbb{R}$-span contains all the elements of $\mathbb{R}^d$.

There is also a corresponding dual notion, which will become relevant when we start doing Fourier analysis on functions over lattices.

## Definition: dual-lattice {#def:dual-lattice lean="LinearMap.BilinForm.dualSubmodule"}

The _dual lattice_ of a lattice $\Lambda$ is the set
  
$$
\Lambda^* := \left\{ v \in \mathbb{R}^d \; \middle| \; \forall l \in \Lambda, \left\langle v,l \right\rangle \in \mathbb{Z} \right\}
$$

We can now define periodic sphere packings.

## Definition: PeriodicSpherePacking {#PeriodicSpherePacking lean="PeriodicSpherePacking" uses="SpherePacking, IsZLattice"}

We say that a sphere packing $\mathcal{P}(X)$ is ($\Lambda$-)_periodic_ if there exists a lattice $\Lambda \subset \mathbb{R}^d$ such that for all $x \in X$ and $y \in \Lambda$, $x + y \in X$ (ie, $X$ is $\Lambda$-periodic).

There is a natural definition of density for periodic sphere packings, namely the ``local'' density of balls in a fundamental domain. However, _a priori_ the density of sphere packing above need not to coincide with this alternative definition. In [psp-density](#theorem:psp-density), we will prove that this is the case.

Now that we have simplified the process of computing the packing densities of specific packings, we can simplify that of computing the sphere packing constant. It turns out that once again, periodicity is key.

## Definition: Periodic-sphere-packing-constant {#def:Periodic-sphere-packing-constant lean="PeriodicSpherePackingConstant" uses="SpherePacking.density, PeriodicSpherePacking"}

The periodic sphere packing constant is defined to be
    
$$
\Delta_{d}^{\text{periodic}} := \sup_{\substack{P \subset \mathbb{R}^d \\ \text{periodic packing}}} \Delta_P
$$

## Theorem: periodic-packing-optimal {#thm:periodic-packing-optimal lean="periodic_constant_eq_constant" uses="SpherePacking.density, def:Periodic-sphere-packing-constant"}

For all $d$, the periodic sphere packing constant in $\mathbb{R}^d$ is equal to the sphere packing constant in $\mathbb{R}^d$.

### Proof

{\color{red}{**State this in Lean (ready).**}}
  {\color{red}{**Fill in proof here (see [@ElkiesCohn---, Appendix A]}}

Thus, one can show a sphere packing to be optimal by showing its density to be equal to the _periodic_ sphere packing constant instead of the regular sphere packing constant. The determination of the periodic constant is easier than that of the general constant, as we shall see when investigating the Linear Programming bounds derived by Cohn and Elkies in [@ElkiesCohn].

**Main Result**

With the terminologies above, we can state the main theorem of this project.

## Theorem: CE_Main {#theorem:CE_Main uses="E8-Lattice, SpherePackingConstant, SpherePacking.density, E8Packing-density, thm:g, thm:Cohn-Elkies-general"}

All _periodic_ packing $\mathcal{P} \subseteq \mathbb{R}^8$ has density satisfying $\Delta_{\mathcal{P}} \leq \Delta_{E_8} = \frac{\pi^4}{384}$, the density of the $E_8$ sphere packing (see [E8Packing](#E8Packing)).

### Proof

Directly follows from [Cohn--Elkies {[@ElkiesCohn]}](#thm:Cohn-Elkies-general) applied to the function $f(x)=g(x/\sqrt{2})$ of [g](#thm:g).

## Corollary: upper-bound-E8 {#corollary:upper-bound-E8 uses="thm:periodic-packing-optimal, theorem:CE_Main"}

All packing $\mathcal{P} \subseteq \mathbb{R}^8$ has density satisfying $\Delta_{\mathcal{P}} \leq \Delta_{E_8}$.

### Proof

This is a direct consequence of Theorem [periodic-packing-optimal](#thm:periodic-packing-optimal) and [CE_Main](#theorem:CE_Main).

## Corollary: MainTheorem {#MainTheorem lean="SpherePacking.MainTheorem" uses="corollary:upper-bound-E8"}

$\Delta_8 = \Delta_{E_8}$.

### Proof

By definition, $\Delta_{E_8} \leq \Delta_8$, while [upper-bound-E8](#corollary:upper-bound-E8) shows $\Delta_8 = \sup_{\mathrm{packing} \, \mathcal{P}} \leq \Delta_{E_8}$, and the result follows.

\pagebreak

