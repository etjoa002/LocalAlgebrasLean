# The sealed statements

Generated from `verify/Challenge.lean` by `verify/make_core_page.py`: the 21 statements that `lake comparator` checks (see the section "Verification" of the front page). Each entry gives the statement in words and the name of its formal version in `Challenge.lean`.

## Setting

There are sites $`\Lambda`$, a finite alphabet $`\sigma_u`$ at every site $`u`$, and a reference configuration $`s_0`$ choosing a letter at every site (so every alphabet is nonempty). For a finite set of sites $`X`$, a matrix on the letters of $`X`$ is a complex matrix indexed by the assignments $`\xi`$ of a letter $`\xi_x \in \sigma_x`$ to each $`x \in X`$, that is, an operator on $`\bigotimes_{x \in X} \mathbb C^{\sigma_x}`$. Bounded operators carry the operator norm, and C$`^*`$-algebras are complex.

**1.** The finitely supported configurations are the configurations $`s`$ that differ from the reference configuration $`s_0`$ at finitely many sites.  
<sub>`Sealed.finConfig_def`</sub>

**2.** The Hilbert space $`H`$ is $`\ell^2(F)`$, the square-summable complex functions on the set $`F`$ of finitely supported configurations.  
<sub>`Sealed.configSpace_def`</sub>

## The local embeddings

For a finite set of sites $`X`$, the local embedding $`\iota_X`$ is a unital $`*`$-homomorphism from the matrices on the letters of $`X`$; this is part of the type of $`\iota_X`$ in the Lean statements. Statement 3 determines $`\iota_X`$ by its matrix elements.

**3.** For a finite set of sites $`X`$, a matrix $`m`$ on the letters of $`X`$ and finitely supported configurations $`s, t`$, the matrix element $`\langle e_s, \iota_X(m) e_t\rangle`$ in the standard basis of $`\ell^2(F)`$ is $`m(s|_X, t|_X)`$ if $`s`$ and $`t`$ agree at every site outside $`X`$, and $`0`$ otherwise.  
<sub>`Sealed.inner_localEmbed`</sub>

**4.** For a finite set of sites $`X`$, the local embedding $`\iota_X`$ is injective and $`\|\iota_X(m)\| = \|m\|`$ for every matrix $`m`$ on the letters of $`X`$, the norm of $`m`$ being its operator norm on $`\ell^2`$.  
<sub>`Sealed.localEmbed_injective_and_norm`</sub>

**5.** Compatibility: for finite sets of sites $`X \subseteq Y`$ and a matrix $`m`$ on the letters of $`X`$, $`\iota_Y(m \otimes 1) = \iota_X(m)`$, where $`(m \otimes 1)(\zeta, \zeta') = m(\zeta|_X, \zeta'|_X)`$ if the letters $`\zeta, \zeta'`$ on $`Y`$ agree outside $`X`$, and $`0`$ otherwise.  
<sub>`Sealed.localEmbed_extend`</sub>

**6.** Local commutativity: for disjoint finite sets of sites $`X`$ and $`Y`$, $`\iota_X(a)`$ and $`\iota_Y(b)`$ commute for all matrices $`a`$ on the letters of $`X`$ and $`b`$ on the letters of $`Y`$.  
<sub>`Sealed.commute_localEmbed_of_disjoint`</sub>

## The net of local algebras

Every set of sites $`O`$ has a $`*`$-subalgebra $`\mathcal A(O)`$ of the bounded operators on $`H`$, closed in norm (statement 7), and the quasi-local algebra is $`\mathcal A_{ql} = \mathcal A(\Lambda)`$.

**7.** For every set of sites $`O`$, the algebra $`\mathcal A(O)`$ is the norm closure, in the bounded operators on $`H`$, of the set of operators $`\iota_X(m)`$ with $`X \subseteq O`$ a finite set of sites and $`m`$ a matrix on the letters of $`X`$.  
<sub>`Sealed.quasiLocalNet_eq_closure`</sub>

**8.** The quasi-local algebra $`\mathcal A_{ql}`$ is the algebra $`\mathcal A(\Lambda)`$ of the set of all sites.  
<sub>`Sealed.quasiLocalAlgebra_def`</sub>

**9.** Local commutativity: for disjoint sets of sites $`O_1`$ and $`O_2`$, every element of $`\mathcal A(O_1)`$ commutes with every element of $`\mathcal A(O_2)`$.  
<sub>`Sealed.commute_of_mem_quasiLocalNet`</sub>

**10.** Isotony: for sets of sites $`O_1 \subseteq O_2`$, $`\mathcal A(O_1) \subseteq \mathcal A(O_2)`$.  
<sub>`Sealed.quasiLocalNet_mono`</sub>

## Symmetries and the reference configuration

**11.** Covariance: let a group $`\Gamma`$ act on the sites, with one finite alphabet $`Q`$ at every site and a reference configuration $`s_0`$ with $`s_0(gu) = s_0(u)`$. For each $`g \in \Gamma`$ there is a unitary $`U`$ on $`H`$ with $`U \iota_X(m) U^* = \iota_{gX}(g_* m)`$ for every finite set of sites $`X`$, where $`gX = \{y : g^{-1} y \in X\}`$ and $`(g_* m)(\zeta, \zeta') = m(\zeta \circ g, \zeta' \circ g)`$, and with $`U \mathcal A(O) U^* = \mathcal A(gO)`$ for every set of sites $`O`$. The unitary is asserted for each $`g`$ separately; the statement does not say that $`g \mapsto U`$ is a representation.  
<sub>`Sealed.exists_unitary_covariance`</sub>

**12.** Independence of the reference configuration: for any two reference configurations $`s_0`$ and $`s_0'`$ (which may differ at infinitely many sites) there is a $`*`$-isomorphism $`\varphi : \mathcal A_{ql} \to \mathcal A_{ql}'`$ of the quasi-local algebras with $`a \in \mathcal A(O) \iff \varphi(a) \in \mathcal A'(O)`$ for every set of sites $`O`$ and every $`a \in \mathcal A_{ql}`$, and with $`\varphi(\iota_X(m)) = \iota'_X(m)`$ for every finite set of sites $`X`$ and matrix $`m`$ on its letters.  
<sub>`Sealed.exists_starAlgEquiv_of_ref`</sub>

## The universal property

**13.** Universal property: let $`D`$ be a C$`^*`$-algebra and $`(\beta_X)`$ a family, indexed by the finite sets of sites $`X`$, of unital $`*`$-homomorphisms from the matrices on the letters of $`X`$ to $`D`$, compatible in the sense $`\beta_Y(m \otimes 1) = \beta_X(m)`$ for $`X \subseteq Y`$ (with $`m \otimes 1`$ as in the compatibility of the local embeddings). Then there is exactly one unital $`*`$-homomorphism $`\Phi : \mathcal A_{ql} \to D`$ with $`\Phi(\iota_X(m)) = \beta_X(m)`$ for all $`X`$ and $`m`$.  
<sub>`Sealed.exists_unique_lift`</sub>

**14.** Let $`D`$ be a C$`^*`$-algebra other than the zero algebra and $`(\beta_X)`$ a compatible family as in the universal property. Then the $`*`$-homomorphism $`\Phi : \mathcal A_{ql} \to D`$ with $`\Phi(\iota_X(m)) = \beta_X(m)`$ for all $`X`$ and $`m`$ is an isometry.  
<sub>`Sealed.isometry_lift`</sub>

## Finite volume

**15.** If the set of sites $`\Lambda`$ is finite, the quasi-local algebra $`\mathcal A_{ql}`$ is the algebra of all bounded operators on $`H`$.  
<sub>`Sealed.quasiLocalAlgebra_eq_top_of_finite`</sub>

**16.** For a finite set of sites $`O`$, the algebra $`\mathcal A(O)`$ is the range of the local embedding $`\iota_O`$.  
<sub>`Sealed.quasiLocalNet_eq_range_of_finite`</sub>

## Examples

These examples show that the hypotheses of the main theorems can be met and that the objects are not degenerate.

**17.** For the chain $`\mathbb N`$ with two letters per site and the reference configuration $`0`$, the quasi-local algebra is not the zero algebra.  
<sub>`Sealed.witness_nontrivial_quasiLocalAlgebra`</sub>

**18.** For the chain $`\mathbb N`$ with two letters per site and the reference configuration $`0`$, the set of finitely supported configurations, which indexes the basis of $`H`$, is infinite.  
<sub>`Sealed.witness_infinite_finConfig`</sub>

**19.** For the chain $`\mathbb N`$ with two letters per site and the reference configuration $`0`$, the algebra $`\mathcal A(\{0\})`$ of the site $`0`$ contains an element that is not a multiple of the identity.  
<sub>`Sealed.witness_quasiLocalNet_singleton_not_scalar`</sub>

**20.** For the chain $`\mathbb Z`$ with two letters per site and the reference configuration $`0`$, which is invariant under translations, there is a unitary $`U`$ on $`H`$ with $`U \mathcal A(\{0\}) U^* = \mathcal A(\{1\})`$.  
<sub>`Sealed.witness_translation_covariant`</sub>

**21.** For the chain $`\mathbb N`$ with two letters per site, the reference configurations $`0`$ and $`1`$ differ at infinitely many sites, and there is a $`*`$-isomorphism $`\varphi`$ of their quasi-local algebras with $`a \in \mathcal A(O) \iff \varphi(a) \in \mathcal A'(O)`$ for every set of sites $`O`$.  
<sub>`Sealed.witness_references_differing_everywhere`</sub>

---

SHA-256 of `verify/Challenge.lean` (LF line endings): `2866d29b91ce79ec230b3c61a2012f131b51ee0a8f19ccfec55d9d8fbc330908`
