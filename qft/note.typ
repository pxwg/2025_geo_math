// Complie with `typst c ./qft/note.typ --input colored=true --root ../` to get pdf version
#import "@preview/commute:0.3.0": arr, commutative-diagram, node

// Packages
#import "@preview/physica:0.9.5": *
// #import "../preamble.typ"
// colors controled by the `colored` variable passed in the command line or by default
// which is `false` and help to manage the default (preview in url) and uncolored (published in pdf) version
// TODO: better false (pdf) color flavors to contral definition block etc.
// TODO: become a package to be used in other documents
#import "@preview/catppuccin:1.0.0": catppuccin, flavors

// Get the `colored` variable from the command line input
// Then determine the color scheme based on the `colored` variable
#let coloreds = sys.inputs
#let get_input(input_dict) = {
  for (key, value) in input_dict {
    if key == "colored" {
      return value
    }
  }
  return true
}

#let colored = get_input(coloreds)

#let get_color_scheme(input_value) = {
  if input_value == "false" {
    (
      background: catppuccin.with(flavors.latte),
      flavors: flavors.latte,
    )
  } else {
    (
      background: catppuccin.with(flavors.mocha),
      flavors: flavors.mocha,
    )
  }
}
#let showed_flavors(colored) = {
  if colored == "false" {
    flavors.latte
  } else {
    flavors.mocha
  }
}
#show: get_color_scheme(colored).background
#let color_flavors = get_color_scheme(colored).flavors

// ### Example:
// ```typst
// #definition(name: 'prefactorization algebra',[
//   A prefactorization algebra $cal(F)$ on $M$ would assign to each open subset $U$ with a vector space $cal(F)$, together with a maps
//   $
//     m_V^(U_1, U_2, dots, U_n): cal(F)(U_1) times.circle cal(F)(U_2) times.circle dots times.circle cal(F)(U_n) --> cal(F)(V),
//   $
// ])
// ```
#let definition(name: none, body) = {
  box(
    stroke: 1pt + rgb(color_flavors.colors.blue.rgb),
    width: 100%,
    fill: rgb(color_flavors.colors.crust.rgb),
    inset: (x: 8pt, y: 8pt),
    [
      #if name != none [*Definition* (#emph(name))] else [*Definition*]
      #body
    ],
  )
}
#let example(name: none, body) = {
  box(
    stroke: 1pt + rgb(color_flavors.colors.maroon.rgb),
    width: 100%,
    fill: rgb(color_flavors.colors.crust.rgb),
    inset: (x: 8pt, y: 8pt),
    [
      #if name != none [*Example* (#emph(name))] else [*Example*]
      #body
    ],
  )
}
#let theorem(name: none, body) = {
  box(
    stroke: 1pt + rgb(color_flavors.colors.peach.rgb),
    width: 100%,
    fill: rgb(color_flavors.colors.crust.rgb),
    inset: (x: 8pt, y: 8pt),
    [
      #if name != none [*Theorem* (#emph(name))] else [*Theorem*]
      #body
    ],
  )
}

#let proposition(name: none, body) = {
  box(
    stroke: 1pt + rgb(color_flavors.colors.green.rgb),
    width: 100%,
    fill: rgb(color_flavors.colors.crust.rgb),
    inset: (x: 8pt, y: 8pt),
    [
      #if name != none [*Proportion* (#emph(name))] else [*Proportion*]
      #body
    ],
  )
}

#let f = flavors.mocha.colors.flamingo

#let remark(name: none, body) = {
  box(
    stroke: 1pt + rgb(color_flavors.colors.flamingo.rgb),
    width: 100%,
    fill: rgb(color_flavors.colors.crust.rgb),
    inset: (x: 8pt, y: 8pt),
    [
      #if name != none [*Remark* (#emph(name))] else [*Remark*]
      #body
    ],
  )
}


#let proof(name: none, body) = {
  block(
    stroke: 1pt + rgb(color_flavors.colors.lavender.rgb),
    width: 100%,
    fill: rgb(color_flavors.colors.crust.rgb),
    inset: (x: 8pt, y: 8pt),
  )[
    #if name != none [_Proof_ (#emph(name)). ] else [_Proof_. ]
    #body
    #h(1fr)
    $qed$
  ]
}

#let sym = "Sym"

//----------------------basic info ----------------------//

#let title = "Quantum Field Theory"
#let author = "Lectured by Prof. Si Li and Noted by Xinyu Xiang"
#let date = "Jul. 2025"

#set document(title: title, author: author, date: auto)

#align(center, text(17pt)[*#title*])

#align(center)[
  #author \
  #date
]

//----------------------main project ----------------------//

#box(
  stroke: 1pt + rgb(color_flavors.colors.blue.rgb),
  width: 100%,
  fill: rgb(color_flavors.colors.crust.rgb),
  inset: (x: 8pt, y: 8pt),
  [
    *Warning*: Lots of potential typos!!!!!!!!!!!!

    *Notations*:
    - $X$: a smooth manifold, usually a compact manifold.
    - $cal(E)$: the space of fields, usually infinite dimensional.
    - $"Conn"(P,X)$: the space of connections on a principal bundle $P$ over $X$.
    - $"Maps"(Sigma, X)$: the space of maps from $Sigma$ to $X$.
    - $Omega^bullet (X)$: the space of differential forms on $X$.
    - $Omega^bullet_c (X)$: the space of differential forms with compact support on $X$.
    - $"Vect"(M)$: the space of smooth vector fields on a manifold $M$, which is Lie algebra of $"Diff"(M)$.
  ],
)

= Day I: Overall Discussion and Mathematical Preliminaries

== Actions and Path Integrals

Action $S: cal(E) arrow bb(k)$ where $cal(E)$ always has infinite dimension, and $bb(K)$ is a field (usually $bb(R)$ or $bb(C)$).

$
  "QM in Imaginary Time" stretch(->)^(" Brownian Motion ") "Wiener Measure on Phase Space"
$
$
  "Asymptotic Analysis" --> "Perturbative Renormalisation Theory"
$

#example(
  name: "Some Examples of Classical Field Theories",
  [
    - Scalar Field Theory $cal(E) = C^infinity (X)$
    - Gauge Theory $cal(E) = "Conn"(P,X)$
    - $sigma$ Model $cal(E) = "Maps"(Sigma, X)$
    - Gravity $cal(E) = "Metrics"(X)$ (Better descriptions does not depend on the background)
  ],
)

== Observables

Observables are functions on the space of fields, i.e. $cal(O) in C^infinity (cal(E))$.

#example(
  name: "field theory",
  [
    - Consider $X = "pt"$, thus $cal(E) = bb(R)^n$ for example.
    - $dim X > 0$, the new algebraic structure arise form topological structures of $X$.
  ],
)

The Key Point is: Capture the data of open sets of $X$ $-->$ Consider the observables supported on open set $U$ of $X$ denoted by $"Obs"(U)$ where $U$ is an open set of $X$.

Local data captures the open sets of $X$. The relations between open sets captures the global data of $X$ $-->$ The algebraic structure of the observables is a sheaf of $X$.
$
  union.sq.big_i U_i --> product "Obs"(U_i)
$
Which implies OPE in physics and factorization algebra in mathematics.

Higher product in QFT: The generalization of products of algebra ('products in any direction instead of left and right') e.g. QM gives only left and right module of an algebra; OPE has products in various directions.

Consider the $dim X = 2$ case in detailed

#example(
  name: "Holomorphic/Chiral Field Theory",
  [
    Various angle of product $A(w) B(z)$ could be denoted by the time of $A(w)$ rotations around $B(z)$, which could be captured by the Fourier mode of $A(w)$. Thus, one can have
    $
      A(w) B(z) = sum_(m in bb(Z)) frac((A_((m)) B(z)), (z - w)^(m+1)),
    $
    which is the Chiral algebra due to Beilinson and Drinfeld and associated with the Dolbeault cohomology $H^0_(diff)(Sigma^2 - Delta) tilde.equiv bb(C)((z^m))$, where $Sigma^2$ is the complex surface and $Delta$ is the diagonal of $Sigma^2$. The higher structure could be captured by the higher cohomology $H^p_(diff)(Sigma^2 - Delta)$, which is the higher chiral algebra associated to the derived holomorphic section.
  ],
)

== de Rham Cohomology

Chain of differential forms $Omega^bullet (X)$
$
  Omega^bullet (X) = (-->^("d") Omega^(n-1)(X) -->^("d") Omega^n(X) -->^("d") Omega^(n+1)(X) -->^("d") dots),
$
where $"d"$ is the exterior derivative, and $Omega^n(X)$ is the space of $n$-forms on $X$. The general construction of differential forms could be constructed over open set $U$ by
$
  Omega^n (U) = plus.circle.big(1 <= i_1 <= dots <= i_n <= n) C^(infinity) (U) "d" x^(i_1) and dots and "d" x^(i_n),
$
where one can prove that $"d"^2 = 0$ and thus $(Omega^bullet (U), "d")$ is a cochain complex. The cohomology of it is called the de Rham cohomology $H^bullet (X)$.

#theorem(
  name: "de Rham cohomology is intrinsic",
  [
    The definition of de Rham cohomology does not depend on the choice of the open set $U$ and the choice of the coordinate system. This mean de Rham cohomology is intrinsic $-->$ we can define the de Rham cochain complex on smooth manifold $X$.
  ],
)

#definition(
  name: "de Rham Cohomology on Compact Support",
  [
    Let $X$ be a smooth manifold, then the de Rham cohomology on compact support is defined as
    $
      H^bullet_c (X) = H^bullet (Omega^bullet_c (X), "d")
    $
    where $Omega^(bullet)_(c) (X)$ is the space of differential forms with compact support.
  ],
)

#theorem(
  name: "Stokes' Theorem",
  [
    Let $X$ be a smooth manifold with boundary, then for any $omega in Omega^(n) (X)$, we have
    $
      integral_X "d" omega = integral_(diff X) omega
    $
    which connects the local data $"d" Omega^bullet_c (X)$ and the global data $diff X$.
  ],
)

#theorem(
  name: "Poincaré Lemma",
  [
    $
      H^p(bb(R)^n) = cases(
        bb(R)", " p = 0,
        0", " p > 0
      ) thin , quad
      H^p_c (bb(R)^n) = cases(
        0", " p < n,
        bb(R)", " p = n
      )
    $
    Generator: $H^p (bb(R)^n)$ $arrow$ constant function, $H^p_c (bb(R)^n)$ $arrow$ a compact support function $alpha = f(x) "vol"_n$, and $integral_(bb(R)^n) alpha = 1$.
  ],
)

Important: An *Integration* arises from the de Rham cohomology!

#box(
  stroke: 1pt + rgb(color_flavors.colors.yellow.rgb),
  width: 100%,
  fill: rgb(color_flavors.colors.crust.rgb),
  inset: (x: 8pt, y: 8pt),
  [
    (1) If $alpha = "d" beta$ where $beta in Omega_c^(n-1)(X)$, then $integral_X alpha = 0$, thus the generator is $alpha$ whose integral is non-zero.
    (2) *Dual Site*: Integration could be captured by the cohomology
    $
      integral_(bb(R)^n) arrow.l.r.double H^n_c (bb(R)^n) tilde.equiv bb(R)
    $
    Path integral could be interpreted as the integration over $cal(E)$, which leads to consider the cohomology of it.
  ],
)

== Cartan Formula

Vector fields could act on smooth functions via
$
  V(f) = V^i frac(diff f, diff x^i) = frac("d", "d" t) f(phi_t(x)) |_(t=0) = frac("d", "d" t) phi_t^* f(x) |_(t=0)
$
Such an action could be extended to differential forms by
$
  "Vect"(M) in.rev V : alpha |-> cal(L)_V alpha = frac("d", "d" t) phi_t^* alpha |_(t=0)
$
which has the property $cal(L)_V (alpha and beta) = cal(L)_V alpha and beta + alpha and cal(L)_V beta$, which implies that the Lie derivative is a derivation on the algebra of differential forms with degree $0$. And we have contraction $iota_V$ which is a derivation of degree $-1$ on the algebra of differential forms.
$
  cal(L)_V = "d" iota_V + iota_V "d"
$
Lie derivative is homotopy trivial i.e. chain homotopic.

=== Proof of Poincaré Lemma

Use Cartan Formula, one can proof Poincaré Lemma.

*Proof:*
Rescaling invariance of $bb(R)^n$ leads to the Euler vector field $E = x^i frac(diff, diff x^i)$. One can consider the associated diffeomorphism $phi_t$, where we assume $phi_0 = 1$ and thus $phi^*_(-infinity) alpha = 0$. Thus, the closed form $alpha$ could be rewritten as:
$
  alpha & = phi^*_0 alpha - phi^*_(-infinity) alpha \
        & = integral_(-infinity)^0 frac("d", "d" t) phi_t^* alpha "d" t \
        & = integral_(-infinity)^0 cal(L)_E (phi^*_t alpha) "d" t,
$
using the Cartan formula and $"d" phi^* = phi^* "d"$, we have
$
  alpha = "d" integral_(-infinity)^0 phi^*_t iota_E alpha "d" t = "d" beta.
$
Thus, the closed form $alpha$ is exact, which implies that the de Rham cohomology $H^p(bb(R)^n)$ is trivial for $p>0$. The same idea could be applied to the de Rham cohomology on compact support $H^p_c (RR^n)$.

= Day II: Classical Field Theory

Assume $cal(E) = Gamma(E, X)$, i.e. a section of a bundle $E -> X$, where $X$ is an oriented manifold.
The action is written as $S[phi] = integral_X cal(L)[phi(x)]$, where $phi in.rev cal(E)$.
Lagrangian $cal(L)$ satisfies:
- Built up by jets of $phi$ (locality)
- Valued in $n$-form on $X$ (oriented)

The solution of Euler-Lagrange equation forms $"Crit"(S)$, which denotes the critical locus of the action $S$.

== Examples

#example(
  name: "Phase Space Quantum Mechanics",
  [
    Consider $X = RR$, then $cal(E) = bb(R)^(2n)$, and the action is
    $
      S[phi] = integral_(bb(R)^(2n)) p dif q - H(q, p) \, d t
      = integral [p dot(q) - H] d t
    $
    where $H$ is the Hamiltonian. The Euler-Lagrange equation becomes $dif H = - iota_(x_* partial) omega$, where $x: bb(R) -> cal(E)$.
  ],
)


#example(
  name: "Scalar Field Theory",
  [
    Consider $(X, g)$ a Riemannian manifold, then $cal(E) = C^infinity(X)$, and the action is
    $
      S[phi] = integral_X [frac(1, 2) abs(nabla phi)^2 + V(phi)] d upright("vol")_g
    $
    where $V(phi)$ is a potential function, and $d upright("vol")_g = sqrt(abs(g)) d^d x$. Assume $partial X = emptyset$, then the Euler-Lagrange equation is
    $
      Delta phi = frac(partial V, partial phi)
    $
    where $Delta f = frac(1, sqrt(abs(g))) partial_i (sqrt(abs(g)) g^(i j) partial_j f)$.
  ],
)

#example(
  name: "Chern-Simons Theory",
  [
    Consider $X$ a 3-manifold and $frak(g)$ a semisimple Lie algebra.
    Denote $P$ as a principal $frak(g)$-bundle over $X$, then the space of fields is $cal(E) = upright("Conn")(P, X)$.
    Assume $frak(g)$ is equipped with a non-degenerate invariant bilinear form $lr(angle.l dot.c, dot.c angle.r)$ (Killing form), then the action is
    $
      "CS"[A] = integral_X frac(1, 2) lr(angle.l A, F_A angle.r) + frac(1, 6) lr(angle.l A, [A, A] angle.r)
    $
    and the Euler-Lagrange equation is encoded by the flat connection $F_A = 0$.
  ],
)

== Symmetry (1)

=== Global Symmetry and Noether's Theorem

Consider a classical action $S: cal(E) -> bb(R)$ with a group action $G arrow.hook cal(E)$ such that $S[g(phi)] = S[phi]$. Then $G$ is a global symmetry of the action $S$.

For continuous symmetry, i.e. $G$ is a Lie group, the infinitesimal action of $G$ on $cal(E)$ is given by a vector field $V in.rev "Vect"(cal(E))$, which satisfies
$
  delta_(V^alpha) phi = V^alpha (phi)
$
thus the variation of the Lagrangian is
$
  delta_(V^alpha) cal(L) = d K_alpha
$
where $K_alpha$ is an $n-1$ form. Using the Euler-Lagrange equation and its boundary contribution, we obtain
$
  delta_(V^alpha) cal(L) -> (E L = 0) d iota_(V^alpha) Theta = d K_alpha
$
thus the Noether current is
$
  J_alpha = iota_(V^alpha) Theta - K_alpha, quad d J_alpha + E L[phi] V_alpha = 0
$
which is an $n-1$ form on $X$ and satisfies $d J_alpha|_("Crit"(S)) = 0$ when the Euler-Lagrange equation holds.

If $Y_1, Y_2 subset X$ are codimension $1$ (hyper) surfaces, homologous by $Sigma$, then
$
  integral_(Y_1) J_alpha - integral_(Y_2) J_alpha = integral_(Sigma) d J_alpha = 0, quad phi in.rev "Crit"(S)
$
and the integration over $J_alpha$ is independent of the choice of hypersurface, so we can define the Noether charge as the integration over $J_alpha$ on a hypersurface $Y$.

Alternatively, one can consider the 'gauged' symmetry, promoting $epsilon$ to a field $epsilon(x)$, and compute the variation of the action by integrating by parts:
$
  delta_(V^alpha) S = integral_X - epsilon(x) d hat(J)_alpha
$
and $hat(J)$ is the Noether current, satisfying the same equation as $J_alpha$ up to an exact form.

= Day III: Breaking

= Day IV: Symmetry (2)
First, we will consider finite dimensional case. We consider $G$ as a
finite dimensional Lie group, $frak(g)$ is the Lie algebra of $G$ and
$W$ is finite dimensional representation of $G$.

== Chevalley-Eilenberg Cohomology

Consider $frak(g)^(\*) equiv "Hom" (frak(g) \, bb(K))$. Consider the
exterior algebra
$
  and.big frak(g)^(\*) = xor.big_(p = 0)^oo attach(and.big, tr: p) frak(g)^(\*) .
$
Assume the basis of $frak(g)$ is ${e_1 \, dots.h.c \, e_n}$ and of
$frak(g)^(\*)$ is ${c^1 \, dots.h.c \, c^n}$, which satisfies
$c_alpha c_beta = - c_beta c_alpha$. Thus, one could identify the
algebra above as a free object in the category of differential graded
algebra, which is a ring equipped with anti-commute generators
$ and.big frak(g)^(\*) = bb(K) [c^1 \, dots.h.c \, c^n] . $

Consider the Lie algebra over $frak(g)$, which equipped with commutator
$[dot.op \, dot.op] : and^2 frak(g) arrow.r frak(g)$. One the dual side,
one would introduce a differential operator
$upright(d) : frak(g)^(\*) arrow.r frak(g)^(\*)$, and we can extend it
to the exterior algebra $and.big frak(g)^(\*)$ by

#set enum(numbering: "(1)", start: 1)
+ Under the level of generators, we have
  $upright(d)_(upright(C E)) : frak(g)^(\*) arrow.r and^2 frak(g)^(\*)$;

+ Using the Leibniz rule, we can extend it to the exterior algebra
  $and.big frak(g)^(\*)$ by
  $
    upright(d)_(upright(C E)) : a and b arrow.r.bar upright(d)_(upright(C E)) a and b + (- 1)^(deg a) a and upright(d)_(upright(C E)) b \.
  $
And thus we have a differential graded algebra
$(and.big frak(g)^(\*) \, upright(d)_(upright(C E)))$, which is called
the Chevalley-Eilenberg complex.

Under the choice of basis above, we have
$[e_alpha \, e_beta] = f_(alpha beta)^gamma e_gamma$, which would lead
to the derivation on the dual side
$
  upright(d)_(upright(C E)) c^alpha = 1 / 2 f_(beta gamma)^alpha c^beta and c^gamma equiv 1 / 2 f_(beta gamma)^alpha c^beta c^gamma .
$
Using the Leibniz rule, we can extend it to the exterior algebra
$and.big frak(g)^(\*)$. Using the Jacobi identity, one can prove that
$upright(d)_(upright(C E))^2 = 0$ (left as exercise), thus we have a
cochain complex $(and.big frak(g)^(\*) \, upright(d)_(upright(C E)))$
which is a differential graded algebra (DGA), where the generator
$c^alpha$ is called the 'ghost field' in physics, the degree is 'ghost
number' and $upright(d)_(upright(C E))$ is BRST operator.

#proof[
  Consider $upright(d)_(upright(C E))^2$ acts on $c^alpha$,
  the higher structure could be derived from Leibniz's rule.
  $
    upright(d)_(upright(C E))^2 c^alpha = & 1 / 2 f_(beta gamma)^alpha [1 / 2 f_(rho lambda)^beta c^rho c^lambda c^gamma - 1 / 2 f_(rho lambda)^gamma c^beta c^rho c^lambda]\
    = & - 1 / 2 f_(gamma beta)^alpha f_(rho lambda)^beta c^rho c^lambda c^lambda\
    = & 1 / 12 f_(beta \[ gamma)^alpha f_(rho lambda \])^beta c^rho c^lambda c^lambda\
    = & 0.
  $
  Extend this result through Leibniz's rule, such a result would be valid in any degree.
]
Let $M$ be a $frak(g)$ representation where
$rho : frak(g) arrow.r "End" (W)$ satisfies
$
  rho (a) rho (b) m - rho (b) rho (a) m = rho ([a \, b]) m \, quad a \, b in frak(g) \, m in M .
$
Consider the free $attach(and.big, tr: bullet) frak(g)^(\*)$-module generated by $M$:
$ attach(and.big, tr: bullet) frak(g)^(\*) times.circle M \, $ there is a natural
extension of the Chevalley-Eilenberg differential
$upright(d)_(upright(C E))$ on it, which is defined by

#set enum(numbering: "(1)", start: 1)
+ $upright(d)_(upright(C E)) : M arrow.r g^(\*) times.circle M$ is dual
  of $g times.circle M arrow.r^rho M$;

+ $upright(d)_(upright(C E)) (a times.circle m) : upright(d)_(upright(C E)) (a) times.circle m + (- 1)^(lr(|a|)) a and upright(d)_(upright(C E)) m$

Where we can prove that $upright(d)_(upright(C E))^2 = 0$, and thus we
have a cochain complex $attach(and.big, tr: bullet) frak(g)^(\*) times.circle M$.

We denote $and^p frak(g)^(\*) times.circle M$ be
$C^p (frak(g)^(\*) \, M)$, then we would find that it is
$C^p (frak(g)^(\*))$-module, i.e.
$
  C^p (frak(g)^(\*)) times.circle C^q (frak(g)^(\*) \, M) in.rev a times.circle v arrow.r.bar a and v in C^(p + q) (frak(g)^(\*) \, M) \,
$
which is compatible with derivation
$
  upright(d)_(upright(C E)) (a and v) = upright(d)_(upright(C E)) a and v + (- 1)^(lr(|a|)) a and upright(d)_(upright(C E)) v \,
$
where $m in M$ and $a in and^bullet frak(g)^(\*)$. The derivation could
be written explicitly with basis $a_k$ of $M$, and it's dual basis
$b^k$:
$
  upright(d)_(upright(C E)) = (rho_alpha)_i^k b^i a_k c^alpha + 1 / 2 f_(beta gamma)^alpha c^beta c^gamma a_alpha \,
$
which could be easily verified that $upright(d)_(upright(C E))^2 = 0$.

#proof[
  There is a general way to prove
  $upright(d)_(upright(C E))^2 = 0$, which is to note that, under the dual
  transformation, one have identity
  $⟨upright(d)_(upright(C E)) phi_1 \, c_1 m_1⟩ = ⟨phi_1 \, rho (c_1) m_1⟩$,
  $⟨upright(d)_(upright(C E)) phi_2 \, c_1 and c_2⟩ = ⟨phi_2 \, [c_1 \, c_2]⟩$
  and Leibniz's law, so that:
  $
    angle.l
    diff_("CE")^2 phi,
    c_1 and c_2 times.circle m_1
    angle.r = angle.l
    phi,
    rho([c_1, c_2]) m + (-1)(rho(c_1) rho(c_2) m + rho(c_2) rho(c_1) m)
    angle.r stretch(->)^( frak(g) "rep."
    ) 0,
  $
  $
    ⟨upright(d)_(upright(C E))^2 phi \, c_1 and c_2 and c_3⟩ stretch(->)^(upright("Jacobian")) 0 \,
  $
  where we note that the dual of $c_1 and c_2$ has degree $1$ graded.
]
== Differential Graded Lie Algebra

We define a $bb(Z)$-graded vector space
$ W = xor.big_(n in bb(Z)) W_n \, $ where $W_n$ is degree of $n$
component.

+ #strong[Degree Shift];: $W [n]_m equiv W_(n + m)$;

+ #strong[Dual];: $W^(\*)$ denote the linear dual of $W$
  $ W_n^(\*) = "Hom" (W_(- n) \, bb(K)) ; $

+ #strong[Symmetry and Anti-Symmetry];:
  $upright(S y m)^(times.circle n) (V) = V^(times.circle n) \/ tilde.op$
  where
  $a times.circle b tilde.op (-)^(lr(|a|) lr(|b|)) b times.circle a$,
  and $attach(and.big, tr: V) = V^(times.circle n) \/ tilde.op$ where
  $a times.circle b tilde.op (- 1)^(lr(|a|) lr(|b|) + 1) b times.circle a$;
which has a natural isomorphism between $attach(and.big, tr: m) (V [1])$ and
$upright(S y m)^m (V) [m]$

#proposition[
  Let $V$ be a DGA, then:
  $ attach(and.big, tr: m) (V [1]) tilde.equiv upright(S y m)^m (V) [m] . $

]
#proof[
  Consider the subspace generated by ideals
  $
    a times.circle b tilde.op (- 1)^((lr(|a|) + 1) (lr(|b|) + 1) + 1) b times.circle a = (- 1)^(lr(|a|) lr(|b|) + lr(|a|) + lr(|b|)) b times.circle a \, quad a \, b in V [1] \,
  $
  $
    a times.circle b tilde.op (- 1)^(lr(|a|) lr(|b|)) b times.circle a \, quad a \, b in V \,
  $
  where $lr(|a|)$ is the degree of $a$ in $V$, thus the total degree in
  $V [1]$ is $lr(|a|) + lr(|b|) + 2$. The element in the left-hand side is
  $
    frac(1, n !) (a_1 a_2 dots.h.c a_n + (- 1)^((lr(|a_1|) + 1) (sum_(i = 2)^n lr(|a_i|) + n - 1) + n - 1) a_2 dots.h.c a_n a_1 + dots.h.c) in attach(and.big, tr: n) (V [1]) \,
  $
  and the element in the right-hand side is
  $
    frac(1, n !) (a_1 a_2 dots.h.c a_n + (- 1)^(lr(|a_1|) sum_(i = 2)^n lr(|a_i|)) a_2 dots.h.c a_n a_1 + dots.h.c) in upright(S y m)^n (V) [n] .
  $
  Consider the shuffle map
  $
    a_1 times.circle a_2 times.circle dots.h.c times.circle a_n arrow.r a_n times.circle a_(n - 1) times.circle dots.h.c times.circle a_1 \,
  $
  the overall sign in $upright(S y m)^m (V) [m]$ and $attach(and.big, tr: m) (V [1])$
  is the same, which is
  $
    (- 1)^(sum_(1 lt.eq i < j lt.eq n) lr(|a_i|) lr(|a_j|)) = (- 1)^(sum_(1 lt.eq i < j lt.eq n) lr(|a_i|) lr(|a_j|) + 2 sum_(i = 1)^n lr(|a_i|)) \,
  $
  where the first term is the sign of the anti-symmetry monomials and the
  second term is the sign of the symmetry monomials.~◻

]
#definition(name: "Differential Graded Algebra")[
  A DGLA is a $bb(Z)$-graded space $ g = xor.big_(m in bb(Z)) g_m $
  together with bilinear map
  $[dot.op \, dot.op] : g times.circle g arrow.r g$ satisfying

  + (graded bracket) $[g_alpha \, g_beta] subset g_(alpha + beta)$,
    $[dot.op \, dot.op] in upright("Hom") (g times.circle g \, g)$,

  + (graded skew-symmetry) $[a \, b] = - (- 1)^(lr(|a|) lr(|b|)) [b \, a]$
    $([dot.op \, dot.op] : and^2 g arrow.r g)$,

  + (graded Jacobi Identity)
    $[[a \, b] \, c] = [a \, [b \, c]] - (- 1)^(lr(|a|) lr(|b|)) [b \, [a \, c]]$,

  with a degree 1 map $d : g arrow.r g$ (i.e.,
  $d : g_alpha arrow.r g_(alpha + 1)$) satisfying $upright(d)^2 = 0$ and

  #set enum(numbering: "1.", start: 4)
  + (graded Leibniz rule)
    $d [a \, b] = [d a \, b] + (- 1)^(lr(|a|)) [a \, d b]$.
]
#example(name: "Chern-Simons Theory")[
  Let $X$ be a manifold, $frak(g)$ a Lie algebra.

  - $(Omega^bullet (X) \, d)$ de Rham complex,

  - $(Omega^bullet (X) times.circle frak(g) \, d \, [dot.op \, dot.op])$
    is DGLA,

  - $Omega^p (X) times.circle frak(g)$ : degree $p$ component,

  - $d : Omega^p times.circle frak(g) arrow.r Omega^(p + 1) times.circle frak(g)$
    de Rham, $d (alpha times.circle h) = d alpha times.circle h$,

  - $[dot.op \, dot.op]$ induced from $frak(g)$,

  - Let $alpha_(1 \, 2) in Omega^bullet (X)$, $h_(1 \, 2) in frak(g)$,
    then
    $[alpha_1 times.circle h_1 \, alpha_2 times.circle h_2] = alpha_1 and alpha_2 times.circle [h_1 \, h_2]$,

  $⤳$ DGLA in Chern-Simons theory.

]
#example(name: "Kodaria-Spencer Gravity")[
  Let $X$ be a complex manifold. Let

  - $(Omega^(0 \, bullet) (X) \, overline(partial))$ Dolbeault Complex,

  - $(sum_(overline(i)_1 \, . . . \, overline(i)_p) phi_(overline(i)_1 . . . overline(i)_p) d overline(z)^(overline(i)_1) and . . . and d overline(z)^(overline(i)_p))$
    where $overline(partial) = d overline(z)^(overline(i)) frac(partial, partial overline(z)^i)$,

  - $T_X times.circle_(bb(C)) bb(C) = T_X^(1 \, 0) xor T_X^(0 \, 1)$,
    where we could choose the basis as
    $
      upright("Span") { frac(partial, partial z^i) } \, quad upright("Span") { frac(partial, partial overline(z)^i) }.
    $
  Which leads that
  $(Omega^(0 \, \*) (X \, T_X^(1 \, 0)) \, overline(partial) \, [dot.op \, dot.op])$
  is a DGLA.

  Explicitly, let ${ z^i }$ be local holomorphic coordinates.
  $alpha in Omega^(0 \, p) (X \, T_X^(1 \, 0))$ takes the form
  $
    alpha = sum_(i \, overline(J)) alpha_(overline(J))^i d overline(z)^(overline(J)) times.circle frac(partial, partial z^i) \, quad d overline(z)^(overline(J)) = d overline(z)^(overline(j)_1) and . . . and d overline(z)^(overline(j)_p) \,
  $
  $
    overline(partial) alpha = sum_i overline(partial) alpha_(overline(J))^i d overline(z)^(overline(J)) times.circle frac(partial, partial z^i) = sum_i frac(partial alpha_(overline(J))^i, partial overline(z)^k) d overline(z)^k and d overline(z)^(overline(J)) times.circle frac(partial, partial z^i) .
  $
  Let
  $alpha = sum_i alpha_(overline(J))^i d overline(z)^(overline(J)) times.circle frac(partial, partial z^i)$
  and
  $beta = sum_m beta_(overline(M))^i d overline(z)^(overline(M)) times.circle frac(partial, partial z^i)$.
  The Lie bracket is
  $
    [alpha \, beta] = sum_i (alpha_(overline(J))^j partial_j beta_(overline(M))^i - beta_(overline(M))^j partial_j alpha_(overline(J))^i) d overline(z)^(overline(J)) and d overline(z)^(overline(M)) times.circle frac(partial, partial z^i)
  $
  On $deg = 0$ component, this is the standard Lie bracket of $(1 \, 0)$
  vector fields. Finally, one can verify that
  $(Omega^(0 \, \*) (X \, T_X^(1 \, 0)) \, overline(partial) \, [dot.op \, dot.op])$
  is a DGLA. $⤳$ Mathematics: Deformation of complex structures
  $arrow.l.r$ Physics: B-twisted topological string (Kodaria-Spencer
  gravity)

]
We can consider the Chevalley-Eilenberg complex for a DGLA
$(frak(g) \, upright(d) \, [med \, med])$.

#definition(name: "Chevalley-Eilenberg Cohomology for DGLA")[
  For a DGLA $(frak(g) \, upright(d) \, [med \, med])$, the
  Chevalley-Eilenberg complex is defined as
  $
    C^bullet (frak(g)) = upright(S y m)^bullet (frak(g)^(\*) [- 1]) = attach(and.big, tr: bullet) frak(g)^(\*) [- bullet] \,
  $
  equipped with the CE differential
  $upright(d)_(upright(C E)) = upright(d)_1 + upright(d)_2$, where

  #set enum(numbering: "(1)", start: 1)
  + $upright(d)_1 : frak(g)^(\*) [- 1] arrow.r frak(g)^(\*) [- 1]$ is the
    dual of $upright(d) : frak(g) arrow.r frak(g)$;

  + $upright(d)_2 : frak(g)^(\*) [- 1] arrow.r upright(S y m)^2 (frak(g)^(\*) [- 1]) tilde.equiv attach(and.big, tr: 2) frak(g)^(\*) [- 2]$
    is the dual of $[med \, med] : attach(and.big, tr: 2) arrow.r frak(g)$;

  + (Graded Leibniz rule) The derivation extends to
    $
      upright(d)_(upright(C E)) : upright(S y m) (frak(g)^(\*) [- 1]) arrow.r upright(S y m) (frak(g) [- 1])
    $
    via the graded Leibniz rule
    $
      upright(d)_(upright(C E)) (a b) = upright(d)_(upright(C E)) a thin b + (- 1)^(lr(|a|)) a thin upright(d)_(upright(C E)) b \,
    $
    and satisfies $upright(d)_(upright(C E))^2 = 0$.
]

#remark[
  If $frak(g)$ degenerated to the ordinary Lie algebra, which would be
  'bosonic' fields. However, the basic object to build CE complex for ordinary Lie algebra is 'fermionic' fields. So we need to impose $[- 1]$
  into the definition of CE complex of DGLA.

  Another generalized consideration could be finished by this. Consider
  $L_oo$ algebra, one can assume
  $dif_m : frak(g)^* [-1] -> sym^m (frak(g)^* \[-1\])\[1\] = and^m frak(g)^* [m+1]$
  is the dual of $l_m$, which is degree $1$. Thus, we could shift by $[1]$,
  then obtain the dual side
  $l_m : and^m frak(g) arrow.r frak(g)^(\*) [2 - m]$. Which implied
  that, while we treat the dual side of $L_oo$ algebra as
  $frak(g)^(\*) [- 1]$ embedded with a degree $1$ derivation, the original
  $L_oo$ algebra would have degree $2 - m$ product $l_m$, which is
  compatible with our original consideration for ordinary $L_oo$ algebra.
]

#definition(name: "DGLA Module")[
  Let $frak(g)$ be a DGLA. A $frak(g)$-module is a cochain complex
  $(M \, d_M)$ with bilinear map $ frak(g) times.circle M arrow.r M $
  where
  $C^bullet (frak(g) \, M) = upright(S y m) (frak(g)^(\*) [- 1]) times.circle N$
  satisfying

  #set enum(numbering: "(1)", start: 1)
  + $upright(d)_M$ is the dual of
    $rho : frak(g)_n times.circle M_p arrow.r M_(n + p)$,

  + $upright(d)_(frak(g))$ is the dual of
    $[med \, med] : rho (a) rho (b) m - (- 1)^(lr(|a|) lr(|b|)) rho (b) rho (a) m = rho ([a \, b]) dot.op m$,

  + (Chevalley-Eilenberg differential)
    $upright(d)_(C E) = upright(d)_M + upright(d)_(frak(g))$,

  + (Leibniz's law)
    $upright(d)_(upright(C E)) (a times.circle m) = (upright(d)_(frak(g)) a) m + (- 1)^(lr(|a|)) a upright(d)_M m$,
]

= Homotopic Lie Algebra ($L_oo$ Algebra)

== Coderivation Side

The original definition could be viewed as a homotopic generalization of
the Lie algebra, which is a DGLA $V$ with 'higher brackets'
$mu_n : V^(times.circle n) arrow.r V$, where the first term at the chain
level formed a (co)chain complex i.e. $mu_1^2 = 0$. The higher brackets
needed to satisfy some self-consistency conditions, which is so called
'homotopic Jacobian identity'. At some low level $n$, which could be
written explicitly as
$
  mu_1 mu_2 (a \, b) = - thin mu_2 (mu_1 a \, b) - (- 1)^(lr(|a|)) thin mu_2 (a \, mu_1 b) \,
$
$
  & mu_1 mu_3 (a \, b \, c) + mu_3 (mu_1 a \, b \, c) + (- 1)^(lr(|a|)) thin mu_3 (a \, mu_1 b \, c) + (- 1)^(lr(|a|) + lr(|b|)) thin mu_3 (a \, b \, mu_1 c)\
  & #h(2em) = - thin mu_2 #scale(x: 120%, y: 120%)[\(] mu_2 (a \, b) \, c #scale(x: 120%, y: 120%)[\)] - (- 1)^((lr(|b|) + lr(|c|)) lr(|a|)) thin mu_2 #scale(x: 120%, y: 120%)[\(] mu_2 (b \, c) \, a #scale(x: 120%, y: 120%)[\)] - (- 1)^((lr(|a|) + lr(|b|)) lr(|c|)) thin mu_2 #scale(x: 120%, y: 120%)[\(] mu_2 (c \, a) \, b #scale(x: 120%, y: 120%)[\)] \,
$
where $a \, b \, c in V$ is the element of $L_oo$ algebra $V$.

The infinite number of brackets could be rewritten into a more compact
form via coalgebra, and it's coderivation. For this need, we introduce
the graded algebra $ S^c V = xor.big_(n = 0)^oo V^(and n) [- n] \, $
where we note that the monomial $a_1 a_2 dots.h.c a_n in V^(and n)$
satisfied
$
  a_1 a_2 dots.h.c a_n = (- 1)^(lr(|a_i|) lr(|a_(i + 1)|)) a_1 a_2 dots.h.c a_(i + 1) a_i dots.h.c a_n.
$
We introduce the coproduct
$Delta : S^c V arrow.r S^c V times.circle S^c V$, which is defined by
$
  Delta : a_1 dots.h.c a_n arrow.r.bar sum_(i = 1)^n sum_(sigma in upright(S h) (i \, n)) (- 1)^sigma a_(sigma (1)) dots.h.c a_(sigma (i)) times.circle a_(sigma (i + 1)) dots.h.c a_(sigma (n)) \,
$
where the shuffle map $upright(S h) (i \, n)$ is the set of all possible
ways of permutations which satisfies $sigma (1) < dots.h.c sigma (i)$
and $sigma (i + 1) < dots.h.c < sigma (n)$, and the sign $(- 1)^sigma$
is the sign of the permutation $sigma$. The coproduct is coassociative,
i.e.
$ (Delta times.circle I d) Delta = (I d times.circle Delta) Delta . $

== Derivation Side

Day V: Perturbation Theory
<day-v-perturbation-theory>
Consider a finite dimensional toy model for quantum field theory, where
the path integral is defined as
$
  Z = sqrt(det (Q)) integral_(bb(R)^n) product_(i = 1)^n frac(upright(d) x_i, sqrt(2 pi planck.reduce)) upright(e)^(- 1 / planck.reduce S [x]) \,
$
where the action function is given by
$ S [x] = 1 / 2 Q (x) - frac(1, 3 !) lambda I (x) \, $ where $Q$ is a
quadratic form, $I$ is a cubic form and $lambda$ is a coupling constant.

There are two ways to compute the path integral, one is the
non-perturbative way, which is to compute the path integral directly.
While consider the definition of the path integral above, one would
observe that the path integral would not be well-defined, since the
integral would diverge. One way to make the path integral well-defined
is to consider the embed the integration region $bb(R)^n$ into
$bb(C)^n$. Thus, using the Cauchy integral, one could compute the path
integral after changing the integration contour into
$Gamma subset bb(C)^n$, where the integration in $Gamma$ would be
convergent.

In physics, people usually consider another way to compute the path
integral, which is called perturbation theory. In perturbation theory,
one would consider the action as a perturbation of the free action,
while $lambda$ would be treated as a small parameter. Thus, the path
integral could be computed by expanding the action in terms of $lambda$
$
  Z arrow.r sum_(m = 0)^oo frac(lambda^m, m ! planck.reduce^m) ⟨(frac(1, 3 !) I (x))^m⟩ \,
$
where $⟨med⟩$ denotes the expectation value with respect to the free
action, which is given by
$
  ⟨cal(O)⟩ arrow.r sqrt(det (Q)) integral_(bb(R)^n) product_(i = 1)^n frac(upright(d) x_i, sqrt(2 pi planck.reduce)) cal(O) (x) upright(e)^(- 1 / planck.reduce S_0 [x]) \,
$
while $S_0 = 1 / 2 Q (x)$ is the free part i.e., quadratic part of the
action. Here, each term in the expansion is well-defined and could be
computed by Wick's contraction. Such a process could be explained by the
Feynman diagram, where each term in the expansion corresponds to a
multiplication of Feynman diagrams, and each Feynman diagram denotes a
pattern of Wick's contraction.

#definition(name: "Graph")[
  By a graph $Gamma$, we refer to the following data
  #set enum(numbering: "(1)", start: 1)
  + A set of vertices $V (Gamma) = { v_1 \, v_2 \, dots.h \, v_n }$, where
    each vertex $v_i$ is a point in the space-time $X$;

  + A set of half-edges $H E (Gamma)$;

  + Inclusion maps from the set of half-edges to the set of vertices
    $iota_Gamma : H E (Gamma) arrow.r V (Gamma)$, which assigns each
    half-edge to a vertex;

  + A set of edges $E (Gamma)$, which is a subset of the Cartesian product
    $H E (Gamma) times H E (Gamma)$, where each edge connects two
    half-edges;

  + For each $v in V (Gamma)$, $\# {i_Gamma^(- 1) (v)}$ is called the
    valency of $v$.
]
Using diagram to represent the process of Wick's contraction, one might
meet the problem of over-counting. A proper way to avoid the
over-counting is to consider the symmetry of the diagram i.e., the
automorphism of a diagram and isomorphism between different diagrams.

#definition(name: "Graph Isomorphism")[
  A graph isomorphism between two graphs is a pair of bijective maps
  $
    sigma_V : V (Gamma_1) arrow.r V (Gamma_2) \, quad sigma_(H E) : H E (Gamma_1) arrow.r H E (Gamma_2) \,
  $
  which are compatible with the inclusion maps:
  #align(center)[#commutative-diagram(
      padding: 0.4em,
      node((0, 0), $"HE"(Gamma)$),
      node((0, 1), $"HE"(Gamma')$),
      node((1, 0), $"V"(Gamma)$),
      node((1, 1), $"V"(Gamma')$),
      arr((0, 0), (0, 1), $sigma_("HE")$),
      arr((1, 0), (1, 1), $sigma_V$),
      arr((0, 0), (1, 0), $i_(Gamma)$),
      arr((0, 1), (1, 1), $i_(Gamma')$),
    )]
  and compatible with the edge set i.e., for any
  $a \, b in H E (Gamma)$, we have
  $
    (a \, b) in E (Gamma) arrow.l.r (sigma_(H E) (a) ,sigma_(H E) (b)) in E (Gamma ') .
  $
]
An automorphism of a graph is a graph isomorphism
$sigma_Gamma : Gamma arrow.r Gamma$, and we denote
$
  upright(A u t) (Gamma) = { sigma_Gamma : Gamma arrow.r Gamma divides sigma_Gamma "is a graph isomorphism" } .
$

Using the language above, we can describe the perturbation theory in
terms of diagrams. Consider the theory in this section, given a graph
$Gamma$, we can associate a Feynman diagram to it, which is a collection
of vertices and edges, where each vertex corresponds to an interaction
term $I (x)$ and each edge corresponds to a contraction between two
fields, which would correspond to $Q^(- 1)$. After summing overall
indices, we would obtain the contribution of this contraction pattern.
Such an identification is called the Feynman rules, which is a set of
rules to associate a Feynman diagram $Gamma$ to a term in perturbative
expansion $omega_Gamma$.

After using the Feynman rules, the perturbative component could be
rephrased as
$
  frac(1, m ! planck.reduce^m) ⟨I (x)^m⟩ = sum_(Gamma in cal(G)_m) frac(1, upright(A u t) (Gamma)) lambda^(lr(|V (Gamma)|)) planck.reduce^(l (Gamma) - 1) omega_Gamma \,
$
where $cal(G)_m$ is the set of trivalent graph with $m$ vertices and
$l (Gamma) = lr(|E (Gamma)|) - lr(|V (Gamma)|) + 1$ is the loop number
of $Gamma$. Thus, the perturbative expansion could be rewritten as
$
  ⟨upright(e)^(frac(lambda, 3 ! planck.reduce) I (x))⟩ = sum_Gamma frac(1, upright(A u t) (Gamma)) lambda^(lr(|V (Gamma)|)) planck.reduce^(l (Gamma) - 1) omega_Gamma = exp (sum_(Gamma upright(" Connected")) frac(1, upright(A u t) (Gamma)) lambda^(lr(|V (Gamma)|)) lambda^(l (Gamma) - 1)) .
$

In general, while the interaction term is
$
  I (x) = frac(lambda_3, 3 !) I_3 (x) + frac(lambda_4, 4 !) I_4 (x) + dots.h.c \,
$
then the series expansion will have all possible graphs, which could be
computed by the Feynman rules
$
  ⟨upright(e)^(1 / planck.reduce sum_(m gt.eq 3) frac(1, m !) lambda_m I_m (x))⟩ = exp (sum_(Gamma upright("Connected")) (product_(m gt.eq 3) lambda_m^(lr(|V (Gamma)_m|))) planck.reduce^(l (Gamma) - 1) omega_Gamma / lr(|upright(A u t) (Gamma)|)) \,
$
where $lr(|V (Gamma)_m|)$ is the number of vertices of type $I_m (x)$ in
the graph $Gamma$.

Day VI: UV Divergence
<day-vi-uv-divergence>
= Perturbative Quantum Field Theory
<perturbative-quantum-field-theory>
We would consider the perturbative theory of a scalar field theory,
where $cal(E) = C^oo (X)$, $X = bb(R)^d$ and the action is given by
$
  S [phi.alt] = integral_X (1 / 2 phi.alt square.stroked phi.alt + 1 / 2 m^2 phi.alt^2) upright(d)^d x \,
$
where the observables could be defined as correlators, which could be
defined as the expectation value of the product of fields
$
  ⟨cal(O)⟩ = frac(integral cal(D) [phi.alt] thin cal(O) exp [- 1 / planck.reduce integral_X upright(d)^d x thin (1 / 2 phi.alt square.stroked phi.alt + 1 / 2 m^2 phi.alt^2)], integral cal(D) [phi.alt] thin exp [- 1 / planck.reduce integral_X upright(d)^d x thin (1 / 2 phi.alt square.stroked phi.alt + 1 / 2 m^2 phi.alt^2)]) \,
$
which could be computed by Wick's contraction and Green's function
$ (square.stroked + m^2) G (x \, y) = planck.reduce delta (x - y) \, $
thus the observable
$⟨phi.alt (x_1) phi.alt (x_2) dots.h.c phi.alt (x_n)⟩$ could be computed
by
$
  ⟨phi.alt (x_1) phi.alt (x_2) dots.h.c phi.alt (x_2 n)⟩ = planck.reduce^n sum_(sigma in bb(S)_(2 n)) G (x_(sigma (1)) \, x_(sigma (2))) G (x_(sigma (3)) \, x_(sigma (4))) dots.h.c G (x_(sigma (2 n - 1)) \, x_(sigma (2 n))) \,
$
which has asymptotic expansion in the limit $x - y arrow.r oo$:
$ G (x \, y) tilde.op 1 / lr(|x - y|)^(d - 2) \, $ for $d > 2$. Such an
asymptotic expansion would lead to the divergence of the observable,
which is called ultraviolet (UV) divergence.

Consider the interaction term
$
  I_3 (phi.alt) = integral_X upright(d)^d x thin frac(lambda_3, 3 !) phi.alt^3 \, quad I_4 (phi.alt) = integral_X upright(d)^d x thin frac(lambda_4, 4 !) phi.alt^4 \,
$
which would twist the observables to a new form which could be also
computed by Feynman diagrams.

= Canonical Quantization
<canonical-quantization>
In classical mechanics, one would consider the phase space
$(M \, omega)$, where $omega$ is the symplectic form, which defined a
symplectic structure on the phase space $M$
$ omega (V_f \, V_g) = {f \, g} \, $ where
$iota_(V_f) omega = upright(d) f$. The deformation quantization would
lead to a non-commutative, where the commutative product in $C^oo (M)$
is replaced by the Moyal product:
$
  (cal(A) = bb(R) [x \, y] \, dot.op \, {med \, med}) stretch(->)^(upright(" Deformation Quantization ")) (cal(A) [[planck.reduce]] \, star.op \, [med \, med]) \,
$
where the Moyal product is defined by
$
  f star.op g = f (x \, p) exp (frac(upright(i) planck.reduce, 2) (partial_x^(⃖) arrow(partial_p) - partial_p^(⃖) arrow(partial_x))) g (x \, p) \,
$
which is a non-commutative and associative product on the algebra
$cal(A) [[planck.reduce]]$.

#proof[
  #emph[The Associativity of Moyal Product.] TBD.
]
We can derive the Moyal product from the path integral, where the action
is
$ S [x \, p] = - upright(i) integral_(bb(R)) bb(P) upright(d) bb(X) \, $
which is called #emph[topological quantum mechanics];, where the path
integral is defined as:
$
  ⟨cal(O)⟩ = frac(integral cal(D) [bb(X) \, bb(P)] thin cal(O) exp (- 1 / planck.reduce S [bb(X) \, bb(P)]), integral cal(D) [bb(X) \, bb(P)] thin exp (- 1 / planck.reduce S [bb(X) \, bb(P)])) \,
$
where the green's function could be defined as:
$
  G \(t_(1 )\,t_(2 )\) = frac(1, 2) sgn \(t_(1 ) - t_(2 )\) =
  cases(
      frac(1, 2)\, & t_(1 ) > t_(2 ) \
              0 \, & t_(1 ) = t_(2 ) \
    - frac(1, 2)\, & t_(1 ) < t_(2 )\,
  )
$
thus,
$⟨bb(X) (t_1) bb(P) (t_2)⟩ = - upright(i) planck.reduce G (t_1 \, t_2)$
and
$⟨bb(P) (t_1) bb(X) (t_2)⟩ = upright(i) planck.reduce G (t_1 \, t_2)$.

We can use the Moyal product to construct the algebra of observables,
whose product could be interpreted as the OPE and derived from the path
integral. Consider $f \, g in bb(R) [x \, p]$, thus, near the classical
solution $(x \, p)$ for each function, one can express the path integral
as
$
  ⟨f (x + bb(X) (t_1) \, p + bb(P) (t_1)) g (x + bb(X) (t_2) \, p + bb(P) (t_2))⟩ = f star.op g .
$

#proof[
  The process of Wick contraction could be realized by the
  operator $(frac(partial, partial P_0^L))_(i j)$, which is defined by
  $
    sum_(k l p q) upright(i) planck.reduce G_(k l) (t_i \, t_j) eta_(p q) (frac(partial, partial (partial^k phi.alt_p times.circle partial^l phi.alt_q)))_(i j) arrow.r^(f \, g in bb(R) [x \, p]) upright(i) planck.reduce sum_(p q) G (t_i \, t_j) omega_(p q) (frac(partial, partial (phi.alt_p times.circle phi.alt_q)))_(i j) \,
  $
  where $phi.alt = (bb(X) \, bb(P))$ and $eta equiv omega$ gives the
  contribution of the correct sign in the Moyal product. The $n$ links
  contraction would lead to the operator
  $
    n "Links Wick Contraction" arrow.long.squiggly frac(1, n !) (frac(partial, partial P_0^L))^n_(i j) \,
  $
  thus the Feynman diagram could be rewritten as
  $
    ⟨f (x + bb(X) (t_1) \, p + bb(P) (t_1)) g (x + bb(X) (t_2) \, p + bb(P) (t_2))⟩ = upright(M u l t) (upright(e)^(frac(partial, partial P_0^L)) (f (phi.alt (t_1)) times.circle g (phi.alt (t_2)))) \,
  $
  where the $upright(M u l t)$ is the multiplication of the algebra
  $cal(A) [[planck.reduce]]$. Write the definition of the contraction
  operator, we obtain OPE
  $
    f (x \, p) star.op g (x \, p) tilde.op f (x \, p) exp (frac(upright(i) planck.reduce, 2) (partial_x^(⃖) arrow(partial_p) - partial_p^(⃖) arrow(partial_x))) g (x \, p) + dots.h.c \,
  $
  where the $dots.h.c$ term is the correction term in $planck.reduce$ while
  $f \, g$ is not polynomial. If $f \, g in bb(R) [x \, y]$ is polynomial,
  then the correction term is zero, and we have the Moyal product.
]
= Counter Term in Perturbative $phi.alt^4$
<counter-term-in-perturbative-phi4>
If one consider the tree level Feynman diagram, we could proof that
there is no UV divergence. However, if one consider the loop level
Feynman diagram, some problems would occur. For example, consider the
1-loop Feynman diagram of the scalar field theory, which is given by
$
  planck.reduce^2 lambda^2 integral_((bb(R)^4)^2) upright(d) x_1 upright(d) x_2 thin phi.alt^2 (x_1) phi.alt^2 (x_2) 1 / lr(|x_1 - x_2|)^4 \,
$
where we assume $d = 4$, such an integral would be divergent
$tilde.op log r$. The physical interpreter is considering the cutting
off and set the coupling constants depending on the cutting of scaling.

After introducing the cutting off, the propagator would become:
$
  G (x \, y) = integral dif^4 k thin upright(e)^(upright(i) k (x - y)) / k^2 stretch(->)^(upright("Cutting Off")) integral_(Lambda_0 lt.eq k lt.eq Lambda_1) upright(d)^4 k thin upright(e)^(upright(i) k (x - y)) / k^2,
$
another way to interpret the cutting off is to consider the heat kernel
cutting off, which is given by
$
  P_epsilon.alt^L = integral_epsilon.alt^L upright(d) t thin upright(e)^(- t square.stroked) = integral_epsilon.alt^L frac(upright(d) t, (2 pi t)^2) thin upright(e)^(- lr(|x - y|)^2 \/ 4 t) .
$
Thus, using the heat kernel cutting off, we can rewrite the Feynman
diagram with propagator as
$
  & planck.reduce lambda^2 integral_((bb(R)^4)^2) upright(d)^4 x_1 upright(d)^4 x_2 thin phi.alt^2 (x_1) phi.alt^2 (x_2) integral_([epsilon.alt \, L]^2) frac(upright(d) t_1, (2 pi t_1)^2) frac(upright(d) t_2, (2 pi t_2)^2) thin upright(e)^(- lr(|x_1 - x_2|)^2 \/ 4 t_1) upright(e)^(- lr(|x_1 - x_2|)^2 \/ 4 t_2)\
  & = - planck.reduce lambda^2 frac(ln epsilon.alt, pi^2) integral_(bb(R)^4) upright(d)^4 x thin phi.alt^4 (x) + upright("Smooth Terms") .
$
To cancel the divergence, we need to introduce a counter term into
action $S [phi.alt]$, which is given by
$
  S arrow.r S + I_1^(upright(c t)) \, quad I_1^(upright(c t)) = frac(planck.reduce lambda^2, 4 ! pi^2) ln epsilon.alt integral_(bb(R)^4) upright(d)^4 x thin phi.alt^4 (x) \,
$
which could be interpreted as the renormalization of the coupling
constant $lambda$:
$
  lambda arrow.r lambda + frac(planck.reduce lambda^2, pi^2) ln epsilon.alt \, quad frac(upright(d) lambda, upright(d) ln epsilon.alt) = frac(planck.reduce lambda^2, pi^2) .
$

= Day XI: Factorization Algebra

First, we would define the prefactorization algebra in the open set category $"Ops"(M)$ whose objects are open subsets $U subset M$ and morphisms are inclusions $U subset V$.

Now, one could define the prefactorization algebra

#definition[
  A prefactorization algebra $cal(F)$ on $M$ would assign to each open subset $U$ with a vector space $cal(F)$, together with a maps
  $
    m_V^(U_1, U_2, dots.c, U_n): cal(F)(U_1) times.circle cal(F)(U_2) times.circle dots.c times.circle cal(F)(U_n) --> cal(F)(V),
  $
]

#example(
  name: [Prefactorization Algebra on $RR$],
  [
    Let $A$ be a unit associative $bb(K)$ algebra, we can define a prefactorization algebra $A^"fact"$ on $RR$, which satisfies
    - For an open set $U = (a,b)$, we have
    $
      A^"fact"(U) = A,
    $
    - For an open set $cal(U) = union.sq.big_(j in J) I_j$, where $I_(j)$ be an open interval, we have
    $
      A^"fact"(cal(U)) = op("colim", limits: #true)_("Finite " K subset J) (times.circle_(j in K) A).
    $
    - The structure maps $m_(V)^(U_1,dots,U_(n))$ are multiplication maps, which could be defined as
    $
      A times.circle A times.circle A --> A, quad a_1 times.circle a_2 times.circle a_3 |-> a_1 a_2 a_3.
    $
    whose associativity is equavalent to the compability of this prefactorization algebra. Such a prefactorization algebra defined the algebraic structure of a topological quantum field theory on $bb(R)$.
  ],
)

#example(
  name: [Prefactorization algebra on $[0,1]$],
  [
    Let $A$ be a $bb(K)$ algebra over $X=[0,1]$, $M$, $N$ are the left and right module respectively, thus the prefactorization algebra $A^("fact")_(X)$ is defined as
    - For an open set $U = (a,b)$, we have $A^("fact")_(X)(U) = A^("fact")$;
    - For $U = U_1 union.sq U_2$ while $U_1 subset (0,1)$ and $U_2 subset (0,1]$, we have $cal(F)(U) = A^("fact")(U_1) times.circle M$;
    - For $U = U_1 union.sq U_2$ while $U_1 subset [0,1)$ and $U_2 subset (0,1]$, we have $cal(F)(U) = N times.circle A^("fact")(U_2)$;
    - For $U = U_1 union.sq U_2 union.sq U_3$, where $U_1 subset [0,1)$, $U_2 subset (0,1)$ and $U_3 subset (0,1]$, we have
    $
      cal(F)(U) = N times.circle A^("fact")(U_2) times.circle M,
    $
  ],
)
