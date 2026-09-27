# Two reductions of the second buyer that fail

Both instances concern the two-unit model of the paper. Their data are in
`obstructions.json`, and `verify.py` replays every computation below.

## 1. Replacing the second buyer by its mean

Fix $B_1=3$, $S_1=1/10$, and let $S_2$ be $1/10$ or $2$ with probability $1/2$
each. If $B_2$ is $1$ or $3$ with probability $1/2$ each, independently of the
seller, then first-best welfare is $21/4$, the best posted price obtains
$201/40$, and the ratio is $67/70$. If $B_2$ is replaced by its mean $2$, the
price $z=2$ obtains first-best welfare $5$ and the ratio is $1$.

With the other three marginal laws held fixed, compressing the second buyer to
its mean can therefore make an instance easier. A reduction to a deterministic
second buyer has to change the other laws as well.

## 2. The optimized first-unit value is not convex in the second buyer

We use the normalized limiting problem: common escaping buyer tails with first
moment one, bounded bodies $1\le Z_2\le Z_1\le2$, sellers $0\le S_1\le S_2$, and

$$
S_2\sim\tfrac1{10}\delta_0+\tfrac9{10}\delta_2,
\qquad
g_p(s,z)=\mathbf 1_{\{s<p\}}\bigl(1+(z-s)\mathbf 1_{\{p\le z\}}\bigr).
$$

Buyer and seller vectors are independent. The tail-price event has total gain
two, so the gain cap is

$$
\Gamma(p)=\mathbb E g_p(S_1,Z_1)+\mathbb E g_p(S_2,Z_2)\le2
\quad\text{at every body price }p. \tag{1}
$$

Let $\mu$ be the law of $Z_2$. For $\lambda>0$ define

$$
V_\lambda(\mu)=\sup\{G-\lambda M:(1)\text{ holds}\},\qquad
G=2+\sum_{q=1}^2\mathbb E(Z_q-S_q)_+,\quad M=\mathbb E(S_1+S_2),
$$

where the supremum ranges over every admissible law of $(Z_1,S_1)$ on the full
continuous domains.

**Theorem.** For every $\lambda\ge25/72$,

$$
V_\lambda(\delta_1)\le\frac{10}3-\frac95\lambda,\qquad
V_\lambda(\delta_2)=\frac{10}3-\frac83\lambda,\qquad
V_\lambda\Bigl(\frac{\delta_1+\delta_2}2\Bigr)\ge\frac{10}3-\frac{32}{15}\lambda .
$$

Consequently
$V_\lambda\bigl(\tfrac{\delta_1+\delta_2}2\bigr)-\tfrac12\bigl(V_\lambda(\delta_1)+V_\lambda(\delta_2)\bigr)\ge\lambda/10>0$,
and $V_\lambda$ is not convex. The range $0.72908\le\beta\le0.729081$ of the
paper gives $\lambda=(1-\beta)/\beta>25/72$.

**Lemma.** Let $\nu=\tfrac13\delta_1+\tfrac{2}{3p^2}\mathbf 1_{(1,2)}(p)\,\mathrm dp$,
a positive measure of mass $2/3$. If $\lambda\ge25/72$, then for $1\le z\le2$ and
$0\le s\le2$,

$$
1+(z-s)_+-\lambda s\le1+\int g_p(s,z)\,\nu(\mathrm dp). \tag{2}
$$

*Proof.* Write $D(s,z)$ for the right side of (2) minus the left side, and
integrate the kernel in the three cases.

If $0\le s<1$, then $D=s\bigl(\lambda+\tfrac2{3z}\bigr)\ge0$.

If $1\le s<z\le2$, then

$$
D=\frac2{3s}-\frac13+\frac{2(z-s)^2}{3sz}-z+(1+\lambda)s
=\frac{(11s-12)^2}{72s}+\Bigl(\lambda-\frac{25}{72}\Bigr)s
+(2-z)\Bigl(1-\frac2{3s}+\frac s{3z}\Bigr)\ge0,
$$

and the last factor is positive because $s\ge1$.

If $1\le z\le s\le2$, only prices above $s$ trade, and
$D=\tfrac{2-s}{3s}+\lambda s\ge0$. $\square$

*Proof of the theorem.* For $Z_2=1$, averaging (2) over $(Z_1,S_1)$ gives
$G_1-\lambda M_1\le1+\int\Gamma_1\,\mathrm d\nu$, where the subscript refers to
the first unit. The second-unit gains are $\Gamma_2(1)=1/5$ and
$\Gamma_2(p)=1/10$ for $1<p<2$, so (1) and the two masses $1/3$ of $\nu$ give
$G_1-\lambda M_1\le1+\tfrac13\cdot\tfrac95+\tfrac13\cdot\tfrac{19}{10}=\tfrac{67}{30}$.
Since the second unit contributes $11/10-\tfrac95\lambda$, this is the first
bound.

For $Z_2=2$, buyer order forces $Z_1=2$. With $r=\Pr(S_1<2)$,
$c=\mathbb E[S_1\mathbf 1_{\{S_1<2\}}]$ and $w=r+1/10$, the gain limit as
$p\uparrow2$ is $3w-c$, so $T:=2w-c\le\min\{2w,2-w\}\le4/3$. Then
$G=2+T$, $M=4-T$, and $G-\lambda M=2-4\lambda+(1+\lambda)T\le\tfrac{10}3-\tfrac83\lambda$.
Equality holds for $S_1\sim\tfrac{17}{30}\delta_0+\tfrac{13}{30}\delta_2$.

For the mixture we take $Z_1=Z_2\sim(\delta_1+\delta_2)/2$ and
$S_1\sim\tfrac7{10}\delta_0+\tfrac4{15}\delta_1+\tfrac1{30}\delta_2$. For body
prices $p\le1$ the total gain is $\bigl(\tfrac7{10}+\tfrac1{10}\bigr)\tfrac52=2$,
and for $1<p\le2$ it is
$\tfrac7{10}\cdot2+\tfrac4{15}\cdot\tfrac32+\tfrac1{10}\cdot2=2$, so (1) holds. Direct expectation gives
$G=10/3$ and $M=32/15$. $\square$

The mixed example has price-welfare ratio $31/41$, above the conjectured
two-unit constant. It refutes the convexity argument for compressing the second
buyer and says nothing about the constant itself.
