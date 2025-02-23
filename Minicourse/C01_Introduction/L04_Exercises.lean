import Mathlib

/- 
Problem 1: Show that $\log{x+1} < \frac{1}{3} + \frac{1}{5} + \cdots + \frac{1}{2n + 1}
Hint 1: Use the induction principle.
Hint 2: Admit the fact that $\log{x} + \frac{2}{x + 1} > 1$ for all $x > 1$.
-/


/-
Problem 2: Let ${a_n}$ be an arithmetic sequence with common difference $d$, and ${b_n}$ be a geometric sequence with common ratio $q$. Given that the summation of the first $n$ terms of ${a_n+b_n}$ is $S_n = n^2 - n + 2^n - 1$, show that $d + q$ is $4$.
Hint 1: Recall that a sequence is realized as type `ℕ → ℝ`, a function from natural numbers to real numbers, with indexing starting from $1$.
Hint 2: You are expected to use `def` to define arithmetic and geometric sequences.
Hint 3: Summation of a sequence can be defined using the `∑` notation.
-/


/-
Problem 3: Let $f$ be a function on $ℝ$ such that $f(x) = \log{\frac{x}{2-x}} + a x$ for some constant $a$. Show that $a \geq 2$ if and only if $f(x)$ is monetonically increasing on $(0, 2)$.
Hint: You could admit the fact that $f$ is differentiable on $(0, 2)$.
-/


/-
Problem 4: Let $S_n$ to be the summation of the first $n$ terms of a sequence ${a_n}$, such that $a_1 = 1$ and $a_{n + 1} = S_n + 1$.
1. Show that $a_n = 2^{n-1}$.
2. Show that the summation of the first $n$ terms of ${n*a_n}$ is $(n-1)*2^n + 1$
-/


/-
Problem 5: Let $f: ℝ → ℝ$ and $g: ℝ → ℝ$, use the definition we inintroduced in the lecture to show that if `lim x → c, f x = a` and `lim x → c, g x = b`, then `lim x → c, (f + g) x = a + b`.
-/


/-
Problem 6: Use `ε-δ` definition to define uniform continuity of a function $f: ℝ → ℝ$, then show that $f(x) = x^2$ is not uniformly continuous on $ℝ$.
Hint: Uniform continuity means that for all $ε > 0$, there exists $δ > 0$ such that for all $x, y$ in the domain of $f$, $|x - y| < δ$ implies $|f(x) - f(y)| < ε$.
-/

/-
Problem 7: Use `ε-δ` definition for limits to define the most basic version of Riemann integral on $[0, 1]$, which is $I(f) := lim n -> 0, ∑ᵢ f(i/n) * 1/n$, then 
show that the integration of $f(x) = x$ on [0, 1] equals $1/2$.
-/

