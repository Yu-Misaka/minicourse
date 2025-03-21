import Mathlib

/- Problem 1
Let `a`, `b`, `c` be positive real numbers satisfying `a + b + c = 1`, show that
`a^2 / b + b^2 / c + c^2 / a ≥ 1`. -/

/- Problem 2
Let `a`, `b`, `c` be positive real number satisfying `a + b + c = 3`, show that 
`1 / (a ^ 3 * (b + c)) + 1 / (b ^ 3 * (a + c)) + 1 / (c ^ 3 * (a + b)) ≥ 3 / 2`. -/

/- Problem 3
Given `f(x) = e ^ x - a * x - b`, show that if `f(x) ≥ 0` for all `x`,
then `a ≥ e`. -/

/- Problem 4
Let `f(x) = x ^ 2 - 2 * x + a`, `g(x) = e ^ x - x - 1`, show that `g(x) < f(x)`
for all positive `x`. -/

/- **Remark**: The following problems are fundamental in analysis. If you finished
any of them, it will be a great work, and you are encouraged to merge your work 
into our `Calculus Game` project. -/

/- Problem 5 - Zhu Yelai
Use the limit definition from Lecture 1, define derivative of function and show
your definition is compatible with definition in Mathlib4, literally `deriv` or
`fderiv`. You will need this if you want to finish problems below. -/
#check deriv

/- Problem 6
Use the limit definition from Lecture 1, state and prove
Fermat's lemma (about stationery point). -/

/- Problem 7 - Zhang Yirui
Use the limit definition from Lecture 1, state and prove Lagrange's mean
value theorem. -/

/- Problem 8
Use the limit definition from Lecture 1, state and prove L'Hopital's rule for
finite limit in both numinator and demumintaor. -/

/- Problem 9
Use the limit definition from Lecture 1, state and prove any Cauchy's sequence
is convergent in ℝ. -/

/- Problem 10
Use the limit definition from Lecture 1, prove Heine-Cantor theorem.
Let `a` be a real number, with function `f` has limit `L` at `a`. Then for every 
sequence {a n}, if `lim n → ∞, a n = a`, we have `lim n → ∞, f(a n) = L`-/

/- Problem 11
Use the limit definition from Lecture 1, state and prove Bolzano–Weierstrass 
theorem. -/
