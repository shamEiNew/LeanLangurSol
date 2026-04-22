import LeanLangur.LangurLang

/-!
# LangurLeaps: LangurLang Examples

This module provides examples of programs written in `LangurLang` using the `#leap` command
and the `climb%` macro. It includes implementations of summation and primality testing.
-/

open LangurLang

/-!
A simple `LangurLang` program illustrating assignments and conditionals.
-/
#leap
  n := 3; m := 4 + 5;
  if (n ≤ 4) {n := (5 + 3 + (2 * 7));} else {n := 2; m := 7}
  return

/-!
A program to calculate the sum of the first `n` natural numbers.
-/
#leap
  n := 10; sum := 0;
  i := 1;
  while (i ≤ n) {sum := sum + i; i := i + 1} return

/--
A simple value for testing primality.
-/
def eg.n := 59

/-!
Primality test for `n = 59` in `LangurLang`.
-/
open eg in
#leap
  i := 2;
  is_prime := 1;
  while (i < n && is_prime = 1) {
    if (i ∣ n) {
      is_prime := 0
    } else {};
    i := i + 1
  };
  if (is_prime = 1) {
    print s!"{n} is prime"
  } else {
    print s!"{n} is not prime; divisor: {i - 1}"
  }
  return


/--
A `climb%` macro usage to check the primality of `n = 57`.
-/
def primality  :=
  climb%
    n := 57;
    i := 2;
    is_prime := 1;
    while (i < n && is_prime = 1) {
    if (i ∣ n) {
      is_prime := 0
    } else {};
    i := i + 1
    };
    return s!"Primality of {n}: {is_prime == 1}"

#eval primality

/-!
Another `climb%` example checking the primality of `n = 59`.
-/
#eval climb%
    i := 2;
    is_prime := 1;
    while (i < n && is_prime = 1) {
    if (i ∣ n) {
      is_prime := 0
    } else {};
    i := i + 1
    }
    from%
    n := 59;
    return s!"Primality of {n}: {is_prime == 1}"

/-!
## Exercise

Implement a `for` loop construct in LangurLang following `C` syntax:
```c
for (init; cond; step) { body }
```
-/
