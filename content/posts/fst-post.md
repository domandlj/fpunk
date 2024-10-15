---
title: "Formal Verification"
date: 2024-10-12
draft: false
---


# Welocome

Software verification simpliy consists in checking that a implementation meets it's specification. Seems straightforward ha? Well, it's really complicated. Inn _the wild_ it's usually never done.  

Let's see why, assume we are a hired dev and some wants a Haskell program that computes the sum of the $n$ first natural numbers (realistic example, isn't it?). We can be more formal saying

**Specification**:
$$
\forall n \in {\bf{N}}, {\tt program} \ n=\sum_{i=0}^n i 
$$
**Implementation:**
Now let's try to implement it, assume we have a type `Nat` that represents natural numbers.

```haskell
program :: Nat -> Nat
program 0 = 0
program n = n + program (n-1) 
```

**Verification**
Ok, our program seems to meet the spec. Let's prove it by induction in $n$ 
*Base case*. trivially true.
*Indctive step.* As _inductive hypothesis_ assume the spec holds for $n$, let's see that it holds for $n+1$.

$$
\begin{align*}
\text{program}(n + 1) & = n + 1 + \text{program}(n) \quad \text{(by definition)} \\
& = n + 1 + \sum_{i=1}^{n} i \quad \text{(by inductive hypothesis)} \\
& = \sum_{i=1}^{n + 1} i \quad \text{(by the formul}\text{ integers)}
\end{align*}
$$

That's it our program is correct.







