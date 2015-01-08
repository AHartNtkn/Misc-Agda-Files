open import Data.Nat
open import Data.Vec

-- =============== μ-recursive function ===============

{- This is how to do it properly, but the Identity function is annoying to use {- -}
data μ-RF : ℕ → Set where
 C : ∀ {k} → ℕ → μ-RF k -- Constant function
 S : μ-RF 1 -- Successor function
 U : ∀ {k} → (i : ℕ) → 1 ≤ i → i ≤ k → μ-RF k -- Identity function
 𝐬 : ∀ {k m} → μ-RF m → Vec (μ-RF k) m → μ-RF k -- Composition (Substitution) operator
 R : ∀ {k} → μ-RF k → μ-RF (2 + k) → μ-RF (suc k) -- Primitive Recursion
 μ : ∀ {k} → μ-RF (suc k) → μ-RF k -- Minimization

{-# NON_TERMINATING #-}
μEval : ∀ {k} → μ-RF k → Vec ℕ k → ℕ
μEval (C x) args = x
μEval S (x ∷ []) = suc x
μEval (U (suc zero) (s≤s _) (s≤s _)) (x ∷ args)     = x
μEval (U (suc (suc m)) (s≤s _) (s≤s p₂)) (x ∷ args) = μEval (U (suc m) (s≤s z≤n) p₂) args
μEval (𝐬 m v) args = μEval m (map (λ x → μEval x args) v)
μEval (R g h) (zero ∷ args)  = μEval g args
μEval (R g h) (suc y ∷ args) = μEval h (y ∷ (μEval (R g h) (y ∷ args)) ∷ args)
μEval (μ f) args = Minimization f (0 ∷ args) where
 Minimization : ∀ {k} → μ-RF (suc k) → Vec ℕ (suc k) → ℕ
 Minimization f (x ∷ args) with μEval f (x ∷ args)
 ... | 0 = μEval f (x ∷ args)
 ... | suc _ = Minimization f (suc x ∷ args)

-- Addition as a μ-recursive function. You can test this with;
--  μEval add (3 ∷ 4 ∷ [])
add : μ-RF 2
add = R (U 1 (s≤s z≤n) (s≤s z≤n)) (𝐬 S (U 2 (s≤s z≤n) (s≤s (s≤s z≤n)) ∷ []))
-}

data μ-RF : ℕ → Set where
 C : ∀ {k} → ℕ → μ-RF k -- Constant function
 S : μ-RF 1 -- Successor function
 U : ∀ {k} → (i : ℕ) → μ-RF k -- Identity function
 𝐬 : ∀ {k m} → μ-RF m → Vec (μ-RF k) m → μ-RF k -- Composition (Substitution) operator
 R : ∀ {k} → μ-RF k → μ-RF (2 + k) → μ-RF (suc k) -- Primitive Recursion
 μ : ∀ {k} → μ-RF (suc k) → μ-RF k -- Minimization

{-# NON_TERMINATING #-}
μEval : ∀ {k} → μ-RF k → Vec ℕ k → ℕ
μEval (C x) args = x
μEval S (x ∷ []) = suc x
μEval (U m)  []  = m
μEval (U 0) (x ∷ args) = x
μEval (U 1) (x ∷ args) = x
μEval (U (suc (suc m))) (x ∷ args) = μEval (U (suc m)) args
μEval (𝐬 m v) args = μEval m (map (λ x → μEval x args) v)
μEval (R g h) (zero ∷ args)  = μEval g args
μEval (R g h) (suc y ∷ args) = μEval h (y ∷ (μEval (R g h) (y ∷ args)) ∷ args)
μEval (μ f) args = Minimization f (0 ∷ args) where
 Minimization : ∀ {k} → μ-RF (suc k) → Vec ℕ (suc k) → ℕ
 Minimization f (x ∷ args) with μEval f (x ∷ args)
 ... | 0 = μEval f (x ∷ args)
 ... | suc _ = Minimization f (suc x ∷ args)

-- Addition as a μ-recursive function. You can test this with;
--  μEval add (3 ∷ 4 ∷ [])
add : μ-RF 2
add = R (U 1) (𝐬 S (U 2 ∷ []))

