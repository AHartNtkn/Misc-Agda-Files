open import Data.Nat
open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Empty
open import Data.Bool
open import Relation.Nullary

-- A straightforward definition of surjection
record _↠_ (A B : Set) : Set where
 constructor sur
 field
  to : A → B
  from : B → A
  rightInv : ∀ x → to (from x) ≡ x

-- The type of proofs that a function has no fixed point
data NoFixpoint {A : Set} (f : A → A) : Set where
 nf : (∀ a → f a ≢ a) → NoFixpoint f

data Fixpoint {A : Set} (f : A → A) : Set where
 fp : Σ[ a ∈ A ] f a ≡ a → Fixpoint f

--======== Lemmas for working with surjections, and in preparation for Cantor's theorem. Probably could be done better =======
--if f is a (higher-order) surjection and f' is the right inverse of f, then f (f' x) t = x t
lem : {A B : Set} → (to : A → A → B) → (from : (A → B) → A) → (∀ a → to (from a) ≡ a) → ∀ g t → to (from g) t ≡ g t
lem to from pr g t rewrite pr g = refl

{-
 A generalization of cantor's proof over arbitrary types. We assume that α is a function with no fixed point,
and then assume a surjection. From there, we define f as the diagnanalization of our surjection. We then define our
counter-example function g in terms of α and f. We then extract the representation of g using canLem. We define t
as the element which happens to produce g (there has to be at least one). We then prove that f (t , t) ≡ g t
by observing that the representation of g is the same diagnalization that we defined f to be. From there, the
proof goes through straightforwardly.
-}
SetFp : {T Y : Set} → (T ↠ (T → Y)) → (α : Y → Y) → Fixpoint α
SetFp {T} {Y} (sur to from ri) α = fp (to t t , e3) where
 g : T → Y
 g x = α (to x x)

 t : T
 t = from g

 e2 : to t t ≡ g t
 e2 = lem to from ri g t

 e3 : α (to t t) ≡ to t t
 e3 rewrite sym e2 = refl

SetFx : {T Y : Set} → (α : Y → Y) → NoFixpoint α → ¬ (T ↠ (T → Y))
SetFx α (nf noFix) sr with SetFp sr α
... | fp (p₁ , p₂) = noFix p₁ p₂

{-
 These functions describe what the significance of surjections are. If a surjection exists, then there exists
a function, g, which can be used to encode an arbitrary function using elements of the input type, and
vice versa.
-}
Encode1 : {A B : Set} → Σ[ g ∈ (A → B) ] ((f : B) → Σ[ n ∈ A ] (g n ≡ f)) → (A ↠ B)
Encode1 {A} {B} (g , encode) = sur g (λ z → proj₁ (encode z)) hlprlem where
 hlprlem : (x : B) → g (proj₁ (encode x)) ≡ x
 hlprlem x with encode x
 ... | _ , ∀m:gnm≡fm = ∀m:gnm≡fm

Encode2 : {A B : Set} → (A ↠ B) → Σ[ g ∈ (A → B) ] ((f : B) → Σ[ n ∈ A ] (g n ≡ f))
Encode2 {A} {B} (sur to from p₂) = to , hlprlem where 
 hlprlem : (f : B) → Σ[ n ∈ A ] (to n ≡ f)
 hlprlem f = from f , p₂ f

{-
EN12 : ∀ {A B} → ∀ x →  Encode1 {A} {B} (Encode2 x) ≡ x
EN12 (sur to (from , p₂)) = {!!}

EN21 : ∀ {A B} → ∀ x →  Encode2 {A} {B} (Encode1 x) ≡ x
EN21 (p₁ , p₂) = {!!}
-}

--Cantor's Theorem. Here, the not function is used for its lack of fixed point.
Cantor : ¬ (ℕ ↠ (ℕ → Bool))
Cantor = SetFx not (nf hlpr) where
 hlpr : (a : Bool) → not a ≢ a
 hlpr true  ()
 hlpr false ()

ChurchLem : ¬ (ℕ ↠ (ℕ → ℕ))
ChurchLem = SetFx suc (nf hlpr) where
 hlpr : (a : ℕ) → suc a ≢ a
 hlpr _ ()

{-
 This is (partly) a proof that Church's Law (the Church-Turing thesis) is false. In the original notation;
 ¬ ((f : ℕ → ℕ) → Σ[ n ∈ ℕ ] (n ⊩ f))

 Where n ⊩ f means that n is the code for the function f, under some encoding scheme. Here, g (in the type
signature) is a function which is assumed to encode all functions (ℕ → ℕ) using an ℕ. Turing machines are
supposed to be a method to encode all computable functions using natural numbers. In a certain sense, this is
a proof that functions are, in general, not computable.

See here for more info;
https://existentialtype.wordpress.com/2012/08/09/churchs-law/
-}
Church : ¬ (Σ[ g ∈ (ℕ → ℕ → ℕ) ] ((f : ℕ → ℕ) → Σ[ n ∈ ℕ ] (g n ≡ f)))
Church = ChurchLem ∘ Encode1

