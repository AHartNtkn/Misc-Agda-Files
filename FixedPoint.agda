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
  rightInv : Σ[ g ∈ (B → A) ] (∀ x → to (g x) ≡ x)

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
counter-example function g in terms of α and f. We then extract the representation of g using canLem. We define t₀
as the element which happens to produce g (there has to be at least one). We then prove that f (t₀ , t₀) ≡ g t₀
by observing that the representation of g is the same diagnalization that we defined f to be. From there, the
proof goes through straightforwardly.
-}
SetFp : {T Y : Set} → (T ↠ (T → Y)) → (α : Y → Y) → Fixpoint α
SetFp {T} {Y} (sur to (from , ff'x≡x)) α = fp (f t₀ t₀ , e3) where
 f : T → T → Y
 f = to

 g : T → Y
 g x = α (f x x)

 t₀ : T
 t₀ = from g

 e2 : f t₀ t₀ ≡ g t₀
 e2 = lem to from ff'x≡x g t₀

 e3 : α (f t₀ t₀) ≡ f t₀ t₀
 e3 rewrite sym e2 = refl

SetFx : {T Y : Set} → (α : Y → Y) → NoFixpoint α → ¬ (T ↠ (T → Y))
SetFx α (nf noFix) sr with SetFp sr α
... | fp (p₁ , p₂) = noFix p₁ p₂

postulate
 funex : {A B : Set} → {f g : A → B} → (∀ a → f a ≡ g a) → f ≡ g

{-
 These functions describe what the significance of surjections are. If a surjection exists, then there exists
a function, g, which can be used to encode an arbitrary function using elements of the input type, and
vice versa.
-}
Encode1 : {A B : Set} → Σ[ g ∈ (A → A → B) ] ((f : A → B) → Σ[ n ∈ A ] (∀ m → g n m ≡ f m)) → (A ↠ (A → B))
Encode1 {A} {B} (g , encode) = sur g ((λ z → proj₁ (encode z)) , hlprlem) where
 hlprlem : (x : A → B) → g (proj₁ (encode x)) ≡ x
 hlprlem x with encode x
 ... | _ , ∀m:gnm≡fm rewrite funex ∀m:gnm≡fm = refl

Encode2 : {A B : Set} → (A ↠ (A → B)) → Σ[ g ∈ (A → A → B) ] ((f : A → B) → Σ[ n ∈ A ] (∀ m → g n m ≡ f m))
Encode2 {A} {B} (sur to (from , p₂)) = to , hlprlem where 
 hlprlem : (f : A → B) → Σ[ n ∈ A ] ((m : A) → to n m ≡ f m)
 hlprlem f = from f , lem to from p₂ f

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
supposed to be a method to encode all computable functions using natural numbers. In ETT, all functions
ℕ → ℕ are computable (this needs to be proved elsewhere). This theorem shows that there are computable
functions which are not encodable, no matter what encoding scheme you choose.

See here for more info;
https://existentialtype.wordpress.com/2012/08/09/churchs-law/
-}
Church : ¬ (Σ[ g ∈ (ℕ → ℕ → ℕ) ] ((f : ℕ → ℕ) → Σ[ n ∈ ℕ ] (∀ m → g n m ≡ f m)))
Church o = ChurchLem (Encode1 o)
