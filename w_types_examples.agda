-- This file contains the definitions of W- and WI-types, as well as our
-- example inductive types represented as W- and WI-types.

open import Data.Nat
open import Data.Bool
open import Data.String
open import Data.List
open import Data.Sum.Base

open import tsig_and_examples

open Sig

-- W-type
data W (S : Set) (P : S → Set) : Set where
  sup : (s : S) → (P s → W S P) → W S P

-- Indexed W-type
data WI (I : Set) (S : I → Set) (P : (i : I) → S i → I → Set) : I → Set where
  sup : (i : I) (s : S i) → ((j : I) → P i s j → WI I S P j) → WI I S P i

-- ℕ W-type

S₁ = Bool -- a.k.a. ⊤ ⊎ ⊤, 2 constructors with no non-recursive args

P₁ : S₁ → Set
P₁ false = ⊥ -- zero has no recursive args
P₁ true = ⊤ -- suc has 1 recursive arg

zero' : W S₁ P₁
zero' = sup false λ ()

suc' : W S₁ P₁ → W S₁ P₁
suc' n = sup true λ {tt → n}

-- ℕ WI-type

I₂ = ⊤ -- 1 sort

S₂ : I₂ → Set
S₂ tt = ⊤ ⊎ ⊤ 

P₂ : (i : I₂) → S₂ i → I₂ → Set
P₂ tt (inj₁ tt) tt = ⊥ -- zero has no recursive args
P₂ tt (inj₂ tt) tt = ⊤ -- suc has 1 recursive arg

zero'' : WI I₂ S₂ P₂ tt
zero'' = sup tt (inj₁ tt) λ {tt → λ ()}

suc'' : WI I₂ S₂ P₂ tt → WI I₂ S₂ P₂ tt
suc'' n = sup tt (inj₂ tt) λ {tt → λ {tt → n}}

-- Lam W-type

S₃ = String ⊎ String ⊎ ⊤ 

P₃ : S₃ → Set
P₃ (inj₁ s) = ⊥ -- var has no recursive args
P₃ (inj₂ (inj₁ s)) = ⊤ -- abs has 1 recursive arg
P₃ (inj₂ (inj₂ tt)) = Bool -- app has 2 recursive args

var' : String → W S₃ P₃
var' s = sup (inj₁ s) λ ()

abs' : String → W S₃ P₃ → W S₃ P₃
abs' s l = sup (inj₂ (inj₁ s)) λ {tt → l}
  
app' : W S₃ P₃ → W S₃ P₃ → W S₃ P₃
app' m n = sup (inj₂ (inj₂ tt)) λ {true → m ; false → n}

-- Lam WI-type

I₄ = ⊤

S₄ : I₄ → Set
S₄ tt = String ⊎ String ⊎ ⊤

P₄ : (i : I₄) → S₄ i → I₄ → Set
P₄ tt (inj₁ s) tt = ⊥
P₄ tt (inj₂ (inj₁ s)) tt = ⊤
P₄ tt (inj₂ (inj₂ tt)) tt = Bool

var'' : String → WI I₄ S₄ P₄ tt
var'' s = sup tt (inj₁ s) λ {tt → λ ()}

abs'' : String → WI I₄ S₄ P₄ tt → WI I₄ S₄ P₄ tt
abs'' s l = sup tt (inj₂ (inj₁ s)) λ {tt → λ {tt → l}}

app'' : WI I₄ S₄ P₄ tt → WI I₄ S₄ P₄ tt → WI I₄ S₄ P₄ tt
app'' m n  = sup tt (inj₂ (inj₂ tt)) λ {tt → λ {true → m ; false → n}}

-- InfTree W-type

S₅ = ⊤ ⊎ ⊤

P₅ : S₅ → Set
P₅ (inj₁ tt) = ⊥ -- ε∞ has no recursive args
P₅ (inj₂ tt) = ℕ -- sp∞ has ℕ-many recursive args

ε∞' : W S₅ P₅
ε∞' = sup (inj₁ tt) λ ()

sp∞' : (ℕ → W S₅ P₅) → W S₅ P₅
sp∞' f = sup (inj₂ tt) f

-- InfTree WI-type

I₆ = ⊤

S₆ : I₆ → Set
S₆ tt = ⊤ ⊎ ⊤

P₆ : (i : I₆) → S₆ i → I₆ → Set
P₆ tt (inj₁ tt) tt = ⊥
P₆ tt (inj₂ tt) tt = ℕ

ε∞'' : WI I₆ S₆ P₆ tt
ε∞'' = sup tt (inj₁ tt) (λ {tt → λ ()})

sp∞'' : (ℕ → WI I₆ S₆ P₆ tt) → WI I₆ S₆ P₆ tt
sp∞'' f = sup tt (inj₂ tt) λ {tt → f}

{-
-- List W-type

S₇ : U → Set
S₇ = λ A → ⊤ ⊎ El A

P₇ : (A : U) → S₇ A → Set
P₇ A (inj₁ tt) = ⊥
P₇ A (inj₂ a) = ⊤

[]' : (A : U) → W (S₇ A) (P₇ A) 
[]' A = sup (inj₁ tt) λ ()

_∷'_ : (A : U) → El A → W (S₇ A) (P₇ A) → W (S₇ A) (P₇ A)
_∷'_ A a l = sup (inj₂ a) λ {tt → l}

-- List WI-type

I₈ = ⊤

S₈ : (A : U) → I₈ → Set
S₈ A tt = ⊤ ⊎ El A 

P₈ : (A : U) (i : I₈) → S₈ A i → I₈ → Set
P₈ A tt (inj₁ tt) tt = ⊥
P₈ A tt (inj₂ a) tt = ⊤

[]'' : (A : U) → WI I₈ (S₈ A) (P₈ A) tt
[]'' A = sup tt (inj₁ tt) (λ {tt → λ ()})

_∷''_ : (A : U) → El A → WI I₈ (S₈ A) (P₈ A) tt → WI I₈ (S₈ A) (P₈ A) tt
_∷''_ A a l = sup tt (inj₂ a) λ {tt → λ {tt → l}}
-}

-- NF/NE WI-type

I₉ = Bool

S₉ : I₉ → Set
S₉ false = ⊤ ⊎ String -- NF
S₉ true = String ⊎ ⊤ -- NE

P₉ : (i : I₉) → S₉ i → I₉ → Set
P₉ false (inj₁ tt) false = ⊥ -- ne has 0 NF recursive args
P₉ false (inj₁ tt) true = ⊤ -- ne has 1 NE recursive arg
P₉ false (inj₂ s) false = ⊤ -- lam has 1 NF recursive arg
P₉ false (inj₂ s) true = ⊥ -- lam has 0 NE recursive args
P₉ true (inj₁ s) false = ⊥ -- var has 0 NF recursive args
P₉ true (inj₁ s) true = ⊥ -- var has 0 NE recursive args
P₉ true (inj₂ tt) false = ⊤ -- app has 1 NF recursive arg
P₉ true (inj₂ tt) true = ⊤ -- app has 1 NE recursive arg

ne' : WI I₉ S₉ P₉ true → WI I₉ S₉ P₉ false
ne' e = sup false (inj₁ tt) λ {true → λ {tt → e} ; false → λ ()}

lam' : String → WI I₉ S₉ P₉ false → WI I₉ S₉ P₉ false
lam' s f = sup false (inj₂ s) λ {true → λ () ; false → λ {tt → f}}

var'NE : String → WI I₉ S₉ P₉ true
var'NE s = sup true (inj₁ s) (λ {true → λ () ; false → λ ()})

app'NE : WI I₉ S₉ P₉ true → WI I₉ S₉ P₉ false → WI I₉ S₉ P₉ true
app'NE e f = sup true (inj₂ tt) λ {true → λ {tt → e} ; false → λ {tt → f}}

-- TreeForest WI-type

I₁₀ = Bool

S₁₀ : (A : U) → I₁₀ → Set
S₁₀ A false = ⊤ -- Tree
S₁₀ A true = ⊤ ⊎ ⊤ -- Forest

P₁₀ : (A : U) (i : I₁₀) → S₁₀ A i → I₁₀ → Set
P₁₀ A false tt false = ⊥ -- Tree has no recursive Tree args
P₁₀ A false tt true = ⊤ -- Tree has 1 recursive Forest arg
P₁₀ A true (inj₁ tt) false = ⊥ -- εF has no recursive args
P₁₀ A true (inj₁ tt) true = ⊥ -- εF has no recursive args
P₁₀ A true (inj₂ tt) false = ⊤ -- consF has 1 Tree recursive arg
P₁₀ A true (inj₂ tt) true = ⊤ --consF has 1 Forest recursive arg

sp' : (A : U) → WI I₁₀ (S₁₀ A) (P₁₀ A) true → WI I₁₀ (S₁₀ A) (P₁₀ A) false
sp' A f = sup false tt (λ {true → λ {tt → f} ; false → λ ()})

εF' : (A : U) → WI I₁₀ (S₁₀ A) (P₁₀ A) true 
εF' A = sup true (inj₁ tt) λ {true → λ () ; false → λ ()}

consF' : (A : U) → WI I₁₀ (S₁₀ A) (P₁₀ A) false → WI I₁₀ (S₁₀ A) (P₁₀ A) true →
         WI I₁₀ (S₁₀ A) (P₁₀ A) true
consF' A t f = sup true (inj₂ tt) (λ {true → λ {tt → f} ; false → λ {tt → t}})


 
