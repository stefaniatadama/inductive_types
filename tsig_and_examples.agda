-- This file contains the definition of our small theory of signatures,
-- as well as specific examples of what we construct in general.

open import Data.Nat 
open import Data.String
open import Data.Fin
open import Data.List
open import Data.Bool hiding ( T )
open import Data.Char
open import Agda.Builtin.Equality

data ⊥ : Set where

data ⊤ : Set where
  tt : ⊤

-- Used in Arg instead of Set
-- Replaced Set with U, A : Set with A : U, A with El A
data U : Set where
  nat : U
  string : U
  --vec : U → El nat → U
  --maybe : U → U
  --π : (a : U)(b : El a → U) → U

El : U → Set
El nat = ℕ
El string = String
--El (vec A n) = Vec (El A) n
--El (maybe S) = Maybe (El S)
--El (π A B) = Π (El A) (λ el_a → El (B el_a))


----- Defining data types -----

{-
data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ
-}

data Lam : Set where
  var : String → Lam
  abs : String → Lam → Lam
  app : Lam → Lam → Lam

data InfTree : Set where
  ε∞ : InfTree
  sp∞ : (ℕ → InfTree) → InfTree

data NF : Set -- β normal form
data NE : Set -- neutral terms

data NF where
  ne : NE → NF
  lam : String → NF → NF

data NE where
  var : String → NE
  app : NE → NF → NE

-- TreeForest is an alternative definition of RoseTree using inductive types
data Tree (A : U) : Set
data Forest (A : U) : Set

data Tree A where
  sp : Forest A → Tree A -- node

data Forest A where
  εF : Forest A -- []
  consF : Tree A → Forest A → Forest A -- ∷
 

----- Defining Sig -----

-- List U is used for when we have something like
-- suc : (ℕ → Ord) → Ord for ordinals, in that case
-- (ℕ ∷ []) would be the List U argument, the
-- arguments to the function type argument (ℕ → Ord).
data Arg (n : ℕ) : Set where
  nrec : U → Arg n
  rec : List U → Fin n → Arg n

-- Constructor
data Con (n : ℕ) : Set where
  cn : List (Arg n) → Con n

-- sorts denotes the number of mutual definitions we have.
-- For each sort, we need a list of constructors. This is
-- given by cns which maps each each sort index to a list
-- of constructors. A constructor is given by a list of
-- arguments (we can ignore the last type in the constructors
-- as that will always be the type we are defining). The
-- arguments can either be empty, or non-recursive (they
-- do not mention the type/s we are constructing), or recursive
-- (they talk about the type/s we are constructing), in which
-- case they might be referring to either one of the types
-- in the different sorts.
record Sig : Set where
  constructor sig
  field
    sorts : ℕ
    cns : Fin sorts → List (Con sorts) 
    
open Sig


----- Defining signatures for data types -----

ℕSig : Sig
sorts ℕSig = 1
cns ℕSig = λ {zero → cn [] -- zero
                    ∷ cn (rec [] zero ∷ []) -- suc
                    ∷ []}

LamSig : Sig
sorts LamSig = 1
cns LamSig = λ {zero → cn (nrec string ∷ []) -- var
                     ∷ cn (nrec string ∷ rec [] zero  ∷ [])  -- abs
                     ∷ cn (rec [] zero ∷ rec [] zero ∷ []) -- app
                     ∷ []}

InfTreeSig : Sig
sorts InfTreeSig = 1
cns InfTreeSig = λ {zero → cn [] -- ε∞
                         ∷ cn (rec (nat ∷ []) zero ∷ []) -- sp∞
                         ∷ []}

consNF : Fin 2 → List (Con 2)
-- NF constructors
consNF zero = cn (rec [] (suc zero) ∷ []) -- ne
            ∷ cn (nrec string ∷ rec [] zero ∷ []) -- lam
            ∷ []
-- NE constructors
consNF (suc zero) = cn (nrec string ∷ []) -- var
                  ∷ cn (rec [] (suc zero) ∷ rec [] zero ∷ []) -- app
                  ∷ []

NFNESig : Sig
sorts NFNESig = 2
cns NFNESig = consNF 

consTF : (A : U) → Fin 2 → List (Con 2)
consTF A zero = cn (rec [] (suc zero) ∷ []) -- sp
              ∷ []
consTF A (suc zero) = cn [] --εF
                      ∷ cn (rec [] zero ∷ rec [] (suc zero) ∷ []) -- consF
                      ∷ []

TreeForestSig : (A : U) → Sig
sorts (TreeForestSig A) = 2
cns (TreeForestSig A) = consTF A


----- Defining algebras for data types -----

record ℕAlg : Set₁ where
  field
    N : Set
    z : N
    s : N → N
open ℕAlg

record LamAlg : Set₁ where
  field
    L : Set
    v : String → L
    ab : String → L → L
    ap : L → L → L
open LamAlg

record InfTreeAlg : Set₁ where
  field
    IT : Set
    e : IT
    s : (ℕ → IT) → IT
open InfTreeAlg

record NormalFormAlg : Set₁ where
  field
    F : Set
    E : Set
    n : E → F
    l : String → F → F
    v : String → E
    a : E → F → E
open NormalFormAlg

record TreeForestAlg (A : U) : Set₁ where
  field
    T : U → Set 
    F : U → Set
    s : F A → T A
    e : F A
    c : T A → F A → F A
open TreeForestAlg


----- Defining morphisms for datatypes -----

record ℕMor (n₁ n₂ : ℕAlg) : Set where
  field
    f : N n₁ → N n₂
    f_z : f (z n₁) ≡ z n₂
    f_s : (x : N n₁) → f ((s n₁) x) ≡ (s n₂) (f x) 
    
record LamMor (l₁ l₂ : LamAlg) : Set where
  field
    f : L l₁ → L l₂
    f_v : (s : String) →  f ((v l₁) s) ≡ (v l₂) s
    f_ab : (s : String) (l : L l₁) → f ((ab l₁) s l) ≡ (ab l₂) s (f l)
    f_ap : (m n : L l₁) → f ((ap l₁) m n) ≡ (ap l₂) (f m) (f n)

record InfTreeMor (t₁ t₂ : InfTreeAlg) : Set where
  field
    f : IT t₁ → IT t₂
    f_e : f (e t₁) ≡ e t₂
    f_s : (g : ℕ → IT t₁) → f ((s t₁) g) ≡ (s t₂) (λ n → f (g n))

record NormalFormMor (nf₁ nf₂ : NormalFormAlg) : Set where
  field
    f_f : F nf₁ → F nf₂
    f_e : E nf₁ → E nf₂
    f_n : (e : E nf₁) → f_f ((n nf₁) e) ≡ (n nf₂) (f_e e) 
    f_l : (s : String) (f : F nf₁) → f_f ((l nf₁) s f) ≡ (l nf₂) s (f_f f)
    f_v : (s : String) → f_e ((v nf₁) s) ≡ (v nf₂) s    
    f_a : (e : E nf₁) (f : F nf₁) → f_e ((a nf₁) e f) ≡ (a nf₂) (f_e e) (f_f f)

record TreeForestMor (A : U) (t₁ t₂ : TreeForestAlg A) : Set where
  field 
    f_t : (T t₁) A → (T t₂) A
    f_f : (F t₁) A → (F t₂) A
    f_s : (f : (F t₁) A) → f_t ((s t₁) f) ≡ (s t₂) (f_f f)
    f_e : f_f (e t₁) ≡ (e t₂)
    f_c : (t : (T t₁ A)) (f : (F t₁ A)) → f_f ((c t₁) t f) ≡ (c t₂) (f_t t) (f_f f)


----- Defining iterators for data types -----

-- The iterator specifies the unique morphism between the initial
-- algebra and any other algebra.
Itℕ : {M : Set} → M → (M → M) → ℕ → M
Itℕ z s zero = z
Itℕ z s (suc n) = s (Itℕ z s n)

ItLam : {M : Set} → (String → M) → (String → M → M) → (M → M → M)→ Lam → M
ItLam v ab ap (var x) = v x
ItLam v ab ap (abs s l) = ab s (ItLam v ab ap l)
ItLam v ab ap (app l₁ l₂) = ap (ItLam v ab ap l₁) (ItLam v ab ap l₂)

ItInfTree : {M : Set} → M → ((ℕ → M) → M) → InfTree → M
ItInfTree e s ε∞ = e
ItInfTree e s (sp∞ x) = s (λ n → ItInfTree e s (x n))

-- We can define these as one iterator with return type ((NF → M) × (NE → N))
ItNormalFormNF : {M N : Set} → (N → M) → (String → M → M) → (String → N) → (N → M → N) →
                 NF → M
ItNormalFormNE : {M N : Set} → (N → M) → (String → M → M) → (String → N) → (N → M → N) →
                 NE → N

{-
ItNormalForm : {M N : Set} → (N → M) → (String → M → M) → (String → N) → (N → M → N) →
               (NF → M) × (NE → M)
-}
ItNormalFormNF n l v a (ne e) = n (ItNormalFormNE n l v a e)
ItNormalFormNF n l v a (lam s nf) = l s (ItNormalFormNF n l v a nf)

ItNormalFormNE n l v a (var x) = v x
ItNormalFormNE n l v a (app p q) = a (ItNormalFormNE n l v a p) (ItNormalFormNF n l v a q)

ItTreeForestT : {A : U} {M N : (A : U) → Set} → (N A → M A) → N A → (M A → N A → N A) →
                Tree A → M A
ItTreeForestF : {A : U} {M N : (A : U) → Set} → (N A → M A) → N A → (M A → N A → N A) →
                Forest A → N A

ItTreeForestT {A} {Tree} {Forest} s ε c (sp f) = s (ItTreeForestF {A} {Tree} {Forest} s ε c f)

ItTreeForestF {A} s ε c εF = ε
ItTreeForestF {A} {Tree} {Forest} s ε c (consF t f) = c (ItTreeForestT {A} {Tree} {Forest} s ε c t)
  (ItTreeForestF {A} {Tree} {Forest} s ε c f)


----- Defining more general iterators for data types -----

ℕInit : ℕAlg
ℕInit = record { N = ℕ ; z = zero ; s = suc }

fℕ : (X : ℕAlg) → ℕ → N X
fℕ X zero = z X
fℕ X (suc n) = (s X) (fℕ X n)

Itℕ-Mor : (X : ℕAlg) → ℕMor ℕInit X
Itℕ-Mor X = record { f = fℕ X ; f_z = refl ; f_s = λ _ → refl } 

-- Example
BoolℕAlg : ℕAlg
BoolℕAlg = record { N = Bool ; z = true ; s = not }

even : ℕ → Bool
even zero = true
even (suc n) = not (even n)

MorℕEven : ℕMor ℕInit BoolℕAlg
MorℕEven = record { f = even ; f_z = refl ; f_s = λ n → refl }

MorℕEven' : ℕMor ℕInit BoolℕAlg
MorℕEven' = Itℕ-Mor BoolℕAlg

LamInit : LamAlg
LamInit = record { L = Lam ; v = var ; ab = abs ; ap = app }

fLam : (X : LamAlg) → Lam → L X
fLam X (var x) = (v X) x
fLam X (abs x l) = (ab X) x (fLam X l)
fLam X (app l₁ l₂) = (ap X) (fLam X l₁) (fLam X l₂)

ItLam-Mor : (X : LamAlg) → LamMor LamInit X
ItLam-Mor X = record { f = fLam X ; f_v = λ s → refl ; f_ab = λ s l → refl ; f_ap = λ m n → refl }

InfTreeInit : InfTreeAlg
InfTreeInit = record { IT = InfTree ; e = ε∞ ; s = sp∞ }

fInfTree : (X : InfTreeAlg) → InfTree → IT X
fInfTree X ε∞ = e X
fInfTree X (sp∞ x) = (s X) (λ n → fInfTree X (x n))

ItInfTree-Mor : (X : InfTreeAlg) → InfTreeMor InfTreeInit X
ItInfTree-Mor X = record { f = fInfTree X ; f_e = refl ; f_s = λ g → refl }

NormalFormInit : NormalFormAlg
NormalFormInit = record { F = NF ; E = NE ; n = ne ; l = lam ; v = var ; a = app }

f_fNormalForm : (X : NormalFormAlg) → NF → F X
f_eNormalForm : (X : NormalFormAlg) → NE → E X

f_fNormalForm X (ne x) = (n X) (f_eNormalForm X x)
f_fNormalForm X (lam str f) = (l X) str (f_fNormalForm X f) 

f_eNormalForm X (var str) = (v X) str
f_eNormalForm X (app e f) = (a X) (f_eNormalForm X e) (f_fNormalForm X f)

ItNormalForm-Mor : (X : NormalFormAlg) → NormalFormMor NormalFormInit X
ItNormalForm-Mor X =  record
                       { f_f = f_fNormalForm X ; f_e = f_eNormalForm X ;
                         f_n = λ e → refl ; f_l = λ s f → refl ; f_v = λ s → refl ;
                         f_a = λ e f → refl } 

TreeForestInit : (A : U) →  TreeForestAlg A
TreeForestInit _ = record { T = λ S → Tree S ; F = λ S → Forest S ;
                            s = sp ;
                            e = εF ; c = consF }

f_tTreeForest : {A : U} (X : TreeForestAlg A) → Tree A →  T X A
f_fTreeForest : {A : U} (X : TreeForestAlg A) → Forest A → F X A

f_tTreeForest X (sp f) = (s X) (f_fTreeForest X f)

f_fTreeForest X εF = e X
f_fTreeForest X (consF t f) = (c X) (f_tTreeForest X t) (f_fTreeForest X f)

ItTreeForest-Mor : {A : U} (X : TreeForestAlg A) → TreeForestMor A (TreeForestInit A) X
ItTreeForest-Mor X = record
                       { f_t = f_tTreeForest X ; f_f = f_fTreeForest X ;
                         f_s = λ f → refl ;
                         f_e = refl ; f_c = λ t f → refl }
