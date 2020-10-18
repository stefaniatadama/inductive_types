-- This file contains the construction of the WI-type algebra, and our
-- attempt at the WI-type iterator.

{-# OPTIONS --rewriting #-}

open import Data.Nat hiding (zero ; suc)
open import Data.List hiding (map)
open import Data.Product hiding (map)
open import Data.Bool 
open import Data.Fin
open import Data.String hiding (_++_)
open import Data.Sum.Base
open import Agda.Builtin.Equality 
open import Agda.Builtin.Equality.Rewrite
open import Relation.Binary.PropositionalEquality

open import general
open import tsig_and_examples
open import w_types_examples

open Sig
open Alg
open Mor

_=Fin_ : {n : ℕ} → Fin n → Fin n → Bool
zero =Fin zero = true
zero =Fin suc _ = false
suc _ =Fin zero = false
suc m =Fin suc n = m =Fin n

_≡Fin_ : {n : ℕ} → (h i : Fin n) → (h =Fin i) ≡ true → h ≡ i
(zero ≡Fin zero) refl = refl
(suc h ≡Fin suc i) p = cong suc {h} {i} ((h ≡Fin i) p)

{-
-- Redefining inspect
data Singleton {A : Set} (x : A) : Set where
  _with≡_ : (y : A) → x ≡ y → Singleton x

inspect' : ∀ {A : Set} (x : A) → Singleton x
inspect' x = x with≡ refl
-}


----- Constructing the carrier -----

-- I = Fin (sorts S) for S : Sig

-- S

argToSetNrec : (S : Sig) → Arg (sorts S) → Set
argToSetNrec S (nrec t) = El t
argToSetNrec S (rec lst fin) = ⊤

-- Returns the type of non-recursive args of the given constructor
conToSetNrec : (S : Sig) → Con (sorts S) → Set
conToSetNrec S (cn []) = ⊤
conToSetNrec S (cn (x ∷ xs)) = argToSetNrec S x × conToSetNrec S (cn xs)

-- Constructor (lam : String → NF → NF) of NF
--    conToSetNrec (S)     (cons.) 
eg8 = conToSetNrec NFNESig (cn (nrec string ∷ rec [] zero ∷ [])) 
-- Σ String (λ x → Σ ⊤ (λ x₁ → ⊤))

-- Returns the sum type of non-recursive args of the constructors of a given sort
listConToSetNrec : (S : Sig) → List (Con (sorts S)) → Set
listConToSetNrec S [] = ⊥ 
listConToSetNrec S (x ∷ xs) = conToSetNrec S x ⊎ listConToSetNrec S xs

-- Constructors of NF 
eg9 = listConToSetNrec NFNESig (cns NFNESig zero)
-- Σ ⊤ (λ x → ⊤) ⊎ Σ String (λ x → Σ ⊤ (λ x₁ → ⊤)) ⊎ ⊥

makeS : (S : Sig) → Fin (sorts S) → Set
makeS S i = listConToSetNrec S (cns S i)

-- Examples

ℕS = makeS ℕSig zero
-- ⊤ ⊎ Σ ⊤ (λ x → ⊤) ⊎ ⊥

LamS = makeS LamSig zero
-- Σ String (λ x → ⊤) ⊎ Σ String (λ x → Σ ⊤ (λ x₁ → ⊤)) ⊎ Σ ⊤ (λ x → Σ ⊤ (λ x₁ → ⊤)) ⊎ ⊥

InfTreeS = makeS InfTreeSig zero
-- ⊤ ⊎ Σ ⊤ (λ x → ⊤) ⊎ ⊥

NFS1 = makeS NFNESig zero
-- Σ ⊤ (λ x → ⊤) ⊎ Σ String (λ x → Σ ⊤ (λ x₁ → ⊤)) ⊎ ⊥
NFS2 = makeS NFNESig (suc zero)
-- Σ String (λ x → ⊤) ⊎ Σ ⊤ (λ x → Σ ⊤ (λ x₁ → ⊤)) ⊎ ⊥

TFS1 = makeS (TreeForestSig nat) zero
-- Σ ⊤ (λ x → ⊤) ⊎ ⊥
TFS2 = makeS (TreeForestSig nat) (suc zero)
-- Σ ⊤ (λ x → ⊤) ⊎ ⊥

-- P

recArg : List U → Set
recArg [] = ⊤
recArg (x ∷ xs) = El x × recArg xs

argToSetRec : (S : Sig) → Arg (sorts S) → Fin (sorts S) → Set
argToSetRec S (nrec x) j = ⊥
argToSetRec S (rec lst fin) j with fin =Fin j
argToSetRec S (rec lst fin) j | false = ⊥
argToSetRec S (rec lst fin) j | true = recArg lst

-- Returns the sum type of recursive args (with respect to a particular sort) of a given constructor 
conToSetRec : (S : Sig) → Con (sorts S) → Fin (sorts S) → Set
conToSetRec S (cn []) j = ⊥
conToSetRec S (cn (x ∷ xs)) j = argToSetRec S x j ⊎ conToSetRec S (cn xs) j

-- Constructor (lam : String → NF → NF) of NF
--     conToSetRec (S)     (cons)                                (fin)
eg10 = conToSetRec NFNESig (cn (nrec string ∷ rec [] zero ∷ [])) zero
-- ⊥ ⊎ ⊤ ⊎ ⊥

-- Constructor (sp∞ : (ℕ → InfTree) → InfTree) of InfTree
eg11 = conToSetRec InfTreeSig (cn (rec (nat ∷ []) zero ∷ [])) zero
-- Σ ℕ (λ x → ⊤) ⊎ ⊥ 

-- Given the (S i) value and the fin (j), parses the (S i) value and returns the P value i.e.
-- the number of recursive args of a given constructor
-- Figures out which constructor we're passing based on its (S i) value
listConToSetRec : (S : Sig) (xs : List (Con (sorts S))) (xsp : listConToSetNrec S xs) →
                  Fin (sorts S) → Set
listConToSetRec S (x ∷ xs) (inj₁ xp) j = conToSetRec S x j
listConToSetRec S (x ∷ xs) (inj₂ xsp) j = listConToSetRec S xs xsp j

-- Like P₉ false (inj₂ s) false = ⊤ -- lam has 1 NF recursive arg
eg12 = listConToSetRec NFNESig (cns NFNESig zero) (inj₂ (inj₁ ("x" , tt , tt))) zero
-- ⊥ ⊎ ⊤ ⊎ ⊥
-- Like P₉ false (inj₂ s) true = ⊥ -- lam has 0 NE recursive args
eg13 = listConToSetRec NFNESig (cns NFNESig zero) (inj₂ (inj₁ ("x" , tt , tt))) (suc zero)
-- ⊥ ⊎ ⊥ ⊎ ⊥

-- i is the sort we are constructing
-- s is the constructor we are using, together with non-recursive args
-- j is the sort for which we will give the number of recursive args required by the constructor s
makeP : (S : Sig) (i : Fin (sorts S)) → makeS S i → Fin (sorts S) → Set 
makeP S i s j = listConToSetRec S (cns S i) s j

-- Examples

-- makeS ℕSig zero = ⊤ ⊎ Σ ⊤ (λ x → ⊤) ⊎ ⊥
ℕP = makeP ℕSig zero (inj₁ tt) zero
-- ⊥ 
ℕP2 = makeP ℕSig zero (inj₂ (inj₁ (tt , tt))) zero
-- ⊤ ⊎ ⊥ 

-- makeS LamSig zero = Σ String (λ x → ⊤) ⊎ Σ String (λ x → Σ ⊤ (λ x₁ → ⊤)) ⊎
-- Σ ⊤ (λ x → Σ ⊤ (λ x₁ → ⊤)) ⊎ ⊥
LamP = makeP LamSig zero (inj₁ ("x" , tt)) zero
-- ⊥ ⊎ ⊥
LamP2 = makeP LamSig zero (inj₂ (inj₁ ("x" , tt , tt))) zero
-- ⊥ ⊎ ⊤ ⊎ ⊥
LamP3 = makeP LamSig zero (inj₂ (inj₂ (inj₁ (tt , tt , tt)))) zero
-- ⊤ ⊎ ⊤ ⊎ ⊥

-- makeS NFNESig zero = Σ ⊤ (λ x → ⊤) ⊎ Σ String (λ x → Σ ⊤ (λ x₁ → ⊤)) ⊎ ⊥
-- makeS NFNESig (suc zero) = Σ String (λ x → ⊤) ⊎ Σ ⊤ (λ x → Σ ⊤ (λ x₁ → ⊤)) ⊎ ⊥
NFP = makeP NFNESig zero (inj₁ (tt , tt)) zero -- ne
-- ⊥ ⊎ ⊥
NFP2 = makeP NFNESig zero (inj₁ (tt , tt)) (suc zero) -- ne
-- ⊤ ⊎ ⊥ 
NFP3 = makeP NFNESig zero (inj₂ (inj₁ ("x" , tt , tt))) zero -- lam
-- ⊥ ⊎ ⊤ ⊎ ⊥
NFP4 = makeP NFNESig zero (inj₂ (inj₁ ("x" , tt , tt))) (suc zero) -- lam
-- ⊥ ⊎ ⊥ ⊎ ⊥
NFP5 = makeP NFNESig (suc zero) (inj₁ ("x" , tt)) zero -- var
-- ⊥ ⊎ ⊥
NFP6 = makeP NFNESig (suc zero) (inj₁ ("x" , tt)) (suc zero) -- var
-- ⊥ ⊎ ⊥
NFP7 = makeP NFNESig (suc zero) (inj₂ (inj₁ (tt , tt , tt))) zero -- app
-- ⊥ ⊎ ⊤ ⊎ ⊥
NFP8 = makeP NFNESig (suc zero) (inj₂ (inj₁ (tt , tt , tt))) (suc zero) -- app
-- ⊤ ⊎ ⊥ ⊎ ⊥

-- makeS InfTreeSig zero = ⊤ ⊎ Σ ⊤ (λ x → ⊤) ⊎ ⊥
InfTreeP = makeP InfTreeSig zero (inj₁ tt) zero
-- ⊥ 
InfTreeP2 = makeP InfTreeSig zero (inj₂ (inj₁ (tt , tt))) zero
-- Σ ℕ (λ x → ⊤) ⊎ ⊥

-- makeS (TreeForestSig nat) zero =  Σ ⊤ (λ x → ⊤) ⊎ ⊥
-- makeS (TreeForestSig nat) (suc zero) = Σ ⊤ (λ x → ⊤) ⊎ ⊥
TreeForestP = makeP (TreeForestSig nat) zero (inj₁ (tt , tt)) zero
-- ⊥ ⊎ ⊥
TreeForestP2 = makeP (TreeForestSig nat) zero (inj₁ (tt , tt)) (suc zero) 
-- ⊤ ⊎ ⊥
TreeForestP3 = makeP (TreeForestSig nat) (suc zero) (inj₁ tt) zero
-- ⊥
TreeForestP4 = makeP (TreeForestSig nat) (suc zero) (inj₁ tt) (suc zero)
-- ⊥
TreeForestP5 = makeP (TreeForestSig nat) (suc zero) (inj₂ (inj₁ (tt , tt , tt))) zero
-- ⊤ ⊎ ⊥ ⊎ ⊥
TreeForestP6 = makeP (TreeForestSig nat) (suc zero) (inj₂ (inj₁ (tt , tt , tt))) (suc zero)
-- ⊥ ⊎ ⊤ ⊎ ⊥

-- Constructor examples

-- C-u C-u C-c C-, to normalise goal
tstzero : WI (Fin (sorts ℕSig)) (makeS ℕSig) (makeP ℕSig) zero
tstzero = sup zero (inj₁ tt) λ {zero → λ ()}

tstsuc : WI (Fin (sorts ℕSig)) (makeS ℕSig) (makeP ℕSig) zero →
         WI (Fin (sorts ℕSig)) (makeS ℕSig) (makeP ℕSig) zero
tstsuc n = sup zero (inj₂ (inj₁ (tt , tt))) λ {zero → λ {(inj₁ tt) → n}}


tstne : WI (Fin (sorts NFNESig)) (makeS NFNESig) (makeP NFNESig) (suc zero) →
        WI (Fin (sorts NFNESig)) (makeS NFNESig) (makeP NFNESig) zero
tstne e = sup zero (inj₁ (tt , tt)) λ {zero → λ {(inj₁ ()) ; (inj₂ ())} ; (suc zero) → λ {(inj₁ tt) → e}}


tstlam : String → WI (Fin (sorts NFNESig)) (makeS NFNESig) (makeP NFNESig) zero →
         WI (Fin (sorts NFNESig)) (makeS NFNESig) (makeP NFNESig) zero
tstlam s f = sup zero (inj₂ (inj₁ (s , tt , tt))) λ {zero → λ {(inj₂ (inj₁ tt)) → f} ;
             (suc zero) → λ {(inj₁ ()) ; (inj₂ (inj₁ ())) ; (inj₂ (inj₂ ()))}}

tstvar : String →
         WI (Fin (sorts NFNESig)) (makeS NFNESig) (makeP NFNESig) (suc zero)
tstvar s = sup (suc zero) (inj₁ (s , tt)) (λ {zero → λ {(inj₁ ()) ; (inj₂ ())} ;
           (suc zero) → λ {(inj₁ ()) ; (inj₂ ())}})

tstapp : WI (Fin (sorts NFNESig)) (makeS NFNESig) (makeP NFNESig) (suc zero) →
         WI (Fin (sorts NFNESig)) (makeS NFNESig) (makeP NFNESig) zero →
         WI (Fin (sorts NFNESig)) (makeS NFNESig) (makeP NFNESig) (suc zero)
tstapp e f = sup (suc zero) (inj₂ (inj₁ (tt , tt , tt)))
             λ {zero → λ {(inj₂ (inj₁ tt)) → f} ;
               (suc zero) → λ {(inj₁ tt) → e ; (inj₂ (inj₁ ())) ; (inj₂ (inj₂ ()))}}
               

tstε∞ : WI (Fin (sorts InfTreeSig)) (makeS InfTreeSig) (makeP InfTreeSig) zero
tstε∞ = sup zero (inj₁ tt) (λ {zero → λ ()})

tstsp∞ : (ℕ → WI (Fin (sorts InfTreeSig)) (makeS InfTreeSig) (makeP InfTreeSig) zero) →
         WI (Fin (sorts InfTreeSig)) (makeS InfTreeSig) (makeP InfTreeSig) zero
tstsp∞ f = sup zero (inj₂ (inj₁ (tt , tt))) (λ {zero → λ {(inj₁ (n , tt)) → f n}})


----- Defining constructors (constructing Alg) -----

sumEq : {A B A' B' : Set} → A ≡ A' → B ≡ B' → (A ⊎ B) ≡ (A' ⊎ B')
sumEq refl refl = refl

=to≡ : {S : Sig} (i j : Fin (sorts S)) (p : (i =Fin j) ≡ true) → i ≡ j 
=to≡ i j p = (i ≡Fin j) p

module _(S : Sig) (srt : Fin (sorts S)) (l : List (Arg (sorts S))) where

  -- Returns the (s : Si) in
  -- sup : (i : I) (s : S i) → ((j : I) → P i s j → WI I S P j) → WI I S P i
  makeSi : (xs : List (Con (sorts S))) → cn l ∈ xs → conToSetNrec S (cn l) →
           listConToSetNrec S xs
  makeSi (.(cn l) ∷ xs) hd nrec_ars = inj₁ nrec_ars
  makeSi (x ∷ xs) (tl p) nrec_ars = inj₂ (makeSi xs p nrec_ars)

  lstToCon : (xs : List (Con (sorts S)))
             (p : (cn l) ∈ xs) (nrec_ars : conToSetNrec S (cn l)) (j : Fin (sorts S)) →
             listConToSetRec S xs (makeSi xs p nrec_ars) j → conToSetRec S (cn l) j
  lstToCon (.(cn l) ∷ xs) hd nars j lst = lst
  lstToCon (x ∷ xs) (tl p) nars j lst = lstToCon xs p nars j lst 

  -- Returns the ((j : I) → P i s j → WI I S P j) in
  -- sup : (i : I) (s : S i) → ((j : I) → P i s j → WI I S P j) → WI I S P i
  makeWI : (p : (cn l) ∈ cns S srt) (nrec_ars : conToSetNrec S (cn l)) →
           ((j : Fin (sorts S)) → conToSetRec S (cn l) j →
           WI (Fin (sorts S)) (makeS S) (makeP S) j) →
           (j : Fin (sorts S)) → makeP S srt (makeSi (cns S srt) p nrec_ars) j →
           WI (Fin (sorts S)) (makeS S) (makeP S) j
  makeWI p nrec_ars f j   with cns S srt
  makeWI hd nrec_ars f j     | .(cn l) ∷ xs =  f j
  makeWI (tl p) nrec_ars f j | x ∷ xs = λ lst → f j (lstToCon xs p nrec_ars j lst)

  ctaToWI : (lst : List U) (j : Fin (sorts S)) →
            conTypeAux (WI (Fin (sorts S)) (makeS S) (makeP S)) lst j → recArg lst → 
            WI (Fin (sorts S)) (makeS S) (makeP S) j
  ctaToWI [] j cta ra = cta
  ctaToWI (x ∷ xs) j cta (fst , snd) = ctaToWI xs j (cta fst) snd

eg14 = makeSi NFNESig zero (nrec string ∷ rec [] zero ∷ []) (cns NFNESig zero) (tl hd)
       ("x" , tt , tt)
-- inj₂ (inj₁ ("x" , tt))

conToSetNrecSnocAux : (S : Sig) (srt : Fin (sorts S)) (x : Arg (sorts S)) → conToSetNrec S (cn []) →
                      (ar : argType (WI (Fin (sorts S)) (makeS S) (makeP S)) x) →
                      argToSetNrec S x
conToSetNrecSnocAux S srt (nrec x) prev el = el
conToSetNrecSnocAux S srt (rec lst fin) prev el = prev

conToSetNrecSnoc : (S : Sig) (srt : Fin (sorts S)) (l : List (Arg (sorts S)))
                   (x : Arg (sorts S)) → conToSetNrec S (cn l) → (ar : argType (WI
                   (Fin (sorts S)) (makeS S) (makeP S)) x) → conToSetNrec S (cn (l ∷ʳ x))
conToSetNrecSnoc S srt [] a prev el = conToSetNrecSnocAux S srt a prev el , prev
conToSetNrecSnoc S srt (x ∷ xs) a (fst , snd) el = fst , conToSetNrecSnoc S srt xs a snd el  

eg15 = conToSetNrecSnoc NFNESig zero [] (nrec string) tt "x"
-- "x" , tt

eg16 = conToSetNrecSnoc NFNESig zero (nrec string ∷ []) (rec [] zero) ("x" , tt)
       (sup zero (inj₁ (tt , tt)) λ {zero → λ {(inj₁ ()) ; (inj₂ ())} ; (suc zero) →
       λ {(inj₁ tt) → sup (suc zero) (inj₁ ("y" , tt)) λ j → λ {(inj₁ ()) ; (inj₂ ())}} }) 
-- "x" , tt , tt

lToSnocAux[] : (S : Sig) (srt : Fin (sorts S)) (lst : List U) (fin : Fin (sorts S)) →
               conTypeAux (WI (Fin (sorts S)) (makeS S) (makeP S)) lst fin →
               recArg lst → WI (Fin (sorts S)) (makeS S) (makeP S) fin
lToSnocAux[] S srt [] fin ar ra = ar
lToSnocAux[] S srt (x ∷ xs) fin ar (el_x , ra) = ctaToWI S srt [] xs fin (ar el_x) ra

-- Mutual definition 
lToSnoc : (S : Sig) (srt : Fin (sorts S)) (l : List (Arg (sorts S))) (lst : List U)
          (fin j : Fin (sorts S)) → (conToSetRec S (cn l) j →
          WI (Fin (sorts S)) (makeS S) (makeP S) j) →
          conTypeAux (WI (Fin (sorts S)) (makeS S) (makeP S)) lst fin →
          (conToSetRec S (cn (l ∷ʳ rec lst fin)) j → WI (Fin (sorts S)) (makeS S) (makeP S) j)

lToSnocAux∷ : (S : Sig) (srt : Fin (sorts S)) (lst : List U) (fin j : Fin (sorts S)) →
              (x : Arg (sorts S)) (xs : List (Arg (sorts S))) →
              (conToSetRec S (cn (x ∷ xs)) j → WI (Fin (sorts S)) (makeS S) (makeP S) j) →
              conTypeAux (WI (Fin (sorts S)) (makeS S) (makeP S)) lst fin →
              argToSetRec S x j ⊎ conToSetRec S (cn (xs ++ rec lst fin ∷ [])) j →
              WI (Fin (sorts S)) (makeS S) (makeP S) j
              
lToSnocAux∷ S srt lst fin j (nrec x)  xs f ar (inj₂ a) =
  lToSnoc S srt xs lst fin j (λ c → f (inj₂ c)) ar a 
lToSnocAux∷ S srt lst fin j (rec lst₁ fin₁) xs f ar a     with fin₁ =Fin j
lToSnocAux∷ S srt lst fin j (rec lst₁ fin₁) xs f ar (inj₂ a) | false =
  lToSnoc S srt xs lst fin j (λ c → f (inj₂ c)) ar a 
lToSnocAux∷ S srt lst fin j (rec lst₁ fin₁) xs f ar (inj₁ x) | true = f (inj₁ x)
lToSnocAux∷ S srt lst fin j (rec lst₁ fin₁) xs f ar (inj₂ y) | true =
  lToSnoc S srt xs lst fin j (λ c → f (inj₂ c)) ar y 

-- Rewrites the function ((j : I) → P i s j → WI I S P j) in
-- sup : (i : I) (s : S i) → ((j : I) → P i s j → WI I S P j) → WI I S P i
-- to accomodate for a snocced argument
-- Pattern matching on l - we want to leave everything that was there before in its place
lToSnoc S srt [] lst fin j f ar a       with fin =Fin j | inspect (_=Fin_ fin) j
lToSnoc S srt [] lst fin j f ar (inj₁ ())  | false      | _ 
lToSnoc S srt [] lst fin j f ar (inj₂ ())  | false      | _
lToSnoc S srt [] lst fin j f ar (inj₁ x)   | true       | Reveal_·_is_.[ eq ]
  rewrite =to≡ {S} fin j eq = lToSnocAux[] S srt lst j ar x
  -- supposed to write fin instead of j but fin = j
--lToSnoc S srt [] lst fin j f ar (inj₁ x) | true | Relation.Binary.PropositionalEquality.[ eq ]
--  rewrite =to≡ {S} fin j eq = lToSnocAux[] S srt lst j ar x -- Replace for Agda 2.6.1
lToSnoc S srt (x ∷ xs) lst fin j f ar a = lToSnocAux∷ S srt lst fin j x xs f ar a

lToSnocNrec : (S : Sig) (srt : Fin (sorts S)) (l : List (Arg (sorts S))) (x : U) (j : Fin (sorts S)) →
              (conToSetRec S (cn l) j → WI (Fin (sorts S)) (makeS S) (makeP S) j) →
              (conToSetRec S (cn (l ∷ʳ nrec x)) j → WI (Fin (sorts S)) (makeS S) (makeP S) j)
lToSnocNrec S srt [] x j f (inj₁ ())
lToSnocNrec S srt [] x j f (inj₂ ())
lToSnocNrec S srt (l ∷ ls) x j f (inj₁ a) = f (inj₁ a)
lToSnocNrec S srt (l ∷ ls) x j f (inj₂ y) = lToSnocNrec S srt ls x j (λ c → f (inj₂ c)) y

module _(S : Sig) (srt : Fin (sorts S)) (l : List (Arg (sorts S))) where

  conToSetRecSnoc : (x : Arg (sorts S)) →
                    ((j : Fin (sorts S)) → conToSetRec S (cn l) j →
                    WI (Fin (sorts S)) (makeS S) (makeP S) j) →
                    argType (WI (Fin (sorts S)) (makeS S) (makeP S)) x →
                    (j : Fin (sorts S)) → conToSetRec S (cn (l ∷ʳ x)) j →
                    WI (Fin (sorts S)) (makeS S) (makeP S) j
  conToSetRecSnoc (nrec x) f ar j = lToSnocNrec S srt l x j (f j) 
  conToSetRecSnoc (rec lst fin) f ar j = lToSnoc S srt l lst fin j (f j) ar  

makeConsWAux : (S : Sig) (srt : Fin (sorts S)) (l₁ l₂ : List (Arg (sorts S))) →
               (p : (cn (l₁ ++ l₂) ∈ cns S srt)) → conToSetNrec S (cn l₁) →
               ((j : Fin (sorts S)) → conToSetRec S (cn l₁) j →
               WI (Fin (sorts S)) (makeS S) (makeP S) j) →
               conType srt (WI (Fin (sorts S)) (makeS S) (makeP S)) (cn l₂)
makeConsWAux S srt l₁ [] p nrec_ars rec_ars =
  sup srt (makeSi S srt l₁ (cns S srt) p nrec_ars) (makeWI S srt l₁ p nrec_ars rec_ars)
makeConsWAux S srt l₁ (x ∷ xs) p nrec_ars rec_ars = 
  λ ar → makeConsWAux S srt (l₁ ∷ʳ x) xs p (conToSetNrecSnoc S srt l₁ x nrec_ars ar) 
          (conToSetRecSnoc S srt l₁ x rec_ars ar)

makeConsW : (S : Sig) (srt : Fin (sorts S)) (c : Con (sorts S)) → c ∈ cns S srt →
            conType srt (WI (Fin (sorts S)) (makeS S) (makeP S)) c
makeConsW S srt (cn x) p = makeConsWAux S srt [] x p tt (λ j → λ ())

WAlg : (S : Sig) → Alg S
WAlg S  = record { carriers = WI (Fin (sorts S)) (makeS S) (makeP S) ;
                   cons = λ srt c p → makeConsW S srt c p } 

tstMC = conToSetNrecSnoc NFNESig zero (nrec string ∷ []) (rec [] zero) ("my_str" , tt) (sup zero (inj₁ (tt , tt)) λ {zero → λ {(inj₁ ()); (inj₂ ())} ; (suc zero) → λ {(inj₁ tt) → sup (suc zero) (inj₁ ("y" , tt)) (λ {zero → λ {(inj₁ ()); (inj₂ ())} ; (suc zero) →  λ {(inj₁ ()); (inj₂ ())}})}})
-- "my_str" , tt , tt

tstMC2 = conToSetRecSnoc NFNESig zero (nrec string ∷ []) (rec [] zero) (λ j → lToSnocNrec NFNESig zero [] string j (λ ())) ((sup zero (inj₁ (tt , tt)) λ {zero → λ {(inj₁ ()); (inj₂ ())} ; (suc zero) → λ {(inj₁ tt) → sup (suc zero) (inj₁ ("y" , tt)) (λ {zero → λ {(inj₁ ()); (inj₂ ())} ; (suc zero) →  λ {(inj₁ ()); (inj₂ ())}})}}))

-- Examples

-- ℕ

zeroWI = makeConsW ℕSig zero (cn []) hd
-- sup zero (inj₁ tt) (λ j ())

sucWI = makeConsW ℕSig zero (cn (rec [] zero ∷ [])) (tl hd)
-- λ ar → sup zero (inj₂ (inj₁ tt))
-- (λ j lst → (lToSnoc ℕSig zero [] [] zero j (λ ()) ar | zero =Fin j | Reveal_·_is_.[ refl ]) lst)
-- (want) λ ar → sup zero (inj₂ (inj₁ ( tt , tt))) λ {zero → λ {(inj₁ tt) → ar}}


-- Example

even'' : WI (Fin (sorts ℕSig)) (makeS ℕSig) (makeP ℕSig) zero → Bool
even'' (sup .zero (inj₁ tt) x) = true
even'' (sup .zero (inj₂ (inj₁ (tt , tt))) x) = not (even'' (x zero (inj₁ tt)))

MorℕEven'''' : Mor ℕSig (WAlg ℕSig) BoolℕAlg'
MorℕEven'''' = record { f = λ {zero → even''} ; 
                         eq = λ {zero → λ c → λ {hd pf → refl ; (tl hd) pf → refl}} }

ℕ→WI : ℕ → WI (Fin (sorts ℕSig)) (makeS ℕSig) (makeP ℕSig) zero
ℕ→WI ℕ.zero = sup zero (inj₁ tt) (λ j ())
ℕ→WI (ℕ.suc n) = sup zero (inj₂ (inj₁ (tt , tt))) λ {zero → λ {(inj₁ tt) → ℕ→WI n}}

isEven : ℕ → Bool
isEven n = (f MorℕEven'''') zero (ℕ→WI n)

-- Example 2

car : WI (Fin (sorts LamSig)) (makeS LamSig) (makeP LamSig) zero → Lam
car (sup .zero (inj₁ (s , tt)) x) = var s
car (sup .zero (inj₂ (inj₁ (s , tt , tt))) x) = abs s (car (x zero (inj₂ (inj₁ tt))))
car (sup .zero (inj₂ (inj₂ (inj₁ (tt , tt , tt)))) x) =
  app (car (x zero (inj₁ tt))) (car (x zero (inj₂ (inj₁ tt))))

MorLam : Mor LamSig (WAlg LamSig) LamInit'
MorLam = record { f = λ {zero → car} ;
                  eq = λ {zero → λ c → λ {hd xs → refl ;
                                           (tl hd) xs → refl ;
                                           (tl (tl hd)) xs → refl}} }


----- Deriving the iterator -----

finEqPf : {n : ℕ} (fin : Fin n) → fin =Fin fin ≡ true
finEqPf zero = refl
finEqPf (suc fin) = finEqPf fin

postulate finEq : {n : ℕ} (fin : Fin n) → fin =Fin fin ≡ true
{-# REWRITE finEq #-}

-- Given details from a WI-type, returns the constructor and its proof
findCon : (S : Sig) (l : List (Con (sorts S))) → listConToSetNrec S l →
          Σ (Con (sorts S)) (λ c → c ∈ l)
findCon S (x ∷ xs) (inj₁ _) = x , hd
findCon S (x ∷ xs) (inj₂ y) = proj₁ rest , tl (proj₂ rest)
  where
    rest = findCon S xs y

module _(S : Sig) (A : Alg S) where

  -- {-# TERMINATING #-} -- to be removed
  funcsW : (srt : Fin (sorts S)) → WI (Fin (sorts S)) (makeS S) (makeP S) srt → carriers A srt

  mapConW : (lst : List U) (fin : Fin (sorts S)) (s : ⊤) →
            (recArg lst → WI (Fin (sorts S)) (makeS S) (makeP S) fin)
            → conTypeAux (carriers A) lst fin
  mapConW [] fin s p = funcsW fin (p s)
  mapConW (x ∷ xs) fin s p = λ el_x → mapConW xs fin s (λ ra → p (el_x , ra))

  argTypeWToCarr : (x : Arg (sorts S)) → argToSetNrec S x →
                   ((j : Fin (sorts S)) → argToSetRec S x j →
                   WI (Fin (sorts S)) (makeS S) (makeP S) j) → argType (carriers A) x
  argTypeWToCarr (nrec x) s p = s
  argTypeWToCarr (rec lst fin) s p = mapConW lst fin s (p fin) 

  -- Extracts non-recursive and recursive arguments from WI-type and transforms them
  -- into arguments for algebra A
  argsWToCarr : (srt : Fin (sorts S)) (c : Con (sorts S)) (s : conToSetNrec S c) →
                ((j : Fin (sorts S)) → conToSetRec S c j → WI (Fin (sorts S)) (makeS S) (makeP S) j)
                → args srt (carriers A) c
  argsWToCarr srt (cn []) s p = s
  argsWToCarr srt (cn (x ∷ xs)) (fst , snd) p =
    argTypeWToCarr x fst (λ j ar → p j (inj₁ ar)) ,
    argsWToCarr srt (cn xs) snd (λ j cr → p j (inj₂ cr)) 

  -- Passing the list of constructors as an argument
  makeArgs : (srt : Fin (sorts S)) (l : List (Con (sorts S)))
             (s : listConToSetNrec S l) → ((j : Fin (sorts S)) → listConToSetRec S l s j →
             WI (Fin (sorts S)) (makeS S) (makeP S) j) → args srt (carriers A) (proj₁ (findCon S l s))
  makeArgs srt (x ∷ xs) (inj₁ y) p = argsWToCarr srt x y p
  makeArgs srt (x ∷ xs) (inj₂ y) p = makeArgs srt xs y p
 
  funcsW srt (sup .srt s p) = apply S A srt c (cons A srt c pf) (makeArgs srt (cns S srt) s p)
    where
      c,pf = findCon S (cns S srt) s
      c = proj₁ c,pf
      pf = proj₂ c,pf

WIt : (S : Sig) (A : Alg S) → Mor S (WAlg S) A
WIt S A = record { f = λ srt → funcsW S A srt ;
                   eq = λ srt c p xs → {!!} }


-- Goal

fNF'' : (A : Alg NFNESig) → WI (Fin (sorts NFNESig)) (makeS NFNESig)
        (makeP NFNESig) zero → carriers A zero
fNE'' : (A : Alg NFNESig) → WI (Fin (sorts NFNESig)) (makeS NFNESig)
        (makeP NFNESig) (suc zero) → carriers A (suc zero)
        
-- ne
fNF'' A (sup .(zero) (inj₁ (tt , tt)) f) =
  (cons A) zero (cn (rec [] (suc zero) ∷ [])) hd (fNE'' A (f (suc zero) (inj₁ tt)))
-- lam
fNF'' A (sup .(zero) (inj₂ (inj₁ (s , tt , tt))) f) =
  (cons A) zero (cn (nrec string ∷ rec [] zero ∷ [])) (tl hd) s (fNF'' A (f zero (inj₂ (inj₁ tt))))

-- var
fNE'' A (sup .(suc zero) (inj₁ (s , tt)) f) = (cons A) (suc zero) (cn (nrec string ∷ [])) hd s
-- app
fNE'' A (sup .(suc zero) (inj₂ (inj₁ (tt , tt , tt))) f) =
  (cons A) (suc zero) (cn (rec [] (suc zero) ∷ rec [] zero ∷ [])) (tl hd)
  (fNE'' A (f (suc zero) (inj₁ tt) ))                               (fNF'' A (f (zero) (inj₂ (inj₁ tt)))) 
--makeP NFNESig (suc zero) (inj₂ (inj₁ (tt , tt , tt))) (suc zero)  makeP NFNESig (suc zero) (inj₂ (inj₁ (tt , tt , tt))) zero


-- Experimental

{-
data HVec : (n : ℕ)(A : Fin n → Set) → Set₁ where
     [] : HVec ℕ.zero (λ ())
     _∷_ : {n : ℕ}{A : Fin (ℕ.suc n) → Set} → A zero → HVec n (λ i → A (suc i)) →
           HVec (ℕ.suc n) A

appH : {n : ℕ}{A : Fin n → Set} → HVec n A → (i : Fin n) → A i
appH {ℕ.suc n} {A} (a ∷ as) zero = a
appH {ℕ.suc n} {A} (a ∷ as) (suc i) = appH {n} {(λ i → A (suc i))} as i

module _(S : Sig) (A : Alg S) where

  funcsW' : (srt : Fin (sorts S)) → WI (Fin (sorts S)) (makeS S) (makeP S) srt → carriers A srt

  mapConW' : (lst : List U) (fin : Fin (sorts S)) (s : ⊤) →
            (recArg lst → WI (Fin (sorts S)) (makeS S) (makeP S) fin)
            → conTypeAux (carriers A) lst fin
  mapConW' [] fin s p = funcsW' fin (p s)
  mapConW' (x ∷ xs) fin s p = λ el_x → mapConW' xs fin s (λ ra → p (el_x , ra))

  argTypeWToCarr' : (x : Arg (sorts S)) → argToSetNrec S x → HVec (sorts S) (λ j → argToSetRec S x j
                    → WI (Fin (sorts S)) (makeS S) (makeP S) j) → argType (carriers A) x
  argTypeWToCarr' (nrec x) s p = s
  argTypeWToCarr' (rec lst fin) s p = mapConW' lst fin s (appH p fin) --(p fin) 

  -- Extracts non-recursive and recursive arguments from WI-type and transforms them
  -- into arguments for algebra A
  argsWToCarr' : (srt : Fin (sorts S)) (c : Con (sorts S)) (s : conToSetNrec S c) →
                 HVec (sorts S) (λ j → conToSetRec S c j → WI (Fin (sorts S)) (makeS S) (makeP S) j)
                 → args srt (carriers A) c
  argsWToCarr' srt (cn []) s p = s
  argsWToCarr' srt (cn (x ∷ xs)) (fst , snd) p =
    argTypeWToCarr' x fst {!!} , --(λ j ar → p j (inj₁ ar)) ,
    argsWToCarr' srt (cn xs) snd {!!} --(λ j cr → p j (inj₂ cr)) 

  -- Passing the list of constructors as an argument
  makeArgs' : (srt : Fin (sorts S)) (l : List (Con (sorts S))) (s : listConToSetNrec S l) →
              HVec (sorts S) (λ j → listConToSetRec S l s j →
              WI (Fin (sorts S))(makeS S)(makeP S) j) → args srt (carriers A) (proj₁ (findCon S l s))
  makeArgs' srt (x ∷ xs) (inj₁ y) p = argsWToCarr' srt x y p
  makeArgs' srt (x ∷ xs) (inj₂ y) p = makeArgs' srt xs y p
 
  -- not checking (cns S srt) in funcs'
  funcsW' srt (sup .srt s p) = apply S A srt c (cons A srt c pf) (makeArgs' srt (cns S srt) s {!!})
    where
      c,pf = findCon S (cns S srt) s
      c = proj₁ c,pf
      pf = proj₂ c,pf

-- Problem - the size of our vector is not getting smaller, but the second argument of our original
-- function is.
-}

{-
data HVec : (n : ℕ)(B : Fin n → Set)(A : (j : Fin n) → B j → Set) → Set₁ where
  [] : HVec ℕ.zero (λ ()) (λ ())
  _∷_ : {n : ℕ}{B : Fin (ℕ.suc n) → Set}{A : (j : Fin (ℕ.suc n)) → B j → Set} → (b : B zero) →
         A zero b → HVec n (λ i → B (suc i)) (λ j b → A (suc j) b) → HVec (ℕ.suc n) B A
-}



