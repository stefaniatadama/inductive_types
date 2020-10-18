-- This file contains the constructions of algebras, morphisms, the initial
-- algebra, the iterator, and a proof of the uniqueness of the iterator for
-- any given signature.

{-# OPTIONS --rewriting #-}

open import Data.Nat
open import Data.Fin
open import Data.Bool
open import Data.List hiding (map)
open import Data.Product hiding (map)
open import Data.String hiding (_++_)
open import Agda.Builtin.Equality 
open import Agda.Builtin.Equality.Rewrite
open import Relation.Binary.PropositionalEquality 
open import Agda.Primitive

open import tsig_and_examples

open Sig


----- Defining Alg -----

-- In the case when a constructor has a function as one of its arguments,
-- e.g. suc : (ℕ → Ord) → Ord for ordinals, this function returns the type of that function
conTypeAux : {n : ℕ} → (Fin n → Set) → List U → Fin n → Set
conTypeAux f [] s = f s
conTypeAux f (set ∷ sets) s = El set → conTypeAux f sets s

-- Constructor (sp∞ : (ℕ → InfTree) → InfTree) of InfTree
--    conTypeAux {no. sorts} (Set name)            (cons. list) (cons. no.)
eg1 = conTypeAux {suc zero}  (λ {zero → InfTree}) (nat ∷ [])   zero  
-- ℕ → InfTree

-- Returns the type of the given argument
argType : {n : ℕ} → (Fin n → Set) → Arg n → Set
argType f (nrec set) = El set
argType f (rec lst fin) = conTypeAux f lst fin

-- Returns the type of the given constructor
conType : {n : ℕ} → Fin n → (Fin n → Set) → Con n → Set
conType s f (cn []) = f s
conType s f (cn (arg ∷ xs)) = argType f arg → conType s f (cn xs)

-- Constructor (lam : String → NF → NF) of NF 
--    conType {no. sorts}      (sort no.) (Set names)                         (cons. spec) 
eg2 = conType {suc (suc zero)} zero       (λ {zero → NF ; (suc zero) → NE}) (cn (nrec string ∷ rec [] zero ∷ [])) 
-- String → NF → NF

infix 5 _∈_

data _∈_ {A : Set}(a : A) : List A → Set where
  hd : {l : List A} → a ∈ (a ∷ l)
  tl : {l : List A}{b : A} → a ∈ l → a ∈ (b ∷ l)

record Alg (S : Sig) : Set₁ where
  field
    carriers : Fin (sorts S) → Set 
    cons : (srt : Fin (sorts S)) (c : Con (sorts S)) → c ∈ (cns S) srt → conType srt carriers c

open Alg

-- Examples

ℕInit' : Alg ℕSig
ℕInit' = record { carriers = λ {zero → ℕ} ;
                   cons = λ {zero → λ c → λ {hd → zero ; (tl hd) → suc}} }

BoolℕAlg' : Alg ℕSig
BoolℕAlg' = record { carriers = λ {zero → Bool} ;
                      cons = λ {zero → λ c → λ {hd → true ; (tl hd) → not}} }

LamInit' : Alg LamSig
LamInit' = record { carriers = λ {zero → Lam} ;
                    cons = λ {zero → λ c → λ {hd → var ; (tl hd) → abs ; (tl (tl hd)) → app}} }

InfTreeInit' : Alg InfTreeSig
InfTreeInit' = record { carriers = λ {zero → InfTree} ;
                        cons = λ {zero → λ c → λ {hd → ε∞ ; (tl hd) → sp∞}} }

NormalFormInit' : Alg NFNESig
NormalFormInit' = record { carriers = λ {zero → NF ; (suc zero) → NE} ;
                           cons = λ {zero → λ c → λ {hd → ne ; (tl hd) → lam} ;
                                    (suc zero) → λ c → λ {hd → var ; (tl hd) → app}} }
                                    
TreeForestInit' : (A : U) → Alg (TreeForestSig A)
TreeForestInit' = λ A → record { carriers =  λ {zero → Tree A ; (suc n) → Forest A} ;
                                  cons = λ {zero → λ c → λ {hd → sp} ;
                                           (suc zero) → λ c → λ {hd → εF ; (tl hd) → consF}} }


----- Defining Mor -----

-- Returns a product type of the arguments to be passed to the constructor
args : {n : ℕ} → Fin n → (Fin n → Set) → Con n → Set
args s f (cn []) = ⊤
args s f (cn (x ∷ xs)) = argType f x × args s f (cn xs)

-- Constructor (lam : String → NF → NF) of NF
--    args {no. sorts}      (sort no.) (Set names)                        (cons. spec)
eg3 = args {suc (suc zero)} zero       (λ {zero → NF ; (suc zero) → NE}) (cn (nrec string ∷ rec [] zero ∷ []))
-- String × NF × ⊤

-- Applies the constructor of type (conType srt (carriers A) c) with spec c to the supplied arguments
apply : (S : Sig) (A : Alg S) (srt : Fin (sorts S)) (c : Con (sorts S)) →
        conType srt (carriers A) c → args srt (carriers A) c → (carriers A) srt
apply S A srt (cn []) con argsEq = con
apply S A srt (cn (x ∷ xs)) con (arsX , arsXs) = apply S A srt (cn xs) (con arsX) arsXs

-- Constructor (lam : String → NF → NF) of NF
--    apply (Sig)   (Alg)           (sort no.) (cons. spec)                          (actual cons.) (arguments to be passed)
eg4 = apply NFNESig NormalFormInit' zero       (cn (nrec string ∷ rec [] zero ∷ [])) lam            ("x" , ne (var "y") , tt)
-- lam "x" (ne (var "y"))

module _(S : Sig) (A₁ A₂ : Alg S) (srt : Fin (sorts S)) where

  mapConTypeAux : (fin : Fin (sorts S)) (lst : List U)
                  (f : (srt : Fin (sorts S)) → (carriers A₁) srt → (carriers A₂) srt) →
                  conTypeAux (carriers A₁) lst fin → conTypeAux (carriers A₂) lst fin
  mapConTypeAux fin [] f cta = f fin cta
  mapConTypeAux fin (x ∷ xs) f cta = λ s → mapConTypeAux fin xs f (cta s)

  mapArgType : (a : Arg (sorts S))
               (f : (srt : Fin (sorts S)) → (carriers A₁) srt → (carriers A₂) srt) →
               argType (carriers A₁) a → argType (carriers A₂) a
  mapArgType (nrec x) f ars = ars
  mapArgType (rec lst fin) f ars = mapConTypeAux fin lst f ars

  -- For A₁ A₂ : Alg S, it maps args of type (carriers A₁ srt) to args of type
  -- (carriers A₂) srt. For ℕMor, map is emulating the (f x) in
  -- f_s : (x : N n₁) → f ((s n₁) x) ≡ (s n₂) (f x). Refer to eg5.
  map : (c : Con (sorts S))
        (f : (srt : Fin (sorts S)) → (carriers A₁) srt → (carriers A₂) srt) →
        args srt (carriers A₁) c → args srt (carriers A₂) c
  map (cn []) f ars = ars
  map (cn (x ∷ xs)) f (arType , ars) =
    mapArgType x f arType , map (cn xs) f ars

record Mor (S : Sig) (A₁ A₂ : Alg S) : Set where
  constructor mor
  field
    f : (srt : Fin (sorts S)) → (carriers A₁) srt → (carriers A₂) srt
    eq : (srt : Fin (sorts S)) (c : Con (sorts S)) (p : c ∈ (cns S) srt) (xs : args srt (carriers A₁) c) →
         (f srt) (apply S A₁ srt c ((cons A₁) srt c p) xs) ≡
         apply S A₂ srt c ((cons A₂) srt c p) (map S A₁ A₂ srt c f xs)

open Mor

MorℕEven'' : Mor ℕSig ℕInit' BoolℕAlg'
MorℕEven'' = record { f = λ {zero → even} ; -- f
                       eq = λ {zero → λ c → λ {hd ar → refl ; -- f_z
                                                (tl hd) ar → refl}} } -- f_s

eg5 = map ℕSig ℕInit' BoolℕAlg' zero (cn (rec [] zero ∷ [])) (f MorℕEven'') ((suc zero) , tt)
-- false , tt

LamAltAlg : Alg LamSig
LamAltAlg = record { carriers = λ {zero → String} ; -- L
                     cons = λ {zero → λ c → λ {hd → λ s → s ; -- v
                                                (tl hd) → λ s t → s ; -- ab
                                                (tl (tl hd)) → λ s t → t}} } -- ap
                                                                                              
fLam' : Lam → String
fLam' (var x) = x
fLam' (abs x l) = (λ s t → s) x (fLam' l)
fLam' (app m n) = (λ s t → t) (fLam' m) (fLam' n)

-- More general fLam'
fLam'' : (A : Alg LamSig) → Lam → (carriers A) zero
fLam'' A (var x) = (cons A) zero (cn (nrec string ∷ [])) hd x
fLam'' A (abs x l) = (cons A) zero (cn (nrec string ∷ rec [] zero ∷ [])) (tl hd) x (fLam'' A l)
fLam'' A (app m n) = (cons A) zero (cn (rec [] zero ∷ rec [] zero ∷ [])) (tl (tl hd)) (fLam'' A m) (fLam'' A n)

-- Even more general fLam'
fLam''' : (A : Alg LamSig) → Lam → (carriers A) zero
fLam''' A (var x) = (cons A) zero (lookup (cns LamSig zero) zero) hd x
fLam''' A (abs x l) = (cons A) zero (lookup (cns LamSig zero) (suc zero)) (tl hd) x (fLam''' A l)
fLam''' A (app m n) = (cons A) zero (lookup (cns LamSig zero) (suc (suc zero))) (tl (tl hd)) (fLam''' A m) (fLam''' A n)

LamMor' : Mor LamSig LamInit' LamAltAlg
LamMor' = record { f = λ {zero → fLam''' LamAltAlg} ; -- fLam'} ;
                   eq = λ {zero → λ c → λ {hd ar → refl ;
                                            (tl hd) ar → refl ;
                                            (tl (tl hd)) ar → refl}} }

NormalFormAltAlg : Alg NFNESig
NormalFormAltAlg = record { carriers = λ {zero → Bool ; (suc zero) → String} ; -- F , E
                            cons = λ {zero → λ c → λ {hd → λ _ → true ; -- n
                                                       (tl hd) → λ s b → b} ; -- l
                                      (suc zero) → λ c → λ {hd → λ s → s ; -- v
                                                             (tl hd) → λ s b → s}} } -- a

fF : NF → Bool
fE : NE → String

fF (ne s) = (λ _ → true) (fE s)
fF (lam s nf) = (λ s b → b) s (fF nf)

fE (var x) = (λ s → s) x
fE (app e f) = (λ s b → s) (fE e) (fF f)

NormalFormMor' : Mor NFNESig NormalFormInit' NormalFormAltAlg
NormalFormMor' = record { f = λ {zero → fF ; (suc zero) → fE} ;
                          eq = λ {zero → λ c → λ {hd ar → refl ; (tl hd) ar → refl} ;
                                  (suc zero) → λ c → λ {hd ar → refl ; (tl hd) ar → refl}} }


----- Defining Initial -----

data ⟦_⟧_ (S : Sig) : Fin (sorts S) → Set
data I-Args (S : Sig) : (srt : Fin (sorts S)) (c : Con (sorts S)) → c ∈ cns S srt → Set

data ⟦_⟧_ S where
  con : (srt : Fin (sorts S)) (c : Con (sorts S)) (p : c ∈ cns S srt) → I-Args S srt c p → ⟦ S ⟧ srt

data I-Args S where
  arg : {srt : Fin (sorts S)} {c : Con (sorts S)} {p : c ∈ cns S srt} → args srt (⟦ S ⟧_) c → I-Args S srt c p

appendNilPf : {A : Set} (l : List A) → l ++ [] ≡ l
appendNilPf [] = refl
appendNilPf (x ∷ xs) = cong (_∷_ x) (appendNilPf xs)

postulate appendNil : {A : Set} (l : List A) → l ++ [] ≡ l
{-# REWRITE appendNil #-}

snocAppendPf : {A : Set} (xs ys : List A) (a : A) → (xs ∷ʳ a) ++ ys ≡ xs ++ a ∷ ys
snocAppendPf [] ys a = refl
snocAppendPf (l ∷ ls) ys a = cong (_∷_ l) (snocAppendPf ls ys a)

postulate snocAppend : {A : Set} (xs ys : List A) (a : A) → (xs ∷ʳ a) ++ ys ≡ xs ++ a ∷ ys
{-# REWRITE snocAppend #-}

argsSnoc : (S : Sig) (srt : Fin (sorts S)) (l : List (Arg (sorts S))) (x : Arg (sorts S)) →
            args srt (⟦_⟧_ S) (cn l) → argType (⟦_⟧_ S) x → args srt (⟦_⟧_ S) (cn (l ∷ʳ x))
argsSnoc S srt [] x ars ar = ar , tt
argsSnoc S srt (l ∷ ls) x (arl , arls) ar = arl , argsSnoc S srt ls x arls ar

-- l₁ seen, l₂ unseen
makeConsAux : (S : Sig) (srt : Fin (sorts S)) (l₁ l₂ : List (Arg (sorts S))) →
              cn (l₁ ++ l₂) ∈ cns S srt → args srt (⟦_⟧_ S) (cn l₁) → conType srt (⟦_⟧_ S) (cn l₂)
makeConsAux S srt l₁ [] p ars = con srt (cn l₁) p (arg ars)
makeConsAux S srt l₁ (x ∷ xs) p ars =
  λ a → makeConsAux S srt (l₁ ∷ʳ x) xs p (argsSnoc S srt l₁ x ars a)
  
makeCons : (S : Sig) (srt : Fin (sorts S)) (c : Con (sorts S)) → c ∈ cns S srt →
           conType srt (⟦_⟧_ S) c
makeCons S srt (cn x) p = makeConsAux S srt [] x p tt

eg6 =  makeCons NFNESig zero (cn (nrec string ∷ rec [] zero ∷ [])) (tl hd) 
-- λ a₁ a₂ → con zero (cn (nrec string ∷ rec [] zero ∷ [])) (tl hd) (arg (a₁ , a₂ , tt))
  
Initial : (S : Sig) → Alg S
Initial S = record { carriers =  λ srt → ⟦ S ⟧ srt ;
                     cons = λ srt c p → makeCons S srt c p } 

-- Goal

even' : ⟦ ℕSig ⟧ zero → Bool
even' (con .zero .(cn []) hd ar) = true
even' (con .zero .(cn (rec [] zero ∷ [])) (tl hd) (arg ar)) = not (even' (proj₁ ar)) 

MorℕEven''' : Mor ℕSig (Initial ℕSig) BoolℕAlg'
MorℕEven''' = record { f = λ {zero → even'} ;
                        eq = λ {zero → λ c → λ {hd ar → refl ; (tl hd) ar → refl}} }

-- ℕ initial algebra
tstℕ : Alg ℕSig
tstℕ = record { carriers = λ {zero → ⟦ ℕSig ⟧ zero} ; -- N
                 cons = λ {zero → λ c → λ {hd → con zero c hd (arg tt) ; -- z
                                            (tl hd) → λ n' → con zero c (tl hd) (arg (n' , tt))}} } -- s

-- NF-NE initial algebra
tstNFNE : Alg NFNESig
tstNFNE = record { carriers = λ {zero → ⟦ NFNESig ⟧ zero ; (suc zero) → ⟦ NFNESig ⟧ (suc zero)} ; -- F , E
                   cons = λ {zero → λ c → λ {hd → λ ne → con zero c hd (arg (ne , tt)) ; -- n
                                              (tl hd) → λ st nf → con zero c (tl hd) (arg (st , nf , tt) )} ; -- l
                            (suc zero) → λ c → λ {hd → λ st → con (suc zero) c hd (arg (st , tt)) ; -- v
                                                  (tl hd) → λ ne nf → con (suc zero) c (tl hd) (arg (ne , nf , tt))}} } -- a


----- Defining Iterator -----

open ≡-Reasoning

-- Functional extensionality
postulate funExt : ∀ {ℓ} {A : Set ℓ} {B : A → Set ℓ} {f g : (x : A) → B x} →
                   ((x : A) → f x ≡ g x) → f ≡ g 

eqTuple : {A B : Set} {a a' : A} {b b' : B} → a ≡ a' → b ≡ b' → (a , b) ≡ (a' , b')
eqTuple {_} {_} {a} {.a} {b} {.b} refl refl = refl

-- f

module _(S : Sig) (A : Alg S) where

  -- For a given sort, returns the function from the (⟦_⟧_ S) type of that sort to the corresponding
  -- type in A
  funcs : (srt : Fin (sorts S)) → ⟦ S ⟧ srt → carriers A srt
  -- Maps (conTypeAux srt (⟦_⟧_ S) lst fin) to (conTypeAux srt (carriers A) lst fin)
  mapCon : (fin : Fin (sorts S)) (lst : List U) →
           conTypeAux (⟦_⟧_ S) lst fin → conTypeAux (carriers A) lst fin 

  -- like mapConTypeAux
  mapCon fin [] cta = funcs fin cta
  mapCon fin (x ∷ xs) cta = λ s → mapCon fin xs (cta s)

  module  _(srt : Fin (sorts S)) where

    -- like mapArgType
    argTypeInitToCarr : (a : Arg (sorts S)) → argType (⟦_⟧_ S) a → argType (carriers A) a 
    argTypeInitToCarr (nrec set) arType = arType
    argTypeInitToCarr (rec lst fin) arType = mapCon fin lst arType  

    -- like map
    argsInitToCarr : (c : Con (sorts S)) → args srt (⟦_⟧_ S) c → args srt (carriers A) c 
    argsInitToCarr (cn []) ars = ars
    argsInitToCarr (cn (x ∷ xs)) (arType , ars) = argTypeInitToCarr x arType ,
                                                  argsInitToCarr (cn xs) ars 

  funcs srt (con .srt c p (arg ar)) = apply S A srt c (cons A srt c p) (argsInitToCarr srt c ar)

-- eq              

  pfMapConTypeAux : (srt fin : Fin (sorts S)) (l : List U) (cta : conTypeAux (⟦_⟧_ S) l fin) → 
                    (mapCon fin l cta) ≡ (mapConTypeAux S (Initial S) A srt fin l funcs cta)
  pfMapConTypeAux srt fin [] cta = refl
  pfMapConTypeAux srt fin (x ∷ xs) cta = funExt (λ s → pfMapConTypeAux srt fin xs (cta s))  

  pfMapArgType : (srt : Fin (sorts S)) (x : Arg (sorts S)) (at : argType (⟦_⟧_ S) x) →
                 argTypeInitToCarr srt x at ≡ mapArgType S (Initial S) A srt x funcs at
  pfMapArgType srt (nrec x) at = refl
  pfMapArgType srt (rec lst fin) at = pfMapConTypeAux srt fin lst at 
  
  pfMap : (srt : Fin (sorts S)) (c : Con (sorts S)) (ar : args srt (⟦_⟧_ S) c) → 
          argsInitToCarr srt c ar ≡ map S (Initial S) A srt c funcs ar
  pfMap srt (cn []) ar = refl 
  pfMap srt (cn (x ∷ xs)) (fst , snd) = eqTuple (pfMapArgType srt x fst) (pfMap srt (cn xs) snd)

module _(S : Sig) (srt : Fin (sorts S)) where

  appArgs : (l₁ l₂ : List (Arg (sorts S))) → args srt (⟦_⟧_ S) (cn l₁)
            → args srt (⟦_⟧_ S) (cn l₂) → args srt (⟦_⟧_ S) (cn (l₁ ++ l₂))
  appArgs [] l₂ a₁ a₂ = a₂
  appArgs (x ∷ xs) [] a₁ a₂ = a₁
  appArgs (x ∷ xs) (y ∷ ys) a₁ a₂ = proj₁ a₁ , appArgs xs (y ∷ ys) (proj₂ a₁) a₂ 

  appArgs≡argsSnocAux : (l₁ : List (Arg (sorts S))) (x : Arg (sorts S))
                        (fst₂ : argType (⟦_⟧_ S) x) (snd₁ : args srt (⟦_⟧_ S) (cn l₁)) →
                        appArgs l₁ (x ∷ []) snd₁ (fst₂ , tt) ≡ argsSnoc S srt l₁ x snd₁ fst₂
  appArgs≡argsSnocAux [] x ar_x tt = refl
  appArgs≡argsSnocAux (x₁ ∷ l₁) x ar_x (fst , snd) = eqTuple refl (appArgs≡argsSnocAux l₁ x ar_x snd)

  appArgs≡argsSnoc : (l₁ l₂ : List (Arg (sorts S))) (x : Arg (sorts S))
                     (fst : args srt (⟦_⟧_ S) (cn l₁)) (snd : argType (⟦_⟧_ S) x ×
                     args srt (⟦_⟧_ S) (cn l₂)) → appArgs l₁ (x ∷ l₂) fst snd ≡
                     appArgs (l₁ ∷ʳ x) l₂ (argsSnoc S srt l₁ x fst (proj₁ snd)) (proj₂ snd)
  appArgs≡argsSnoc [] [] x tt (fst , tt) = refl
  appArgs≡argsSnoc [] (x₁ ∷ l₂) x tt a₂ = refl
  appArgs≡argsSnoc (x₁ ∷ l₁) [] x (fst₁ , snd₁) (fst₂ , tt) =
    eqTuple refl (appArgs≡argsSnocAux l₁ x fst₂ snd₁)
  appArgs≡argsSnoc (x₁ ∷ l₁) (x₂ ∷ l₂) x (fst₁ , snd₁) (fst₂ , snd₂) =
    eqTuple refl (appArgs≡argsSnoc l₁ (x₂ ∷ l₂) x snd₁ (fst₂ , snd₂))

  apply≡conAppMcaAux : (l₁ l₂ : List (Arg (sorts S))) (p : (cn l₁) ∈ cns S srt)
                       (a₁ : args srt (⟦_⟧_ S) (cn l₁)) →
                       con srt (cn l₁) p (arg a₁) ≡ con srt (cn l₁) p (arg (appArgs l₁ [] a₁ tt))
  apply≡conAppMcaAux [] l₂ p tt = refl
  apply≡conAppMcaAux (x ∷ l₁) l₂ p a₁ = refl
  
  apply≡conAppMca : (l₁ l₂ : List (Arg (sorts S))) (p : (cn (l₁ ++ l₂)) ∈ cns S srt)
                    (fst : args srt (⟦_⟧_ S) (cn l₁)) (snd : args srt (⟦_⟧_ S) (cn l₂)) →
                    apply S (Initial S) srt (cn l₂) (makeConsAux S srt l₁ l₂ p fst) snd
                    ≡ con srt (cn (l₁ ++ l₂)) p (arg (appArgs l₁ l₂ fst snd))
  apply≡conAppMca l₁ [] p a₁ tt = apply≡conAppMcaAux l₁ [] p a₁
  apply≡conAppMca l₁ (x ∷ l₂) p a₁ a₂ =
    begin
      apply S (Initial S) srt (cn l₂)
      (makeConsAux S srt (l₁ ∷ʳ x) l₂ p (argsSnoc S srt l₁ x a₁ (proj₁ a₂))) (proj₂ a₂)

      ≡⟨ apply≡conAppMca (l₁ ∷ʳ x) l₂ p (argsSnoc S srt l₁ x a₁ (proj₁ a₂)) (proj₂ a₂) ⟩

      con srt (cn (l₁ ++ x ∷ l₂)) p
      (arg (appArgs (l₁ ∷ʳ x) l₂ (argsSnoc S srt l₁ x a₁ (proj₁ a₂)) (proj₂ a₂)))

      ≡⟨ cong (λ ars → con srt (cn (l₁ ++ x ∷ l₂)) p (arg ars))
        (sym (appArgs≡argsSnoc l₁ l₂ x a₁ a₂)) ⟩
     
      con srt (cn (l₁ ++ x ∷ l₂)) p (arg (appArgs l₁ (x ∷ l₂) a₁ a₂))
    ∎
    
  apply≡conApp : (l₁ l₂ : List (Arg (sorts S))) (p : cn (l₁ ++ l₂) ∈ cns S srt)
                 (ars : args srt (⟦_⟧_ S) (cn (l₁ ++ l₂))) →
                 apply S (Initial S) srt (cn (l₁ ++ l₂)) (makeCons S srt (cn (l₁ ++ l₂)) p) ars
                 ≡ con srt (cn (l₁ ++ l₂)) p (arg ars) 
  apply≡conApp l₁ [] p ars = apply≡conAppMca [] l₁ p tt ars  
  apply≡conApp l₁ (x ∷ l₂) p ars = apply≡conApp (l₁ ∷ʳ x) l₂ p ars 

  apply≡conMca : (x : Arg (sorts S)) (xs : List (Arg (sorts S))) (p : (cn (x ∷ xs)) ∈ cns S srt)
                 (fst : argType (⟦_⟧_ S) x) (snd : args srt (⟦_⟧_ S) (cn xs)) →
                 apply S (Initial S) srt (cn xs) (makeConsAux S srt ([] ∷ʳ x) xs p (fst , tt)) snd
                 ≡ con srt (cn (x ∷ xs)) p (arg (fst , snd))
  apply≡conMca x [] p fst tt = refl
  apply≡conMca x (y ∷ ys) p fst snd = apply≡conApp (x ∷ y ∷ []) ys p (fst , snd)

  apply≡con : (c : Con (sorts S)) (p : c ∈ cns S srt) (ars : args srt (⟦_⟧_ S) c) →
              apply S (Initial S) srt c (makeCons S srt c p) ars ≡ con srt c p (arg ars)
  apply≡con (cn []) p tt = refl
  apply≡con (cn (x ∷ xs)) p (fst , snd) = apply≡conMca x xs p fst snd 

eqProof : (S : Sig) (A : Alg S) (srt : Fin (sorts S)) (c : Con (sorts S)) (p : c ∈ cns S srt)
          (xs : args srt (⟦_⟧_ S) c) →
          funcs S A srt (apply S (Initial S) srt c (makeCons S srt c p) xs) ≡
          apply S A srt c (cons A srt c p) (map S (Initial S) A srt c (λ srt₁ → funcs S A srt₁) xs)
eqProof S A srt c p ars =
  begin
     funcs S A srt (apply S (Initial S) srt c (makeCons S srt c p) ars)

     ≡⟨ cong (funcs S A srt) (apply≡con S srt c p ars) ⟩
     
     funcs S A srt (con srt c p (arg ars))

     ≡⟨ refl ⟩
     
     apply S A srt c (cons A srt c p) (argsInitToCarr S A srt c ars)

     ≡⟨ cong (apply S A srt c (cons A srt c p)) (pfMap S A srt c ars) ⟩

     apply S A srt c (cons A srt c p) (map S (Initial S) A srt c (funcs S A) ars)
  ∎  

It : (S : Sig) (A : Alg S) → Mor S (Initial S) A
It S A = record { f = λ srt → funcs S A srt ; 
                  eq = λ srt c p xs → eqProof S A srt c p xs }

eg7 = apply NFNESig NormalFormInit' zero (cn (nrec string ∷ rec [] zero ∷ [])) lam
      (argsInitToCarr NFNESig NormalFormInit' zero ((cn (nrec string ∷ rec [] zero ∷ []))) 
      (("x" , con zero (cn (rec [] (suc zero) ∷ [])) (hd) (arg (con (suc zero) (cn (nrec string ∷ []))
      (hd) (arg ("y" , tt)) , tt)) , tt)))
-- lam "x" (ne (var "y"))

-- Goal 

fℕ' : (X : Alg ℕSig) → carriers (Initial ℕSig) zero → carriers X zero
fℕ' X (con .zero .(cn []) hd (arg ar)) = (cons X) zero (cn []) hd 
fℕ' X (con .zero .(cn (rec [] zero ∷ [])) (tl hd) (arg (n , tt))) =
  (cons X) zero (cn (rec [] zero ∷ [])) (tl hd) (fℕ' X n)

Itℕ' : Mor ℕSig (Initial ℕSig) (BoolℕAlg')
Itℕ' = record { f = λ {zero → fℕ' BoolℕAlg'} ;
                 eq = λ {zero → λ c → λ {hd ar → refl ;
                                          (tl hd) ar → refl}} }

tst = mapConTypeAux ℕSig (Initial ℕSig) BoolℕAlg' zero zero [] (funcs ℕSig BoolℕAlg')
      (con zero (cn []) hd (arg tt)) 
-- true

fNF' : (X : Alg NFNESig) → carriers (Initial NFNESig) zero → carriers X zero
fNE' : (Y : Alg NFNESig) → carriers (Initial NFNESig) (suc zero) → carriers Y (suc zero)

fNF' X (con .zero .(cn (rec [] (suc zero) ∷ [])) hd (arg (e , tt))) =
  (cons X) zero (cn (rec [] (suc zero) ∷ [])) hd (fNE' X e) 
fNF' X (con .zero .(cn (nrec string ∷ rec [] zero ∷ [])) (tl hd) (arg (str , f , tt))) =
  (cons X) zero (cn (nrec string ∷ rec [] zero ∷ [])) (tl hd) str (fNF' X f)

fNE' Y (con .(suc zero) .(cn (nrec string ∷ [])) hd (arg (str , tt))) =
  (cons Y) (suc zero) (cn (nrec string ∷ [])) hd str
fNE' Y (con .(suc zero) .(cn (rec [] (suc zero) ∷ rec [] zero ∷ [])) (tl hd) (arg (e , f , tt))) =
  (cons Y) (suc zero) (cn (rec [] (suc zero) ∷ rec [] zero ∷ [])) (tl hd) (fNE' Y e) (fNF' Y f)

-- Example 

-- Mimicking this
--dbl-it : ℕ → ℕ
--dbl-it = Itℕ 0 λ dbl_n → suc (suc dbl_n)

dblℕAlg : Alg ℕSig
dblℕAlg = record { carriers = λ {zero → ⟦ ℕSig ⟧ zero} ;
                    cons = λ {zero → λ c → λ {hd → con zero (cn []) hd (arg tt) ; -- 0
                                                       -- λ dbl_n → suc (suc dbl_n)  
                                               (tl hd) → λ dbl_n →
                              con zero (cn (rec [] zero ∷ [])) (tl hd)
                                       (arg ((con zero  (cn (rec [] zero ∷ [])) (tl hd)
                                       (arg (dbl_n , tt))) , tt))}} }

dbl : carriers (Initial ℕSig) zero → carriers (Initial ℕSig) zero
dbl = f (It ℕSig dblℕAlg) zero

-- Double of 2 is 4
tstdbl = dbl (con zero (cn (rec [] zero ∷ [])) (tl hd)
         (arg ((con zero (cn (rec [] zero ∷ [])) (tl hd)
         (arg ((con zero (cn []) hd (arg tt)) , tt))) , tt)))


----- Uniqueness of Iterator -----

uItF : (S : Sig) (A : Alg S) (srt : Fin (sorts S)) (i : ⟦ S ⟧ srt) (m : Mor S (Initial S) A) →
       f m srt i ≡ f (It S A) srt i

module _(S : Sig) (A : Alg S) (m : Mor S (Initial S) A) (srt : Fin (sorts S)) where

  pfMapConTypeAux' : (fin : Fin (sorts S)) (l : List U) (cta : conTypeAux (⟦_⟧_ S) l fin) → 
                     (mapCon S A fin l cta) ≡ (mapConTypeAux S (Initial S) A srt fin l (f m) cta)
  pfMapConTypeAux' fin [] cta = sym (uItF S A fin cta m)
  pfMapConTypeAux' fin (x ∷ xs) cta =
    funExt (λ s → pfMapConTypeAux' fin xs (cta s))

  pfMapArgType' : (x : Arg (sorts S)) (at : argType (⟦_⟧_ S) x) →
                  argTypeInitToCarr S A srt x at ≡ mapArgType S (Initial S) A srt x (f m) at
  pfMapArgType' (nrec x) at = refl
  pfMapArgType' (rec lst fin) at = pfMapConTypeAux' fin lst at 

  pfMap' : (c : Con (sorts S)) (ar : args srt (⟦_⟧_ S) c) → 
           argsInitToCarr S A srt c ar ≡ map S (Initial S) A srt c (f m) ar
  pfMap' (cn []) ar = refl 
  pfMap' (cn (x ∷ xs)) (fst , snd) =
    eqTuple (pfMapArgType' x fst) (pfMap' (cn xs) snd)

subproof : (S : Sig) (A : Alg S) (srt : Fin (sorts S)) (c : Con (sorts S))
           (p : c ∈ cns S srt) (ar : args srt (⟦_⟧_ S) c) (m : Mor S (Initial S) A) →
           (f m) srt (con srt c p (arg ar)) ≡
           apply S A srt c (cons A srt c p) (map S (Initial S) A srt c (f m) ar) →
           (f m) srt (con srt c p (arg ar)) ≡
           apply S A srt c (cons A srt c p) (argsInitToCarr S A srt c ar)
subproof S A srt c p ar (mor fm eqm) e =
  begin
    fm srt (con srt c p (arg ar))
    
    ≡⟨ e ⟩

    apply S A srt c (cons A srt c p) (map S (Initial S) A srt c fm ar)

    ≡⟨ sym (cong (apply S A srt c (cons A srt c p)) (pfMap' S A (mor fm eqm) srt c ar)) ⟩
    
    apply S A srt c (cons A srt c p) (argsInitToCarr S A srt c ar)
  ∎

uItF S A srt (con .srt c p (arg ar)) (mor fm eqm) = subproof S A srt c p ar (mor fm eqm)
  (trans (sym (cong (fm srt) (apply≡con S srt c p ar))) (eqm srt c p ar)) 

mor≡intro : {S : Sig} {A₁ A₂ : Alg S} →
  {fun fun' : (srt : Fin (sorts S)) → (carriers A₁) srt → (carriers A₂) srt}
  {e : (srt : Fin (sorts S)) (c : Con (sorts S)) (p : c ∈ (cns S) srt) (xs : args srt (carriers A₁) c)
  → (fun srt) (apply S A₁ srt c ((cons A₁) srt c p) xs) ≡ apply S A₂ srt c ((cons A₂) srt c p)
  (map S A₁ A₂ srt c fun xs)} →
  {e' : (srt : Fin (sorts S)) (c : Con (sorts S)) (p : c ∈ (cns S) srt)(xs : args srt (carriers A₁) c)
  → (fun' srt) (apply S A₁ srt c ((cons A₁) srt c p) xs) ≡ apply S A₂ srt c ((cons A₂) srt c p)
  (map S A₁ A₂ srt c fun' xs)}
  (p : fun ≡ fun') →
  (subst (λ fun → (srt : Fin (sorts S)) (c : Con (sorts S)) (p : c ∈ (cns S) srt)
  (xs : args srt (carriers A₁) c) → (fun srt) (apply S A₁ srt c ((cons A₁) srt c p) xs) ≡
  apply S A₂ srt c ((cons A₂) srt c p) (map S A₁ A₂ srt c fun xs)) p e) ≡ e' →
  mor fun e ≡ mor fun' e'
mor≡intro refl refl = refl

UIP : ∀ {a} {A : Set a} {x y : A} (p q : x ≡ y) → p ≡ q
UIP refl refl = refl

uIt : (S : Sig) (A : Alg S) (f : Mor S (Initial S) A) → f ≡ It S A
uIt S A (mor fm eqm) with (funExt (λ s → funExt (λ i → uItF S A s i (mor fm eqm))))
uIt S A (mor .(funcs S A) eqm) | refl =
  mor≡intro refl (funExt (λ srt → funExt (λ c → funExt (λ p → funExt (λ xs →
  UIP (eqm srt c p xs) (eqProof S A srt c p xs))))))
