module Exe1 where

open import Basics public

-- \section{Zipping Lists of Compatible Shape}

data List (X : Set) : Set where
  <>    :                 List X
  _,_   : X -> List X ->  List X

infixr 4 _,_

zip0 : {S T : Set} -> List S -> List T -> List (S * T)
zip0 <>        <>        = <>
zip0 (s , ss)  (t , ts)  = (s , t) , zip0 ss ts
zip0 _         _         = <>  -- a dummy value, for cases we should not reach

data Nat : Set where
  zero  :         Nat
  suc   : Nat ->  Nat

{-# BUILTIN NATURAL Nat #-}

length : {X : Set} -> List X -> Nat
length <>        = zero
length (x , xs)  = suc (length xs)

data Vec (X : Set) : Nat -> Set where
  <>   :                               Vec X zero
  _,_  : {n : Nat} -> X -> Vec X n ->  Vec X (suc n)

zip1 : forall {n S T} -> Vec S n -> Vec T n -> Vec (S * T) n
zip1 <> <> = <>
zip1 (s , ss) (t , ts) = (s , t) , zip1 ss ts

vec : forall {n X} -> X -> Vec X n
vec {zero} x = <>
vec {suc n} x = x , vec x

vapp :  forall {n S T} -> Vec (S -> T) n -> Vec S n -> Vec T n
vapp <> <> = <>
vapp (f , fs) (x , xs) = f x , vapp fs xs

vmap : forall {n S T} -> (S -> T) -> Vec S n -> Vec T n
vmap f xs = vapp (vec f) xs

zip2 : forall {n S T} -> Vec S n -> Vec T n -> Vec (S * T) n
zip2 ss ts = vapp (vapp (vec _,_) ss) ts

zip3 : forall {n S T} -> Vec S n -> Vec T n -> Vec (S * T) n
zip3 ss ts = vapp (vmap _,_ ss) ts

--[Finite sets and projection from vectors]

data Fin : Nat -> Set where
  zero : {n : Nat} -> Fin (suc n)
  suc  : {n : Nat} -> Fin n -> Fin (suc n)

proj : forall {n X} -> Vec X n -> Fin n -> X
proj (x , _) zero = x
proj (_ , xs) (suc i) = proj xs i

tabulate : forall {n X} -> (Fin n -> X) -> Vec X n
tabulate {zero} f = <>
tabulate {suc n} f = f zero , (tabulate (λ fn → f (suc fn)))

-- Functors and Applicatives

record EndoFunctor (F : Set -> Set) : Set1 where
  field
    map  : forall {S T} -> (S -> T) -> F S -> F T
open EndoFunctor {{...}} public

record Applicative (F : Set -> Set) : Set1 where
  infixl 2 _<*>_
  field
    pure    : forall {X} -> X -> F X
    _<*>_   : forall {S T} -> F (S -> T) -> F S -> F T
  applicativeEndoFunctor : EndoFunctor F
  applicativeEndoFunctor = record { map = _<*>_ o pure }
open Applicative {{...}} public

instance applicativeVec  : forall {n} -> Applicative (\ X -> Vec X n)
applicativeVec  = record { pure = vec; _<*>_ = vapp }

endoFunctorVec  : forall {n} -> EndoFunctor \ X -> Vec X n
endoFunctorVec  = applicativeEndoFunctor

applicativeFun : forall {S} -> Applicative \ X -> S -> X
applicativeFun = record
  {  pure    = \ x s -> x              -- also known as K (drop environment)
  ;  _<*>_   = \ f a s -> f s (a s)    -- also known as S (share environment)
  }

record Monad (F : Set -> Set) : Set1 where
  field
    return  : forall {X} -> X -> F X
    _>>=_   : forall {S T} -> F S -> (S -> F T) -> F T
  monadApplicative : Applicative F
  monadApplicative = record
    {  pure   = return
    ;  _<*>_  = \ ff fs -> ff >>= \ f -> fs >>= \ s -> return (f s) }
open Monad {{...}} public

monadVec : {n : Nat} -> Monad \ X -> Vec X n
monadVec = record { return = vec
                  ; _>>=_  = λ ss f → tabulate (λ i → proj (f (proj ss i)) i)}

instance applicativeId : Applicative id
applicativeId = record { pure = id; _<*>_ = \ f x -> f x}

applicativeComp : forall {F G} -> Applicative F -> Applicative G -> Applicative (F o G)
applicativeComp aF aG =
  record { pure  = pf o pg
         ; _<*>_ = λ fgf fgx → (pf _<g>_) <f> fgf <f> fgx}
  where
    open Applicative aF renaming (pure to pf; _<*>_ to _<f>_)
    open Applicative aG renaming (pure to pg; _<*>_ to _<g>_)


record Monoid (X : Set) : Set where
  infixr 4 _&_
  field
    neut  : X
    _&_   : X -> X -> X
  instance monoidApplicative : Applicative \ _ -> X
  monoidApplicative = record { pure = \ _ -> neut; _<*>_ = _&_ }
open Monoid {{...}} public -- it's not obvious that we'll avoid ambiguity

--Show by construction that the pointwise product of |Applicative|s is
-- |Applicative|.

record Traversable (F : Set -> Set) : Set1 where
  field
    traverse :  forall {G S T}{{AG : Applicative G}} ->
                (S -> G T) -> F S -> G (F T)
  instance traversableEndoFunctor : EndoFunctor F
  traversableEndoFunctor = record { map = traverse }
open Traversable {{...}} public

instance traversableVec : {n : Nat} -> Traversable \ X -> Vec X n
traversableVec = record { traverse = vtr } where
  vtr :  forall {n G S T}{{_ : Applicative G}} ->
         (S -> G T) -> Vec S n -> G (Vec T n)
  vtr {{aG}} f <>        = pure {{aG}} <>
  vtr {{aG}} f (s , ss)  = pure {{aG}} _,_ <*> f s <*> vtr f ss

transpose : forall {m n X} -> Vec (Vec X n) m -> Vec (Vec X m) n
transpose = traverse id

crush :  forall {F X Y}{{TF : Traversable F}}{{M : Monoid Y}} ->
         (X -> Y) -> F X -> Y
crush {{M = M}} =
  traverse {T = One}{{AG = monoidApplicative {{M}}}}  -- |T| arbitrary


{-Show that |Traversable| is closed under identity and composition.
What other structure does it preserve?-}

--\section{Arithmetic}

_+Nat_ : Nat -> Nat -> Nat
zero +Nat y = y
suc x +Nat y = suc (x +Nat y)

_*Nat_ : Nat -> Nat -> Nat
zero *Nat y = zero
suc x *Nat y = y +Nat (x *Nat y)

--\section{Normal Functors}

record Normal : Set1 where
  constructor _/_
  field
    Shape  : Set
    size   : Shape -> Nat
  <!_!>N : Set -> Set
  <!_!>N X = Sg Shape \ s -> Vec X (size s)
open Normal public
infixr 0 _/_

VecN : Nat -> Normal
VecN n = One / (\ _ -> n)

ListN : Normal
ListN = Nat / id

KN : Set -> Normal
KN A = A / (λ _ → 0)

IN : Normal
IN = One / (λ _ → 1)

_+N_ : Normal -> Normal -> Normal
(ShF / szF) +N (ShG / szG) = (ShF + ShG) / vv szF <?> szG

_*N_ : Normal -> Normal -> Normal
(ShF / szF) *N (ShG / szG) = (ShF * ShG) / vv \ f g -> szF f +Nat szG g

nInj : forall {X}(F G : Normal) -> <! F !>N X + <! G !>N X -> <! F +N G !>N X
nInj F G (tt , ShF , xs) = (tt , ShF) , xs
nInj F G (ff , ShG , xs) = (ff , ShG) , xs

data _^-1_ {S T : Set}(f : S -> T) : T -> Set where
  from : (s : S) -> f ^-1 f s

nCase : forall {X} F G (s : <! F +N G !>N X) -> nInj F G ^-1 s
nCase F G ((tt , ShF) , xs) = from (tt , ShF , xs)
nCase F G ((ff , ShG) , xs) = from (ff , ShG , xs)

nOut : forall {X}(F G : Normal) -> <! F +N G !>N X -> <! F !>N X + <! G !>N X
nOut F G xs' with nCase F G xs'
nOut F G .(nInj F G xs) | from xs = xs

_++_ : forall {m n X} -> Vec X m -> Vec X n -> Vec X (m +Nat n)
<> ++ ys = ys
(x , xs) ++ ys = x , xs ++ ys

split : forall {n X} (m : Nat) -> Vec X (m +Nat n) -> (Vec X m * Vec X n)
split  zero    xs = <> , xs
split (suc m) (x , xs) with split m xs
split (suc m) (x , xs)    | ys , zs = (x , ys) , zs

nPair : forall {X}(F G : Normal) -> <! F !>N X * <! G !>N X -> <! F *N G !>N X
nPair F G ((shF , xs) , (shG , ys)) = (shF , shG) , xs ++ ys

nCaseOut : forall {X}(F G : Normal) -> <! F *N G !>N X -> <! F !>N X * <! G !>N X
nCaseOut F G ((shF , shG) , xs)
   with split (size F shF) xs
...   | ys , zs = (shF , ys) , (shG , zs)

instance listNMonoid : {X : Set} -> Monoid (<! ListN !>N X)
listNMonoid {X} =
  record { neut = zero , <>
         ; _&_ = λ z z₁ → (fst z) +Nat (fst z₁) , (snd z) ++ (snd z₁)
         }

instance sumMonoid : Monoid Nat
sumMonoid = record { neut = 0; _&_ = _+Nat_ }

instance normalTraversable : (F : Normal) -> Traversable <! F !>N
normalTraversable F = record
  { traverse = \ {{aG}} f -> vv \ s xs -> pure {{aG}}  (_,_ s) <*> traverse f xs }

_oN_ : Normal -> Normal -> Normal
F oN (ShG / szG) = <! F !>N ShG / crush {{normalTraversable F}} szG

sizeT : forall {F}{{TF : Traversable F}}{X} -> F X -> Nat
sizeT = crush (\ _ -> 1)

normalT : forall F {{TF : Traversable F}} -> Normal
normalT F = F One / sizeT

shapeT : forall {F}{{TF : Traversable F}}{X} -> F X -> F One
shapeT = traverse (\ _ -> <>)

one : forall {X} -> X -> <! ListN !>N X
one x = 1 , (x , <>)

contentsT : forall {F}{{TF : Traversable F}}{X} -> F X -> <! ListN !>N X
contentsT = crush one

--[normal morphisms]

_-N>_ : Normal -> Normal -> Set
F -N> G = (s : Shape F) -> <! G !>N (Fin (size F s))

nMorph : forall {F G} -> F -N> G -> forall {X} -> <! F !>N X -> <! G !>N X
nMorph f (s , xs)  with f s
...                | s' , is = s' , map (proj xs) is

--Show how to compute the normal morphism representing a given natural
--transformation.

morphN : forall {F G} -> (forall {X} -> <! F !>N X -> <! G !>N X) -> F -N> G
morphN {F} {G} f s = f (s , tabulate id)

--[Hancock's tensor]
_><_ : Normal -> Normal -> Normal
(ShF / szF) >< (ShG / szG) = (ShF * ShG) / vv \ f g -> szF f *Nat szG g

toMat : forall {X}
      -> (m : Nat)
      -> (n : Nat)
      -> Vec X (m *Nat n)
      -> Vec (Vec X n) m
toMat  zero   n xss = <>
toMat (suc m) n xss with split n xss
...                    | xs , xss' = xs , toMat m n xss'

fromMat : forall {X}
        -> (m : Nat)
        -> (n : Nat)
        -> Vec (Vec X n) m
        -> Vec X (m *Nat n)
fromMat  zero   n  xss = <>
fromMat (suc m) n (xss , xss₁) = xss ++ fromMat m n xss₁

swap : (F G : Normal) -> (F >< G) -N> (G >< F)
swap F G (shF , shG) =
  let sf = size F shF
      sg = size G shG
  in (shG , shF) , fromMat sg sf
                    (transpose
                     (toMat sf sg
                      (tabulate id)))

dropLemma :  (m   : Nat)
          -> (G   : Normal)
          -> (shG : Shape G)
          -> m *Nat size G shG == crush (size G) (vec {m} shG)
dropLemma  zero   G shG                           = refl
dropLemma (suc m) G shG rewrite dropLemma m G shG = refl

drop : (F G : Normal) -> (F >< G) -N> (F oN G)
drop F G (shF , shG) rewrite dropLemma (size F shF) G shG =
  (shF , vec shG) , tabulate id

--\section{Proving Equations}


record MonoidOK X {{M : Monoid X}} : Set where
  field
    absorbL  : (x : X) ->      neut & x == x
    absorbR  : (x : X) ->      x & neut == x
    assoc    : (x y z : X) ->  (x & y) & z == x & (y & z)

natMonoidOK : MonoidOK Nat
natMonoidOK = record
  {  absorbL  = \ _ -> refl
  ;  absorbR  = _+zero
  ;  assoc    = assoc+
  }  where    -- see below
  _+zero : forall x -> x +Nat zero == x
  zero   +zero                  = refl
  suc n  +zero rewrite n +zero  = refl

  assoc+ : forall x y z -> (x +Nat y) +Nat z  == x +Nat (y +Nat z)
  assoc+ zero     y z                       = refl
  assoc+ (suc x)  y z rewrite assoc+ x y z  = refl

listNMonoidOK : {X : Set} -> MonoidOK (<! ListN !>N X)
listNMonoidOK {X} =
  record { absorbL = \ _ -> refl
         ; absorbR = _++neut
         ; assoc = assoc++
         } where

  _++neut : (xs : <! ListN !>N X) -> (fst xs +Nat 0 , snd xs ++ <>) == xs
  (zero  , <>)     ++neut = refl
  (suc n , y , ys) ++neut =
    cong (vv (λ m zs → suc m , y , zs))
         ((n , ys) ++neut)

  assoc++ : (xs ys zs : <! ListN !>N X)
          -> ((fst xs +Nat fst ys) +Nat fst zs , (snd xs ++ snd ys) ++ snd zs)
          == (fst xs +Nat (fst ys +Nat fst zs) , snd xs ++ (snd ys ++ snd zs))
  assoc++ (zero  , <>)      ys zs = refl
  assoc++ (suc n , x , xs') ys zs =
    cong (vv (λ m as → suc m , x , as))
         (assoc++ (n , xs') ys zs)

{-
\begin{exe}[a not inconsiderable problem]
Find out what goes wrong when you try to state associativity of vector |++|,
let alone prove it. What does it tell you about our |==| setup?
\end{exe}

Associacitivity-of-Vec-++ : forall {l m n X}
                          -> (xs : Vec X l)
                          -> (ys : Vec X m)
                          -> (zs : Vec X n)
                          -> (xs ++ ys) ++ zs
                          == xs ++ (ys ++ zs)


-}

record MonoidHom {X}{{MX : Monoid X}}{Y}{{MY : Monoid Y}}(f : X -> Y) : Set where
  field
    respNeut  :                 f neut == neut
    resp&     : forall x x' ->  f (x & x') == f x & f x'

fstHom : forall {X} -> MonoidHom {<! ListN !>N X}{Nat} fst
fstHom = record { respNeut = refl; resp& = \ _ _ -> refl }

record EndoFunctorOK F {{FF : EndoFunctor F}} : Set1 where
  field
    endoFunctorId  : forall {X} ->
      map {{FF}}{X} id == id
    endoFunctorCo  : forall {R S T}(f : S -> T)(g : R -> S) ->
      map {{FF}} f o map g == map (f o g)

{-
{- fool'e errand -}
vecEndoFunctorOK : forall {n} -> EndoFunctorOK \ X -> Vec X n
vecEndoFunctorOK = record
  {  endoFunctorId  = {!!}
  ;  endoFunctorCo  = \ f g -> {!!}
  }
-}

_=1=_ :  forall {l} {S : Set l} {T : S -> Set l}
         (f g : (x : S) -> T x) -> Set l
f =1= g = forall x -> f x == g x
infix 1 _=1=_

record EndoFunctorOKP F {{FF : EndoFunctor F}} : Set1 where
  field
    endoFunctorId  : forall {X} ->
      map {{FF}}{X} id =1= id
    endoFunctorCo  : forall {R S T}(f : S -> T)(g : R -> S) ->
      map {{FF}} f o map g =1= map (f o g)

--\section{Laws for |Applicative| and |Traversable|}

record ApplicativeOKP F {{AF : Applicative F}} : Set1 where
  field
    lawId :   forall {X}(x : F X) ->
      pure {{AF}} id <*> x == x
    lawCo :   forall {R S T}(f : F (S -> T))(g : F (R -> S))(r : F R) ->
      pure {{AF}} (\ f g -> f o g) <*> f <*> g <*> r == f <*> (g <*> r)
    lawHom :  forall {S T}(f : S -> T)(s : S) ->
      pure {{AF}} f <*> pure s == pure (f s)
    lawCom :  forall {S T}(f : F (S -> T))(s : S) ->
      f <*> pure s == pure {{AF}} (\ f -> f s) <*> f
  applicativeEndoFunctorOKP : EndoFunctorOKP F {{applicativeEndoFunctor}}
  applicativeEndoFunctorOKP = record
    {  endoFunctorId = lawId
    ;  endoFunctorCo = \ f g r ->
         pure {{AF}} f <*> (pure {{AF}} g <*> r)
           << lawCo (pure f) (pure g) r !!=
         pure {{AF}} (\ f g -> f o g) <*> pure f <*> pure g <*> r
           =!! cong (\ x -> x <*> pure g <*> r) (lawHom (\ f g -> f o g) f) >>
         pure {{AF}} (_o_ f) <*> pure g <*> r
           =!! cong (\ x -> x <*> r) (lawHom (_o_ f) g) >>
         pure {{AF}} (f o g) <*> r
           <QED>
    }


vecApplicativeOKP : {n : Nat} -> ApplicativeOKP \ X -> Vec X n
vecApplicativeOKP =
  record { lawId  = Preservation-of-Identity
         ; lawCo  = Applicative-Composition
         ; lawHom = Applicative-Hom
         ; lawCom = Applicative-Commutativity
         } where

  Preservation-of-Identity
    :  forall {m X} (x : Vec X m)
    -> vapp (vec (λ x₁ → x₁)) x == x

  Preservation-of-Identity
    <>
    = refl

  Preservation-of-Identity
    (x , xs)
    rewrite Preservation-of-Identity xs
    = refl

  Applicative-Composition
    :  forall {m R S T}
    -> (f : Vec (S -> T) m)
    -> (g : Vec (R -> S) m)
    -> (r : Vec R m)
    -> vapp (vapp (vapp (vec (λ f₁ g₁ a → f₁ (g₁ a))) f) g) r
    == vapp f (vapp g r)

  Applicative-Composition
    <> <> <>
    = refl

  Applicative-Composition
    (f , fs) (g , gs) (r , rs)
    rewrite Applicative-Composition fs gs rs
    = refl

  Applicative-Hom
    :  forall {m : Nat} {S T}
    -> (f : S -> T)
    -> (s : S)
    -> vapp {m} (vec f) (vec s)
    == vec  {m} (f s)

  Applicative-Hom
    {zero} fs ss
    = refl

  Applicative-Hom
    {suc m} fs ss
    rewrite Applicative-Hom {m} fs ss
    = refl

  Applicative-Commutativity
    :  forall {m S T}
    -> (f : Vec (S -> T) m)
    -> (s : S)
    -> vapp f (vec s)
    == vapp (vec (λ f₁ → f₁ s)) f

  Applicative-Commutativity
    <> s
    = refl

  Applicative-Commutativity
    (f , fs) s
    rewrite Applicative-Commutativity fs s
    = refl

--ApplicativeHomomorphisms

_-:>_ : forall (F G : Set -> Set) -> Set1
F -:> G = forall {X} -> F X -> G X

record AppHom  {F}{{AF : Applicative F}}{G}{{AG : Applicative G}}
               (k : F -:> G) : Set1 where
  field
    respPure  : forall {X}(x : X) -> k (pure x) == pure x
    respApp   : forall {S T}(f : F (S -> T))(s : F S) -> k (f <*> s) == k f <*> k s

monoidApplicativeHom :
  forall {X}{{MX : Monoid X}}{Y}{{MY : Monoid Y}}
  (f : X -> Y){{hf : MonoidHom f}} ->
  AppHom {{monoidApplicative {{MX}}}} {{monoidApplicative {{MY}}}} f
monoidApplicativeHom f {{hf}} = record
  {  respPure  = \ x -> MonoidHom.respNeut hf
  ;  respApp   = MonoidHom.resp& hf
  }

--Show that a homomorphism from |F| to |G| induces applicative structure
--on their pointwise sum.

homSum :  forall {F G} {{AF : Applicative F}} {{AG : Applicative G}}
       -> (f : F -:> G)
       -> Applicative \ X -> F X + G X
homSum {F} {G} {{AF}}{{AG}} f =
  record
  { pure  = λ x → tt , (pf x)
  ; _<*>_ = _<fg>_
  } where
    open Applicative AF renaming (pure to pf; _<*>_ to _<f>_)
    open Applicative AG renaming (pure to pg; _<*>_ to _<g>_)

    _<fg>_ :  forall {S T}
           -> (F (S -> T) + G (S -> T))
           -> (F S + G S)
           -> (F T + G T)

    (tt , ffs) <fg> (tt , fss) = tt , (ffs   <f> fss)
    (tt , ffs) <fg> (ff , gss) = ff , (f ffs <g> gss)
    (ff , gfs) <fg> (tt , fss) = ff , (gfs   <g> f fss)
    (ff , gfs) <fg> (ff , gss) = ff , (gfs   <g> gss)

homSumOKP :  forall {F G} {{AF : Applicative F}} {{AG : Applicative G}}
          -> ApplicativeOKP F
          -> ApplicativeOKP G
          -> (f : F -:> G)
          -> AppHom {F} {G} f
          -> ApplicativeOKP _ {{homSum f}}

homSumOKP {F} {G} {{AF}} {{AG}} FOK GOK f homf =
  record { lawId  = Preservation-of-Identity
         ; lawCo  = Applicative-Composition
         ; lawHom = Applicative-Hom
         ; lawCom = Applicative-Commutativity
         } where
  open Applicative (homSum f) renaming (pure to pfg; _<*>_ to _<fg>_)
  open Applicative  AF        renaming (pure to pf;  _<*>_ to _<f>_)
  open Applicative  AG        renaming (pure to pg;  _<*>_ to _<g>_)

  open ApplicativeOKP FOK renaming ( lawId  to f-lawId
                                   ; lawCo  to f-lawCo
                                   ; lawHom to f-lawHom
                                   ; lawCom to f-lawCom)

  open ApplicativeOKP GOK renaming ( lawId  to g-lawId
                                   ; lawCo  to g-lawCo
                                   ; lawHom to g-lawHom
                                   ; lawCom to g-lawCom)

  open AppHom homf

  Preservation-of-Identity
    :  forall {X}
    -> (x : F X + G X)
    -> pfg id <fg> x == x

  Preservation-of-Identity
    (tt , fx)
    rewrite f-lawId fx
    = refl

  Preservation-of-Identity
    (ff , gx)
    =   pfg id <fg> ff , gx
    =!! cong (λ fid → ff , (fid <g> gx)) (respPure id)
    >>  cong (_,_ ff) (g-lawId gx)

  f-comp : forall {R S T} -> F ((S -> T) -> (R -> S) -> R -> T)
  f-comp = pf \ h i -> h o i

  g-comp : forall {R S T} -> G ((S -> T) -> (R -> S) -> R -> T)
  g-comp = pg \ h i -> h o i

  Applicative-Composition
    :  forall {R S T}
    -> (f : F (S -> T) + G (S -> T))
    -> (g : F (R -> S) + G (R -> S))
    -> (r : F R + G R)
    -> pfg (\ h i -> h o i) <fg> f <fg> g <fg> r
    == f <fg> (g <fg> r)

  Applicative-Composition
    (tt , ffs) (tt , fgs) (tt , frs)
    rewrite f-lawCo ffs fgs frs
    = refl

  Applicative-Composition
    (tt , ffs) (tt , fgs) (ff , grs)
    =   ff , (f (f-comp <f> ffs <f> fgs) <g> grs)

    =!! cong (\ hole -> ff , (hole <g> grs))
             (respApp (f-comp <f> ffs) fgs)

    >>  ff , (f (f-comp <f> ffs) <g> f fgs <g> grs)

    =!! cong (\ hole -> ff , (hole <g> f fgs <g> grs))
             (respApp f-comp ffs)

    >>  (ff , (f f-comp <g> f ffs <g> f fgs <g> grs))

    =!! cong (\ hole -> ff , (hole <g> f ffs <g> f fgs <g> grs))
             (respPure (\ h i -> h o i))

    >>  (ff , (g-comp <g> f ffs <g> f fgs <g> grs))

    =!! cong (λ hole → ff , hole) (g-lawCo (f ffs) (f fgs) grs)

    >>  (ff , (f ffs <g> (f fgs <g> grs)))
    <QED>

  Applicative-Composition
    (tt , ffs) (ff , ggs) (tt , frs)
    =   ff , (f (f-comp <f> ffs) <g> ggs <g> f frs)

    =!! cong (\ hole -> ff , (hole <g> ggs <g> f frs))
             (respApp f-comp ffs)

    >>  ff , (f f-comp <g> f ffs <g> ggs <g> f frs)

    =!! cong (\ hole -> ff , (hole <g> f ffs <g> ggs <g> f frs))
             (respPure (\ h i -> h o i))

    >>  ff , (g-comp <g> f ffs <g> ggs <g> f frs)

    =!! cong (\ hole -> ff , hole)
             (g-lawCo (f ffs) ggs (f frs))

    >>  ff , (f ffs <g> (ggs <g> f frs))
    <QED>

  Applicative-Composition
    (tt , ffs) (ff , ggs) (ff , grs)
    =   ff , (f (f-comp <f> ffs) <g> ggs <g> grs)

    =!! cong (\ hole -> ff , (hole <g> ggs <g> grs))
             (respApp f-comp ffs)

    >>  ff , (f f-comp <g> f ffs <g> ggs <g> grs)

    =!! cong (\ hole -> ff , (hole <g> f ffs <g> ggs <g> grs))
             (respPure (\ h i -> h o i))

    >>  ff , (g-comp <g> f ffs <g> ggs <g> grs)

    =!! cong (\ hole -> ff , hole)
              (g-lawCo (f ffs) ggs grs)

    >>  (ff , (f ffs <g> (ggs <g> grs)))
    <QED>

  Applicative-Composition
    (ff , gfs) (tt , fgs) (tt , frs)
    =   ff , (f f-comp <g> gfs <g> f fgs <g> f frs)

    =!! cong (\ hole -> ff , (hole <g> gfs <g> f fgs <g> f frs))
             (respPure (\ h i -> h o i))

    >>  ff , (g-comp <g> gfs <g> f fgs <g> f frs)

    =!! cong (\ hole -> ff , hole) (g-lawCo gfs (f fgs) (f frs))

    >>  ff , (gfs <g> (f fgs <g> f frs))

    <<  cong (\ hole -> ff , (gfs <g> hole)) (respApp fgs frs)

    !!= (ff , (gfs <g> f (fgs <f> frs)))
    <QED>

  Applicative-Composition
    (ff , gfs) (tt , fgs) (ff , grs)
    =   ff , (f f-comp <g> gfs <g> f fgs <g> grs)

    =!! cong (\ hole -> ff , (hole <g> gfs <g> f fgs <g> grs))
             (respPure (\ h i -> h o i))

    >>  ff , (pg (\ h i -> h o i) <g> gfs <g> f fgs <g> grs)

    =!! cong (\ hole -> ff , hole)
             (g-lawCo gfs (f fgs) grs)

    >>  (ff , (gfs <g> (f fgs <g> grs)))
    <QED>

  Applicative-Composition
    (ff , gfs) (ff , ggs) (tt , frs)
    =   ff , (f f-comp <g> gfs <g> ggs <g> f frs)

    =!! cong (\ hole -> ff , (hole <g> gfs <g> ggs <g> f frs))
             (respPure \ h i -> h o i)

    >>  ff , (g-comp <g> gfs <g> ggs <g> f frs)

    =!! cong (\ hole -> ff , hole)
             (g-lawCo gfs ggs (f frs))

    >>  ff , (gfs <g> (ggs <g> f frs))
    <QED>

  Applicative-Composition
    (ff , gfs) (ff , ggs) (ff , grs)
    =   ff , (f f-comp <g> gfs <g> ggs <g> grs)

    =!! cong (\ hole -> ff , (hole <g> gfs <g> ggs <g> grs))
             (respPure \ h i -> h o i)

    >>  (ff , (g-comp <g> gfs <g> ggs <g> grs))

    =!! cong (\ hole -> ff , hole)
             (g-lawCo gfs ggs grs)

    >>  (ff , (gfs <g> (ggs <g> grs)))
    <QED>

  Applicative-Hom
    :  forall {S T}
    -> (h : S -> T)
    -> (s : S)
    -> pfg h <fg> pfg s
    == pfg (h s)

  Applicative-Hom
    h s
    =   tt , (pf h <f> pf s)

    =!! cong (\ hole -> tt , hole) (f-lawHom h s)

    >>  (tt , (pf (h s)))
    <QED>

  Applicative-Commutativity
    :  forall {S T}
    -> (fgh : F (S -> T) + G (S -> T))
    -> (s : S)
    -> fgh <fg> (pfg s)
    == pfg (\ h -> h s) <fg> fgh

  Applicative-Commutativity
    (tt , fh) s
    =   tt , (fh <f> pf s)

    =!! cong (\ hole -> tt , hole)
             (f-lawCom fh s)

    >>  tt , (pf (\ h -> h s) <f> fh)
    <QED>

  Applicative-Commutativity
    (ff , gh) s
    =   ff , (gh <g> f (pf s))

    =!! cong (\ hole -> ff , (gh <g> hole))
             (respPure s)

    >>  ff , (gh <g> pg s)

    =!! cong (\ hole -> ff , hole)
             (g-lawCom gh s)

    >>  ff , (pg (\ h -> h s) <g> gh)

    <<  cong (\ hole -> ff , (hole <g> gh))
             (respPure (\ h -> h s))

    !!= (ff , (f (pf \ h -> h s) <g> gh))
    <QED>

-- traversable laws

record TraversableOKP F {{TF : Traversable F}} : Set1 where
  field
    lawId :  forall {X} (xs : F X) -> traverse id xs == xs

    lawCo :  forall {G} {{AG : Applicative G}}
                    {H} {{AH : Applicative H}}
                    {R S T}
          -> (g : S -> G T)
          -> (h : R -> H S)
          -> (rs : F R)
          -> let  EH : EndoFunctor H
                  EH = applicativeEndoFunctor
             in   map {H} (traverse g) (traverse h rs)
             ==   traverse {{TF}} {{applicativeComp AH AG}} (map{H} g o h) rs

    lawHom :  forall {G} {{AG : Applicative G}}
                     {H} {{AH : Applicative H}}
              (h : G -:> H)
              {S T}
              (g : S -> G T)
           -> AppHom {G} {H} h
           -> (ss : F S)
           -> traverse (h o g) ss
           == h (traverse g ss)

-- fromNormal

Batch : Set -> Set -> Set
Batch X Y = Sg Nat \ n -> Vec X n -> Y

instance batchApplicative : forall {X} -> Applicative (Batch X)
batchApplicative {X} =
  record { pure  = batch-pure
         ; _<*>_ = _<b>_
         } where
  batch-pure : forall {Y} -> Y -> Batch X Y
  batch-pure y = 0 , (\ _ -> y)

  mkT :  forall {m n X S T}
      -> (Vec X m -> S -> T)
      -> (Vec X n -> S)
      -> Vec X (m +Nat n)
      -> T
  mkT {m} mkF mkS xs with split m xs
  ...                   | fxs , xss = mkF fxs (mkS xss)

  _<b>_ :  forall {S T}
        -> Batch X (S -> T)
        -> Batch X S
        -> Batch X T

  (m , mkF) <b> (n , mkS) = (m +Nat n) , mkT mkF mkS

{-
fromNormal :  forall {F} {{TF : Traversable F}}
           -> TraversableOKP F
           -> forall {X}
           -> <! normalT F !>N X
           -> F X
fromNormal tokf {X} (sh , xs) = (vv \ n mkF -> mkF xs) (traverse alignX sh)
  where
    unbox : forall {X} → Vec X 1 → X
    unbox (x , <>) = x

    alignX : One -> Batch X X
    alignX <> = 1 , unbox
 -}

-- fixpoints of normal functors

data Tree (N : Normal) : Set where
  <$_$> : <! N !>N (Tree N) -> Tree N

NatT : Normal
NatT = Two / 0 <?> 1

zeroT : Tree NatT
zeroT = <$ tt , <> $>

sucT : Tree NatT -> Tree NatT
sucT n = <$ ff , n , <> $>

NatInd :  forall {l}
       -> (P : Tree NatT -> Set l)
       -> P zeroT
       -> ((n : Tree NatT) -> P n -> P (sucT n))
       -> (n : Tree NatT)
       -> P n
NatInd P z s <$ tt , <> $>     = z
NatInd P z s <$ ff , n , <> $> = s n (NatInd P z s n)

tl : forall {n X} -> Vec X (suc n) -> Vec X n
tl (_ , xs) = xs

hd : forall {n X} -> Vec X (suc n) -> X
hd (x , _) = x

eq? :  (N : Normal)
    -> ((s s' : Shape N) -> Dec (s == s'))
    -> (t t' : Tree N)
    -> Dec (t == t')

eq? N sheq? <$ shT , xs $> <$ shU , ys $> with sheq? shT shU

eq? N sheq? <$ shT , xs $> <$ shU , ys $> | ff , contra =
  ff , contra o cong extractShape
  where
    extractShape : forall {N} -> Tree N -> Shape N
    extractShape <$ sh , _ $> = sh

eq? N sheq? <$ shT , xs $> <$ shU , ys $> | tt , sheq
  with veq? (subst sheq (\ sh -> Vec (Tree N) (size N sh)) xs) ys
  where
    veq? : forall {n}
        -> (xs : Vec (Tree N) n)
        -> (ys : Vec (Tree N) n)
        -> Dec (xs == ys)

    veq? (x , xs') (y , ys')   with eq? N sheq? x y
    veq? (x , xs') (y , ys')   | ff , contra             = ff , contra o cong hd
    veq? (x , xs') (.x , ys')  | tt , refl with veq? xs' ys'
    veq? (x , xs') (.x , ys')  | tt , refl | ff , contra = ff , contra o cong tl
    veq? (x , xs') (.x , .xs') | tt , refl | tt , refl   = tt , refl
    veq? <>        <>                                    = tt , refl

eq? N sheq? <$ shT , xs $> <$ shU , ys $> | tt , sheq | ff , contra =
  ff , (\ lie -> contra (expose-lie sheq lie))
  where
    expose-lie :  forall {shT shU xs ys}
               -> (p : shT == shU)
               -> (q : <$ shT , xs $> == <$ shU , ys $>)
               -> subst p (\ sh -> Vec (Tree N) (size N sh)) xs == ys
    expose-lie refl refl = refl

eq? N sheq? <$ shT , xs $> <$ shU , ys $> | tt , sheq | tt , veq =
  tt , unify-types sheq veq
  where
    unify-types :  forall {shT shU xs ys}
                -> (p : shT == shU)
                -> (q : subst p (\ sh -> Vec (Tree N) (size N sh)) xs == ys)
                -> <$ shT , xs $> == <$ shU , ys $>
    unify-types refl refl = refl
