module Exe3 where

open import Proving public
open import NormF public

record Con : Set1 where
  constructor _<1_
  field
    Sh  : Set             -- a set of shapes
    Po  : Sh -> Set       -- a family of positions
  <!_!>c : Set -> Set
  <!_!>c X = Sg Sh \ s -> Po s -> X
open Con public
infixr 1 _<1_

Kc : Set -> Con
Kc A = A <1 \ _ -> Zero

Ic : Con
Ic = One <1 \ _ -> One

_+c_ : Con -> Con -> Con
(S <1 P) +c (S' <1 P') = (S + S') <1 vv P <?> P'

_*c_ : Con -> Con -> Con
(S <1 P) *c (S' <1 P') = (S * S') <1 vv \ s s' -> P s + P' s'

Sgc : (A : Set)(C : A -> Con) -> Con
Sgc A C = (Sg A \ a -> Sh (C a)) <1 vv \ a s -> Po (C a) s

Pic : (A : Set)(C : A -> Con) -> Con
Pic A C = ((a : A) -> Sh (C a)) <1 \ f -> Sg A \ a -> Po (C a) (f a)

_oc_ : Con -> Con -> Con
(S <1 P) oc C = Sgc S \ s -> Pic (P s) \ p -> C

{- {exe}[containers are endofunctors]
Check that containers yield endofunctors which obey the laws. -}

instance conEndoFunctor : {C : Con} -> EndoFunctor <! C !>c
conEndoFunctor {S <1 P} = record { map = conMap }
  where
    conMap :
         forall {A B}
      -> (A -> B)
      -> <! S <1 P !>c A
      -> <! S <1 P !>c B

    conMap f (sh , po) = sh , (f o po)

conEndoFunctorOKP : {C : Con} -> EndoFunctorOKP <! C !>c
conEndoFunctorOKP {S <1 P} =
  record { endoFunctorId = Identity-Law
         ; endoFunctorCo = Composition-Law
         }
  where
    open EndoFunctor conEndoFunctor renaming (map to cmap)

    Identity-Law :
         forall {X}
      -> cmap {X} id =1= id
    Identity-Law x = refl

    Composition-Law :
         forall {R S T}
      -> (f : S -> T)
      -> (g : R -> S)
      -> cmap f o cmap g =1= cmap (f o g)

    Composition-Law f g (sh , po) =
          cmap f (cmap g (sh , po)) =!! refl
      >>  cmap f (sh , g o po)      =!! refl
      >>  sh , f o (g o po)         <<  refl
      !!= sh , (f o g) o po         <<  refl
      !!= cmap (f o g) (sh , po)    <QED>


{- {exe}[closure properties]
Check that the meanings of the operations on containers are justified
by their interpretations as functors. -}


-----------------------------------------------------------------------
_-c>_ : Con -> Con -> Set
(S <1 P) -c> (S' <1 P') = Sg (S -> S') \ f -> (s : S) -> P' (f s) -> P s

_/c_ : forall {C C'} -> C -c> C' -> forall {X} -> <! C !>c X -> <! C' !>c X
(to , fro) /c (s , k) = to s , k o fro s

{- {exe}[representing natural transformations]
Check that you can represent any natural transformation between
containers as a container morphism. -}

morphc : forall {C C'} -> (forall {X} -> <! C !>c X -> <! C' !>c X) -> C -c> C'
morphc {S <1 P} {S' <1 P'} f = shF , poF
  where
    shF : S -> S'
    shF sh with f {P sh} (sh , id)
    shF sh |    sh' , _ = sh'

    poF : (sh : S) -> P' (shF sh) -> P sh
    poF sh with f {P sh} (sh , id)
    poF sh |    _ , po' = po'

{- {exe}[identity and composition]
Check that you can define identity and composition for container morphisms. -}

idmc : forall {C} -> C -c> C
idmc = id , (\ _ -> id)

_omc_ : forall {C D E} -> (D -c> E) -> (C -c> D) -> (C -c> E)
(eShF , ePoF) omc (dShF , dPoF) = (eShF o dShF) , (λ s → dPoF s o ePoF (dShF s))


------------------------------------------------------------------------
data W (C : Con) : Set where
  <$_$> : <! C !>c (W C) -> W C

{- {exe}[natural numbers]
Define natural numbers as a |W|-type. Implement the constructors.
Hint: |magic : Zero -> {A : Set} -> A|.
Implement primitive recursion and use it to implement addition. -}

NatW : Set
NatW = W (Two <1 (Zero <?> One))

zeroW : NatW
zeroW = <$ tt , magic $>

sucW : NatW -> NatW
sucW n = <$ ff , (\ <> -> n) $>

precW : forall {l}{T : Set l} -> T -> (NatW -> T -> T) -> NatW -> T
precW z s <$ tt , _ $> = z
precW z s <$ ff , snd $> =
  let prd : NatW
      prd = snd <>
  in
      s prd (precW z s prd)

addW : NatW -> NatW -> NatW
addW x y = precW zeroW (λ _ → sucW) x

{- How many different implementations of |zeroW| can you find?
Meanwhile, discover for yourself why an attempt to establish the
induction principle is a fool's errand.

indW :
     forall {l}
  -> (P : NatW -> Set l)
  ->  P zeroW
  -> ((n : NatW) -> P n -> P (sucW n))
  -> (n : NatW)
  -> P n
indW P z s <$ tt , snd $> = {!z!}
-- magic x != snd x of type W (Two <1 Zeor <?> One)
indW P z s <$ ff , snd $> = {!!}
-}


_^*_ : Con -> Set -> Set
C ^* X = W (Kc X +c C)

{- {exe}[free monad]
Construct the components for -}

instance freeMonad : (C : Con) -> Monad (_^*_ C)
freeMonad C =
  record { return = λ x → <$ (tt , x) , magic $>
         ; _>>=_  = bind
         }
  where
    bind :
      {S T : Set}
      -> C ^* S
      -> (S -> C ^* T)
      -> C ^* T
    bind         <$ (tt , x)  , chs $> f = f x
    bind {T = T} <$ (ff , sh) , chs $> f =
      <$ (ff , sh) , (λ po → bind (chs po) f) $>


{- {exe}[free monad closure]
Define an operator -}

_^*c : Con -> Con
C ^*c = C ^* One <1 po
  where
    po : C ^* One -> Set
    po <$ (tt , <>) , _   $> = One
    po <$ (ff , sh) , po' $> =
      Sg (Po (Kc One +c C) (ff , sh)) \ p -> po (po' p)

-- I wanted quite badly to define this as `Ic +c (C oc (C ^*c))` but strictness
-- prevented me.

{- and exhibit an isomorphism
\[
  |C ^* X| \cong |<! C ^*c !>c X|
\] -}

{-We can model\nudge{in too much detail}, the general recursive function
space as the means to perform finite, on demand expansion of call trees. -}

Pib : (S : Set)(T : S -> Set) -> Set
Pib S T = (s : S) -> (S <1 T) ^* T s

{- {exe}[general recursion]
Define the monadic computation which performs one command-response
interaction: -}

call : forall {C} -> Pib (Sh C) (Po C)
call {S <1 P} s = <$ (ff , s) , (\ p -> <$ (tt , p) , magic $>) $>

{- Give the `gasoline-driven' interpreter for this function space,
delivering a result provided the call tree does not expand more times
than a given number. -}

gas : forall {S T} -> Nat -> Pib S T -> (s : S) -> T s + One
gas          zero   _ _ = ff , <>
gas {S} {T} (suc n) f s = go (f s)
  where
    go : (S <1 T) ^* T s -> T s + One
    go <$ (tt , res) , _ $> = tt , res
    go <$ (ff , s') , more $> with gas n f s'
    go <$ (ff , s') , more $> | tt , mid = go (more mid)
    go <$ (ff , s') , more $> | ff , <> = ff , <>

{- Feel free to implement reduction for the untyped
$\lambda$-calculus, or some other model of computation, as a recursive
function in this way. -}

_=m>_ : Set -> Set -> Set
X =m> Y = Pib X (\ _ -> Y)

driver : Set -> Set -> Set -> Set
driver Cmd Rsp Ret = (Cmd <1 \ _ -> Rsp) ^* Ret

delay :
     {{m : Monad (driver Nat Nat)}}
  -> Nat =m> Nat
delay  zero   = return zero
delay (suc n) = call n >>= (return o suc)

{-
 `delay` is the monadic equivalent of:

     foo : Nat -> Nat
     foo  zero   = zero
     foo (suc n) = suc (foo n)
 -}

----------------------------------------------------------------------
_-_ : (X : Set)(x : X) -> Set
X - x = Sg X \ x' -> x' == x -> Zero

der : Con -> Con
der (S <1 P) = Sg S P <1 vv \ s p -> P s - p

{- {exe}[|plug|]
Exhibit a container morphism which witnesses the ability to
fill the hole, provided equality on positions is decidable. -}

plug :
      forall {C}
  -> ((s : Sh C) -> (p p' : Po C s) -> Dec (p == p'))
  -> (der C *c Ic) -c> C
plug {C} poeq? = plugShape , plugPo
  where
    plugShape : Sh (der C *c Ic) -> Sh C
    plugShape ((sh , hole) , <>) = sh

    plugPo :
         (s : Sh (der C *c Ic))
      -> (Po C (plugShape s))
      -> (Po (der C *c Ic) s)
    plugPo ((sh , hole) , <>) po with poeq? sh po hole
    plugPo ((sh , hole) , <>) po | tt , eq     = ff , <>
    plugPo ((sh , hole) , <>) po | ff , contra = tt , po , contra


{- {exe}[laws of calculus]
Check that the following laws hold at the level of mutually inverse
container morphisms.

\[\begin{array}{r@@{\quad\cong\quad}l}
|der (Kc A)| & |Kc Zero| \\
|der I|      & |Kc One| \\
|der (C +c D)| & |der C +c der D| \\
|der (C *c D)| & |(der C *c D) +c (C *c der D)| \\
|der (C oc D)| & |(der C oc D) *c der D|
\end{array}\]

What is |der (C ^*c)| ?
-}
