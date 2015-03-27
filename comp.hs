{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ViewPatterns              #-}
{- CHAPTER 3: Categories and Functors -}
import           Control.Arrow ((***))
import           Data.Set      (Set)
import qualified Data.Set      as S

{- CATEGORIES -}
composeErr = error "Arrows don't compose"
data Cat o a = Cat {src, tgt :: a -> o, iden :: o -> a, comp :: a -> a -> a}

{- Category of set morphisms -}
data SetArrow a = SetArrow {setSrc :: Set a, setFun :: a -> a, setTgt :: Set a}

finSet :: Eq a => Cat (Set a) (SetArrow a)
finSet = Cat setSrc setTgt setId setComp where
  setId o = SetArrow o id o
  setComp (SetArrow b' g c) (SetArrow a f b) = if b'==b then SetArrow a (g . f) c
                                               else composeErr

{- Kleisli Catgory of term substitutions -}
data Opr a = Opr {oprName :: String, oprArity :: Set a} deriving (Show,Eq)
data Term a = Var a | Apply (Opr a) (a -> Term a)
data Substitution a = Subst {substSrc :: (Set a), substFun :: a -> Term a, substTgt :: (Set a)}
substApply t s@(Subst a f b) = case t of
  Var x -> f x
  Apply psi s' -> Apply psi $ \x -> substApply (s' x) s
finKleisli = Cat substSrc substTgt substId substComp where
  substId o = Subst o Var o
  substComp s@(Subst b' g c) (Subst a f b) = if b'==b then Subst a (\x -> substApply (f x) s) c
                                             else composeErr

{- Finite Category -}
data Obj = A | B | C deriving (Show,Eq)
data Arrow = F | G | H | K | ID Obj deriving (Show,Eq)
exampleCategory =
  let src arr = case arr of;F -> B;G -> A;H -> A;K -> B; ID x -> x
      tgt arr = case arr of;F -> A;G -> C;H -> C;K -> C; ID x -> x
      iden = ID
      comp g f = case (g,f) of
        (G,F) -> K; (H,F) -> K;
        (ID x,u) | tgt u==x -> u
        (u,ID x) | src u==x -> u
        _ -> composeErr
  in Cat src tgt iden comp

{- FUNCTORS -}

data Funct oA aA oB aB = Funct {fSrc   :: Cat oA aA,
                                objFun :: oA -> oB,
                                arrFun :: aA -> aB,
                                fTgt   :: Cat oB aB}
fIden a = Funct a id id a

cartProd a b = S.fromDistinctAscList
                    [(i,j) | i <- S.toAscList a, j <- S.toAscList b]
prodArrow (SetArrow a f b) (SetArrow a' g b') = SetArrow (a `cartProd` a')
                                                         (f *** g)
                                                         (b `cartProd` b')
diagFunctor = Funct finSet (\a -> cartProd a a) (\f -> prodArrow f f) finSet

{- DUALITY -}
dualCat (Cat s t i c) = Cat t s i (flip (.))
dualFun (Funct a fo fa b) = Funct (dualCat a) fo fa (dualCat b)

{- CHAPTER 4: Limits and Colimits -}

data InitialObj o a = Initial {initObj :: o, univInit :: o -> a}

setInitial :: InitialObj (Set a) (SetArrow a)
setInitial =  Initial S.empty (SetArrow S.empty undefined)


isoInitial :: InitialObj o a -> InitialObj o a -> (a,a) {-Inverses-}
isoInitial (Initial a univ_a) (Initial a' univ_a') = (univ_a a',univ_a' a)


type HasCoproducts o a =  o -> o -> Coproduct o a
data Coproduct o a = Coprod {coprodObj :: {-z-} o, inl :: {-x->z-} a, inr :: {-y->z-} a,
                                   univCoprod :: {-z'-} o -> {-x->z'-} a -> {-y->z'-} a -> {-z->z'-} a}

data Tag a = Just' a | Left' (Tag a) | Right' (Tag a) deriving (Show,Eq,Ord)

setCoprod :: Ord a => Set (Tag a) -> Set (Tag a) -> Coproduct (Set (Tag a)) (SetArrow (Tag a))
setCoprod a b =
  let sumAB = S.map Left' a `S.union` S.map Right' b
      {- the disjoint union -}
      univ c (setFun -> f) (setFun -> g) = let fg x = case x of
                                                 Left' x -> f x
                                                 Right' x -> g x
                                           in SetArrow sumAB fg c
      {- the universal part -}
  in Coprod sumAB (SetArrow a Left' sumAB) (SetArrow b Right' sumAB) univ

type HasCoequalizers o a = a -> a -> Coequalizer o a
data Coequalizer o a = Coeq {coeqObj :: o, coeqArr :: a, univCoeq :: o -> a -> a}

type HasPushout o a = a -> a -> Pushout o a
data Pushout o a = Pushout {gpushf :: a, fpushg :: a, univPushout :: a -> a -> a}


{- COLIMITS -}
data Graph n e = Graph {nodes :: Set n, edges :: Set e, graphSrc, graphTgt :: e -> n}
data Diagram n e o a = Diagram {graph :: Graph n e, nodeData :: n -> o, edgeData :: e -> a}

data Cocone o a = forall n e. Cocone {coconeObj :: o, coconeBase :: Diagram n e o a, coconeArrows :: n -> a}
data CoconeArrow o a = CoconeArrow {coconeSrc :: Cocone o a, coconeFun :: a, coconeTgt :: Cocone o a}
--TODO: Turn into category

data Colimit o a = Colimit {colimitObj :: Cocone o a,
                            univColimit :: Cocone o a -> CoconeArrow o a}
data Cocomplete o a = forall n e.  Cocomplete {objCocomplete :: Cat o a,
                                               univCocomplete :: Diagram n e o a -> Colimit o a}
--TODO: Make objX/univX naming consistent

data CoContinuous oA aA oB aB  = Cocontinuous {objCocontinuous :: Funct oA aA oB aB,
                                               univCocontinuous :: Colimit oA aA -> Colimit oB aB}

type FiniteCoproduct o a = Cat o a -> InitialObj o a -> HasCoproducts o a -> (Diagram o a -> Colimit o a)
--PAGE 85
