{-# LANGUAGE BangPatterns, DeriveFunctor, DeriveFoldable, DeriveTraversable, ScopedTypeVariables, DeriveGeneric, DeriveDataTypeable, GeneralizedNewtypeDeriving #-}
module LTL where

import Data.Data
import Data.List (find)
import Data.Set (Set)
import qualified Data.Set as S
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IM
import Data.IntSet (IntSet)
import qualified Data.IntSet as IS
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Class
import Control.Monad.IO.Class
import GHC.Generics
import Data.Graph.Inductive.PatriciaTree

{-
- Specification is toplevel conjuction of formulae
- we want to check if a system satisfies the Specification
- To do this we build a Buchi automoton of the system and a Buchi automoton
- of the Specification and check if the intersection is empty.
-
- What does it mean for a formula in LTL to be valid?
- We construct Buchi Automoton from Formula, take its complement, then
- check if complement is empty.
- 
-
-}

newtype FreshNodeT m a = FNT { extractFNTState :: StateT Int m a }
  deriving (Typeable, Generic, Functor, Applicative, Monad, MonadTrans, MonadIO)


data Formula a = 
    Var a
  | Truth                           -- true
  | Falsehood                       -- false
  | Neg (Formula a)
  | Next (Formula a)
  | Always (Formula a)              -- aka globally
  | Eventually (Formula a)          -- aka finally
  | Implies (Formula a) (Formula a) -- true if f1 is False or (f1 and f2 are true)
  | Iff (Formula a) (Formula a)     -- if and only if
  | Conj (Formula a) (Formula a)    -- and
  | Disj (Formula a) (Formula a)    -- or
  | Until (Formula a) (Formula a)   -- f1 is true at least until f2 is true,
                                    -- and f2 is true currently or in future
  | Release (Formula a) (Formula a) -- f2 is true until and including when 
                                    -- f1 first becomes true, if f1 never 
                                    -- becomes true, f2 must remain true forever
  deriving (Show, Eq, Ord, Read, Functor, Data, Typeable, Generic, Foldable, Traversable)



data DSFormula a = 
    DsVar a
  | DsTruth                               -- true
  | DsFalsehood                           -- false
  | DsNeg (DSFormula a)
  | DsNext (DSFormula a)
  | DsConj (DSFormula a) (DSFormula a)    -- and
  | DsDisj (DSFormula a) (DSFormula a)    -- or
  | DsUntil (DSFormula a) (DSFormula a)   -- f1 is true at least until f2 is true,
                                          -- and f2 is true currently or in future
  | DsRelease (DSFormula a) (DSFormula a) -- f2 is true until and including when 
                                          -- f1 first becomes true, if f1 never 
                                          -- becomes true, f2 must remain true forever
  deriving (Show, Eq, Ord, Read, Functor, Data, Typeable, Generic, Foldable, Traversable)


data NNF a = 
    NnfVar a
  | NnfNegVar a
  | NnfTruth                   -- true
  | NnfFalsehood               -- false
  | NnfNext (NNF a)
  | NnfConj (NNF a) (NNF a)    -- and
  | NnfDisj (NNF a) (NNF a)    -- or
  | NnfUntil (NNF a) (NNF a)   -- f1 is true at least until f2 is true,
                               -- and f2 is true currently or in future
  | NnfRelease (NNF a) (NNF a) -- f2 is true until and including when 
                               -- f1 first becomes true, if f1 never 
                               -- becomes true, f2 must remain true forever
  deriving (Show, Eq, Ord, Read, Functor, Data, Typeable, Generic, Foldable, Traversable)


desugarFormula :: Formula x -> DSFormula x
desugarFormula f =
  case f of
    Var a -> DsVar a
    Truth -> DsTruth
    Falsehood -> DsFalsehood
    Neg f1 -> DsNeg (desugarFormula f1)
    Next f1 -> DsNext (desugarFormula f1)
    Always f1 -> DsRelease DsFalsehood (desugarFormula f1)
    Eventually f1 -> DsUntil DsTruth (desugarFormula f1)
    Implies f1 f2 -> DsDisj (DsNeg (desugarFormula f1)) (desugarFormula f2)
    Iff f1 f2 -> DsConj (desugarFormula (Implies f1 f2)) (desugarFormula (Implies f2 f1))
    Conj f1 f2 -> DsConj (desugarFormula f1) (desugarFormula f2)
    Disj f1 f2 -> DsDisj (desugarFormula f1) (desugarFormula f2)
    Until f1 f2 -> DsUntil (desugarFormula f1) (desugarFormula f2)
    Release f1 f2 -> DsRelease (desugarFormula f1) (desugarFormula f2)

nnf :: DSFormula x -> NNF x
nnf f =
  case f of
    DsVar a -> NnfVar a
    DsTruth -> NnfTruth
    DsFalsehood -> NnfFalsehood
    DsNext f1 -> NnfNext (nnf f1)
    DsRelease f1 f2 -> NnfRelease (nnf f1) (nnf f2)
    DsUntil f1 f2 -> NnfUntil (nnf f1) (nnf f2)
    DsConj f1 f2 -> NnfConj (nnf f1) (nnf f2)
    DsDisj f1 f2 -> NnfDisj (nnf f1) (nnf f2)
    DsNeg f' ->
      case f' of
        DsVar a -> NnfNegVar a
        DsNeg f2 -> nnf f2
        DsTruth -> NnfFalsehood
        DsFalsehood -> NnfTruth
        DsConj f1 f2 -> NnfDisj (nnf (DsNeg f1)) (nnf (DsNeg f2))
        DsDisj f1 f2 -> NnfConj (nnf (DsNeg f1)) (nnf (DsNeg f2))
        DsNext f1 -> NnfNext (nnf (DsNeg f1))
        DsUntil f1 f2 -> NnfRelease (nnf (DsNeg f1)) (nnf (DsNeg f2))
        DsRelease f1 f2 -> NnfUntil (nnf (DsNeg f1)) (nnf (DsNeg f2))


runFreshNode :: Monad m => FreshNodeT m a -> m a
runFreshNode (FNT f) = evalStateT f 0

getNewId :: Monad m => FreshNodeT m Int
getNewId = FNT $ do s <- get
                    put (s + 1)
                    return s

data ExpandParams a = 
  EP { epNodes :: IntSet
     , epIncoming :: IntMap IntSet
     , epNow :: IntMap (Set (NNF a))
     , epNext :: IntMap (Set (NNF a)) }
     deriving (Show, Eq)

curr1 :: Ord a => NNF a -> Set (NNF a)
curr1 f = 
  case f of
    NnfUntil f1 _ -> S.singleton f1
    NnfRelease _ f2 -> S.singleton f2
    NnfDisj _ f2 -> S.singleton f2
    _ -> error "curr1 goofed"

next1 :: Ord a => NNF a -> Set (NNF a)
next1 f =
  case f of
    NnfUntil _ _ -> S.singleton f
    NnfRelease _ _ -> S.singleton f
    NnfDisj _ _ -> S.empty
    _ -> error "next1 goofed"

curr2 :: Ord a => NNF a -> Set (NNF a)
curr2 f = 
  case f of
    NnfUntil _ f2 -> S.singleton f2
    NnfRelease f1 f2 -> S.fromList [f1, f2]
    NnfDisj f1 _ -> S.singleton f1
    _ -> error "curr2 goofed"

expand :: Ord a =>
          Set (NNF a)               -- current formulas
        -> Set (NNF a)              -- old formulas
        -> Set (NNF a)              -- next formulas
        -> IntSet                   -- incoming edges
        -> FreshNodeT (State (ExpandParams a)) ()
expand !curr !old !next !incoming
  | S.empty == curr = do
      ep <- lift get 
      ls <- return $ find 
           (\nid -> IM.lookup nid (epNext ep) == Just next 
                      && IM.lookup nid (epNow ep) == Just old)
           (IS.toList $ epNodes ep)
      case ls of
        (Just nid) -> do
          epincoming' <- return $ IM.insertWith IS.union nid incoming (epIncoming ep)
          lift (put (ep {epIncoming = epincoming'} ))
        Nothing -> do
          nid <- getNewId
          epNodes' <- return $ IS.insert nid (epNodes ep)
          epIncoming' <- return $ IM.insert nid incoming (epIncoming ep)
          epNow' <- return $ IM.insert nid old (epNow ep)
          epNext' <- return $ IM.insert nid next (epNext ep)
          lift $ put (ep { epNodes = epNodes', epIncoming = epIncoming', epNow = epNow', epNext = epNext'})
  | otherwise = do
      f <- return $ S.elemAt 0 curr
      curr' <- return $ S.deleteAt 0 curr
      old' <- return $ S.insert f old
      case f of
        NnfTruth -> expand curr' old' next incoming
        NnfFalsehood -> return ()
        NnfVar a | S.member (NnfNegVar a) old' -> return ()
                 | otherwise -> expand curr' old' next incoming
        NnfNegVar a | S.member (NnfVar a) old' -> return ()
                    | otherwise -> expand curr' old' next incoming
        NnfConj f1 f2 -> do
          curr'' <- return $ S.union curr' (S.fromList [f1,f2] `S.difference` old')
          expand curr'' old' next incoming
        NnfNext f1 -> expand curr' old' (S.union next (S.singleton f1)) incoming
        NnfDisj _ _ -> expand_h f curr' old' next incoming
        NnfUntil _ _ -> expand_h f curr' old' next incoming
        NnfRelease _ _ -> expand_h f curr' old' next incoming
        where
          expand_h f cur ol nxt incm =
            expand (S.union cur (S.difference (curr1 f) ol)) ol (S.union nxt (next1 f)) incm >>
            expand (S.union cur (S.difference (curr2 f) ol)) ol nxt incm

createGraph :: Ord a => Formula a -> (IntSet, IntMap IntSet, IntMap (Set (NNF a)))
createGraph f = (epNodes ep, epIncoming ep, epNow ep)
  where
    curr = S.singleton (nnf (desugarFormula f))
    old = S.empty
    next = S.empty
    incoming = IS.singleton (-1)
    ep0 = EP IS.empty IM.empty IM.empty IM.empty
    ep = execState (evalStateT (extractFNTState (expand curr old next incoming)) 0) ep0

data LGBA a =
  LGBA { lgbaStates :: IntSet
       , lgbaAlphabet :: Set a
       , lgbaLabel :: IntMap a
       , lgbaTransition :: IntMap Int
       , lgbaInit :: IntSet
       , lgbaFinal :: IntSet }
  deriving (Show, Eq)

{-
constructLGBA :: Set a -> IntSet -> IntMap IntSet -> IntMap (Set (NNF a)) -> LGBA a
constructLGBA ap nodes now incoming = lgba
  where
    lables = IM.fromList (map
                         (\q ->
                            let p = S.toList ap
                                qs = IM.lookup q now
                                ps = filter (\p -> NnfNegVar p `IS.member` qs)
                            in (q, qs, IM.lookup q now)
                         (IS.toList nodes)
-}


sugared :: Formula String
sugared = Always (Implies (Var "Alive")
                          (Eventually (Neg (Var "Alive"))))

desugared :: DSFormula String
desugared = desugarFormula sugared


spec :: Formula String
spec = undefined
