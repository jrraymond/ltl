{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, ScopedTypeVariables, DeriveGeneric, DeriveDataTypeable #-}
module LTP where

import Data.Data
import GHC.Generics


data Formula a = 
    Var a
  | Truth                             -- true
  | Falsehood                          -- false
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
  | DsTruth                             -- true
  | DsFalsehood                          -- false
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
  | NnfTruth                             -- true
  | NnfFalsehood                          -- false
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


sugared :: Formula String
sugared = Always (Implies (Var "Alive")
                          (Eventually (Neg (Var "Alive"))))

desugared :: DSFormula String
desugared = desugarFormula sugared
