{-# LANGUAGE BangPatterns, DeriveFunctor, DeriveFoldable, DeriveTraversable, ScopedTypeVariables, DeriveGeneric, DeriveDataTypeable, GeneralizedNewtypeDeriving #-}
module LTL where

import Data.Data
import GHC.Generics
import Data.Graph (Graph)
import qualified Data.Graph as G
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IM
import Data.IntSet (IntSet)
import qualified Data.IntSet as IS
import Data.List (find, intersect)
import Data.Maybe (mapMaybe, fromMaybe)
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Class
import Control.Monad.IO.Class
import Data.Set (Set)
import qualified Data.Set as S
import Data.Tree (Tree)
import qualified Data.Tree as T (flatten)


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
- The algorithm we use for translating LTL formulae to Buchi Automaton is
- from Gerth et al "Simple On-The-Fly Automatic Verification of Linear
- Temporal Logic".
- For a more detailed explanation of the algorithm see Theorem Proving in
- Higher Order Logics, 22nd International Conference.
- More refences:
- https://en.wikipedia.org/wiki/Linear_temporal_logic_to_B%C3%BCchi_automaton
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

negateNNF :: NNF a -> NNF a
negateNNF p =
  case p of
    NnfVar a -> NnfNegVar a
    NnfNegVar a -> NnfVar a
    NnfTruth -> NnfFalsehood
    NnfFalsehood -> NnfTruth
    NnfNext p1 -> NnfNext (negateNNF p1)
    NnfConj p1 p2 -> NnfDisj (negateNNF p1) (negateNNF p2)
    NnfDisj p1 p2 -> NnfConj (negateNNF p1) (negateNNF p2)
    NnfUntil p1 p2 -> NnfRelease (negateNNF p1) (negateNNF p2)
    NnfRelease p1 p2 -> NnfUntil (negateNNF p1) (negateNNF p2)


runFreshNode :: Monad m => FreshNodeT m a -> m a
runFreshNode (FNT f) = evalStateT f (initSymbol + 1)

getNewId :: Monad m => FreshNodeT m Int
getNewId = FNT $ do s <- get
                    put (s + 1)
                    return s

{-
- nodes: the names of all the nodes in the graph
- incoming: the set of nodes that have an edge pointing to the current node
- now: LTL formulae promised by this node but that have not yet
- been processed
- old: LTL formulae promised by this node that have already been processed
- next: set of LTL formulae that all successor nodes must promise
-}
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
           Set (NNF a)              -- current formulas
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

initSymbol :: Int
initSymbol = 0

createGraph :: Ord a => Formula a -> (IntSet, IntMap IntSet, IntMap (Set (NNF a)))
createGraph f = (epNodes ep, epIncoming ep, epNow ep)
  where
    curr = S.singleton (nnf (desugarFormula f))
    old = S.empty
    next = S.empty
    incoming = IS.singleton initSymbol
    ep0 = EP IS.empty IM.empty IM.empty IM.empty
    ep = execState (evalStateT (extractFNTState (expand curr old next incoming)) (initSymbol + 1)) ep0


{- A generalized Buchi automaton (GBA) consists of
-     Q             - a finite set of states
-     I \subset Q   - a set of initial states
-     G \subset QxQ - a transition relation
-     F \subset 2^Q - the set of acceptance sets
-   An omega-word sigma over Q is a _path_ of the GBA if sigma_o \in I and
-     (sigma_i, sigma_{i+1}) \in G \forall i \in N
-   limit(sigma) := {q | exists n. sigma_n = q}
-   The GBA accepts a path if limit(sigma) \intersection M \neq {} holds
-   for all M in F
-
-   A labelled generalized Buchi automaton (LGBA) is 
-     A = (Q, I, G, F) a GBA
-     D a finite set of labels
-     L : Q -> 2^D the label function
- 
-   A path sigma of A is _consistent_ with an omega-word Epsilon over D if
-   Epsilon_i \in L(sigma_i) for all i \in N.
-   An LGBA accepts an omega-word Epsilon over D iff it accepts some path
-   of A that is consistent with Epsilon
-
-
-}
data GBA a =
  GBA { gbaStates :: IntSet
      , gbaInit :: IntSet
      , gbaTransition :: IntMap Int
      , gbaFinal :: Set IntSet }
      deriving (Eq, Read, Show)

data LGBA a =
  LGBA { lgbaGBA :: GBA a
       , lgbaLabel :: IntMap (Set (NNF a)) }
       deriving (Show, Eq)


isUntil :: NNF a -> Bool
isUntil (NnfUntil _ _) = True
isUntil _ = False


{- See wiki page on LTL to BA for formal specification -}
closureUnderNeg :: (Show a, Ord a) => NNF a -> Set (NNF a)
closureUnderNeg f0 = S.union (go False f0) (S.fromList [NnfTruth, NnfFalsehood])
  where
    go !negated !f
      | not negated = S.union (go True negf) (S.insert f cl)
      | otherwise = S.insert f cl
      where
        negf = negateNNF f
        cl = case f of
               NnfTruth -> S.empty
               NnfFalsehood -> S.empty
               NnfVar _ -> S.empty
               NnfNegVar _ -> S.empty
               NnfConj f1 f2 -> S.union (go False f1) (go False f2)
               NnfDisj f1 f2 -> S.union (go False f1) (go False f2 )
               NnfUntil f1 f2 -> S.union (go False f1) (go False f2)
               NnfRelease f1 f2 -> S.union (go False f1) (go False f2)
               NnfNext f1 -> go False f1




{- A Labeled Generalized Buchi Automaton is a GBA where
- input is associated as labels with the states rather than
- with the transitions -}
constructLGBA :: (Show a, Ord a) =>
       Formula a
    -> Set (NNF a)            --atomic propositions
    -> IntSet                 --nodes
    -> IntMap IntSet          --incoming
    -> IntMap (Set (NNF a))   --now
    -> LGBA a
constructLGBA formula ap nodes incoming now = lgba
  where
    gba = GBA nodes initial transitions final
    lgba = LGBA gba lbls
    nodeLst = IS.toList nodes
    initial = IS.fromList [ q | q <- nodeLst
                          , fromMaybe False (IS.member initSymbol <$> IM.lookup q incoming) ]
    final = S.singleton $ IS.fromList
            [ q | q <- nodeLst
                , let clf = S.toList (closureUnderNeg (nnf (desugarFormula formula)))
                , NnfUntil f1 f2 <- filter isUntil clf
                , let ns = IM.lookup q now
                , Just True == ((||) <$> (S.member f2 <$> ns) <*> (S.member (NnfUntil f1 f2) <$> ns)) ]
    lbls = IM.fromList (mapMaybe labels nodeLst)
    labels q 
      | ps `S.isSubsetOf` qs = Just (q, ps)
      | otherwise = Nothing
      where
        qs = S.intersection ap (IM.findWithDefault S.empty q now)
        ps = S.fromList [ p | p <- S.toList ap
                             , not (S.member (negateNNF p) qs) ]
    transitions = IM.fromList [ (q, q') | q' <- nodeLst
                                        , q <- fromMaybe [] (IS.toList <$> IM.lookup q' incoming)]


{- Checks if an LTL forumula is valid, ie it is true under all possible
- interpretations. We construct a graph of the negation of the formula, and
- if it is empty then the formula is valid.
- A BA is empty if and only if there is a final state reachabel from an
- initial state and lies on a cycle. We do this by decomposing the graph
- into strongly connected components. Run a depth first search to find
- which strongly connected components are reachable from the intial states.
- If any of the strongly connected components are reachable, the BA is
- non-empty.
-}
isValid :: (Show a, Ord a) => Formula a -> Bool
isValid f = not (any (\c -> length c > 1 && not (null (reachable `intersect` c))) sccs)
  where
    sccs = map T.flatten (G.scc g)
    !reachable = G.reachable g initSymbol
    (nodes, incoming, _) = createGraph (Neg f)
    outgoing = buildOutgoing (IM.toList incoming) IM.empty
    (g, _, _) = G.graphFromEdges $ map (\n -> (n, n, lkpFun n)) (initSymbol:IS.toList nodes)
    lkpFun = IS.toList . fromMaybe IS.empty . flip IM.lookup outgoing
    buildOutgoing ins outs = 
      case ins of
        [] -> outs
        (n, incm):ins' ->
          let alterFun x out = Just (IS.insert x (fromMaybe IS.empty out))
              outs' = IS.foldl' (flip (IM.alter (alterFun n))) outs incm
          in buildOutgoing ins' outs'


{- -------------------- TESTS -------------------- -}
sugared :: Formula String
sugared = Always (Implies (Var "Alive")
                          (Eventually (Neg (Var "Alive"))))

desugared :: DSFormula String
desugared = desugarFormula sugared


data AP = A | B | C | D deriving (Eq, Read, Show, Ord)

spec :: Formula AP
spec = Implies (Conj (Var A) (Var B)) (Disj (Var A) (Var B))

specBad :: Formula AP
specBad = Implies (Disj (Var A) (Var B)) (Conj (Var A) (Var B))
