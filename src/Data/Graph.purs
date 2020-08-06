-- | A data structure and functions for graphs

module Data.Graph
  ( Graph
  , unfoldGraph
  , fromMap
  , toMap
  , empty
  , insertEdge
  , insertVertex
  , insertEdgeWithVertices
  , vertices
  , lookup
  , outEdges
  , children
  , descendants
  , parents
  , ancestors
  , topologicalSort
  , isInCycle
  , isCyclic
  , isAcyclic
  , alterVertex
  , alterEdges
  , adjacent
  , isAdjacent
  , areConnected
  , shortestPath
  , stronglyConnectedComponents
  , allPaths
  ) where

import Prelude

import Data.Array as Array
import Data.Bifunctor (lmap, rmap)
import Data.CatList (CatList)
import Data.CatList as CL
import Data.Foldable (class Foldable)
import Data.Foldable as Foldable
import Data.List (List(..))
import Data.List as L
import Data.List as List
import Data.Map (Map)
import Data.Map as M
import Data.Maybe (Maybe(..), fromJust, isJust, maybe)
import Data.Set (Set)
import Data.Set as S
import Data.Set as Set
import Data.Tuple (Tuple(..), fst, snd, uncurry)
import Partial.Unsafe (unsafePartial)

-- | A graph with vertices of type `v`.
-- |
-- | Edges refer to vertices using keys of type `k`, and are decorated by the
-- | type `d`.
newtype Graph k d v = Graph (Map k (Tuple v (List (Tuple k d))))

instance functorGraph :: Functor (Graph k d) where
  map f (Graph m) = Graph (map (lmap f) m)

-- | An empty graph.
empty :: forall k d v. Graph k d v
empty = Graph M.empty

-- | Insert an edge from the start key to the end key.
insertEdge :: forall k d v. Ord k => k -> k -> d -> Graph k d v -> Graph k d v
insertEdge from to decoration (Graph g) =
  Graph $ M.alter (map (rmap (L.insertBy (\x y -> fst x `compare` fst y) (Tuple to decoration)))) from g

-- | Insert a vertex into the graph.
-- |
-- | If the key already exists, replaces the existing value and
-- |preserves existing edges.
insertVertex :: forall k d v. Ord k => k -> v -> Graph k d v -> Graph k d v
insertVertex k v (Graph g) = Graph $ M.insertWith (\(Tuple _ ks) _ -> Tuple v ks) k (Tuple v mempty) g

-- | Insert two vertices and connect them.
insertEdgeWithVertices :: forall k d v. Ord k => Tuple k v -> Tuple k v -> d -> Graph k d v -> Graph k d v
insertEdgeWithVertices from@(Tuple fromKey _) to@(Tuple toKey _) decoration =
  insertEdge fromKey toKey decoration <<< uncurry insertVertex from <<< uncurry insertVertex to

-- | Unfold a `Graph` from a collection of keys and functions which label keys
-- | and specify out-edges.
unfoldGraph
  :: forall f k d v out
   . Ord k
  => Functor f
  => Foldable f
  => Foldable out
  => f k
  -> (k -> v)
  -> (k -> out (Tuple k d))
  -> Graph k d v
unfoldGraph ks label edges =
  Graph (M.fromFoldable (map (\k ->
            Tuple k (Tuple (label k) (L.fromFoldable (edges k)))) ks))

-- | Create a `Graph` from a `Map` which maps vertices to their labels and
-- | outgoing edges.
fromMap :: forall k d v. Map k (Tuple v (List (Tuple k d))) -> Graph k d v
fromMap = Graph

-- | Turn a `Graph` into a `Map` which maps vertices to their labels and
-- | outgoing edges.
toMap :: forall k d v. Graph k d v -> Map k (Tuple v (List (Tuple k d)))
toMap (Graph g) = g

-- | Check if the first key is adjacent to the second.
isAdjacent :: forall k d v. Ord k => k -> k -> Graph k d v -> Boolean
isAdjacent k1 k2 g = k1 `Set.member` adjacent k2 g

-- | Find all keys adjacent to given key.
adjacent :: forall k d v. Ord k => k -> Graph k d v -> Set k
adjacent k g = children k g `Set.union` parents k g

-- | Returns shortest path between start and end key if it exists.
-- |
-- | Cyclic graphs may return bottom.
shortestPath :: forall k d v. Ord k => k -> k -> Graph k d v -> Maybe (List k)
shortestPath start end g =
  Array.head <<< Array.sortWith List.length <<< S.toUnfoldable $ allPaths start end g

-- | Returns shortest path between start and end key if it exists.
-- |
-- | Cyclic graphs may return bottom.
allPaths :: forall k d v. Ord k => k -> k -> Graph k d v -> Set (List k)
allPaths start end g = Set.map L.reverse $ go mempty start
  where
    go hist k =
      if end == k
      then Set.singleton hist'
      else
        if children' == Set.empty
        then Set.empty
        else Foldable.foldMap (go hist') children'
      where
        children' = children k g
        hist' = k `Cons` hist

-- | Checks if there's a directed path between the start and end key.
areConnected :: forall k d v. Ord k => k -> k -> Graph k d v -> Boolean
areConnected start end g = isJust $ shortestPath start end g

-- | List all vertices in a graph.
vertices :: forall k d v. Graph k d v -> List v
vertices (Graph g) = map fst (M.values g)

-- | Lookup a vertex by its key.
lookup :: forall k d v. Ord k => k -> Graph k d v -> Maybe v
lookup k (Graph g) = map fst (M.lookup k g)

-- | Get the keys which are directly accessible from the given key.
outEdges :: forall k d v. Ord k => k -> Graph k d v -> Maybe (List (Tuple k d))
outEdges k (Graph g) = map snd (M.lookup k g)

-- | Returns immediate ancestors of given key.
parents :: forall k d v. Ord k => k -> Graph k d v -> Set k
parents k (Graph g) = M.keys <<< M.filter (Foldable.elem k <<< map fst <<< snd) $ g

-- | Returns all ancestors of given key.
-- |
-- | Will return bottom if `k` is in cycle.
ancestors :: forall k d v. Ord k => k -> Graph k d v -> Set k
ancestors k' g = go k'
  where
   go k = Set.unions $ Set.insert da $ Set.map go da
     where
       da = parents k g

-- | Returns immediate descendants of given key.
children :: forall k d v. Ord k => k -> Graph k d v -> Set k
children k (Graph g) = maybe mempty (Set.fromFoldable <<< map fst <<< snd) <<< M.lookup k $ g

-- | Returns all descendants of given key.
-- |
-- | Will return bottom if `k` is in cycle.
descendants :: forall k d v. Ord k => k -> Graph k d v -> Set k
descendants k' g = go k'
  where
   go k = Set.unions $ Set.insert dd $ Set.map go dd
     where
       dd = children k g

-- | Checks if given key is part of a cycle.
isInCycle :: forall k d v. Ord k => k -> Graph k d v -> Boolean
isInCycle k' g = go mempty k'
  where
    go seen k =
      case Tuple (dd == mempty) (k `Set.member` seen) of
        Tuple true _ -> false
        Tuple _ true -> k == k'
        Tuple false false -> Foldable.any (go (Set.insert k seen)) dd
      where
        dd = children k g

-- | Checks if there any cycles in graph.
-- There's presumably a faster implementation but this is very easy to implement
isCyclic :: forall k d v. Ord k => Graph k d v -> Boolean
isCyclic g = Foldable.any (flip isInCycle g) <<< keys $ g
  where
    keys (Graph g') = M.keys g'

-- | Checks if there are not any cycles in the graph.
isAcyclic :: forall k d v. Ord k => Graph k d v -> Boolean
isAcyclic = not <<< isCyclic

alterVertex ::
  forall k d v.
  Ord k =>
  (Maybe v -> Maybe v) ->
  k -> Graph k d v -> Graph k d v
alterVertex f k (Graph g) = Graph $ M.alter (applyF =<< _) k g
  where
    applyF (Tuple v es) = flip Tuple es <$> f (Just v)

alterEdges ::
  forall k d v.
  Ord k =>
  (Maybe (List (Tuple k d)) -> Maybe (List (Tuple k d))) ->
  k -> Graph k d v -> Graph k d v
alterEdges f k (Graph g) = Graph $ M.alter (applyF =<< _) k g
  where
    applyF (Tuple v es) = Tuple v <$> f (Just es)

type SortState k d v =
  { unvisited :: Map k (Tuple v (List (Tuple k d)))
  , result :: List k
  }

-- To defunctionalize the `topologicalSort` function and make it tail-recursive,
-- we introduce this data type which captures what we intend to do at each stage
-- of the recursion.
data SortStep a = Emit a | Visit a
derive instance eqSortStep :: Eq a => Eq (SortStep a)
derive instance ordSortStep :: Ord a => Ord (SortStep a)

-- | Topologically sort the vertices of a graph.
-- |
-- | If the graph contains cycles, then the behavior is undefined.
topologicalSort :: forall k d v. Ord k => Graph k d v -> List k
topologicalSort (Graph g) =
    go initialState
  where
    go :: SortState k d v -> List k
    go state@{ unvisited, result } =
      case M.findMin unvisited of
        Just { key } -> go (visit state (CL.fromFoldable [Visit key]))
        Nothing -> result

    visit :: SortState k d v -> CatList (SortStep k) -> SortState k d v
    visit state stack =
      case CL.uncons stack of
        Nothing -> state
        Just (Tuple (Emit k) ks) ->
          let state' = { result: Cons k state.result
                       , unvisited: state.unvisited
                       }
          in visit state' ks
        Just (Tuple (Visit k) ks)
          | k `M.member` state.unvisited ->
            let start :: SortState k d v
                start =
                  { result: state.result
                  , unvisited: M.delete k state.unvisited
                  }

                next :: List k
                next = maybe mempty (map fst <<< snd) (M.lookup k g)
            in visit start (CL.fromFoldable (map Visit next) <> CL.cons (Emit k) ks)
          | otherwise -> visit state ks

    initialState :: SortState k d v
    initialState = { unvisited: g
                   , result: Nil
                   }

-- | Tarjan's algorithm for Strongly Connected Components (SCCs).
-- |
-- | Defines a `Map` where each node is mapped to its equivalence class
-- | representative once the graph is partitioned into SCCs.
-- |
-- | Running time: O(|E| log |V|)
stronglyConnectedComponents :: forall k d v. Ord k => Graph k d v -> Map k k
stronglyConnectedComponents (Graph g) =
  Foldable.foldl
    ( \scc next ->
        if isJust (M.lookup next scc) then
          -- have already found the SCC representative of `next`
          scc
        else
          dfs next M.empty scc
    )
    M.empty
    $ M.keys g
  where
  dfs :: k -> Map k Int -> Map k k -> Map k k
  -- perform a depth-first search in the graph starting from `n`
  -- `depth` tracks the depth at which each node is visited
  -- `scc` is the accumulating map from each node to its representative in its
  -- SCC
  --   - when `scc` is defined on all vertices of the graph, the procedure is
  --     complete
  dfs n depth scc = case ( Foldable.foldl
        ( \(Tuple sccAcc shallowest) c -> case M.lookup c depth of
            -- fold over the children `c` of `n`; the accumulator is a pair
            -- consisting of
            --   - `sccAcc`: the accumulating SCC map
            --   - `shallowest`: the shallowest node we have seen so far in
            --                   this branch of the DFS (this will become the
            --                   SCC representative)
            Just _ -> Tuple sccAcc $ shallower shallowest c
            Nothing ->
              let
                sccWithChildData = dfs c (M.insert n (M.size depth) depth) sccAcc

                shallowestForChild = unsafePartial $ fromJust $ M.lookup c sccWithChildData
                -- not actually partial; `c` is guaranteed to be in the map
              in
                Tuple sccWithChildData $ shallower shallowest shallowestForChild
        )
        (Tuple scc n)
        $ children n (Graph g)
    ) of
    Tuple newState shallow -> M.insert n shallow newState -- `shallow` becomes the representative
                                                          -- of the SCC containing `n`
    where
    shallower :: k -> k -> k
    -- determine whether `x` or `y` was visited first in the DFS, as determined
    -- by `depth`
    shallower x y = case (Tuple (M.lookup x depth) (M.lookup y depth)) of
      Tuple _ Nothing -> x
      Tuple Nothing _ -> y
      Tuple (Just p) (Just q) -> if q < p then y else x
