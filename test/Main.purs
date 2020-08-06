module Test.Main where

import Data.Functor
import Prelude

import Data.Graph (insertEdgeWithVertices)
import Data.Graph as Graph
import Data.List as List
import Data.Map as Map
import Data.Set as Set
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Test.Spec (describe, it)
import Test.Spec.Assertions (shouldEqual, shouldNotEqual)
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner (run)

emptyDecorate :: forall f k. Functor f => f k -> f (Tuple k Unit)
emptyDecorate = map (\k -> Tuple k unit)

main :: Effect Unit
main = do
  run [consoleReporter] do
    let n k v = Tuple k (Tuple k (List.fromFoldable v ))
        --       4 - 8
        --      /     \
        -- 1 - 2 - 3 - 5 - 7
        --          \
        --           6
        acyclicGraph =
          Graph.fromMap (
            Map.fromFoldable
              [ n 1 (emptyDecorate [ 2 ])
              , n 2 (emptyDecorate [ 3, 4 ])
              , n 3 (emptyDecorate [ 5, 6 ])
              , n 4 (emptyDecorate [ 8 ])
              , n 5 (emptyDecorate [ 7 ])
              , n 6 (emptyDecorate [ ])
              , n 7 (emptyDecorate [ ])
              , n 8 (emptyDecorate [ 5 ])
              ])
        --       2 - 4
        --      / \
        -- 5 - 1 - 3
        cyclicGraph =
          Graph.fromMap (
            Map.fromFoldable
              [ n 1 (emptyDecorate [ 2 ])
              , n 2 (emptyDecorate [ 3, 4 ])
              , n 3 (emptyDecorate [ 1 ])
              , n 4 (emptyDecorate [ ])
              , n 5 (emptyDecorate [ 1 ])
              ])
    describe "topologicalSort" do
      it "works for an example" do
        Graph.topologicalSort acyclicGraph `shouldEqual` List.fromFoldable [ 1, 2, 4, 8, 3, 6, 5, 7 ]
    describe "insertEdgeWithVertices" do
      it "works for examples" do
        let t x = Tuple x x
            graph =
              Graph.insertEdgeWithVertices (t 1) (t 2) unit $
              Graph.insertEdgeWithVertices (t 2) (t 4) unit $
              Graph.insertEdgeWithVertices (t 4) (t 8) unit $
              Graph.insertEdgeWithVertices (t 8) (t 5) unit $
              Graph.insertEdgeWithVertices (t 5) (t 7) unit $
              Graph.insertEdgeWithVertices (t 2) (t 3) unit $
              Graph.insertEdgeWithVertices (t 3) (t 5) unit $
              Graph.insertEdgeWithVertices (t 3) (t 6) unit $
              Graph.empty
        Graph.toMap graph `shouldEqual` Graph.toMap acyclicGraph
        let graph' =
               Graph.insertEdgeWithVertices (t 5) (t 1) unit $
               Graph.insertEdgeWithVertices (t 1) (t 2) unit $
               Graph.insertEdgeWithVertices (t 2) (t 4) unit $
               Graph.insertEdgeWithVertices (t 2) (t 3) unit $
               Graph.insertEdgeWithVertices (t 3) (t 1) unit $
               Graph.empty
        Graph.toMap graph' `shouldEqual` Graph.toMap cyclicGraph
    describe "multiple edges between a pair of nodes" do
       it "works for an example" do
        let t x = Tuple x x
            graph =
              Graph.insertEdgeWithVertices (t 1) (t 2) unit $
              Graph.empty
        Graph.toMap graph `shouldNotEqual` Graph.toMap (Graph.insertEdgeWithVertices (t 1) (t 2) unit graph)
    describe "descendants" do
      it "works for examples" do
        Graph.descendants 1 acyclicGraph `shouldEqual` Set.fromFoldable [ 2, 3, 4, 5, 6, 7, 8 ]
        Graph.descendants 2 acyclicGraph `shouldEqual` Set.fromFoldable [ 3, 4, 5, 6, 7, 8 ]
        Graph.descendants 3 acyclicGraph `shouldEqual` Set.fromFoldable [ 5, 6, 7 ]
        Graph.descendants 4 acyclicGraph `shouldEqual` Set.fromFoldable [ 5, 7, 8 ]
        Graph.descendants 5 acyclicGraph `shouldEqual` Set.fromFoldable [ 7 ]
        Graph.descendants 6 acyclicGraph `shouldEqual` Set.fromFoldable [ ]
        Graph.descendants 7 acyclicGraph `shouldEqual` Set.fromFoldable [ ]
        Graph.descendants 8 acyclicGraph `shouldEqual` Set.fromFoldable [ 5, 7 ]
    describe "ancestors" do
      it "works for examples" do
        Graph.ancestors 1 acyclicGraph `shouldEqual` Set.fromFoldable [ ]
        Graph.ancestors 2 acyclicGraph `shouldEqual` Set.fromFoldable [ 1 ]
        Graph.ancestors 3 acyclicGraph `shouldEqual` Set.fromFoldable [ 1, 2 ]
        Graph.ancestors 4 acyclicGraph `shouldEqual` Set.fromFoldable [ 1, 2 ]
        Graph.ancestors 5 acyclicGraph `shouldEqual` Set.fromFoldable [ 1, 2, 3, 4, 8 ]
        Graph.ancestors 6 acyclicGraph `shouldEqual` Set.fromFoldable [ 1, 2, 3 ]
        Graph.ancestors 7 acyclicGraph `shouldEqual` Set.fromFoldable [ 1, 2, 3, 4, 5, 8 ]
        Graph.ancestors 8 acyclicGraph `shouldEqual` Set.fromFoldable [ 1, 2, 4 ]
    describe "inCycle" do
      it "works for examples" do
        Graph.isInCycle 1 cyclicGraph `shouldEqual` true
        Graph.isInCycle 2 cyclicGraph `shouldEqual` true
        Graph.isInCycle 3 cyclicGraph `shouldEqual` true
        Graph.isInCycle 4 cyclicGraph `shouldEqual` false
        Graph.isInCycle 5 cyclicGraph `shouldEqual` false
    describe "cyclic" do
      it "works for examples" do
        Graph.isCyclic cyclicGraph `shouldEqual` true
        Graph.isCyclic acyclicGraph `shouldEqual` false
        Graph.isAcyclic cyclicGraph `shouldEqual` false
        Graph.isAcyclic acyclicGraph `shouldEqual` true
    describe "adjacent" do
      it "works for examples" do
        Graph.adjacent 1 acyclicGraph `shouldEqual` Set.fromFoldable [ 2 ]
        Graph.adjacent 2 acyclicGraph `shouldEqual` Set.fromFoldable [ 1, 3, 4 ]
        Graph.adjacent 3 acyclicGraph `shouldEqual` Set.fromFoldable [ 2, 5, 6 ]
        Graph.adjacent 4 acyclicGraph `shouldEqual` Set.fromFoldable [ 2, 8 ]
        Graph.adjacent 5 acyclicGraph `shouldEqual` Set.fromFoldable [ 3, 7, 8 ]
        Graph.adjacent 6 acyclicGraph `shouldEqual` Set.fromFoldable [ 3 ]
        Graph.adjacent 7 acyclicGraph `shouldEqual` Set.fromFoldable [ 5 ]
        Graph.adjacent 8 acyclicGraph `shouldEqual` Set.fromFoldable [ 4, 5 ]
        Graph.adjacent 1 cyclicGraph `shouldEqual` Set.fromFoldable [ 2, 3, 5 ]
        Graph.adjacent 2 cyclicGraph `shouldEqual` Set.fromFoldable [ 1, 3, 4 ]
        Graph.adjacent 3 cyclicGraph `shouldEqual` Set.fromFoldable [ 1, 2 ]
        Graph.adjacent 4 cyclicGraph `shouldEqual` Set.fromFoldable [ 2 ]
        Graph.adjacent 5 cyclicGraph `shouldEqual` Set.fromFoldable [ 1 ]
    describe "allPaths" do
      it "works for examples" do
        Graph.allPaths 2 1 acyclicGraph `shouldEqual` Set.empty
        Graph.allPaths 1 9 acyclicGraph `shouldEqual` Set.empty
        Graph.allPaths 1 1 acyclicGraph `shouldEqual` Set.singleton (List.fromFoldable [ 1 ])
        Graph.allPaths 1 2 acyclicGraph `shouldEqual` Set.singleton (List.fromFoldable [ 1, 2 ])
        Graph.allPaths 1 7 acyclicGraph `shouldEqual`
          Set.fromFoldable [ List.fromFoldable [ 1, 2, 4, 8, 5, 7 ], List.fromFoldable [ 1, 2, 3, 5, 7 ] ]
        Graph.allPaths 1 8 acyclicGraph `shouldEqual` Set.singleton (List.fromFoldable [ 1, 2, 4, 8 ])
        Graph.allPaths 2 6 acyclicGraph `shouldEqual` Set.singleton (List.fromFoldable [ 2, 3, 6 ])
        Graph.allPaths 5 3 cyclicGraph `shouldEqual` Set.singleton (List.fromFoldable [ 5, 1, 2, 3 ])
    describe "stronglyConnectedComponents" do
       it "works for examples" do
          Graph.stronglyConnectedComponents acyclicGraph `shouldEqual` (Map.fromFoldable [ Tuple 1 1, Tuple 2 2, Tuple 3 3, Tuple 4 4, Tuple 5 5, Tuple 6 6, Tuple 7 7, Tuple 8 8])
          Graph.stronglyConnectedComponents cyclicGraph `shouldEqual` (Map.fromFoldable [ Tuple 1 1, Tuple 2 1, Tuple 3 1, Tuple 4 4, Tuple 5 5])
