import Test.Hspec
import Test.QuickCheck
import Control.Exception (evaluate)

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Map (Map)
import qualified Data.Map as Map

import Syntax
import AutoDeriv
import Epik
import GuardedStrings

h = AtomicTest "H"
t = AtomicTest "T"

heads = Atom { posa = Set.singleton h
             , nega = Set.singleton t }

tails = Atom { posa = Set.singleton t
             , nega = Set.singleton h }

pah = AtomicProgram "announce_H"
pat = AtomicProgram "announce_T"
aph = AtomicProgram "aly_peek_H"
apt = AtomicProgram "aly_peek_T"
bph = AtomicProgram "bob_peek_H"
bpt = AtomicProgram "bob_peek_T"

pID = AtomicProgram "id"

mkActKat act pre post = ( act
                        , ktest (tvar pre) `kseq` kvar pID `kseq` ktest (tvar post))


htDecls =
  Program { alphabet = Set.fromList [h,t]
          , assertions = [(tneg (tvar h `tand` tvar t)) `tand` (tvar h `tor` tvar t)]
          , actions = [ mkActKat pah h h
                      , mkActKat pat t t
                      , mkActKat aph h h
                      , mkActKat apt t t
                      , mkActKat bph h h
                      , mkActKat bpt t t
                      ]
          , views = [ ("aly",
                       Map.fromList
                        [ (pah, [pah])
                        , (pat, [pat])
                        , (aph, [aph])
                        , (apt, [apt])
                        , (bph, [bph, bpt])
                        , (bpt, [bph, bpt])
                        ])
                      
                    , ("bob",
                      Map.fromList
                        [ (pah, [pah])
                        , (pat, [pat])
                        , (aph, [aph, apt])
                        , (apt, [aph, apt])
                        , (bph, [bph])
                        , (bpt, [bpt])
                        ])
                    ]
          , queries = []
          }

htContext = compileDecls htDecls

f = getAlts htContext

deriv a (at, k) = deriv' a f (at,k)

katom' = katom . posa

main :: IO ()
main = hspec $ do


  describe "Alternative Function" $ do
    it "produces (h,bph,h), (t,bpt,t) for <aly>bph" $ do
      f "aly" bph `shouldBe` Just [(heads, bph, heads), (tails, bpt, tails)]

  
  describe "Derivative of Negation" $ do
    it "returns 0 for ~1 with bph heads" $ do
      deriv bph (heads, KNeg KEps) `shouldBe` kzero
  
    it "no derivs for ~0 with bph tails" $ do
      deriv bph (heads, KNeg KZ) `shouldBe` kzero
      
    it "returns 0 for ~(h,bph,h) with bph,heads" $ do
      deriv bph (heads, kneg $ kvar (heads, bph, heads))
        `shouldBe` kzero

    it "returns 0 for ~(h, bph, h) with bph, tails" $ do
      deriv bph (tails, kneg $ kvar (heads, bph, heads))
        `shouldBe` kzero

    -- it "returns test
    it "interacts externally with modality" $ do
      deriv bph (heads, kneg $ kapply "aly" $ kneg (kvar (heads, bph, heads) `kseq` kvar (heads, pah, heads)))
        `shouldBe` kzero

    it "does something for sequences" $ do
      deriv bph (heads, kneg (kvar (heads, bph, heads) `kseq` kvar (heads, pah, heads)))
        `shouldBe` (katom' heads `kseq` kvar (heads, pah, heads))


    it "computes personal knowledge (postive)" $ do
      -- ~<aly>~(aly_peek_H)
      deriv aph (heads, kneg $ kapply "aly" $ kneg $ kvar (heads, aph, heads))
      `shouldBe` (katom' heads)

    it "doesn't leak unknown personal knowledge (negative)" $ do
      deriv apt (heads, kneg $ kapply "aly" $ kneg $ kvar (heads, aph, heads))
      `shouldBe` kzero

    it "Translates world state" $ do
      deriv apt (heads, kneg $ kvar (heads, aph, heads))
      `shouldBe` katom tails

    
      

  describe "Derivative of Sequence" $ do
    it "returns (h)?;(h,pah,h) for D bph (heads, ((h,bph,h);(h,pah,h)))" $ do
      deriv bph (heads, kvar (heads, bph, heads) `kseq` kvar (heads, pah, heads))
      `shouldBe` katom' heads `kseq` kvar (heads, pah, heads)

  describe "Derivative of Diamond" $ do
    it "returns <aly>(h?) for D pah (h, <aly> (h,pah,h))" $ do
      deriv pah (heads, kapply "aly" (kvar (heads, pah, heads)))
        `shouldBe` (kapply "aly" $ katom' heads)

    it "returns <aly>(h?) for D pah (h, <aly>(h;(h,pah,h)))" $ do
      deriv pah (heads, kapply "aly" $ katom' heads `kseq` kvar (heads, pah, heads))
      `shouldBe` (kapply "aly" $ katom' heads)

    it "returns <aly>(h;(h,pah,h)) for D bph (h, <aly> ((h,bph,h);(h,pah,h)))" $do
      deriv bph (heads, kapply "aly" $ kvar (heads, bph, heads) `kseq` kvar (heads, pah, heads))
        `shouldBe` kapply "aly" (katom' heads `kseq` kvar (heads, pah, heads))

    it "returns 0 for D bph (t, <aly> ((h,bph,h);(h,pah,h)))" $ do
      deriv bph (tails, kapply "aly" (kvar (heads, bph, heads) `kseq` kvar (heads, pah, heads)))
        `shouldBe` kzero

    it "returns 0 for D pah T <aly>((T);((H~T),announce_H,(H~T)))" $ do
      deriv pah (tails, kapply "aly" (katom' tails `kseq` kvar (heads, pah, heads)))
      `shouldBe` kzero

    it "returns 0 for D pah H <aly>((T);((H~T),announce_H,(H~T)))" $ do
      deriv pah (heads, kapply "aly" (katom' tails `kseq` kvar (heads, pah, heads)))
        `shouldBe`kzero

    it "returns something for D bpt (h, <aly>((h,bph,h);(h,pah,h)))" $ do
      deriv bpt (heads, kapply "aly" (kvar (heads, bph, heads) `kseq` kvar (heads, pah, heads)))
      `shouldBe` kzero


  describe "nullable of Diamond" $ do
    it "returns true for E heads <aly>h" $ do
      nullable heads (kapply "aly" $ katom' heads)
      `shouldBe` True
      
    it "returns fals for E tails <aly>h" $ do
      nullable tails (kapply "aly" $ katom' heads)
      `shouldBe` False

