-- DO NOT MODIFY THE FOLLOWING LINES

module Huffman(HuffmanTree, characterCounts, huffmanTree, codeTable, encode, compress, decompress) where

import Table
import PriorityQueue

import Test.HUnit
import Debug.Trace
{- a bit code (of a character or string) is represented by a list of Booleans
   INVARIANT:
     the bit code is a concatenation of (0 or more) valid code words for some Huffman tree
 -}
type BitCode = [Bool]

-- END OF DO NOT MODIFY ZONE

--------------------------------------------------------------------------------

{- characterCounts s
   RETURNS: a table that maps each character that occurs in s to the number of
         times the character occurs in s
   EXAMPLES:
 -}
characterCounts :: String -> Table Char Int
characterCounts = characterCounts' Table.empty

characterCounts' acc [] = acc
characterCounts' acc (x:xs)
  | Table.exists acc x = let Just c = Table.lookup acc x 
    in characterCounts' (Table.insert acc x (c+1)) xs

  | otherwise = characterCounts' (Table.insert acc x 1) xs


-- modify and add comments as needed
data HuffmanTree = Leaf Char Int | Node (HuffmanTree) Int (HuffmanTree) deriving Show
s = "this is an example of a huffman tree"

{- huffmanTree t
  iterates over all (key, value) pairs in t and adds them as HuffmanTrees into a PriorityQueue,
  merges the trees in the PriorityQueue in increasing order of priority into a single HuffmanTree.
   PRE:  t maps each key to a positive value
   RETURNS: a Huffman tree based on the character counts in t
   EXAMPLES: 
 -}
huffmanTree :: Table Char Int -> HuffmanTree 
huffmanTree t = hqmerge $ Table.iterate t hqinsert PriorityQueue.empty 

{- hqinsert q (x, c)
  inserts a HuffmanTree that consists just of a leaf labeled with x and c into the priority queue, with priority c

  RETURNS: q but with the (Leaf x c, c) inserted 
-}
hqinsert :: PriorityQueue HuffmanTree -> (Char, Int) -> PriorityQueue HuffmanTree
hqinsert q (x,c) = PriorityQueue.insert q (Leaf x c, c)

{-hqmerge q
  Merges the HuffmanTrees in q into one tree, in increasing order of priority
  If there is only one tree in q, that tree is returned, otherwise it merges the trees until there is only one.
  RETURNS: A merged tree consisting of all the trees in q

-}
hqmerge :: PriorityQueue HuffmanTree -> HuffmanTree
hqmerge q 
  | PriorityQueue.is_empty $ snd $ least q = fst $ fst $ least q
  | otherwise = hqmerge $ hqmerge' q


{-hqmerge' q
  Helper function for hqmerge.
  Merges the two trees with least priority in q

  RETURNS: q but with the two trees with least priority merged into one tree.

-}
hqmerge' :: PriorityQueue HuffmanTree -> PriorityQueue HuffmanTree
hqmerge' q =
  let ((l1, p1), rest1) = least q 
  in 
    let ((l2, p2), rest2) = least rest1 
      in PriorityQueue.insert rest2 (Node l1 (p1+p2) l2, p1+p2)


{- codeTable h
   RETURNS: a table that maps each character in h to its Huffman code
   EXAMPLES:
 -}
codeTable :: HuffmanTree -> Table Char BitCode
codeTable = undefined


{- encode h s
   PRE: All characters in s appear in h
   RETURNS: the concatenation of the characters of s encoded using the Huffman code table of h.
   EXAMPLES:
 -}
encode :: HuffmanTree -> String -> BitCode
encode = undefined

{- compress s
   RETURNS: (a Huffman tree based on s, the Huffman coding of s under this tree)
   EXAMPLES:
 -}
compress :: String -> (HuffmanTree, BitCode)
compress = undefined


{- decompress h bits
   PRE:  bits is a concatenation of valid Huffman code words for h
   RETURNS: the decoding of bits under h
   EXAMPLES:
 -}
decompress :: HuffmanTree -> BitCode -> String
decompress = undefined


--------------------------------------------------------------------------------
-- Test Cases
-- You may add your own test cases here:
-- Follow the pattern and/or read about HUnit on the interwebs.
--------------------------------------------------------------------------------

-- characterCounts
test1 = TestCase $ assertEqual "characterCounts"
            (Just 7) (Table.lookup (characterCounts "this is an example of a huffman tree") ' ')

-- codeTable
-- while the precise code for ' ' may vary, its length (for the given example string) should always be 3 bits
test2 = TestCase $ assertEqual "codeTable"
            3 (maybe (-1) length (Table.lookup (codeTable (huffmanTree (characterCounts "this is an example of a huffman tree"))) ' '))

-- compress
-- while the precise code for the given example string may vary, its length should always be 135 bits
test3 = TestCase $ assertEqual "compress"
            135 (length (snd (compress "this is an example of a huffman tree")))

-- decompress
test4 =
    let s = "this is an example of a huffman tree"
    in
      TestCase $ assertEqual ("decompress \"" ++ s ++ "\"")
        s (let (h, bits) = compress s in decompress h bits)

test5 =
    let s = "xxx"
    in
      TestCase $ assertEqual ("decompress \"" ++ s ++ "\"")
        s (let (h, bits) = compress s in decompress h bits)

test6 =
    let s = ""
    in
      TestCase $ assertEqual ("decompress \"" ++ s ++ "\"")
        s (let (h, bits) = compress s in decompress h bits)

-- for running all the tests
runtests = runTestTT $ TestList [test1, test2, test3, test4, test5, test6]


{-Node (Node (Node (Node (Leaf 'n' 2) 4 (Node (Leaf 'l' 1) 2 (Leaf 'r' 1))) 8 (Node (Leaf 't' 2) 4 (Leaf 'm' 2))) 16 (Node (Node (Leaf 's' 2) 4 (Leaf 'h' 2)) 8 (Leaf 'e' 4))) 
36 
(Node (Node (Leaf 'a' 4) 8 (Node (Leaf 'i' 2) 4 (Node (Leaf 'x' 1) 2 (Leaf 'o' 1)))) 20 (Node (Node (Node (Leaf 'p' 1) 2 (Leaf 'u' 1)) 5 (Leaf 'f' 3)) 12 (Leaf ' ' 7)))
-}
