// Personal final Project
// Verification of encode/decode with Huffman codes
// Formal verification (CS-550, EPFL)
//
// Samuel Chassot 270955
// Daniel Filipe Nunes Silva 275197

import stainless.collection._
import stainless.lang._
import stainless.annotation._
import stainless.equations._
import stainless.proof.check
import scala.collection.immutable.ListSet
import HuffmanCode.InnerNode
import HuffmanCode.Leaf

object HuffmanCode {
  // functional implemention of Huffman's Algorithm-----------------------------
  
  // datatypes------------------------------------------------------------------

  sealed abstract class Tree
  case class InnerNode(w: BigInt, chars: List[Char], t1: Tree, t2: Tree) extends Tree
  case class Leaf(w: BigInt, c: Char) extends Tree

  type Forest = List[Tree]

  // return true if tree is an InnerNode----------------------------------------
  def isInnerNode(t: Tree): Boolean = t match {
    case InnerNode(_, _, _, _) => true
    case Leaf(_, _) => false
  }

  // return true if tree is a Leaf----------------------------------------------
  def isLeaf(t: Tree): Boolean = t match {
    case InnerNode(_, _, _, _) => false
    case Leaf(_, _) => true
  }

  // return the number of leaves with a given character in the given tree-------
  def countChar(t: Tree, c: Char): BigInt = {
    t match {
      case Leaf(_, lC) => if (lC == c) BigInt(1) else BigInt(0)
      case InnerNode(_, _, t1, t2) => countChar(t1, c) + countChar(t2, c)
    }
  }.ensuring(r => r >= 0)

  def countChar(f: Forest, c: Char): BigInt = {
    f match {
      case Nil() => 0
      case hd :: tl => countChar(hd, c) + countChar(tl, c)
    }
  }

  def countLeaves(t: Tree): BigInt = {
    t match {
      case InnerNode(_, _, t1, t2) => countLeaves(t1) + countLeaves(t2)
      case Leaf(_, _) => 1
    }
  }

  def countLeaves(f: Forest): BigInt = {
    f match {
      case Nil() => 0
      case hd :: tl => countLeaves(hd) + countLeaves(tl)
    }
  }

  // return true iff two trees are the same-------------------------------------
  def isSameTree(t1: Tree, t2: Tree): Boolean = t1 match {
    case Leaf(w1, c1) => t2 match {
      case Leaf(w2, c2) if (w1 == w2 && c1 == c2) => true
      case _ => false 
    }
    case InnerNode(w1, _, t11, t12) => t2 match {
      case InnerNode(w2, _, t21, t22) => w1 == w2 && isSameTree(t11, t21) && isSameTree(t12, t22)
      case _ => false
    }
  }

  // prove that isSameTree is a reflexive relation------------------------------
  def isSameTreeReflexivity(t: Tree): Unit = {
    t match {
      case Leaf(w, c) => ()
      case InnerNode(w, _, t1, t2) => {
        isSameTreeReflexivity(t1)
        isSameTreeReflexivity(t2)
      }
    }
  }.ensuring(_ => isSameTree(t, t))

  // prove that isSameTree is a transitive relation-----------------------------
  def isSameTreeTransitivity(t1: Tree, t2: Tree, t3: Tree): Unit = {
    require(isSameTree(t1, t2) && isSameTree(t2, t3))

    (t1, t2, t3) match {
      case (InnerNode(_, _, t11, t12), InnerNode(_, _, t21, t22), InnerNode(_, _, t31, t32)) => {
        isSameTreeTransitivity(t11, t21, t31)
        isSameTreeTransitivity(t12, t22, t32)
      }
      case _ => ()
    }
  }.ensuring(_ => isSameTree(t1, t3))

  // return true if st is a substree of t---------------------------------------
  def isSubTree(t: Tree, st: Tree): Boolean = {
    if (isSameTree(t, st)) true
    else t match {
      case Leaf(_, _) => false
      case InnerNode(_, _, t1, t2) => st match { case _ => isSubTree(t1, st) || isSubTree(t2, st) }
    }
  }

  // prove isSubTree is a reflexive relation------------------------------------
  def isSubTreeReflexivity(t: Tree): Unit = {
    isSameTreeReflexivity(t)
  }.ensuring(_ => isSubTree(t, t))

  // prove isSubTree is a transitive relation-----------------------------------
  def isSubTreeTransitivity(t: Tree, st: Tree, sst: Tree): Unit = {
    require(isSubTree(t, st) && isSubTree(st, sst))

    t match {
      case Leaf(_, _) => ()
      case t@InnerNode(_, _, t1, t2) => st match {
        case Leaf(_, _) => ()
        case InnerNode(stw, _, st1, st2) => {
          if (isSameTree(t, st)) isSameSubTree(t, st, sst)
          else if (isSubTree(t1, st)) isSubTreeTransitivity(t1, st, sst)
          else if (isSubTree(t2, st)) isSubTreeTransitivity(t2, st, sst)
        }
      }
    }
  }.ensuring(_ => isSubTree(t, sst))

  // if st is a subtree of t2 and t1 is the same as t2 then st is---------------
  // a subtree of t1------------------------------------------------------------
  def isSameSubTree(t1: Tree, t2: Tree, st: Tree): Unit = {
    require(isSameTree(t1, t2) && isSubTree(t2, st))

    if (isSameTree(t2, st)) {
      isSameTreeTransitivity(t1, t2, st)
    } else t2 match {
      case Leaf(_, _) => ()
      case InnerNode(_, _, t21, t22) => t1 match { case InnerNode(_, _, t11, t12) => {
        if (isSubTree(t21, st)) isSameSubTree(t11, t21, st)
        else if (isSubTree(t22, st)) isSameSubTree(t12, t22, st)
      }}
    }
  }.ensuring(_ => isSubTree(t1, st))

  // prove children of a node are subtrees or the node itself-------------------
  def childrenAreSubTrees(t: Tree): Unit = {
    require(isInnerNode(t))
    isSubTreeReflexivity(t)
  }.ensuring(_ => t match { case InnerNode(_, _, t1, t2) => isSubTree(t, t1) && isSubTree(t, t2) })

  // return the weight of a Tree------------------------------------------------
  def cachedWeight(t: Tree): BigInt = t match {
    case InnerNode(w, _, _, _) => w
    case Leaf(w, _) => w
  }

  // return the list of chars of the Tree---------------------------------------
  def cachedChars(t: Tree): List[Char] = t match {
    case InnerNode(_, chars, t1, t2) => cachedChars(t1) ++ cachedChars(t2)
    case Leaf(_, c) => List(c)
  } 

  def cachedChars(f: Forest): List[Char] = f match {
    case hd :: tl => cachedChars(hd) ++ cachedChars(tl)
    case Nil() => Nil()
  }

  // merge two Tree in one by adding an InnerNode-------------------------------
  def uniteTrees(t1: Tree, t2: Tree): Tree = {
    require(ListSpecs.noDuplicate(cachedChars(t1) ++ cachedChars(t2)))
    InnerNode(cachedWeight(t1) + cachedWeight(t2), cachedChars(t1) ++ cachedChars(t2), t1, t2)
  }.ensuring(t => ListSpecs.noDuplicate(cachedChars(t)))

  // insert a Tree in a Forest and sort the latter------------------------------
  def insortTree(t: Tree, f: Forest): Forest = {
    decreases(f.length)

    f match {
      case Nil() => List(t)
      case hd :: tl => if (cachedWeight(t) <= cachedWeight(hd)) t :: f else hd :: insortTree(t, tl)
    }
  }.ensuring(r => r.length == f.length+1 && (t::f).content == r.content && countLeaves(t) + countLeaves(f) == countLeaves(r) && cachedChars(r).content == cachedChars(t :: f).content)

  def removeDuplicates(s: List[Char]): List[Char] = {
    s match {
      case Nil() => Nil[Char]()
      case hd :: tl => {
        val temp = removeDuplicates(tl)
        if(temp.contains(hd)) temp else hd :: temp
      }
    }
  }.ensuring(r => ListSpecs.noDuplicate(r))

  def lemmaConcatNoDuplicate(c: (Char, BigInt), l: List[(Char, BigInt)]): Unit = {
    require(ListSpecs.noDuplicate(l.map(_._1)) && !l.map(_._1).contains(c._1))
  }.ensuring(ListSpecs.noDuplicate((c::l).map(_._1)))

  def generateOccurencesTuplesHelper(withoutDuplicates: List[Char], s: List[Char]): List[(Char, BigInt)] = {
    require(ListSpecs.noDuplicate(withoutDuplicates))
    withoutDuplicates match {
      case Nil() => Nil[(Char, BigInt)]()
      case hd :: tl => {
        val tuple =  (hd, s.count(_ == hd))
        val tuplesList = generateOccurencesTuplesHelper(tl, s)
        
        assert(ListSpecs.noDuplicate(tuplesList.map(_._1)))
        assert(!tuplesList.map(_._1).contains(tuple._1))

        lemmaConcatNoDuplicate(tuple, tuplesList)

        tuple :: tuplesList
      } 
    }
  }.ensuring(r => ListSpecs.noDuplicate(r.map(_._1)) && r.map(_._1) == withoutDuplicates)

  def generateOccurencesTuples(s: List[Char]): List[(Char, BigInt)] = {
    val withoutDuplicates = removeDuplicates(s)
    generateOccurencesTuplesHelper(withoutDuplicates, s)

  }.ensuring(r => ListSpecs.noDuplicate(r.map(_._1)) && r.length == removeDuplicates(s).length && r.map(_._1) == removeDuplicates(s))
  
  def lemmaForallCanEncodeUniquelyWithOneMoreLeafInTheForestNotAlreadyContained(f: Forest, l: Leaf, s: List[Char]): Unit = {
    require(s.forall(canEncodeCharUniquely(f, _)) && f.forall(isLeaf) && !cachedChars(f).contains(l.c))

    val newForest = l :: f
    s match {
      case hd :: tl => {
        assert(s.forall(canEncodeCharUniquely(f, _)))
        assert(canEncodeCharUniquely(f, hd))
        assert(cachedChars(f).contains(hd))
        assert(hd != l.c)
        assert( s == hd :: tl)
        lemmaForallCanEncodeUniquelyWithOneMoreLeafInTheForestNotAlreadyContained(f, l, tl)
        assert(tl.forall(canEncodeCharUniquely(l :: f, _)))
        assert((hd :: tl).forall(canEncodeCharUniquely(l :: f, _)))
        assert(s.forall(canEncodeCharUniquely(l :: f, _)))
      } 
      case Nil() => assert(s.forall(canEncodeCharUniquely(l :: f, _)))
    }
    assert(s.forall(canEncodeCharUniquely(l :: f, _)))
   

  }.ensuring(_ => s.forall(canEncodeCharUniquely(l :: f, _)))

  def lemmaForallCanEncodeUniquelyImpliesForallWithNewHeadAndCorrespondingLeaf(f: Forest, s: List[Char], l: Leaf, hd: Char): Unit = {
    require(f.forall(isLeaf) && s.forall(canEncodeCharUniquely(f, _)) && l.c == hd && !s.contains(hd) && !cachedChars(f).contains(hd))

    assert(canEncodeCharUniquely(l, hd))
    assert(s.forall(canEncodeCharUniquely(f, _)))
    assert(s.forall(canEncodeCharUniquely(l :: f, _)))
    assert(canEncodeCharUniquely(l :: f, hd))
    assert(s.forall(canEncodeCharUniquely(l :: f, _)))
    assert((hd :: s).forall(canEncodeCharUniquely(l :: f, _)))
  }.ensuring(_ => (hd :: s).forall(canEncodeCharUniquely(l :: f, _)))

  def leavesGen(occ: List[(Char, BigInt)]): Forest = {
    require(ListSpecs.noDuplicate(occ.map(_._1)))
    occ match {
      case hd :: tl => {
        val newLeaf = Leaf(hd._2, hd._1) 
        val tailLeaves = leavesGen(tl)

        // assert(tailLeaves.filter(cachedChars(_).contains(newLeaf.c)).isEmpty)
        // assert(!cachedChars(tailLeaves).contains(hd._1))
        // lemmaForallCanEncodeUniquelyWithOneMoreLeafInTheForestNotAlreadyContained(tailLeaves, newLeaf, tl.map(_._1))

        assert(!cachedChars(tailLeaves).contains(hd._1))
        val res = newLeaf :: tailLeaves
        assert(res.forall(isLeaf))
        assert(res.length == occ.length)
        assert(occ.map(_._1).forall(canEncodeCharUniquely(res, _)))
        res
      }
      case Nil() => Nil[Tree]()
    }
  }.ensuring((r: Forest) => r.forall(isLeaf) && r.length == occ.length && occ.map(_._1).forall(canEncodeCharUniquely(r, _)))

  def lemmaForallCanEncodeUniquelyWithoutDuplicatesImpliesForallCanEncodeUniquelyOnCompleteList(f: Forest, s: List[Char]): Unit = {
    require(removeDuplicates(s).forall(canEncodeCharUniquely(f, _)))

    s match {
      case hd :: tl => {
        assert(removeDuplicates(s).contains(hd))
        ListSpecs.forallContained(removeDuplicates(s), (c:Char) => canEncodeCharUniquely(f, c), hd)
        assert(canEncodeCharUniquely(f, hd))
        lemmaForallCanEncodeUniquelyWithoutDuplicatesImpliesForallCanEncodeUniquelyOnCompleteList(f, tl)
      }
      case Nil() => () 
    }

  }.ensuring( _ => s.forall(canEncodeCharUniquely(f, _)))
  // generate the Forest of Leaf for a given list of characters-----------------
  def generateUnsortedForest(s: List[Char]): Forest = {
    val occurences = generateOccurencesTuples(s)
    val leaves = leavesGen(occurences)

    lemmaIsAllLeavesThenCountLeavesEqualsForestLength(leaves)
    assert(occurences.map(_._1) == removeDuplicates(s))
    assert(removeDuplicates(s).forall(canEncodeCharUniquely(leaves, _)))
    lemmaForallCanEncodeUniquelyWithoutDuplicatesImpliesForallCanEncodeUniquelyOnCompleteList(leaves, s)
    leaves

    // TODO last condition in the ensuring 
  }.ensuring(r => r.forall(isLeaf) && r.length == generateOccurencesTuples(s).length && s.forall(canEncodeCharUniquely(r, _)))

  // sort a Forest--------------------------------------------------------------
  def sortForest(f: Forest): Forest = {
    require(f.forall(isLeaf))
    f match {
          case Nil() => Nil[Tree]()
          case hd :: tl => {
            val res = insortTree(hd, sortForest(tl))
            assert(res.length == f.length)
            lemmaSameContentImpliesSameForallIsLeaf(f, res)
            res
            }

      }
  }.ensuring(r => r.length == f.length && r.content == f.content && r.forall(isLeaf))

  def lemmaSameContentImpliesSameForallIsLeaf(l1: Forest, l2: Forest): Unit = { 
    require(l1.forall(isLeaf) && l2.content.subsetOf(l1.content))
    l2 match {
      case Nil() => () 
      case hd :: tl => {
        assert(l1.contains(hd))
        ListSpecs.forallContained(l1, isLeaf, hd)
        assert(isLeaf(hd))
        lemmaSameContentImpliesSameForallIsLeaf(l1, tl)
      } 
    }
  }.ensuring(l2.forall(isLeaf))

  def lemmaSameContentImpliesSameForallCanEncodeCharUniquely(f1: Forest, f2: Forest, s: List[Char]): Unit = {
    require(s.forall(canEncodeCharUniquely(f1, _)) && f1.content == f2.content && f1.length == f2.length && f1.forall(isLeaf) && f2.forall(isLeaf) && f1.length == removeDuplicates(s).length)

    s match {
      case Nil() => ()
      case hd :: tl => {
        assert(canEncodeCharUniquely(f1, hd))
        assert(canEncodeCharUniquely(f2, hd))
        assert(tl.forall(canEncodeCharUniquely(f1, _)))
        assert(tl.forall(canEncodeCharUniquely(f2, _)))
      }
    }

  } .ensuring(_ => s.forall(canEncodeCharUniquely(f2, _)))

  // generate and sort a Forest given a list of characters----------------------
  def generateSortedForest(s: List[Char]): Forest = {
    require(removeDuplicates(s).length > 1)
    val unsortedForest = generateUnsortedForest(s)
    assert(s.forall(canEncodeCharUniquely(unsortedForest, _)))
    val res = sortForest(unsortedForest)
    lemmaSameContentImpliesSameForallIsLeaf(unsortedForest, res)
    lemmaSameContentImpliesSameForallCanEncodeCharUniquely(unsortedForest, res, s)
    res
  }.ensuring(r => r.forall(isLeaf) && s.forall(canEncodeCharUniquely(r, _)) && r.length > 1 && r.length == removeDuplicates(s).length)
  

  def lemmaCanEncodeUniquelyAndSameNLeavesThanCharsImpliesNoDuplicateInChars(f: Forest, s: List[Char]): Unit = {
    require(s.forall(canEncodeCharUniquely(f, _)) && countLeaves(f) == removeDuplicates(s).length)

  }.ensuring(_ => ListSpecs.noDuplicate(cachedChars(f)))

  def lemmaNoDuplicateInForestCharsImpliesNoDuplicateInTwoFirstTreesChars(f: Forest): Unit = {
    require(ListSpecs.noDuplicate(cachedChars(f)))
    f match {
      case t1 :: t2 :: tl => {
        (
          ListSpecs.noDuplicate(cachedChars(f))                                                ==:| trivial |:
          ListSpecs.noDuplicate(cachedChars(t1) ++ cachedChars(t2::tl))                        ==:| trivial |:
          ListSpecs.noDuplicate(cachedChars(t1) ++ (cachedChars(t2) ++ cachedChars(tl)))       ==:| ListSpecs.appendAssoc(cachedChars(t1), cachedChars(t2), cachedChars(tl)) |:
          ListSpecs.noDuplicate((cachedChars(t1) ++ cachedChars(t2)) ++ cachedChars(tl))       ==:| ListSpecs.noDuplicateSubseq(cachedChars(t1) ++ cachedChars(t2), cachedChars(t1) ++ (cachedChars(t2) ++ cachedChars(tl))) |:
          ListSpecs.noDuplicate(cachedChars(t1) ++ cachedChars(t2))         
        ).qed

        assert(f match { 
          case t1 :: t2 :: tl => ListSpecs.noDuplicate(cachedChars(t1) ++ cachedChars(t2))
          case t :: tl => ListSpecs.noDuplicate(cachedChars(t))
          case Nil() => ListSpecs.noDuplicate(cachedChars(f))
        })
        ()
      }
      case t :: tl => ()
      case Nil() => ()
        
    }
  }.ensuring(_ => f match { 
    case t1 :: t2 :: tl => ListSpecs.noDuplicate(cachedChars(t1) ++ cachedChars(t2))
    case t :: tl => ListSpecs.noDuplicate(cachedChars(t))
    case Nil() => ListSpecs.noDuplicate(cachedChars(f))
    })


  def lemmaCanEncodeUniquelyForestOneTreeImpliesCanEncodeUniquelyTree(f: Forest, s: List[Char]): Unit = {
    require(f.length == 1 && s.forall(canEncodeCharUniquely(f, _)) && isInnerNode(f(0)))

  }.ensuring(_ => f match {
    case t :: Nil() => s.forall(canEncodeCharUniquely(t, _))
  })

  def lemmaSameCachedCharsAndNumLeavesImpliesCanEncodeUniquely(f1: Forest, f2: Forest, s: List[Char]): Unit = {
    require(s.forall(canEncodeCharUniquely(f1, _)) && cachedChars(f1).content == cachedChars(f2).content && countLeaves(f1) == countLeaves(f2))

  }.ensuring(_ => s.forall(canEncodeCharUniquely(f2, _)))

  // generate Huffman code's Tree recursively given a Forest--------------------
  def huffmansAlgorithmHelper(f: Forest)(implicit s: List[Char]): Tree = {
    require((f.length == 1 && isInnerNode(f(0)) || f.length > 1 ) && s.forall(canEncodeCharUniquely(f, _)) && countLeaves(f) == removeDuplicates(s).length)
    decreases(f.length)

    f match {
      case t1 :: t2 :: tl => {
        lemmaCanEncodeUniquelyAndSameNLeavesThanCharsImpliesNoDuplicateInChars(f, s)
        lemmaNoDuplicateInForestCharsImpliesNoDuplicateInTwoFirstTreesChars(f)
        assert(ListSpecs.noDuplicate(cachedChars(t1) ++ cachedChars(t2)))
        val newTree = uniteTrees(t1, t2)
        val newForest = insortTree(newTree, tl)
        assert(cachedChars(newForest).content == cachedChars(newTree :: tl).content)
        assert(cachedChars(newForest).content == cachedChars(f).content)
        assert(countLeaves(newForest) == removeDuplicates(s).length)
        lemmaSameCachedCharsAndNumLeavesImpliesCanEncodeUniquely(f, newForest, s)
        assert(s.forall(canEncodeCharUniquely(newForest, _)))
        huffmansAlgorithmHelper(newForest)
        }
      case t :: Nil() => {
        lemmaCanEncodeUniquelyForestOneTreeImpliesCanEncodeUniquelyTree(f, s)
        assert(f(0) == t) //WHY?
        assert(s.forall(canEncodeCharUniquely(t, _)))
        assert(isInnerNode(t))
        assert(countLeaves(t) == removeDuplicates(s).length)
        t
      }
    }
  }.ensuring(t => isInnerNode(t) && s.forall(canEncodeCharUniquely(t, _)) && countLeaves(t) == removeDuplicates(s).length)

  // generate Huffman code's Tree given a Forest--------------------------------
  def huffmansAlgorithm(f: Forest)(implicit s: List[Char]): Tree = {
    require(f.length > 1 && f.forall(isLeaf) && s.forall(canEncodeCharUniquely(f, _)) && f.length == removeDuplicates(s).length && f.length == countLeaves(f))
    huffmansAlgorithmHelper(f)(s)
  }.ensuring(t => isInnerNode(t) && s.forall(canEncodeCharUniquely(t, _)))

  // encode/decode--------------------------------------------------------------

  // encode lemmas--------------------------------------------------------------

  // define that a character is uniquely encodable iff it appears once----------
  // in the tree----------------------------------------------------------------
  def canEncodeCharUniquely(t: Tree, c: Char): Boolean = (countChar(t, c) == 1)
  def canEncodeCharUniquely(f: Forest, c: Char): Boolean = (countChar(f, c) == 1)

  // prove that if we encode a character with a given tree then we can----------
  // decode it and get back the correct character-------------------------------
  def encodeCharIsDecodableAndCorrect(t: Tree, c: Char): Unit = {
    require(isInnerNode(t) && canEncodeCharUniquely(t, c))
    decreases(encodeChar(t, c).length)

    canDecodeExactlyOneCharImpliesCanDecode(t, encodeChar(t, c))(t)
    
    t match { case InnerNode(_, _, t1, t2) => {
        (t1, t2) match {
          case (Leaf(_, c1), t2@InnerNode(_, _, _, _)) if (c1 != c) => encodeCharIsDecodableAndCorrect(t2, c)
          case (t1@InnerNode(_, _, _, _), Leaf(_, c2)) if (c2 != c) => encodeCharIsDecodableAndCorrect(t1, c)
          case (t1@InnerNode(_, _, t11, t12), t2@InnerNode(_, _, t21, t22)) => if (canEncodeCharUniquely(t1, c)) encodeCharIsDecodableAndCorrect(t1, c) else encodeCharIsDecodableAndCorrect(t2, c)
          case (Leaf(_, c1), _) if (c1 == c) => ()
          case (_, Leaf(_, c2)) if (c2 == c) => ()
        }
      }
    }
  }.ensuring(_ => canDecode(t, encodeChar(t, c))(t) && decode(t, encodeChar(t, c)) == List(c))

  // encode functions-----------------------------------------------------------

  // encode a character as a list of bits recursively with a given tree---------
  def encodeChar(t: Tree, c: Char): List[Boolean] = {
    require(isInnerNode(t) && canEncodeCharUniquely(t, c))

    t match { case InnerNode(_, _, t1, t2) => {
      if (canEncodeCharUniquely(t1, c)) t1 match {
        case Leaf(_, _) => List(false)
        case t1@InnerNode(_, _, _, _) => List(false) ++ encodeChar(t1, c)
      } else t2 match {
        case Leaf(_, _) => List(true)
        case t2@InnerNode(_, _, _, _) => List(true) ++ encodeChar(t2, c)
      }
    }}
  }.ensuring(bs => canDecodeAtLeastOneChar(t, bs) && decodeChar(t, bs) == (List(c), Nil[Boolean]()))

  // prove that if we can decode exactly the given character with the given-----
  // tree from the given binary string then we can concatenate to it------------
  // anything and decoding the first char will remain the given one and the-----
  // remaining bits to decode will be the ones that we added to-----------------
  // the initial string---------------------------------------------------------
  def canDecodeExactlyImpliesCanDecodeOneCharPlusSomething(t: Tree, c: Char, bs: List[Boolean], tlBs: List[Boolean]): Unit = {
    require(isInnerNode(t) && canDecodeAtLeastOneChar(t, bs) && decodeChar(t, bs) == (List(c), Nil[Boolean]()) && canDecodeAtLeastOneChar(t, bs ++ tlBs))

    t match { case t@InnerNode(_, _, t1, t2) => bs match {
      case hd :: tl => {
        if (!hd) t1 match {
          case Leaf(_, _) => ()
          case InnerNode(_, _, _, _) => canDecodeExactlyImpliesCanDecodeOneCharPlusSomething(t1, c, tl, tlBs)
        } else t2 match {
          case Leaf(_, _) => ()
          case InnerNode(_, _, _, _) => canDecodeExactlyImpliesCanDecodeOneCharPlusSomething(t2, c, tl, tlBs)
        }
      }
      case Nil() => ()
    }}
  }.ensuring(_ => decodeChar(t, bs ++ tlBs) == (List(c), tlBs))

  // encode a list of characters as list of bits with a given tree--------------
  def encode(t: Tree, s: List[Char]): List[Boolean] = {
    require(isInnerNode(t) && !s.isEmpty && s.forall(c => canEncodeCharUniquely(t, c)))
    decreases(s.length)

    s match { case hd :: tl => {
      if (tl.isEmpty) {
        encodeCharIsDecodableAndCorrect(t, hd)
        encodeChar(t, hd)
      } else {
        val hdBs = encodeChar(t, hd)
        val tlBs = encode(t, tl)

        canDecodeExactlyOneCharAndCanDecodeImpliesCanDecodeConcatenation(t, hdBs, tlBs)(t)
        canDecodeImpliesCanDecodeAtLeastOneChar(t, hdBs ++ tlBs)(t)
        canDecodeImpliesCanDecodeTailAfterOneCharDecoded(t, hdBs ++ tlBs)(t)
        canDecodeExactlyImpliesCanDecodeOneCharPlusSomething(t, hd, hdBs, tlBs)
        decodableConcatenationIsDecodableAndCorect(t, hdBs, tlBs, List(hd), tl)

        hdBs ++ tlBs
      }
    }}
  }.ensuring(bs => canDecode(t, bs)(t) && decode(t, bs) == s)

  // decode lemmas--------------------------------------------------------------

  // prove that the length of the remaining list of bits after decoding---------
  // the first decodable character is smaller than the original list of bits----
  def decodeCharLength(t: Tree, bs: List[Boolean]): Unit = {
    require(isInnerNode(t) && canDecodeAtLeastOneChar(t, bs))
    decreases(bs.length)
    
    t match { case InnerNode(_, _, t1, t2) => { bs match {
        case hd :: tl => {
          if (!hd) {
            t1 match {
              case t1@InnerNode(_, _, t11, t12) => decodeCharLength(t1, tl)
              case Leaf(_, _) => ()
            }
          } else {
            t2 match {
              case t2@InnerNode(_, _, t11, t12) => decodeCharLength(t2, tl)
              case Leaf(_, _) => ()
            }
          }
        }
        case Nil() => ()
    }}}
  }.ensuring(_ => decodeChar(t, bs) match { case (_, nBs) => nBs.length < bs.length })
  
  // check if at least one character can be decoded-----------------------------
  def canDecodeAtLeastOneChar(t: Tree, bs: List[Boolean]): Boolean = {
    require(isInnerNode(t))
    decreases(bs.length)

    t match { case InnerNode(_, _, t1, t2) => { bs match {
      case hd :: tl => {
        if (!hd) t1 match {
          case Leaf(_, _) => true
          case t1@InnerNode(_, _, _, _) => canDecodeAtLeastOneChar(t1, tl)
        } else t2 match {
          case Leaf(_, _) => true
          case t2@InnerNode(_, _, _, _) => canDecodeAtLeastOneChar(t2, tl)
        }
      }
      case Nil() => false
    }}}
  }

  // check if the whole list of bits can be correctly decoded-------------------
  def canDecode(s: Tree, bs: List[Boolean])(implicit t: Tree): Boolean = {
    require(isInnerNode(s) && isInnerNode(t))
    decreases(bs.length)

    canDecodeAtLeastOneChar(s, bs) && {
      decodeCharLength(s, bs)
      val (_, nBs) = decodeChar(s, bs)
      nBs.isEmpty || canDecode(t, nBs)
    }
  }

  // prove that canDecode implies canDecodeAtLeastOneChar-----------------------
  def canDecodeImpliesCanDecodeAtLeastOneChar(s: Tree, bs: List[Boolean])(implicit t: Tree): Unit = {
    require(isInnerNode(s) && isInnerNode(t) && canDecode(s, bs)(t) && isSubTree(t, s))
    decreases(bs.length)

    s match { case InnerNode(_, _, t1, t2) => { bs match {
      case hd :: tl => {
        if (!hd) t1 match {
          case Leaf(_, c) => ()
          case t1@InnerNode(_, _, _, _) => {
            childrenAreSubTrees(s)
            isSubTreeTransitivity(t, s, t1)
            canDecodeImpliesCanDecodeAtLeastOneChar(t1, tl)
          }
        } else t2 match {
          case Leaf(_, c) => ()
          case t2@InnerNode(_, _, _, _) => {
            childrenAreSubTrees(s)
            isSubTreeTransitivity(t, s, t2)
            canDecodeImpliesCanDecodeAtLeastOneChar(t2, tl)
          }
        }
      }
      case Nil() => ()
    }}}
  }.ensuring(_ => canDecodeAtLeastOneChar(s, bs))

  // prove that can decode implies that we can decode the remaining bits--------
  // after having decoded the first decodable character-------------------------
  def canDecodeImpliesCanDecodeTailAfterOneCharDecoded(s: Tree, bs: List[Boolean])(implicit t: Tree): Unit = {
    require(isInnerNode(s) && isInnerNode(t) && canDecode(s, bs)(t) && isSubTree(t, s))
    decreases(bs.length)

    isSubTreeReflexivity(t)
    canDecodeImpliesCanDecodeAtLeastOneChar(s, bs)(t)

    bs match {
      case Nil() => ()
      case hd :: tl => { s match { case InnerNode(_, _, s1, s2) => {
        if (!hd) {
          s1 match {
            case s1@InnerNode(_, _, _, _) => canDecodeImpliesCanDecodeTailAfterOneCharDecoded(s1, tl)(t)
            case Leaf(_, c) => ()
          }
        } else {
          s2 match {
            case s2@InnerNode(_, _, _, _) => canDecodeImpliesCanDecodeTailAfterOneCharDecoded(s2, tl)(t)
            case Leaf(_, c) => ()
          }
        }
    }}}}
  }.ensuring(_ => decodeChar(s, bs) match { case(_, nBs) => nBs.isEmpty || canDecode(t, nBs)(t) })

  // prove than if we can exactly decode exactly one character from ------------
  // a binary string with a given tree then we can decode the binary string-----
  def canDecodeExactlyOneCharImpliesCanDecode(s: Tree, bs: List[Boolean])(implicit t: Tree): Unit = {
    require(isInnerNode(s) && isInnerNode(t) && canDecodeAtLeastOneChar(s, bs) && decodeChar(s, bs)._2 ==  Nil())
    decreases(bs.length)

    s match { case InnerNode(_, _, t1, t2) => { bs match {
      case hd :: tl => {
        if (!hd) t1 match {
          case Leaf(_, _) => ()
          case t1@InnerNode(_, _, _, _) => canDecodeExactlyOneCharImpliesCanDecode(t1, tl)
        } else t2 match {
          case Leaf(_, _) => ()
          case t2@InnerNode(_, _, _, _) => canDecodeExactlyOneCharImpliesCanDecode(t2, tl)
        }
      }
      case Nil() => ()
    }}}
  }.ensuring(_ => canDecode(s, bs)(t))

  // prove that if we can decode exactly one char and can decode an other-------
  // string then we can decode their concatenation------------------------------
  def canDecodeExactlyOneCharAndCanDecodeImpliesCanDecodeConcatenation(s: Tree, bs1: List[Boolean], bs2: List[Boolean])(implicit t: Tree): Unit = {
    require(isInnerNode(s) && isInnerNode(t) && (bs1.isEmpty && t == s || canDecodeAtLeastOneChar(s, bs1) && decodeChar(s, bs1)._2 == Nil[Boolean]()) && canDecode(t, bs2)(t))
    decreases(bs1.length)

    s match { case InnerNode(_, _, t1, t2) => bs1 match {
      case hd :: tl => {
        if (!hd) t1 match {
          case Leaf(_, c) => canDecodeExactlyOneCharAndCanDecodeImpliesCanDecodeConcatenation(t, Nil(), bs2)
          case t1@InnerNode(_, _, _, _) => canDecodeExactlyOneCharAndCanDecodeImpliesCanDecodeConcatenation(t1, tl, bs2)
        } else t2 match {
          case Leaf(_, c) => canDecodeExactlyOneCharAndCanDecodeImpliesCanDecodeConcatenation(t, Nil(), bs2)
          case t2@InnerNode(_, _, _, _) => canDecodeExactlyOneCharAndCanDecodeImpliesCanDecodeConcatenation(t2, tl, bs2)
        }
      }
      case Nil() => ()
    }}
  }.ensuring(_ => canDecode(s, bs1 ++ bs2)(t))

  // prove that we can stil decode the concatenation of two binary strings------
  // and the result is correct--------------------------------------------------
  def decodableConcatenationIsDecodableAndCorect(t: Tree, bs1: List[Boolean], bs2: List[Boolean], s1: List[Char], s2: List[Char]): Unit = {
    require(isInnerNode(t) && canDecodeAtLeastOneChar(t, bs1 ++ bs2) && decodeChar(t, bs1 ++ bs2) == (s1, bs2) && canDecode(t, bs2)(t) && decode(t, bs2) == s2)
    // this is strange as it is automatically proven but removing this lemma----
    // prevents the proof from being validated----------------------------------
  }.ensuring(_ => decode(t, bs1 ++ bs2) == s1 ++ s2)

  // decode functions-----------------------------------------------------------

  // decode a single character from a list of bits with a given tree------------
  def decodeChar(t: Tree, bs: List[Boolean]): (List[Char], List[Boolean]) = {
    require(isInnerNode(t) && canDecodeAtLeastOneChar(t, bs))
    decreases(bs.length)

    (t, bs) match { case (InnerNode(_, _, t1, t2), hd :: tl) => {
      if (!hd) t1 match {
        case Leaf(_, c) => (List(c), tl)
        case t1@InnerNode(_, _, _, _) => decodeChar(t1, tl)
      } else t2 match {
        case Leaf(_, c) => (List(c), tl)
        case t2@InnerNode(_, _, _, _) => decodeChar(t2, tl)
      }
    }}
  }.ensuring(r => r._1.length == 1)

  // decode a list of bits as a list of characters with a given tree------------
  def decode(t: Tree, bs: List[Boolean]): List[Char] = {
    require(isInnerNode(t) && canDecode(t, bs)(t))
    decreases(bs.length)

    bs match {
      case Nil() => Nil()
      case _ => {
        isSubTreeReflexivity(t)
        canDecodeImpliesCanDecodeAtLeastOneChar(t, bs)(t)
        canDecodeImpliesCanDecodeTailAfterOneCharDecoded(t, bs)(t)

        val (c, nBs) = decodeChar(t, bs)
        if (nBs.isEmpty) c else c ++ decode(t, nBs)
      }
    }
  }

  // final theorem--------------------------------------------------------------

  // return true if the given list of characters contains-----------------------
  // more than two different ones-----------------------------------------------
  def containsAtLeastTwoDifferentCharacters(s: List[Char]): Boolean = {
    s.foldLeft[List[Char]](Nil())((l, c) => if (l.contains(c)) l else (c :: l)).length >= 2
  }


  def lemmaIsAllLeavesThenCountLeavesEqualsForestLength(f: Forest): Unit = {
    require(f.forall(isLeaf))
    f match {
      case Nil() => ()
      case hd :: tl => lemmaIsAllLeavesThenCountLeavesEqualsForestLength(tl)
    }

  }.ensuring(_ => f.length == countLeaves(f))

  // return the Huffman code tree for a given list of characters that contains--
  // at least two different characters otherwise there is no meaningful---------
  // encoding for this----------------------------------------------------------
  def generateHuffmanCodeTree(s: List[Char]): Tree = {
    require(removeDuplicates(s).length > 1)
    val forest = generateSortedForest(s)
    lemmaIsAllLeavesThenCountLeavesEqualsForestLength(forest)
    assert(countLeaves(forest) == removeDuplicates(s).length)
    val huffman = huffmansAlgorithm(forest)(s)
    assert(s.forall(c => canEncodeCharUniquely(huffman, c)))

    huffman
    //TODO
  }.ensuring(t => isInnerNode(t) && s.forall(c => canEncodeCharUniquely(t, c)))

  // prove that decode(encode(x)) is equal to x using Huffman's algorithm-------
  def decodeEncodedString(s: List[Char]): Unit = {
    require(removeDuplicates(s).length > 1)
  }.ensuring(_ => {
    val t = generateHuffmanCodeTree(s)
    val e = encode(t, s)
    val d = decode(t, e)
    s == d
  })

  @extern
  def main(args: Array[String]) = {
    val s = List('a', 'a', 'b', 'c')

    val t = generateHuffmanCodeTree(s)
    val e = encode(t, s)
    val d = decode(t, e)

    println(t)
    println(e)
    println(d)
  }
}
