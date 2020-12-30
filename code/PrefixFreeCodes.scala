// Personal final Project
// Verification of encode/decode with prefix-free codes
// Formal verification (CS-550, EPFL)
//
// Samuel Chassot 270955
// Daniel Filipe Nunes Silva 275197

import stainless.annotation._
import stainless.collection._
import stainless.equations._
import stainless.lang._
import stainless.proof.check
import PrefixFreeCodes.InnerNode
import PrefixFreeCodes.Leaf

object PrefixFreeCodes {

   @extern // WARNING: @extern is unsound, only use for debugging
   def assume(b: Boolean): Unit = {
     (??? : Unit)
   }.ensuring(_ => b)
  
  // datatypes------------------------------------------------------------------

  sealed abstract class Tree
  case class InnerNode(t1: Tree, t2: Tree) extends Tree
  case class Leaf(w: BigInt, c: Char) extends Tree

  type Forest = List[Tree]

  // datatypes helper functions-------------------------------------------------

  // return true if tree is an InnerNode----------------------------------------
  def isInnerNode(t: Tree): Boolean = t match {
    case InnerNode(_, _) => true
    case Leaf(_, _) => false
  }

  // return true if tree is a Leaf----------------------------------------------
  def isLeaf(t: Tree): Boolean = t match {
    case InnerNode(_, _) => false
    case Leaf(_, _) => true
  }

  // return the weight of a Tree------------------------------------------------
  def containedWeights(t: Tree): BigInt = t match {
    case InnerNode(t1, t2) => containedWeights(t1) + containedWeights(t2)
    case Leaf(w, _) => w
  }

  // return the list of chars contained in the tree-----------------------------
  def containedChars(t: Tree): List[Char] = t match {
    case InnerNode(t1, t2) => containedChars(t1) ++ containedChars(t2)
    case Leaf(_, c) => List(c)
  }

  // return the list of chars contained in the forest---------------------------
  def containedChars(f: Forest): List[Char] = f match {
    case hd :: tl => containedChars(hd) ++ containedChars(tl)
    case Nil() => Nil()
  }

  // return the number of leaves with a given character in the given tree-------
  def countChar(t: Tree, c: Char): BigInt = {
    containedChars(t).count(_ == c)
  }.ensuring(r => r >= 0)

  // return the number of leaves with a given character in the given forest-----
  def countChar(f: Forest, c: Char): BigInt = {
    containedChars(f).count(_ == c)
  }.ensuring(r => r >= 0)

  // return the number of leaves in the given tree------------------------------
  def countLeaves(t: Tree): BigInt = {
    t match {
      case Leaf(_, _) => BigInt(1)
      case InnerNode(t1, t2) => countLeaves(t1) + countLeaves(t2)
    }
  }.ensuring(r => r >= 0)

  // return the number of leaves in the given forest----------------------------
  def countLeaves(f: Forest): BigInt = {
    f match {
      case Nil() => BigInt(0)
      case hd :: tl => countLeaves(hd) + countLeaves(tl)
    }
  }.ensuring(r => r >= 0)

  // return true iff two trees are the same-------------------------------------
  def isSameTree(t1: Tree, t2: Tree): Boolean = t1 match {
    case Leaf(w1, c1) => t2 match {
      case Leaf(w2, c2) if (w1 == w2 && c1 == c2) => true
      case _ => false 
    }
    case InnerNode(t11, t12) => t2 match {
      case InnerNode(t21, t22) => isSameTree(t11, t21) && isSameTree(t12, t22)
      case _ => false
    }
  }

  // return true if st is a substree of t---------------------------------------
  def isSubTree(t: Tree, st: Tree): Boolean = {
    if (isSameTree(t, st)) true
    else t match {
      case Leaf(_, _) => false
      case InnerNode(t1, t2) => st match { case _ => isSubTree(t1, st) || isSubTree(t2, st) }
    }
  }

  // datatypes lemmas-----------------------------------------------------------

  // prove that isSameTree is a reflexive relation------------------------------
  def isSameTreeReflexivity(t: Tree): Unit = {
    t match {
      case Leaf(w, c) => ()
      case InnerNode(t1, t2) => {
        isSameTreeReflexivity(t1)
        isSameTreeReflexivity(t2)
      }
    }
  }.ensuring(_ => isSameTree(t, t))

  // prove that isSameTree is a transitive relation-----------------------------
  def isSameTreeTransitivity(t1: Tree, t2: Tree, t3: Tree): Unit = {
    require(isSameTree(t1, t2) && isSameTree(t2, t3))

    (t1, t2, t3) match {
      case (InnerNode(t11, t12), InnerNode(t21, t22), InnerNode(t31, t32)) => {
        isSameTreeTransitivity(t11, t21, t31)
        isSameTreeTransitivity(t12, t22, t32)
      }
      case _ => ()
    }
  }.ensuring(_ => isSameTree(t1, t3))

  // prove isSubTree is a reflexive relation------------------------------------
  def isSubTreeReflexivity(t: Tree): Unit = {
    isSameTreeReflexivity(t)
  }.ensuring(_ => isSubTree(t, t))

  // prove isSubTree is a transitive relation-----------------------------------
  def isSubTreeTransitivity(t: Tree, st: Tree, sst: Tree): Unit = {
    require(isSubTree(t, st) && isSubTree(st, sst))

    t match {
      case Leaf(_, _) => ()
      case t@InnerNode(t1, t2) => st match {
        case Leaf(_, _) => ()
        case InnerNode(st1, st2) => {
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
      case InnerNode(t21, t22) => t1 match { case InnerNode(t11, t12) => {
        if (isSubTree(t21, st)) isSameSubTree(t11, t21, st)
        else if (isSubTree(t22, st)) isSameSubTree(t12, t22, st)
      }}
    }
  }.ensuring(_ => isSubTree(t1, st))

  // prove children of a node are subtrees or the node itself-------------------
  def childrenAreSubTrees(t: Tree): Unit = {
    require(isInnerNode(t))
    isSubTreeReflexivity(t)
  }.ensuring(_ => t match { case InnerNode(t1, t2) => isSubTree(t, t1) && isSubTree(t, t2) })
  
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
    
    t match { case InnerNode(t1, t2) => {
        (t1, t2) match {
          case (Leaf(_, c1), t2@InnerNode(_, _)) if (c1 != c) => encodeCharIsDecodableAndCorrect(t2, c)
          case (t1@InnerNode(_, _), Leaf(_, c2)) if (c2 != c) => encodeCharIsDecodableAndCorrect(t1, c)
          case (t1@InnerNode(t11, t12), t2@InnerNode(t21, t22)) => if (canEncodeCharUniquely(t1, c)) encodeCharIsDecodableAndCorrect(t1, c) else encodeCharIsDecodableAndCorrect(t2, c)
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

    t match { case InnerNode(t1, t2) => {
      if (canEncodeCharUniquely(t1, c)) t1 match {
        case Leaf(_, _) => List(false)
        case t1@InnerNode(_, _) => List(false) ++ encodeChar(t1, c)
      } else {
        //TODO prove the following body assertion, maybe update canEncodeCharUniquely, countChar or ? definitions
        assert(canEncodeCharUniquely(t2, c))
        t2 match {
          case Leaf(_, _) => List(true)
          case t2@InnerNode(_, _) => List(true) ++ encodeChar(t2, c)
        }
      }
    }}
  }.ensuring(bs => canDecodeAtLeastOneChar(t, bs) && decodeChar(t, bs) == (List(c), Nil[Boolean]()))

  // prove that if we can decode exactly the given character with the given-----
  // tree from the given binary string then we can concatenate to it------------
  // anything and decoding the first char will remain the given one and the-----
  // remaining bits to decode will be the ones that we added to-----------------
  // the initial string---------------------------------------------------------
  def canStillDecodeOneCharAndSomething(t: Tree, c: Char, bs: List[Boolean], tlBs: List[Boolean]): Unit = {
    require(isInnerNode(t) && canDecodeAtLeastOneChar(t, bs) && decodeChar(t, bs) == (List(c), Nil[Boolean]()) && canDecodeAtLeastOneChar(t, bs ++ tlBs))

    t match { case t@InnerNode(t1, t2) => bs match {
      case hd :: tl => {
        if (!hd) t1 match {
          case Leaf(_, _) => ()
          case InnerNode(_, _) => canStillDecodeOneCharAndSomething(t1, c, tl, tlBs)
        } else t2 match {
          case Leaf(_, _) => ()
          case InnerNode(_, _) => canStillDecodeOneCharAndSomething(t2, c, tl, tlBs)
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

        canStillDecodeConcatenation(t, hdBs, tlBs)(t)
        canDecodeImpliesCanDecodeAtLeastOneChar(t, hdBs ++ tlBs)(t)
        canDecodeImpliesCanDecodeTailAfterOneCharDecoded(t, hdBs ++ tlBs)(t)
        canStillDecodeOneCharAndSomething(t, hd, hdBs, tlBs)
        concatenationIsStillDecodableAndCorrect(t, hdBs, tlBs, List(hd), tl)

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
    
    t match { case InnerNode(t1, t2) => { bs match {
        case hd :: tl => {
          if (!hd) {
            t1 match {
              case t1@InnerNode(t11, t12) => decodeCharLength(t1, tl)
              case Leaf(_, _) => ()
            }
          } else {
            t2 match {
              case t2@InnerNode(t11, t12) => decodeCharLength(t2, tl)
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

    t match { case InnerNode(t1, t2) => { bs match {
      case hd :: tl => {
        if (!hd) t1 match {
          case Leaf(_, _) => true
          case t1@InnerNode(_, _) => canDecodeAtLeastOneChar(t1, tl)
        } else t2 match {
          case Leaf(_, _) => true
          case t2@InnerNode(_, _) => canDecodeAtLeastOneChar(t2, tl)
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

    s match { case InnerNode(t1, t2) => { bs match {
      case hd :: tl => {
        if (!hd) t1 match {
          case Leaf(_, c) => ()
          case t1@InnerNode(_, _) => {
            childrenAreSubTrees(s)
            isSubTreeTransitivity(t, s, t1)
            canDecodeImpliesCanDecodeAtLeastOneChar(t1, tl)
          }
        } else t2 match {
          case Leaf(_, c) => ()
          case t2@InnerNode(_, _) => {
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
      case hd :: tl => { s match { case InnerNode(s1, s2) => {
        if (!hd) {
          s1 match {
            case s1@InnerNode(_, _) => canDecodeImpliesCanDecodeTailAfterOneCharDecoded(s1, tl)(t)
            case Leaf(_, c) => ()
          }
        } else {
          s2 match {
            case s2@InnerNode(_, _) => canDecodeImpliesCanDecodeTailAfterOneCharDecoded(s2, tl)(t)
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

    s match { case InnerNode(t1, t2) => { bs match {
      case hd :: tl => {
        if (!hd) t1 match {
          case Leaf(_, _) => ()
          case t1@InnerNode(_, _) => canDecodeExactlyOneCharImpliesCanDecode(t1, tl)
        } else t2 match {
          case Leaf(_, _) => ()
          case t2@InnerNode(_, _) => canDecodeExactlyOneCharImpliesCanDecode(t2, tl)
        }
      }
      case Nil() => ()
    }}}
  }.ensuring(_ => canDecode(s, bs)(t))

  // prove that if we can decode exactly one char and can decode an other-------
  // string then we can decode their concatenation------------------------------
  def canStillDecodeConcatenation(s: Tree, bs1: List[Boolean], bs2: List[Boolean])(implicit t: Tree): Unit = {
    require(isInnerNode(s) && isInnerNode(t) && (bs1.isEmpty && t == s || canDecodeAtLeastOneChar(s, bs1) && decodeChar(s, bs1)._2 == Nil[Boolean]()) && canDecode(t, bs2)(t))
    decreases(bs1.length)

    s match { case InnerNode(t1, t2) => bs1 match {
      case hd :: tl => {
        if (!hd) t1 match {
          case Leaf(_, c) => canStillDecodeConcatenation(t, Nil(), bs2)
          case t1@InnerNode(_, _) => canStillDecodeConcatenation(t1, tl, bs2)
        } else t2 match {
          case Leaf(_, c) => canStillDecodeConcatenation(t, Nil(), bs2)
          case t2@InnerNode(_, _) => canStillDecodeConcatenation(t2, tl, bs2)
        }
      }
      case Nil() => ()
    }}
  }.ensuring(_ => canDecode(s, bs1 ++ bs2)(t))

  // prove that we can stil decode the concatenation of two binary strings------
  // and the result is correct--------------------------------------------------
  def concatenationIsStillDecodableAndCorrect(t: Tree, bs1: List[Boolean], bs2: List[Boolean], s1: List[Char], s2: List[Char]): Unit = {
    require(isInnerNode(t) && canDecodeAtLeastOneChar(t, bs1 ++ bs2) && decodeChar(t, bs1 ++ bs2) == (s1, bs2) && canDecode(t, bs2)(t) && decode(t, bs2) == s2)
    // this is strange as it is automatically proven but removing this lemma----
    // prevents the proof from being validated----------------------------------
  }.ensuring(_ => decode(t, bs1 ++ bs2) == s1 ++ s2)

  // decode functions-----------------------------------------------------------

  // decode a single character from a list of bits with a given tree------------
  def decodeChar(t: Tree, bs: List[Boolean]): (List[Char], List[Boolean]) = {
    require(isInnerNode(t) && canDecodeAtLeastOneChar(t, bs))
    decreases(bs.length)

    (t, bs) match { case (InnerNode(t1, t2), hd :: tl) => {
      if (!hd) t1 match {
        case Leaf(_, c) => (List(c), tl)
        case t1@InnerNode(_, _) => decodeChar(t1, tl)
      } else t2 match {
        case Leaf(_, c) => (List(c), tl)
        case t2@InnerNode(_, _) => decodeChar(t2, tl)
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

  // generatePrefixFreeCode functions-------------------------------------------

  // return a copy of the string without duplicates-----------------------------
  def removeDuplicates(s: List[Char]): List[Char] = {
    s match {
      case Nil() => Nil[Char]()
      case hd :: tl => {
        val tmp = removeDuplicates(tl)
        if (tmp.contains(hd)) tmp else hd :: tmp
      }
    }
  }.ensuring(r => ListSpecs.noDuplicate(r))

  // return a prefix free code for the given list of characters that contains---
  // at least two different characters otherwise there is no meaningful---------
  // encoding for this----------------------------------------------------------
  def generatePrefixFreeCode(s: List[Char]): Tree = {
    require(removeDuplicates(s).length > 1)

    naivePrefixFreeCode(generateForest(s))(s)
  }.ensuring(t => isInnerNode(t) && s.forall(c => canEncodeCharUniquely(t, c)))

  // generate a forest of leaves for a given list of characters-----------------
  def generateForest(s: List[Char]): Forest = {
    require(removeDuplicates(s).length > 1)

    val occ = generateOccurrences(removeDuplicates(s))(s)
    val f = occurrencesToLeaves(occ, removeDuplicates(s))

    canStillEncodeSameCharsUniquely(f, s)

    f
  }.ensuring(f => s.forall(canEncodeCharUniquely(f, _)))

  // return the list of occurences tuples of the given chars the given string---
  def generateOccurrences(chars: List[Char])(implicit s: List[Char]): List[(Char, BigInt)] = {
    require(ListSpecs.noDuplicate(chars))

    chars match {
      case Nil() => Nil[(Char, BigInt)]()
      case hd :: tl => {
        val tuple =  (hd, s.count(_ == hd))
        val tuples = generateOccurrences(tl)

        assert(ListSpecs.noDuplicate((tuple::tuples).map(_._1)))

        tuple :: tuples
      }
    }
  }.ensuring(r => ListSpecs.noDuplicate(r.map(_._1)) && r.map(_._1) == chars)

  //TODO prove postcondition and document
  def occurrencesToLeaves(occ: List[(Char, BigInt)], chars: List[Char]): Forest = {
    require(ListSpecs.noDuplicate(occ.map(_._1)) && occ.map(_._1) == chars)

    (occ, chars) match {
      case (occHd :: occTl, chardHd :: charsTl) => {
        val newLeaf = Leaf(occHd._2, occHd._1)
        val newLeaves = occurrencesToLeaves(occTl, charsTl)

        newLeaf :: newLeaves
      }
      case _ => Nil[Tree]()
    }
  }.ensuring(r => r.forall(isLeaf) && chars.forall(canEncodeCharUniquely(r, _)))

  // generate the corresponding prefix free code given a Forest-----------------
  def naivePrefixFreeCode(f: Forest)(implicit s: List[Char]): Tree = {
    require((f.length == 1 && isInnerNode(f.head) || f.length > 1) && s.forall(canEncodeCharUniquely(f, _)))
    decreases(f.length)
    f match {
      case t1 :: t2 :: tl => {
        sameContainedCharsForMergedTreesInForest(f)
        tempLemma(f, InnerNode(t1, t2) :: tl, s)
        naivePrefixFreeCode(InnerNode(t1, t2) :: tl)
      }
      case t :: _ => {
        canStillEncodeUniquelyWithSingleTree(f, s)
        t
      }
    }
  }.ensuring(pfc => isInnerNode(pfc) && s.forall(canEncodeCharUniquely(pfc, _)))

  // instead of using a naive algorithm to generate a prefix-free code----------
  // we may use Huffman's algorithm that generate the optimal code--------------
  // for a given forest, we assume this for now since it is much more-----------
  // challenging to prove as it should remain sorted at each iteration.---------
  // This can be kept for further work------------------------------------------

  // generatePrefixFreeCode lemmas---------------------------------------------

  // prove that if we can encode uniquely a string removing all the duplicates--
  // then we can decode its initial form----------------------------------------
  def canStillEncodeSameCharsUniquely(f: Forest, s: List[Char]): Unit = {
    require(removeDuplicates(s).forall(canEncodeCharUniquely(f, _)))
    decreases(s.length)

    s match {
      case hd :: tl => {
        ListSpecs.forallContained(removeDuplicates(s), (c: Char) => canEncodeCharUniquely(f, c), hd)
        canStillEncodeSameCharsUniquely(f, tl)
      }
      case Nil() => () 
    }
  }.ensuring( _ => s.forall(canEncodeCharUniquely(f, _)))

  // prove that if we can encode uniquely with a forest of one tree then--------
  // we can encode uniquely with the single tree of it--------------------------
  def canStillEncodeUniquelyWithSingleTree(f: Forest, s: List[Char]): Unit = {
    require(f.length == 1 && s.forall(canEncodeCharUniquely(f, _)))

    s match {
      case Nil() => ()
      case hd :: tl => canStillEncodeUniquelyWithSingleTree(f, tl)
    }
  }.ensuring(_ => s.forall(canEncodeCharUniquely(f.head, _)))

  // You're entering dangerous land---------------------------------------------

  //TODO clean and document
  def tempLemma3Tree(t: Tree, c: Char): Unit = {
  }.ensuring(_ => containedChars(t).count(_ == c) == countChar(t, c))

  //TODO clean and document
  def tempLemma3(f: Forest, c: Char): Unit = {
  }.ensuring(_ => containedChars(f).count(_ == c) == countChar(f, c))

  //TODO clean and document
  def tempLemma2(f1: Forest, f2: Forest, c: Char): Unit = {
    require(containedChars(f1) == containedChars(f2))
    tempLemma3(f1, c)
    tempLemma3(f2, c)
    assert(containedChars(f1).count(_ == c) == containedChars(f2).count(_ == c))
  }.ensuring(_ => countChar(f1, c) == countChar(f2, c))

  //TODO clean and document
  def tempLemma(f1: Forest, f2: Forest, s: List[Char]) : Unit = {
    require(containedChars(f1) == containedChars(f2) && s.forall(canEncodeCharUniquely(f1, _)))
    s match {
      case hd :: tl => {
        assert(canEncodeCharUniquely(f1, hd))
        tempLemma2(f1, f2, hd)
        assert(canEncodeCharUniquely(f2, hd))
        tempLemma(f1, f2, tl)
      }
      case Nil() => ()
    }

  }.ensuring( _ => s.forall(canEncodeCharUniquely(f2, _)))

  //TODO clean and document
  def sameContainedCharsForMergedTreesInForest(f: Forest): Unit = {
    require(f.length >= 2)

    f match {
      case t1 :: t2 :: tl => {
        assert(ListSpecs.appendAssoc(containedChars(t1), containedChars(t2), containedChars(tl)))
      }
      case _ => ()
    }

  }.ensuring(_ => f match {
    case t1 :: t2 :: tl => containedChars(f) == containedChars(InnerNode(t1, t2) :: tl)
  })

  // You're leaving dangerous land----------------------------------------------

  // final theorem--------------------------------------------------------------

  // prove that decode(encode(x)) is equal to x using a prefix-free code--------
  def decodeEncodedString(s: List[Char]): Unit = {
    require(removeDuplicates(s).length > 1)
  }.ensuring(_ => {
    val t = generatePrefixFreeCode(s)
    val e = encode(t, s)
    val d = decode(t, e)
    s == d
  })
}
