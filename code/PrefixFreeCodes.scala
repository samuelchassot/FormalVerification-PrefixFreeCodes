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

object PrefixFreeCodes {

  // datatypes------------------------------------------------------------------

  sealed abstract class Tree
  case class InnerNode(t1: Tree, t2: Tree) extends Tree
  case class Leaf(w: BigInt, c: Char) extends Tree

  type Forest = List[Tree]

  // datatypes helper functions-------------------------------------------------

  // return true if tree is an InnerNode----------------------------------------
  // usefull to make sure encoding and decoding operations are performed--------
  // with a node and not a leaf which would lead to a meaningless interpretaton-
  def isInnerNode(t: Tree): Boolean = t match {
    case InnerNode(_, _) => true
    case Leaf(_, _) => false
  }

  // return true if tree is a Leaf----------------------------------------------
  // usefull to make sure when generating a forest from the input string--------
  // that we have only leaves---------------------------------------------------
  def isLeaf(t: Tree): Boolean = t match {
    case InnerNode(_, _) => false
    case Leaf(_, _) => true
  }

  // return the list of chars contained in a tree-------------------------------
  def containedChars(t: Tree): List[Char] = t match {
    case InnerNode(t1, t2) => containedChars(t1) ++ containedChars(t2)
    case Leaf(_, c) => List(c)
  }

  // return the list of chars contained in a forest-----------------------------
  def containedChars(f: Forest): List[Char] = f match {
    case hd :: tl => containedChars(hd) ++ containedChars(tl)
    case Nil() => Nil()
  }

  // return the number of leaves with a given character in a tree---------------
  def countChar(t: Tree, c: Char): BigInt = {
    containedChars(t).count(_ == c)
  }

  // return the number of leaves with a given character in the a forest---------
  def countChar(f: Forest, c: Char): BigInt = {
    containedChars(f).count(_ == c)
  }

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
  // usefull to show that isSubTree is also a reflexive relation----------------
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
  // usefull to prove isSameSubTree---------------------------------------------
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
  // usefull when we need to call functions where explicit and implicit---------
  // tree parameters are actually the same but it is not trivial----------------
  // it is a subTree of itself--------------------------------------------------
  def isSubTreeReflexivity(t: Tree): Unit = {
    isSameTreeReflexivity(t)
  }.ensuring(_ => isSubTree(t, t))

  // if st is a subtree of t2 and t1 is the same as t2 then st is---------------
  // a subtree of t1------------------------------------------------------------
  // usefull to prove isSubTreeTransitivity-------------------------------------
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

  // prove isSubTree is a transitive relation-----------------------------------
  // usefull in recursive calls to make sure children of a tree is actually-----
  // a subTree------------------------------------------------------------------
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

  // prove children of a node are subtrees or the node itself-------------------
  // usefull in recursive calls to make sure children of a tree is actually-----
  // a subTree------------------------------------------------------------------
  def childrenAreSubTrees(t: Tree): Unit = {
    require(isInnerNode(t))
    isSubTreeReflexivity(t)
  }.ensuring(_ => t match { case InnerNode(t1, t2) => isSubTree(t, t1) && isSubTree(t, t2) })
  
  // encode/decode--------------------------------------------------------------

  // encode lemmas--------------------------------------------------------------

  // define that a character is uniquely encodable iff it appears once----------
  // in a tree or a forest------------------------------------------------------
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
    }}
  }.ensuring(_ => canDecode(t, encodeChar(t, c))(t) && decode(t, encodeChar(t, c)) == List(c))

  // prove that counting how many time a predicate is satisfied on two lists----
  // is equivalent to counting it in the concatenation of the lists-------------
  def countPreservedOnConcat(l1: List[Char], l2: List[Char], p: Char => Boolean): Unit = {
    l1 match {
      case hd1 :: tl1 => countPreservedOnConcat(tl1, l2, p)
      case Nil() => ()
    }
  }.ensuring(_ => (l1 ++ l2).count(p) == l1.count(p) + l2.count(p))

  // prove that if we can encode uniquely a character with a tree then it-------
  // means we can encode it with one xor the other child of the tree------------
  // usefull to show that while encoding you will chose exactly one of the------
  // children
  def canEncodeUniquelyImpliesWithExactlyOneChild(t: Tree, c: Char): Unit = {
    require(isInnerNode(t) && canEncodeCharUniquely(t, c))
    t match { case InnerNode(t1, t2) => countPreservedOnConcat(containedChars(t1), containedChars(t2), c1 => c1 == c) }
  }.ensuring(_ => t match { case InnerNode(t1, t2) => canEncodeCharUniquely(t1, c) ^ canEncodeCharUniquely(t2, c) })

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

  // encode functions-----------------------------------------------------------

  // encode a character as a list of bits recursively with a given tree---------
  def encodeChar(t: Tree, c: Char): List[Boolean] = {
    require(isInnerNode(t) && canEncodeCharUniquely(t, c))

    t match { case InnerNode(t1, t2) => {
      if (canEncodeCharUniquely(t1, c)) t1 match {
        case Leaf(_, _) => List(false)
        case t1@InnerNode(_, _) => List(false) ++ encodeChar(t1, c)
      } else {
        // make sure that if we cannot encode the char uniquely with t1---------
        // then it means we eventually can with t2------------------------------
        canEncodeUniquelyImpliesWithExactlyOneChild(t, c)
        t2 match {
          case Leaf(_, _) => List(true)
          case t2@InnerNode(_, _) => List(true) ++ encodeChar(t2, c)
        }
      }
    }}
  // the result is decodable and decoding it returns the original character-----
  // and nothing more to decode-------------------------------------------------
  }.ensuring(bs => canDecodeAtLeastOneChar(t, bs) && decodeChar(t, bs) == (List(c), Nil[Boolean]()))

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
  // the result is decodable and decoding it returns exactly the original string
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

    forallTrivial(f, removeDuplicates(s))
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

  // alternative definition of a forall function that checks if all chars
  // of the given list yields to a countChar value of 1 when called on the 
  // given forest
  // ensuring that it is equivalent to the forall of the library
  def forallAltcountChar(s: List[Char], f: Forest) : Boolean = {
    decreases(s.length)
    s match {
      case hd :: tl => (countChar(f, hd) == 1) && forallAltcountChar(tl, f)
      case Nil() => true
    }
  }.ensuring(b => b == s.forall(countChar(f, _) == 1))

  // prove that if we can encode uniquely with a forest, adding a leaf with a char that is not
  // in the list does not change anything
  def addingNewLeafToForestPreservesForallCountChar(f: Forest, l: Leaf, s: List[Char]): Unit = {
    require(s.forall(countChar(f, _) == 1) && s.forall(countChar(l, _) == 0))
    decreases(s.length)

    s match {
      case hd :: tl => {
        addingNewLeafToForestPreservesForallCountChar(f, l, tl)
      }
      case Nil() => ()
    }
  }.ensuring(_ => forallAltcountChar(s, l :: f))

  // prove that countChar called on a leaf forall char of a list gives 0 if the character of the
  // leaf is not in the list
  def countCharOnALeafWithDifferentCharacterAlwaysGivesZero(l: Leaf, s: List[Char]): Unit = {
    require(!s.contains(l.c))
    decreases(s.length)

    s match {
      case hd :: tl => {
        countCharOnALeafWithDifferentCharacterAlwaysGivesZero(l, tl)
      } 
      case Nil() => ()
    }

  }.ensuring(_ => s.forall(countChar(l, _) == 0))

  // generate a forest of leaves given the occurences and the list of chars.
  // the occurences is a list of tuples containing the char with the number of times
  // it appears in the original list.
  // each char must appear only once in the occurences as well as in chars.
  // it ensures that the produced forest only contains leaves and that it contains
  // all the chars of the list once and only once.
  def occurrencesToLeaves(occ: List[(Char, BigInt)], chars: List[Char]): Forest = {
    require(ListSpecs.noDuplicate(occ.map(_._1)) && occ.map(_._1) == chars)
    decreases(occ.length)

    (occ, chars) match {
      case (occHd :: occTl, chardHd :: charsTl) => {
        val newLeaf = Leaf(occHd._2, occHd._1)
        val newLeaves = occurrencesToLeaves(occTl, charsTl)
        val r = newLeaf :: newLeaves

        countCharOnALeafWithDifferentCharacterAlwaysGivesZero(newLeaf, charsTl)
        addingNewLeafToForestPreservesForallCountChar(newLeaves, newLeaf, charsTl)

        r
      }
      case _ => Nil[Tree]()
    }
  }.ensuring(r => r.forall(isLeaf) && containedChars(r) == chars && chars.forall(countChar(r, _) == 1))

  // generate the corresponding prefix free code given a Forest-----------------
  def naivePrefixFreeCode(f: Forest)(implicit s: List[Char]): Tree = {
    require((f.length == 1 && isInnerNode(f.head) || f.length > 1) && s.forall(canEncodeCharUniquely(f, _)))
    decreases(f.length)
    f match {
      case t1 :: t2 :: tl => {
        sameContainedCharsForMergedTreesInForest(f)
        sameContainedCharsImpliesSameCanEncodeUniquely(f, InnerNode(t1, t2) :: tl, s)
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
  def trivial(f: Forest, c: Char): Unit = {
    require(countChar(f, c) == 1)
  }.ensuring(_ => canEncodeCharUniquely(f, c))

  //TODO clean and document
  def forallTrivial(f: Forest, c: List[Char]): Unit = {
    require(c.forall(countChar(f, _) == 1))

    c match {
      case hd :: tl => {
        trivial(f, hd)
        forallTrivial(f, tl)
      }
      case _ => ()
    }
  }.ensuring(_ => c.forall(canEncodeCharUniquely(f, _)))


  //TODO clean and document
  def tempLemma3Tree(t: Tree, c: Char): Unit = {
  }.ensuring(_ => containedChars(t).count(_ == c) == countChar(t, c))

  // prove that counting how many times a char appears in the contained chars of a forest
  // gives the same result as calling the countChar function on that forest
  def countCharIsSameAsCountingInContainedChars(f: Forest, c: Char): Unit = {
  }.ensuring(_ => containedChars(f).count(_ == c) == countChar(f, c))

  // prove that counting how many times a given char appears in two forests with the same containedChars
  // gives the same result
  def sameContainedCharsImpliesSameCountChar(f1: Forest, f2: Forest, c: Char): Unit = {
    require(containedChars(f1) == containedChars(f2))

    countCharIsSameAsCountingInContainedChars(f1, c)
    countCharIsSameAsCountingInContainedChars(f2, c)
  }.ensuring(_ => countChar(f1, c) == countChar(f2, c))

  // prove that if we can encode uniquely with a forest then we can with a forest with the same contained chars
  // as well
  def sameContainedCharsImpliesSameCanEncodeUniquely(f1: Forest, f2: Forest, s: List[Char]) : Unit = {
    require(containedChars(f1) == containedChars(f2) && s.forall(canEncodeCharUniquely(f1, _)))
    s match {
      case hd :: tl => {
        sameContainedCharsImpliesSameCountChar(f1, f2, hd)
        sameContainedCharsImpliesSameCanEncodeUniquely(f1, f2, tl)
      }
      case Nil() => ()
    }

  }.ensuring( _ => s.forall(canEncodeCharUniquely(f2, _)))

  // prove that the contained chars of a forest are preserved when merging the two first trees in a new InnerNode
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
