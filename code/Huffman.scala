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

object HuffmanCode {
  // functional implemention of Huffman's Algorithm-----------------------------
  
  // datatypes------------------------------------------------------------------
  sealed abstract class Tree
  case class InnerNode(w: BigInt, t1: Tree, t2: Tree) extends Tree
  case class Leaf(w: BigInt, c: Char) extends Tree

  type Forest = List[Tree]

  // return true if tree is an InnerNode----------------------------------------
  def isInnerNode(t: Tree): Boolean = t match {
    case InnerNode(_, _, _) => true
    case Leaf(_, _) => false
  }

  // return true if tree is a Leaf----------------------------------------------
  def isLeaf(t: Tree): Boolean = t match {
    case InnerNode(_, _, _) => false
    case Leaf(_, _) => true
  }

  // return the number of leaves with a given character in the given tree-------
  def countChar(t: Tree, c: Char): BigInt = {
    t match {
      case Leaf(_, lC) => if (lC == c) BigInt(1) else BigInt(0)
      case InnerNode(_, t1, t2) => countChar(t1, c) + countChar(t2, c)
    }
  }.ensuring(r => r >= 0)

  // return true iff two trees are the same-------------------------------------
  def isSameTree(t1: Tree, t2: Tree): Boolean = t1 match {
    case Leaf(w1, c1) => t2 match {
      case Leaf(w2, c2) if (w1 == w2 && c1 == c2) => true
      case _ => false 
    }
    case InnerNode(w1, t11, t12) => t2 match {
      case InnerNode(w2, t21, t22) => w1 == w2 && isSameTree(t11, t21) && isSameTree(t12, t22)
      case _ => false
    }
  }

  // prove that isSameTree is a reflexive relation------------------------------
  def isSameTreeReflexivity(t: Tree): Unit = {
    t match {
      case Leaf(w, c) => ()
      case InnerNode(w, t1, t2) => {
        isSameTreeReflexivity(t1)
        isSameTreeReflexivity(t2)
      }
    }
  }.ensuring(_ => isSameTree(t, t))

  // prove that isSameTree is a transitive relation-----------------------------
  def isSameTreeTransitivity(t1: Tree, t2: Tree, t3: Tree): Unit = {
    require(isSameTree(t1, t2) && isSameTree(t2, t3))

    (t1, t2, t3) match {
      case (InnerNode(_, t11, t12), InnerNode(_, t21, t22), InnerNode(_, t31, t32)) => {
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
      case InnerNode(_, t1, t2) => st match { case _ => isSubTree(t1, st) || isSubTree(t2, st) }
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
      case t@InnerNode(_, t1, t2) => st match {
        case Leaf(_, _) => ()
        case InnerNode(stw, st1, st2) => {
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
      case InnerNode(_, t21, t22) => t1 match { case InnerNode(_, t11, t12) => {
        if (isSubTree(t21, st)) isSameSubTree(t11, t21, st)
        else if (isSubTree(t22, st)) isSameSubTree(t12, t22, st)
      }}
    }
  }.ensuring(_ => isSubTree(t1, st))

  // prove children of a node are subtrees or the node itself-------------------
  def childrenAreSubTrees(t: Tree): Unit = {
    require(isInnerNode(t))
    isSubTreeReflexivity(t)
  }.ensuring(_ => t match { case InnerNode(_, t1, t2) => isSubTree(t, t1) && isSubTree(t, t2) })

  // return the weight of a Tree------------------------------------------------
  def cachedWeight(t: Tree): BigInt = t match {
    case InnerNode(w, _, _) => w
    case Leaf(w, _) => w
  }

  // merge two Tree in one by adding an InnerNode-------------------------------
  def uniteTrees(t1: Tree, t2: Tree): Tree = InnerNode(cachedWeight(t1) + cachedWeight(t2), t1, t2)

  // insert a Tree in a Forest and sort the latter------------------------------
  def insortTree(t: Tree, f: Forest): Forest = {
    decreases(f.length)

    f match {
      case Nil() => List(t)
      case hd :: tl => if (cachedWeight(t) <= cachedWeight(hd)) t :: f else hd :: insortTree(t, tl)
    }
  }.ensuring(r => r.length == f.length+1)

  // generate the Forest of Leaf for a given list of characters-----------------
  def generateUnsortedForest(s: List[Char]): Forest = {
    s.foldLeft[List[Char]](Nil())((l, c) => if (l.contains(c)) l else (c :: l)).map(c => Leaf(s.count(_ == c), c))
  }

  // sort a Forest--------------------------------------------------------------
  def sortForest(f: Forest): Forest = f match {
      case Nil() => Nil()
      case hd :: tl => insortTree(hd, sortForest(tl))
  }

  // generate and sort a Forest given a list of characters----------------------
  def generateSortedForest(s: List[Char]): Forest = {
    sortForest(generateUnsortedForest(s))
  }
  
  // generate Huffman code's Tree recursively given a Forest--------------------
  def huffmansAlgorithmHelper(f: Forest): Tree = {
    require(f.length == 1 && isInnerNode(f(0)) || f.length > 1 )
    decreases(f.length)

    f match {
      case t1 :: t2 :: tl => huffmansAlgorithmHelper(insortTree(uniteTrees(t1, t2), tl))
      case t :: _ => t
    }
  }.ensuring(t => isInnerNode(t))

  // generate Huffman code's Tree given a Forest--------------------------------
  def huffmansAlgorithm(f: Forest): Tree = {
    require(f.length > 1)
    huffmansAlgorithmHelper(f)
  }.ensuring(t => isInnerNode(t))

  // encode/decode--------------------------------------------------------------

  // encode lemmas--------------------------------------------------------------

  // define that a character is uniquely encodable iff it appears once----------
  // in the tree----------------------------------------------------------------
  def canEncodeCharUniquely(t: Tree, c: Char): Boolean = (countChar(t, c) == 1)

  // prove than if we can exactly decode exactly one character from ------------
  // a binary string with a given tree then we can decode the binary string-----
  def canDecodeExactlyOneCharImpliesCanDecode(s: Tree, bs: List[Boolean])(implicit t: Tree): Unit = {
    require(isInnerNode(s) && isInnerNode(t) && canDecodeAtLeastOneChar(s, bs) && decodeChar(s, bs)._2 ==  Nil())
    decreases(bs.length)

    s match { case InnerNode(_, t1, t2) => { bs match {
      case hd :: tl => {
        if (!hd) t1 match {
          case Leaf(_, _) => ()
          case t1@InnerNode(_, _, _) => canDecodeExactlyOneCharImpliesCanDecode(t1, tl)
        } else t2 match {
          case Leaf(_, _) => ()
          case t2@InnerNode(_, _, _) => canDecodeExactlyOneCharImpliesCanDecode(t2, tl)
        }
      }
      case Nil() => ()
    }}}
  }.ensuring(_ => canDecode(s, bs)(t))

  // prove that if we encode a character with a given tree then we can----------
  // decode it and get back the correct character-------------------------------
  def encodeCharIsDecodableAndCorrect(t: Tree, c: Char): Unit = {
    require(isInnerNode(t) && canEncodeCharUniquely(t, c))
    decreases(encodeChar(t, c).length)

    canDecodeExactlyOneCharImpliesCanDecode(t, encodeChar(t, c))(t)
    
    t match { case InnerNode(_, t1, t2) => {
        (t1, t2) match {
          case (Leaf(_, c1), t2@InnerNode(_, _, _)) if (c1 != c) => encodeCharIsDecodableAndCorrect(t2, c)
          case (t1@InnerNode(_, _, _), Leaf(_, c2)) if (c2 != c) => encodeCharIsDecodableAndCorrect(t1, c)
          case (t1@InnerNode(_, t11, t12), t2@InnerNode(_, t21, t22)) => if (canEncodeCharUniquely(t1, c)) encodeCharIsDecodableAndCorrect(t1, c) else encodeCharIsDecodableAndCorrect(t2, c)
          case (Leaf(_, c1), _) if (c1 == c) => ()
          case (_, Leaf(_, c2)) if (c2 == c) => ()
        }
      }
    }
  }.ensuring(_ => {
    val bs = encodeChar(t, c)
    canDecode(t, bs)(t) && decode(t, bs) == List(c)
  })

  //TODO comment this
  def canDecodeExactlyOneCharAndCanDecodeImpliesCanDecodeConcatenation(s: Tree, bs1: List[Boolean], bs2: List[Boolean])(implicit t: Tree): Unit = {
    require(isInnerNode(s) && isInnerNode(t) && (bs1.isEmpty && t == s || canDecodeAtLeastOneChar(s, bs1) && decodeChar(s, bs1)._2 == Nil[Boolean]()) && canDecode(t, bs2)(t))
    decreases(bs1.length)

    s match { case InnerNode(_, t1, t2) => bs1 match {
      case hd :: tl => {
        if (!hd) t1 match {
          case Leaf(_, c) => canDecodeExactlyOneCharAndCanDecodeImpliesCanDecodeConcatenation(t, Nil(), bs2)
          case t1@InnerNode(_, _, _) => canDecodeExactlyOneCharAndCanDecodeImpliesCanDecodeConcatenation(t1, tl, bs2)
        } else t2 match {
          case Leaf(_, c) => canDecodeExactlyOneCharAndCanDecodeImpliesCanDecodeConcatenation(t, Nil(), bs2)
          case t2@InnerNode(_, _, _) => canDecodeExactlyOneCharAndCanDecodeImpliesCanDecodeConcatenation(t2, tl, bs2)
        }
      }
      case Nil() => ()
    }}
  }.ensuring(_ => canDecode(s, bs1 ++ bs2)(t))

  //TODO comment this and rename
  def temp(t: Tree, bs1: List[Boolean], bs2: List[Boolean], s1: List[Char], s2: List[Char]): Unit = {
    require(isInnerNode(t) && canDecodeAtLeastOneChar(t, bs1 ++ bs2) && decodeChar(t, bs1 ++ bs2) == (s1, bs2) && canDecode(t, bs2)(t) && decode(t, bs2) == s2)
    //TODO parse next and call recursively on bs2
  }.ensuring(_ => decode(t, bs1 ++ bs2) == s1 ++ s2)

  // encode functions-----------------------------------------------------------

  // encode a character as a list of bits recursively with a given tree---------
  def encodeChar(t: Tree, c: Char): List[Boolean] = {
    require(isInnerNode(t) && canEncodeCharUniquely(t, c))

    t match { case InnerNode(_, t1, t2) => {
      if (canEncodeCharUniquely(t1, c)) t1 match {
        case Leaf(_, _) => List(false)
        case t1@InnerNode(_, _, _) => List(false) ++ encodeChar(t1, c)
      }
      else t2 match {
        case Leaf(_, _) => List(true)
        case t2@InnerNode(_, _, _) => List(true) ++ encodeChar(t2, c)
      }
    }}
  }.ensuring(bs => canDecodeAtLeastOneChar(t, bs) && decodeChar(t, bs) == (List(c), Nil[Boolean]()))

//def canDecodeConcatenationImpliesCorrectDecoding(t: Tree, hd: List[Char], tl: List[Char], hdBs: List[Boolean], tlBs: List[Boolean]): Unit = {
  //  require(isInnerNode(t) && canDecodeAtLeastOneChar(t, hdBs) && decodeChar(t, hdBs) == (hd, Nil[Boolean]()) && canDecode(t, tlBs)(t) && decode(t, tlBs) == tl)
  //  decreases(hdBs.length)
  //  //TODO
  //}.ensuring(_ => {
  //  canDecodeExactlyOneCharAndCanDecodeImpliesCanDecodeConcatenation(t, hdBs, tlBs)(t)
  //  decode(t, hdBs ++ tlBs) == hd ++ tl
  //})

  // encode a list of characters as list of bits with a given tree--------------
  def encode(t: Tree, s: List[Char]): List[Boolean] = {
    require(isInnerNode(t) && !s.isEmpty && s.forall(c => canEncodeCharUniquely(t, c)))
    decreases(s.length)

    s match { case hd :: tl => {
      if (tl.isEmpty) {
        encodeCharIsDecodableAndCorrect(t, hd)
        encodeChar(t, hd)
      }
      else {
        val hdBs = encodeChar(t, hd)
        val tlBs = encode(t, tl)

        canDecodeExactlyOneCharAndCanDecodeImpliesCanDecodeConcatenation(t, hdBs, tlBs)(t)
        canDecodeImpliesCanDecodeAtLeastOneChar(t, hdBs ++ tlBs)(t)
        canDecodeImpliesCanDecodeTailAfterOneCharDecoded(t, hdBs ++ tlBs)(t)
        //TODO add lemma to say that if we can decode exactly one char and add some string then decodechar returns that string
        temp(t, hdBs, tlBs, List(hd), tl)
        hdBs ++ tlBs
      }
    }}
  }.ensuring(bs => canDecode(t, bs)(t) && decode(t, bs) == s)

  // decode lemmas--------------------------------------------------------------
  
  // check if at least one character can be decoded-----------------------------
  def canDecodeAtLeastOneChar(t: Tree, bs: List[Boolean]): Boolean = {
    require(isInnerNode(t))
    decreases(bs.length)

    t match { case InnerNode(_, t1, t2) => { bs match {
      case hd :: tl => {
        if (!hd) t1 match {
          case Leaf(_, _) => true
          case t1@InnerNode(_, _, _) => canDecodeAtLeastOneChar(t1, tl)
        } else t2 match {
          case Leaf(_, _) => true
          case t2@InnerNode(_, _, _) => canDecodeAtLeastOneChar(t2, tl)
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

    s match { case InnerNode(_, t1, t2) => { bs match {
      case hd :: tl => {
        if (!hd) t1 match {
          case Leaf(_, c) => ()
          case t1@InnerNode(_, _, _) => {
            childrenAreSubTrees(s)
            isSubTreeTransitivity(t, s, t1)
            canDecodeImpliesCanDecodeAtLeastOneChar(t1, tl)
          }
        } else t2 match {
          case Leaf(_, c) => ()
          case t2@InnerNode(_, _, _) => {
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
      case hd :: tl => { s match { case InnerNode(_, s1, s2) => {
        if (!hd) {
          s1 match {
            case s1@InnerNode(_, _, _) => canDecodeImpliesCanDecodeTailAfterOneCharDecoded(s1, tl)(t)
            case Leaf(_, c) => ()
          }
        } else {
          s2 match {
            case s2@InnerNode(_, _, _) => canDecodeImpliesCanDecodeTailAfterOneCharDecoded(s2, tl)(t)
            case Leaf(_, c) => ()
          }
        }
    }}}}
  }.ensuring(_ => decodeChar(s, bs) match { case(_, nBs) => nBs.isEmpty || canDecode(t, nBs)(t) })

  // decode functions-----------------------------------------------------------

  // decode a single character from a list of bits with a given tree------------
  def decodeChar(t: Tree, bs: List[Boolean]): (List[Char], List[Boolean]) = {
    require(isInnerNode(t) && canDecodeAtLeastOneChar(t, bs))
    decreases(bs.length)

    (t, bs) match { case (InnerNode(_, t1, t2), hd :: tl) => {
      if (!hd) t1 match {
        case Leaf(_, c) => (List(c), tl)
        case t1@InnerNode(_, _, _) => decodeChar(t1, tl)
      } else t2 match {
        case Leaf(_, c) => (List(c), tl)
        case t2@InnerNode(_, _, _) => decodeChar(t2, tl)
      }
    }}
  }.ensuring(r => r._1.length == 1)

  // prove that the length of the remaining list of bits after decoding---------
  // the first decodable character is smaller than the original list of bits----
  def decodeCharLength(t: Tree, bs: List[Boolean]): Unit = {
    require(isInnerNode(t) && canDecodeAtLeastOneChar(t, bs))
    decreases(bs.length)
    
    t match { case InnerNode(_, t1, t2) => { bs match {
        case hd :: tl => {
          if (!hd) {
            t1 match {
              case t1@InnerNode(_, t11, t12) => decodeCharLength(t1, tl)
              case Leaf(_, _) => ()
            }
          } else {
            t2 match {
              case t2@InnerNode(_, t11, t12) => decodeCharLength(t2, tl)
              case Leaf(_, _) => ()
            }
          }
        }
        case Nil() => ()
    }}}
  }.ensuring(_ => decodeChar(t, bs) match { case (_, nBs) => nBs.length < bs.length })

  // decode a list of bits with a given tree recursively------------------------
  def decodeHelper(t: Tree, bs: List[Boolean], acc: List[Char]): List[Char] = {
    require(isInnerNode(t) && !bs.isEmpty && canDecode(t, bs)(t))
    decreases(bs.length)

    isSubTreeReflexivity(t)
    canDecodeImpliesCanDecodeTailAfterOneCharDecoded(t, bs)(t)
    decodeCharLength(t, bs)

    decodeChar(t, bs) match { case(c, nBs) => if (nBs.isEmpty) acc ++ c else decodeHelper(t, nBs, acc ++ c) }
  }

  // decode a list of bits as a list of characters with a given tree------------
  def decode(t: Tree, bs: List[Boolean]): List[Char] = {
    require(isInnerNode(t) && canDecode(t, bs)(t))
    decreases(bs.length)

    bs match {
      case Nil() => Nil()
      case _ => {
        isSubTreeReflexivity(t)
        canDecodeImpliesCanDecodeAtLeastOneChar(t, bs)(t)
        decodeHelper(t, bs, Nil())
      }
    }
  }

  // final theorem--------------------------------------------------------------

  // return true if the given list of characters contains-----------------------
  // more than two different ones-----------------------------------------------
  def containsAtLeastTwoDifferentCharacters(s: List[Char]): Boolean = {
    s.foldLeft[List[Char]](Nil())((l, c) => if (l.contains(c)) l else (c :: l)).length >= 2
  }

  // return the Huffman code tree for a given list of characters that contains--
  // at least two different characters otherwise there is no meaningful---------
  // encoding for this----------------------------------------------------------
  def generateHuffmanCodeTree(s: List[Char]): Tree = {
    require(containsAtLeastTwoDifferentCharacters(s))
    huffmansAlgorithm(generateSortedForest(s))
    //TODO
  }.ensuring(t => isInnerNode(t) && s.forall(c => canEncodeCharUniquely(t, c)))

  // prove that decode(encode(x)) is equal to x using Huffman's algorithm-------
  def decodeEncodedString(s: List[Char]): Unit = {
    require(containsAtLeastTwoDifferentCharacters(s))
  }.ensuring(_ => {
    val t = generateHuffmanCodeTree(s)
    val e = encode(t, s)
    val d = decode(t, e)
    s == d
  })
}
