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

  // functional implemantion of Huffman's Algorithm-----------------------------
  
  // datatypes------------------------------------------------------------------
  sealed abstract class Tree
  case class InnerNode(w: BigInt, t1: Tree, t2: Tree) extends Tree
  case class Leaf(w: BigInt, c: Char) extends Tree

  type Forest = List[Tree]

  // return true if Tree is an InnerNode----------------------------------------
  def isInnerNode(t: Tree): Boolean = t match {
    case InnerNode(_, _, _) => true
    case Leaf(_, _) => false
  }

  // return true if Tree is a Leaf----------------------------------------------
  def isLeaf(t: Tree): Boolean = t match {
    case InnerNode(_, _, _) => false
    case Leaf(_, _) => true
  }

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
      case t@InnerNode(tw, t1, t2) => st match {
        case Leaf(_, _) => ()
        case InnerNode(stw, st1, st2) => {
          if (isSameTree(t, st)) {
            isSameSubTree(t, st, sst)
          } else if (isSubTree(t1, st)) {
            isSubTreeTransitivity(t1, st, sst)
          } else if (isSubTree(t2, st)) {
            isSubTreeTransitivity(t2, st, sst)
          }
        }
      }
    }
  }.ensuring(_ => isSubTree(t, sst))

  // if st is a subtree of t2 and t1 is the same as t2 then st is---------------
  // a subtree of t1------------------------------------------------------------
  def isSameSubTree(t1: Tree, t2: Tree, st: Tree): Unit = {
    require(isSameTree(t1, t2) && isSubTree(t2, st))

    ()
    //TODO
  }.ensuring(_ => isSubTree(t1, st))

  // prove children of a node are subtrees or the node itself-------------------
  def childrenAreSubTrees(t: InnerNode): Unit = {
    ()
    //TODO
  }.ensuring(_ => t match { case InnerNode(_, t1, t2) => isSubTree(t, t1) && isSubTree(t, t2)})

  // return the weight of a Tree------------------------------------------------
  def cachedWeight(t: Tree): BigInt = t match {
    case InnerNode(w, t1, t2) => w
    case Leaf(w, c) => w
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
  }

  // prove insortTree increases the Forest size by 1----------------------------
  def insortTreeLength(t: Tree, f: Forest): Unit = {
    f match {
      case Nil() => ()
      case hd :: tl if (cachedWeight(t) <= cachedWeight(hd)) => ()
      case hd :: tl => (
        insortTree(t, f).length          ==:| trivial |:
        (hd :: insortTree(t, tl)).length ==:| trivial |:
        1+insortTree(t, tl).length       ==:| insortTreeLength(t, tl) |:
        1+tl.length+1                    ==:| trivial |:
        (hd :: tl).length+1              ==:| trivial |:
        f.length+1
      ).qed
    }
  }.ensuring(_ => insortTree(t, f).length == f.length+1)

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

  // generate Huffman code's Tree given a Forest--------------------------------
  def huffmansAlgorithm(f: Forest): Tree = {
    require(!f.isEmpty)
    decreases(f.length)

    f match {
      case t1 :: t2 :: tl => {
        insortTreeLength(uniteTrees(t1, t2), tl)
        huffmansAlgorithm(insortTree(uniteTrees(t1, t2), tl))
      }
      case t :: _ => t
    }
  }

  // encode/decode--------------------------------------------------------------

  // encode a character as a list of bits with a given tree---------------------
  def encodeChar(t: Tree, c: Char, acc: List[Boolean]): List[Boolean] = {
    t match {
      case Leaf(_, lC) => if (lC == c) acc else Nil()
      case InnerNode(_, t1, t2) => {
        encodeChar(t1, c, acc ++ List(false)) match {
          case Nil() => encodeChar(t2, c, acc ++ List(true))
          case l => l
        }
      }
    }
  }

  // encode a list of chararcters with a given tree recursively-----------------
  def encodeHelper(t: InnerNode, s: List[Char]) : List[Boolean] = {
    s match {
      case Nil() => Nil()
      case hd :: tl => encodeChar(t, hd, Nil()) ++ encodeHelper(t, tl)
    }
  }

  // encode a list of characters as list of bits with a given tree--------------
  def encode(t: InnerNode, s: List[Char]): List[Boolean] = {
    encodeHelper(t, s)
  }
  
  // check if at least one character can be decoded-----------------------------
  def canDecodeAtLeastOneChar(t: InnerNode, bs: List[Boolean]): Boolean = {
    t match { case InnerNode(_, t1, t2) => { bs match {
      case hd :: tl => {
        if (!hd) t1 match {
          case Leaf(_, c) => true
          case tt1@InnerNode(_, _, _) => canDecodeAtLeastOneChar(tt1, tl)
        } else t2 match {
          case Leaf(_, c) => true
          case tt2@InnerNode(_, _, _) => canDecodeAtLeastOneChar(tt2, tl)
        }
      }
      case Nil() => false
    }}}
  }

  // check if the whole list of bits can be correctly decoded-------------------
  def canDecode(s: InnerNode, bs: List[Boolean])(implicit t: InnerNode): Boolean = {
    decreases(bs.length)

    s match { case InnerNode(_, t1, t2) => { bs match {
      case hd :: tl => {
        if (!hd) t1 match {
          case Leaf(_, c) => if (tl.isEmpty) true else canDecode(t, tl)
          case tt1@InnerNode(_, _, _) => canDecode(tt1, tl)
        } else t2 match {
          case Leaf(_, c) => if (tl.isEmpty) true else canDecode(t, tl)
          case tt2@InnerNode(_, _, _) => canDecode(tt2, tl)
        }
      }
      case Nil() => false
    }}}
  }

  // prove that canDecode implies canDecodeAtLeastOneChar-----------------------
  def canDecodeImpliesCanDecodeAtLeastOneChar(s: InnerNode, bs: List[Boolean])(implicit t: InnerNode): Unit = {
    require(canDecode(s, bs)(t) && isSubTree(t, s))
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
  def canDecodeImpliesCanDecodeTailAfterOneCharDecoded(t: InnerNode, bs: List[Boolean]): Unit = {
    require(canDecode(t, bs)(t))

    isSubTreeReflexivity(t)
    canDecodeImpliesCanDecodeAtLeastOneChar(t, bs)(t)

    //TODO
  }.ensuring(_ => decodeChar(t, bs) match { case(_, nBs) => if (nBs.isEmpty) true else canDecode(t, nBs)(t) })

  // decode a single character from a list of bits with a given tree------------
  def decodeChar(t: InnerNode, bs: List[Boolean]): (Char, List[Boolean]) = {
    require(canDecodeAtLeastOneChar(t, bs))
    decreases(bs.length)

    t match { case InnerNode(_, t1, t2) => { bs match {
      case hd :: tl => {
        if (!hd) t1 match {
          case Leaf(_, c) => (c, tl)
          case tt1@InnerNode(_, _, _) => decodeChar(tt1, tl)
        } else t2 match {
          case Leaf(_, c) => (c, tl)
          case tt2@InnerNode(_, _, _) => decodeChar(tt2, tl)
        }
      }
    }}}
  }

  // prove that the length of the remaining list of bits after decoding---------
  // the first decodable character is smaller than the original list of bits----
  def decodeCharLength(t: InnerNode, bs: List[Boolean]): Unit = {
    require(canDecodeAtLeastOneChar(t, bs))

    ()

    //TODO
  }.ensuring(_ => decodeChar(t, bs) match { case (_, nBs) => nBs.length < bs.length })

  // decode a list of bits with a given tree recursively------------------------
  def decodeHelper(t: InnerNode, bs: List[Boolean], acc: List[Char]): List[Char] = {
    require(!bs.isEmpty && canDecode(t, bs)(t))
    decreases(bs.length)

    canDecodeImpliesCanDecodeTailAfterOneCharDecoded(t, bs)
    decodeCharLength(t, bs)

    decodeChar(t, bs) match { case(c, nBs) => if (nBs.isEmpty) acc else decodeHelper(t, nBs, acc ++ List(c)) }
  }

  // decode a list of bits as a list of characters with a given tree------------
  def decode(t: InnerNode, bs: List[Boolean]): List[Char] = {
    require(canDecode(t, bs)(t))
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
  
  // main-----------------------------------------------------------------------
  @extern
  def main(args: Array[String]): Unit = {
 
    def scalaListToStainlessList[T](l: scala.collection.immutable.List[T]): List[T] = l match {
      case scala.collection.immutable.Nil => Nil()
      case scala.collection.immutable.::(x, xs) => Cons(x, scalaListToStainlessList(xs))
    }
 
    def stainlessListToScalaList[T](l: List[T]): scala.collection.immutable.List[T] = l match {
      case Nil()        => scala.collection.immutable.Nil
      case Cons(x, xs)  => scala.collection.immutable.::(x, stainlessListToScalaList(xs))
    }

    def printHuffmanCode(t: Tree): Unit = {
      def printHuffmanCodeHelper(t: Tree, cw: String): Unit = t match {
        case InnerNode(_, t1, t2) => {
          printHuffmanCodeHelper(t2, cw.concat("1"))
          printHuffmanCodeHelper(t1, cw.concat("0"))
        }
        case Leaf(_, c) => {
          println(s"$c : $cw")
        }
      }

      printHuffmanCodeHelper(t, "")
    }

    if (args.size != 1) {
      println("This expects only one String")
      return
    }

    val f: Forest = generateSortedForest(scalaListToStainlessList(args(0).toList))
    val t: Tree = huffmansAlgorithm(f)

    printHuffmanCode(t)
  }
}
