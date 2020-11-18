// Personal final Project
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

  // return the weight of a tree------------------------------------------------
  def cachedWeight(t: Tree): BigInt = t match {
    case InnerNode(w, t1, t2) => w
    case Leaf(w, c) => w
  }

  // merge two trees in one by adding an innernode------------------------------
  def uniteTrees(t1: Tree, t2: Tree): Tree = InnerNode(cachedWeight(t1) + cachedWeight(t2), t1, t2)

  // insert a tree in a forest and sort the latter------------------------------
  def insortTree(t: Tree, f: Forest): Forest = {
    decreases(f.length)
    f match {
      case Nil() => List(t)
      case hd :: tl => if (cachedWeight(t) <= cachedWeight(hd)) t :: f else hd :: insortTree(t, tl)
    }
  }

  // prove insortTree increases the forest size by 1----------------------------
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

  // generate the forest of leaves for a given list of characters---------------
  def generateUnsortedForest(s: List[Char]): Forest = {
    s.foldLeft[List[Char]](Nil())((l, c) => if (l.contains(c)) l else (c :: l)).map(c => Leaf(s.count(_ == c), c))
  }

  // sort a forest--------------------------------------------------------------
  def sortForest(f: Forest): Forest = f match {
      case Nil() => Nil()
      case hd :: tl => insortTree(hd, sortForest(tl))
  }

  // generate and sort a forest given a list of characters----------------------
  def generateSortedForest(s: List[Char]): Forest = {
    sortForest(generateUnsortedForest(s))
  }

  // generate Huffman code's tree given a forest--------------------------------
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

  // Tokenizer------------------------------------------------------------------

  // datatypes------------------------------------------------------------------
  sealed abstract class Token
  case class ValidToken(bits: List[Boolean]) extends Token
  case class ElementNotFoundToken() extends Token

  // return true iff a token is valid-------------------------------------------
  def isValidToken(t: Token): Boolean = t match {
    case ElementNotFoundToken() => false
    case ValidToken(_) => true
  }

  // to complete----------------------------------------------------------------
  def encodeElement(t: Tree, e: Char, acc: List[Boolean]): Token = t match {
    case Leaf(w, c) => if (c == e) ValidToken(acc) else ElementNotFoundToken()
    case InnerNode(w, t1, t2) => encodeElement(t1, e, acc ++ List(false)) match {
      case ValidToken(bits) => ValidToken(bits)
      case ElementNotFoundToken() => encodeElement(t2, e, acc ++ List(true)) 
    }
  }

  // to complete----------------------------------------------------------------
  def encodeHelper(t: Tree, s: List[Char]) : List[Token] = s match {
    case Nil() => Nil()
    case hd :: tl => encodeElement(t, hd, Nil()) :: encodeHelper(t, tl)
  }

  // to complete----------------------------------------------------------------
  def encode(s: List[Char]): (Tree, List[Token]) = {
    val t = huffmansAlgorithm(generateSortedForest(s))
    (t, encodeHelper(t, s))
  }
  
  // to complete----------------------------------------------------------------
  def decodeOneChar(t: Tree, bs: List[Boolean]): (Char, List[Boolean]) = {
    t match {
      case Leaf(_, c) => (c, bs)
      case InnerNode(_, t1, t2) => bs match {
        case hd :: tl => if (!hd) decodeOneChar(t1, tl) else decodeOneChar(t2, tl)
      }
    }
  }

  def decodeHelper(t: Tree, bs: List[Boolean], acc: List[Char]): List[Char] = {
    bs match {
      case Nil() => acc
      case _ => {
        val (c, nBs) = decodeOneChar(t, bs)
        decodeHelper(t, nBs, c :: acc)
      }
    }
  }

  def decode(t: Tree, bs: List[Boolean]): List[Char] = {
    decodeHelper(t, bs, Nil()).reverse
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
