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

  // Huffman's Algorithm--------------------------------------------------------
  type Forest = List[Tree]
  
  sealed abstract class Tree
  case class InnerNode(w: BigInt, t1: Tree, t2: Tree) extends Tree
  case class Leaf(w: BigInt, c: Char) extends Tree

  def cachedWeight(t: Tree): BigInt = t match {
    case InnerNode(w, t1, t2) => w
    case Leaf(w, c) => w
  }

  def uniteTrees(t1: Tree, t2: Tree): Tree = InnerNode(cachedWeight(t1) + cachedWeight(t2), t1, t2)

  def insortTree(t: Tree, f: Forest): Forest = {
    decreases(f.length)
    f match {
      case Nil() => List(t)
      case hd :: tl => if (cachedWeight(t) <= cachedWeight(hd)) t :: f else hd :: insortTree(t, tl)
    }
  }

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

  def huffmansAlgorithm(f: Forest): Tree = {
    require(!f.isEmpty)
    decreases(f.length)

    f match {
      case t1 :: t2 :: tl => {
        insortTreeLength(uniteTrees(t1, t2), tl)
        huffmansAlgorithm(insortTree(uniteTrees(t1, t2), tl))
      }
      case t :: Nil() => t
    }
  }

  // Tokenizer -----------------------------------------------------------------
  sealed abstract class Token
  case class ValidToken(bits: List[Boolean]) extends Token
  case class ElementNotFoundToken() extends Token

  def isValidToken(t: Token): Boolean = t match {
    case ElementNotFoundToken() => false
    case ValidToken(_) => true
  }

  def encodeElement(t: Tree, e: Char, acc: List[Boolean]): Token = t match {
    case Leaf(w, c) => if (c == e) ValidToken(acc) else ElementNotFoundToken()
    case InnerNode(w, t1, t2) => encodeElement(t1, e, acc ++ List(false)) match {
      case ValidToken(bits) => ValidToken(bits)
      case ElementNotFoundToken() => encodeElement(t2, e, acc ++ List(true)) 
    }
  }

  def encode(t: Tree, s: List[Char]): List[Token] = s match {
    case Nil() => Nil()
    case hd :: tl => encodeElement(t, hd, Nil()) :: encode(t, tl)
  }
  
  def decodeElement(t: Tree, token: Token): Option[Char] = {

    def decodeElementHelper(t: Tree, bits: List[Boolean]): Option[Char] = t match {
      case Leaf(w, c) => if (bits.size == 0) Some(c) else None()
      case InnerNode(w, t1, t2) => {
        bits match {
          case Nil() => None()
          case hd :: tl => if (!hd) decodeElementHelper(t1, tl) else decodeElementHelper(t2, tl)
        }
      }
    }
    
    token match {
      case ElementNotFoundToken() => None()
      case ValidToken(bits) => decodeElementHelper(t, bits)
    }
  }
  
  def decode(t: Tree, tokens: List[Token]): Option[List[Char]] = {
    require(tokens.forall(isValidToken))

    tokens match {
      case Nil() => Some(Nil())
      case hd :: tl => decodeElement(t, hd) match {
        case None() => None()
        case Some(elmt) => decode(t, tl) match {
          case Some(value) => Some(elmt :: value)
          case None() => None()
        }
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

    def generateSortedForest(s: String): Forest = {
      scalaListToStainlessList(args(0).toList.groupBy(c => c).map(t => Leaf(t._2.length, t._1)).toList.sortBy(l => cachedWeight(l)))
    }

    def printHuffmanCode(t: Tree): Unit = {
      def printHuffmanCodeHelper(t: Tree, cw: String): Unit = t match {
        case InnerNode(_, t1, t2) => {
          printHuffmanCodeHelper(t1, cw.concat("0"))
          printHuffmanCodeHelper(t2, cw.concat("1"))
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

    val f: Forest = generateSortedForest(args(0))
    val t: Tree = huffmansAlgorithm(f)

    printHuffmanCode(t)
  }
}
