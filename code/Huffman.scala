//Project Formal verification (CS-550, EPFL)
//
//Samuel Chassot 270955
//Daniel Filipe Nunes Silva 275197

import stainless.collection._
import stainless.lang._
import stainless.annotation._
import stainless.equations._
import stainless.proof.check

object HuffmanCode {

  // Tree -----------------------------------------------------------

  type Alphabet = Char
  type Forest = List[Tree]
  
  sealed abstract class Tree {
  }

  case class InnerNode(w: BigInt, t1: Tree, t2: Tree) extends Tree
  case class Leaf(w: BigInt, c: Alphabet) extends Tree

  def cachedWeight(t: Tree): BigInt = t match {
    case InnerNode(w, t1, t2) => w
    case Leaf(w, c) => w
  }

  def uniteTrees(t1: Tree, t2: Tree): Tree = InnerNode(cachedWeight(t1) + cachedWeight(t2), t1, t2)

  def insortTree(t: Tree, f: Forest): Forest = f match {
    case Nil() => List(t)
    case head :: tail => if (cachedWeight(t) <= cachedWeight(head)) t :: f else head :: insortTree(t, tail)
  }

  def huffmansAlgorithm(f: Forest): Tree = f match {
    case t1 :: t2 :: ts => huffmansAlgorithm(insortTree(uniteTrees(t1, t2), ts))
    case t :: _ => t
  }

  // ------------------------------------------------------------------
  // Token ------------------------------------------------------------

  sealed abstract class Token

  case class ValidToken(bits: List[Boolean]) extends Token
  case class ElementNotFoundToken() extends Token

  def isValidToken(t: Token): Boolean = t match {
    case ElementNotFoundToken() => false
    case ValidToken(_) => true
  }

  def encodeElement(t: Tree, elmt: Alphabet, acc: List[Boolean]): Token = t match {
    case Leaf(w, c) => if (c == elmt) ValidToken(acc) else ElementNotFoundToken()
    case InnerNode(w, t1, t2) => encodeElement(t1, elmt, acc ++ List(false)) match {
      case ValidToken(bits) => ValidToken(bits)
      case ElementNotFoundToken() => encodeElement(t2, elmt, acc ++ List(true)) 
    }
  }
  def encode(t: Tree, content: List[Alphabet]): List[Token] = content match {
    case Nil() => Nil()
    case head :: tl => encodeElement(t, head, Nil()) :: encode(t, tl)
  }
  
  def decodeElement(t: Tree, token: Token): Option[Alphabet] = {
    
    def decodeElementHelper(t: Tree, bits: List[Boolean]): Option[Alphabet] = t match {
      case Leaf(w, c) => if(bits.size == 0) Some(c) else None()
      case InnerNode(w, t1, t2) => {
        bits match {
          case Nil() => None()
          case head :: tl => if(!head) decodeElementHelper(t1, tl) else decodeElementHelper(t2, tl)
        }
      }
    }
    token match {
      case ElementNotFoundToken() => None()
      case ValidToken(bits) => decodeElementHelper(t, bits)
    }
    
  }
  
  def decode(t: Tree, tokens: List[Token]): Option[List[Alphabet]] = {
    require(isValidListOfTokens(tokens))
    tokens match {
      case Nil() => Some(Nil())
      case head :: tl => decodeElement(t, head) match {
        case Some(elmt) => decode(t, tl) match {
          case Some(value) => Some(elmt :: value)
          case None() => None()
        }
        case None() => None()
      } 
    }
}

  def isValidListOfTokens(l: List[Token]): Boolean = {
    l.forall(isValidToken)
  }
  
 // Token ------------------------------------------------------------
  @extern
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
 
  @extern
  def main(args: Array[String]): Unit = {
    printHuffmanCode(huffmansAlgorithm(List(Leaf(1, 'a'), Leaf(3, 'b'), Leaf(4, 'c'), Leaf(12, 'd'))))
  }
}
