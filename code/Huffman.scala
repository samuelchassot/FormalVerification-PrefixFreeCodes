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

  type Alphabet = Char
  type Forest = List[Tree]
  
  sealed abstract class Tree {
  }

  case class InnerNode(w: Int, t1: Tree, t2: Tree) extends Tree
  case class Leaf(w: Int, c: Alphabet) extends Tree

  def cachedWeight(t: Tree): Int = t match {
    case InnerNode(w, t1, t2) => w
    case Leaf(w, c) => w
  }

  def uniteTrees(t1: Tree, t2: Tree): Tree = InnerNode(cachedWeight(t1) + cachedWeight(t2), t1, t2)

  def insortTree(t: Tree, f: Forest): Forest = f match {
    case Nil() => List(t)
    case Cons(t, ts) => if (cachedWeight(t) <= cachedWeight(t)) t :: t :: ts
                        else t :: insortTree(t, ts)
  }

  def huffmansAlgorithm(f: Forest): Tree = f match {
    case t1 :: t2 :: ts => huffmansAlgorithm(insortTree(uniteTrees(t1, t2), ts))
    case t :: _ => t
  }
}
