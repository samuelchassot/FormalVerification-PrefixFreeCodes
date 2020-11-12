//Proejct Formal verification (CS-550, EPFL)
//
//Samuel Chassot 270955
//Daniel Filipe Nunes Silva 275197

import stainless.collection._
import stainless.lang._
import stainless.annotation._

import stainless.equations._
 
object Huffman {

    def test() = {

    }.ensuring( _ => true)
    
 
}

object  HuffmanTree{
    type Alphabet = Byte
    type Forest = List[HuffmanTree]
    sealed abstract class HuffmanTree {

    }
    case class Leaf(w: Int, c: Alphabet) extends HuffmanTree
    case class InnerNode(w: Int, t1: HuffmanTree, t2: HuffmanTree) extends HuffmanTree

    def cachedWeight(tree: HuffmanTree): Int = tree match {
            case InnerNode(w, t1, t2) => w
            case Leaf(w, c) => w
        }

    def uniteTrees(t1: HuffmanTree, t2: HuffmanTree): HuffmanTree = InnerNode(cachedWeight(t1) + cachedWeight(t2), t1, t2)

    def insortTree(tree: HuffmanTree, forest: Forest): Forest = forest match {
        case Nil() => tree :: Nil()
        case head :: tl => if (cachedWeight(tree) <= cachedWeight(head)) tree :: head :: tl 
                            else head :: insortTree(tree, tl)
    }

    def huffmanAlgorithm(forest: Forest) : HuffmanTree = forest match {
        case t :: Nil() => t
        case t1 :: t2 ::  tl => huffmanAlgorithm(insortTree(uniteTrees(t1, t2), tl))
    }
    
}
