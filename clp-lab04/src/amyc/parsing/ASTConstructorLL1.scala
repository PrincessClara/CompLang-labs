package amyc
package parsing

import grammarcomp.parsing._
import utils.Positioned
import ast.NominalTreeModule._
import Tokens._

import amyc.ast.NominalTreeModule

// Implements the translation from parse trees to ASTs for the LL1 grammar,
// that is, this should correspond to Parser.amyGrammarLL1.
// We extend the plain ASTConstructor as some things will be the same -- you should
// override whatever has changed. You can look into ASTConstructor as an example.
class ASTConstructorLL1 extends ASTConstructor {

  
  override def constructQname(pTree: NodeOrLeaf[Token]): (QualifiedName, Positioned) = {
    pTree match {
      case Node('QName ::= _, List(id, qname1)) =>
        constructQname1(id, qname1)
    }
  }
  
  def constructQname1(id: NodeOrLeaf[Token], pTree: NodeOrLeaf[Token]): (QualifiedName, Positioned) = {
    pTree match {
      case Node('Qname1 ::= _, List(_, nm)) =>
        val (mod, pos) = constructName(id)
        (QualifiedName(Some(mod), constructName(nm)._1), pos)
      case Node('QName1 ::= _, List()) =>
        val (nm, pos) = constructName(id)
        (QualifiedName(None, nm), pos)
    }
  }
  
  override def constructExpr(ptree: NodeOrLeaf[Token]): NominalTreeModule.Expr = {
    ptree match {
      case Node('Expr ::= (VAL() :: _), List(Leaf(v), param, _, value, _, body)) =>
        Let(constructParam(param), constructExpr(value), constructExpr(body)).setPos(v)
      case Node('Expr ::= List('Expr1, _), List(mtch, expr2)) =>
        constructExprMatch(mtch, expr2)
      case Node('Expr1 ::= _, List(op1, mtch)) =>
        constructMatch(op1, mtch)
      case Node('Op1 ::= _, List(op, opSeq)) =>
        constructOpExpr(constructExpr(op), opSeq)
      case Node('Op2 ::= _, List(op, opSeq)) =>
        constructOpExpr(constructExpr(op), opSeq)
      case Node('Op3 ::= _, List(op, opSeq)) =>
        constructOpExpr(constructExpr(op), opSeq)
      case Node('Op4 ::= _, List(op, opSeq)) =>
        constructOpExpr(constructExpr(op), opSeq)
      case Node('Op5 ::= _, List(op, opSeq)) =>
        constructOpExpr(constructExpr(op), opSeq)
      case Node('Op6 ::= _, List(op, opSeq)) =>
        constructOpExpr(constructExpr(op), opSeq)
      case Node('Unary ::= (BANG() :: _), List(Leaf(p), priority)) =>
        Not(constructExpr(priority)).setPos(p)
      case Node('Unary ::= (MINUS() :: _), List(Leaf(p), priority)) =>
        Neg(constructExpr(priority)).setPos(p)
      case Node('Unary ::= ('TopPrio :: _), List(priority)) =>
        constructExpr(priority)
      case Node('Priority ::= List('Literal), List(lit)) =>
        constructLiteral(lit)
      case Node('Priority ::= (IF() :: _), List(Leaf(t), _, cond, _, _, thn, _, _, _, els, _)) =>
        Ite(
          constructExpr(cond),
          constructExpr(thn),
          constructExpr(els)
        ).setPos(t)
      case Node('Priority ::= (ERROR() :: _), List(Leaf(t), _, msg, _)) =>
        Error(constructExpr(msg)).setPos(t)
      case Node('Priority ::= List(LPAREN() :: _), List(par, rest)) =>
        constructPriorityParen(par, rest)
      case Node('Priority ::= ('Id :: _), List(id, rest)) =>
        constructPriorityId(id, rest)
    }
  }
  
  def constructExprMatch(mtch: NodeOrLeaf[Token], expr2: NodeOrLeaf[Token]): NominalTreeModule.Expr = {
    expr2 match {
      case Node('Expr2 ::= _, List()) => constructExpr(mtch)
      case Node('Expr2 ::= _, List(_, exprAfterSemicolon)) =>
        val e1 = constructExpr(mtch)
        val e2 = constructExpr(exprAfterSemicolon)
        Sequence(e1, e2).setPos(e1)
    }
  }
  
  def constructMatch(op: NodeOrLeaf[Token], mtch: NodeOrLeaf[Token]): NominalTreeModule.Expr = {
    mtch match {
      case Node('ExprMatch ::= _, List()) => constructExpr(op)
      case Node('ExprMatch ::= _, List(_, _, cases, _)) =>
        val expr = constructExpr(op)
        Match(expr, constructCases(cases)).setPos(expr)
    }
  }
  
  def constructCases(cases: NodeOrLeaf[Token]): List[NominalTreeModule.MatchCase] = {
    cases match {
      case Node('Cases ::= _, List(c, others)) =>
        val caseOpt = constructOption(others, constructCases)
        if(caseOpt.isEmpty) List(constructCase(c))
        else constructCase(c) :: caseOpt.get
    }
  }
  
  override def constructLiteral(pTree: NodeOrLeaf[Token]): Literal[_] = {
    pTree match {
      case Node('Literal ::= List(INTLITSENT), List(Leaf(it@INTLIT(i)))) =>
        IntLiteral(i).setPos(it)
      case Node('Literal ::= List(STRINGLITSENT), List(Leaf(st@STRINGLIT(s)))) =>
        StringLiteral(s).setPos(st)
      case Node('Literal ::= _, List(Leaf(tt@TRUE()))) =>
        BooleanLiteral(true).setPos(tt)
      case Node('Literal ::= _, List(Leaf(tf@FALSE()))) =>
        BooleanLiteral(false).setPos(tf)
    }
  }
  
  def constructPriorityParen(par: NodeOrLeaf[Token], rest: NodeOrLeaf[Token]): NominalTreeModule.Expr = {
    (par, rest) match {
      case (Leaf(t), Node('PriorityParen ::= (RPAREN() :: Nil),  _)) =>
        UnitLiteral().setPos(t)
      case (Leaf(t), Node('PriorityParen ::= ('Expr :: _), List(expr))) =>
        constructExpr(expr).setPos(t)
    }
  }
  
  def constructPriorityId(id: NodeOrLeaf[Token], rest: NodeOrLeaf[Token]): NominalTreeModule.Expr = {
    rest match {
      case Node('PriorityId ::= _, List()) =>
        val (nm, pos) = constructName(id)

        Variable(nm).setPos(pos)
      case Node('PriorityId ::= ('QName1 :: _), List(qname1, _, args, _)) =>
        val (nm, pos) = constructQname1(id, qname1)
        val argsEval = constructList(args, constructExpr, hasComma = true)

        Call(nm, argsEval).setPos(pos)
    }
  }
  
  override def constructPattern(pTree: NodeOrLeaf[Token]): NominalTreeModule.Pattern = {
    pTree match {
      case Node('Pattern ::= List(UNDERSCORE()), List(Leaf(ut))) =>
        WildcardPattern().setPos(ut)
      case Node('Pattern ::= List('Literal), List(lit)) =>
        val literal = constructLiteral(lit)
        LiteralPattern(literal).setPos(literal)
      case Node('Pattern ::= _, List(Leaf(lp@LPAREN()), Leaf(RPAREN()))) =>
        val literal = UnitLiteral().setPos(lp)
        LiteralPattern(literal).setPos(literal)
      case Node('Pattern ::= ('Id :: _), List(id, rest)) =>
        constructPatternId(id, rest)
    }
  }

  def constructPatternId(id: NodeOrLeaf[Token], rest: NodeOrLeaf[Token]): NominalTreeModule.Pattern = {
    rest match {
      case Node('PatternId ::= _, List(qname1, _, ps, _)) =>
        val (nm, pos) = constructQname1(id, qname1)
        val patterns = constructList(ps, constructPattern, hasComma = true)
        CaseClassPattern(nm, patterns).setPos(pos)
      case Node('PatternId ::= _, List()) =>
        val (nm, pos) = constructName(id)
        IdPattern(nm).setPos(pos)
    }
  }

  // Important helper method:
  // Because LL1 grammar is not helpful in implementing left associativity,
  // we give you this method to reconstruct it.
  // This method takes the left operand of an operator (leftopd)
  // as well as the tree that corresponds to the operator plus the right operand (ptree)
  // It parses the right hand side and then reconstruct the operator expression
  // with correct associativity.
  // If ptree is empty, it means we have no more operators and the leftopd is returned.
  // Note: You may have to override constructOp also, depending on your implementation
  def constructOpExpr(leftopd: Expr, ptree: NodeOrLeaf[Token]): Expr = {
    ptree match {
      case Node(_, List()) => //epsilon rule of the nonterminals
        leftopd
      case Node(sym ::= _, List(Leaf(op), rightNode))
        if Set('Op1Seq, 'Op2Seq, 'Op3Seq, 'Op4Seq, 'Op5Seq, 'Op6Seq) contains sym =>
        rightNode match {
          case Node(_, List(nextOpd, suf)) => // 'Expr? ::= Expr? ~ 'OpExpr,
            val nextAtom = constructExpr(nextOpd)
            constructOpExpr(tokenToExpr(op)(leftopd, nextAtom).setPos(leftopd), suf) // captures left associativity
        }
    }
  }

}

