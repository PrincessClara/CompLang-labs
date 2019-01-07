package amyc
package parsing

import scala.util.parsing.combinator.syntactical._
import grammarcomp.grammar.CFGrammar._
import grammarcomp.grammar.GrammarDSL._
import grammarcomp.grammar.GrammarUtils.InLL1
import grammarcomp.grammar._
import grammarcomp.parsing._
import amyc.utils._
import ast.NominalTreeModule._
import Tokens._
import java.io.File

object SmartParser extends StandardTokenParsers {
  lexical.reserved += ("object", "abstract", "class", "case", "extends", "def", "int", "String",
    "Boolean", "Unit", "val", "if", "else", "match", "error", "true", "false")
  lexical.delimiters += ("(", ")", ":", "=", "{", "}", ",", ".", ";", "+", "-", "*", "/", "%", "<", "<=",
    "&&", "||", "==", "++", "=>", "!", "_")

  def program: Parser[Program] = rep(moduleDef) ^^ (Program(_))
  def moduleDef: Parser[ModuleDef] = "object" ~ ident ~ "(" ~ rep(abstractClassDef | caseClassDef | funDef) ~ opt(expr) ~ ")" ~ lexical.EOF ^^ {
    case "object" ~ id ~ "(" ~ defs ~ expr ~ ")" ~ eof => ModuleDef(id, defs, expr)
  }
  def abstractClassDef: Parser[AbstractClassDef] = "abstract" ~ "class" ~ ident ^^
    { case "abstract" ~ "class" ~ ident => AbstractClassDef(ident) }
  def caseClassDef: Parser[CaseClassDef] = "case" ~ "class" ~ ident ~ "(" ~ repsep(param, ",") ~ ")" ~ "extends" ~ ident ^^ {
    case "case" ~ "class" ~ id ~ "(" ~ params ~ ")" ~ "extends" ~ mod => CaseClassDef(id, params.map(_.tt), mod) 
  }
  def funDef: Parser[FunDef] = "def" ~ ident ~ "(" ~ repsep(param, ",") ~ ")" ~ ":" ~ tpe ~ "=" ~ "{" ~ expr ~ "}" ^^ {
    case "def" ~ id ~ "(" ~ params ~ ")" ~ ":" ~ tpe ~ "=" ~ "{" ~ expr ~ "}" => FunDef(id, params, tpe, expr)
  }
  def param: Parser[ParamDef] = ident ~ ":" ~ tpe ^^ { case id ~ ":" ~ tpe => ParamDef(id, tpe) }
  def tpe: Parser[TypeTree] = "int" ^^^ TypeTree(IntType) | "String" ^^^ TypeTree(StringType) | "Boolean" ^^^ TypeTree(BooleanType) | 
    "Unit" ^^^ TypeTree(UnitType) | qName ^^ { case qn => TypeTree(ClassType(qn)) }
  def qName: Parser[QualifiedName] = ident ^^ (QualifiedName(None, _)) |
    ident ~ "." ~ ident ^^ { case mod ~ "." ~ id => QualifiedName(Some(mod), id) }
  def expr: Parser[Expr] = ident ^^ (Variable(_)) | literal | expr ~ binOp ~ expr ^^ { case a ~ op ~ b => op(a,b) } | 
    "!" ~> expr ^^ (Not(_)) | "-" ~> expr ^^ (Neg(_)) | qName ~ "(" ~ repsep(expr, ",") ~ ")" ^^ { case qn ~ "(" ~ exprs ~ ")" => Call(qn, exprs) } | 
    expr ~ ";" ~ expr ^^ { case a ~ ";" ~ b => Sequence(a,b) } | "val" ~ param ~ "=" ~ expr ~ ";" ~ expr ^^ { case "val" ~ par ~ "=" ~ a ~ ";" ~ b => Let(par,a,b) } |
    "if" ~ "(" ~ expr ~ ")" ~ "{" ~ expr ~ "}" ~ "else" ~ "{" ~ expr ~ "}" ^^ { 
      case "if" ~ "(" ~ cond ~ ")" ~ "{" ~ thn ~ "}" ~ "else" ~ "{" ~ elze ~ "}" => Ite(cond, thn, elze)
    } | expr ~ "match" ~ "{" ~ rep1(cse) ~ "}" ^^ { case scrut ~ "match" ~ "{" ~ cases ~ "}" => Match(scrut, cases) } |
    // TODO "error" ~ "(" ~ expr ~ ")" ^^ { case "error" ~ "(" ~ msg ~ ")" => Error(msg) } |
    "(" ~> expr <~ ")"
  def literal: Parser[Literal[_]] = "true" ^^^ BooleanLiteral(true) | "false" ^^^ BooleanLiteral(false) | "(" ~ ")" ^^^ UnitLiteral() | 
    numericLit ^^ {case nb => IntLiteral(nb.toInt) } | stringLit ^^^ StringLiteral(stringLit.toString())
  def binOp: Parser[(Expr, Expr) => Expr] = "+" ^^^ Plus | "-" ^^^ Minus | "*" ^^^ Times | "/" ^^^ Div | "%" ^^^ Mod | "<" ^^^ LessThan | 
    "<=" ^^^ LessEquals | "&&" ^^^ And | "||" ^^^ Or | "==" ^^^ Equals | "++" ^^^ Concat
  def cse: Parser[MatchCase] = "case" ~ pattern ~ "=>" ~ expr ^^ { case "case" ~ pat ~ "=>" ~ expr => MatchCase(pat, expr) }
  def pattern: Parser[Pattern] = "_" ^^^ WildcardPattern() | literal ^^ (LiteralPattern(_)) | ident ^^ (IdPattern(_)) | 
    qName ~ "(" ~ repsep(pattern, ",") ~ ")" ^^ { case qn ~ "(" ~ patterns ~ ")" => CaseClassPattern(qn, patterns) }
  
  def run(ctx: Context)(files: List[File]): Program = {
    val input = files.mkString(lexical.EOF.chars)
    val tokens = new lexical.Scanner(input)
    phrase(program)(tokens).get
  }
  
}

// The parser for Amy
// Absorbs tokens from the Lexer and then uses grammarcomp to generate parse trees.
// Defines two different grammars, a naive one which does not obey operator precedence (for demonstration purposes)
// and an LL1 grammar that implements the true syntax of Amy
object Parser extends Pipeline[Stream[Token], Program] {

  /* This grammar does not implement the correct syntax of Amy and is not LL1
   * It is given as an example
   */
  val amyGrammar = Grammar('Program, List[Rules[Token]](
    'Program ::= 'ModuleDefs,
    'ModuleDefs ::= 'ModuleDef ~ 'ModuleDefs | epsilon(),
    'ModuleDef ::= OBJECT() ~ 'Id ~ LBRACE() ~ 'Definitions ~ 'OptExpr ~ RBRACE() ~ EOF(),
    'Definitions ::= 'Definition ~ 'Definitions | epsilon(),
    'Definition ::= 'AbstractClassDef | 'CaseClassDef | 'FunDef,
    'AbstractClassDef ::= ABSTRACT() ~ CLASS() ~ 'Id,
    'CaseClassDef ::= CASE() ~ CLASS() ~ 'Id ~ LPAREN() ~ 'Params ~ RPAREN() ~ EXTENDS() ~ 'Id,
    'FunDef ::= DEF() ~ 'Id ~ LPAREN() ~ 'Params ~ RPAREN() ~ COLON() ~ 'Type ~ EQSIGN() ~ LBRACE() ~ 'Expr ~ RBRACE(),
    'Params ::= epsilon() | 'Param ~ 'ParamList,
    'ParamList ::= epsilon() | COMMA() ~ 'Param ~ 'ParamList,
    'Param ::= 'Id ~ COLON() ~ 'Type,
    'OptExpr ::= 'Expr | epsilon(),
    'Type ::= INT() | STRING() | BOOLEAN() | UNIT() | 'QName,
    'QName ::= 'Id | 'Id ~ DOT() ~ 'Id,
    'Expr ::= 'Id | 'Literal | 'Expr ~ 'BinOp ~ 'Expr | BANG() ~ 'Expr | MINUS() ~ 'Expr |
      'QName ~ LPAREN() ~ 'Args ~ RPAREN() | 'Expr ~ SEMICOLON() ~ 'Expr |
      VAL() ~ 'Param ~ EQSIGN() ~ 'Expr ~ SEMICOLON() ~ 'Expr |
      IF() ~ LPAREN() ~ 'Expr ~ RPAREN() ~ LBRACE() ~ 'Expr ~ RBRACE() ~ ELSE() ~ LBRACE() ~ 'Expr ~ RBRACE() |
      'Expr ~ MATCH() ~ LBRACE() ~ 'Cases ~ RBRACE() |
      ERROR() ~ LPAREN() ~ 'Expr ~ RPAREN() |
      LPAREN() ~ 'Expr ~ RPAREN(),
    'Literal ::= TRUE() | FALSE() | LPAREN() ~ RPAREN() | INTLITSENT | STRINGLITSENT,
    'BinOp ::= PLUS() | MINUS() | TIMES() | DIV() | MOD() | LESSTHAN() | LESSEQUALS() |
      AND() | OR() | EQUALS() | CONCAT(),
    'Cases ::= 'Case | 'Case ~ 'Cases,
    'Case ::= CASE() ~ 'Pattern ~ RARROW() ~ 'Expr,
    'Pattern ::= UNDERSCORE() | 'Literal | 'Id | 'QName ~ LPAREN() ~ 'Patterns ~ RPAREN(),
    'Patterns ::= epsilon() | 'Pattern ~ 'PatternList,
    'PatternList ::= epsilon() | COMMA() ~ 'Pattern ~ 'PatternList,
    'Args ::= epsilon() | 'Expr ~ 'ExprList,
    'ExprList ::= epsilon() | COMMA() ~ 'Expr ~ 'ExprList,
    'Id ::= IDSENT))

  // TODO: Write a grammar that implements the correct syntax of Amy and is LL1.
  // You can start from the example above and work your way from there.
  // Make sure you use the warning (see `run` below) that tells you which part is not in LL1.
  lazy val amyGrammarLL1 = Grammar('Program, List[Rules[Token]](
    'Program ::= 'ModuleDefs,
    'ModuleDefs ::= 'ModuleDef ~ 'ModuleDefs | epsilon(),
    'ModuleDef ::= OBJECT() ~ 'Id ~ LBRACE() ~ 'Definitions ~ 'OptExpr ~ RBRACE() ~ EOF(),
    'Definitions ::= 'Definition ~ 'Definitions | epsilon(),
    'Definition ::= 'AbstractClassDef | 'CaseClassDef | 'FunDef,
    'AbstractClassDef ::= ABSTRACT() ~ CLASS() ~ 'Id,
    'CaseClassDef ::= CASE() ~ CLASS() ~ 'Id ~ LPAREN() ~ 'Params ~ RPAREN() ~ EXTENDS() ~ 'Id,
    'FunDef ::= DEF() ~ 'Id ~ LPAREN() ~ 'Params ~ RPAREN() ~ COLON() ~ 'Type ~ EQSIGN() ~ LBRACE() ~ 'Expr ~ RBRACE(),
    'Params ::= epsilon() | 'Param ~ 'ParamList,
    'ParamList ::= epsilon() | COMMA() ~ 'Param ~ 'ParamList,
    'Param ::= 'Id ~ COLON() ~ 'Type,
    'OptExpr ::= 'Expr | epsilon(),
    'Type ::= INT() | STRING() | BOOLEAN() | UNIT() | 'QName,
    'QName ::= 'Id ~ 'QName1,
    'QName1 ::= epsilon() | DOT() ~ 'Id,
    'Expr ::= VAL() ~ 'Param ~ EQSIGN() ~ 'Expr1 ~ SEMICOLON() ~ 'Expr | 'Expr1 ~ 'Expr2,
    'Expr1 ::= 'Op1 ~ 'ExprMatch,
    'ExprMatch ::= epsilon() | MATCH() ~ LBRACE() ~ 'Cases ~ RBRACE(),
    'Expr2 ::= epsilon() | SEMICOLON() ~ 'Expr,
    'Op1 ::= 'Op2 ~ 'Op1Seq,
    'Op1Seq ::= epsilon() | OR() ~ 'Op1,
    'Op2 ::= 'Op3 ~ 'Op2Seq,
    'Op2Seq ::= epsilon() | AND() ~ 'Op2,
    'Op3 ::= 'Op4 ~ 'Op3Seq,
    'Op3Seq ::= epsilon() | EQUALS() ~ 'Op3,
    'Op4 ::= 'Op5 ~ 'Op4Seq,
    'Op4Seq ::= epsilon() | LESSTHAN() ~ 'Op4 | LESSEQUALS() ~ 'Op4,
    'Op5 ::= 'Op6 ~ 'Op5Seq,
    'Op5Seq ::= epsilon() | PLUS() ~ 'Op5 | MINUS() ~ 'Op5 | CONCAT() ~ 'Op5,
    'Op6 ::= 'Unary ~ 'Op6Seq,
    'Op6Seq ::= epsilon() | TIMES() ~ 'Op6 | DIV() ~ 'Op6 | MOD() ~ 'Op6,
    'Unary ::= BANG() ~ 'Priority | MINUS() ~ 'Priority | 'Priority,
    'Priority ::= 'Literal | IF() ~ LPAREN() ~ 'Expr ~ RPAREN() ~ LBRACE() ~ 'Expr ~ RBRACE() ~ ELSE() ~ LBRACE() ~ 'Expr ~ RBRACE() |
      ERROR() ~ LPAREN() ~ 'Expr ~ RPAREN() | LPAREN() ~ 'PriorityParen | 'Id ~ 'PriorityId,
    'PriorityParen ::= RPAREN() | 'Expr ~ RPAREN(),
    'PriorityId ::= 'QName1 ~ LPAREN() ~ 'Args ~ RPAREN() | epsilon(),
    'Literal ::= TRUE() | FALSE() | INTLITSENT | STRINGLITSENT,
    'BinOp ::= PLUS() | MINUS() | TIMES() | DIV() | MOD() | LESSTHAN() | LESSEQUALS() |
      AND() | OR() | EQUALS() | CONCAT(),
    'Cases ::= 'Case ~ 'Cases1,
    'Cases1 ::= epsilon() | 'Cases,
    'Case ::= CASE() ~ 'Pattern ~ RARROW() ~ 'Expr,
    'Pattern ::= UNDERSCORE() | 'Literal | LPAREN() ~ RPAREN() | 'Id ~ 'PatternId,
    'PatternId ::= epsilon() | DOT() ~ 'Id ~ LPAREN() ~ 'Patterns ~ RPAREN() | LPAREN() ~ 'Patterns ~ RPAREN(),
    'Patterns ::= epsilon() | 'Pattern ~ 'PatternList,
    'PatternList ::= epsilon() | COMMA() ~ 'Pattern ~ 'PatternList,
    'Args ::= epsilon() | 'Expr ~ 'ExprList,
    'ExprList ::= epsilon() | COMMA() ~ 'Expr ~ 'ExprList,
    'Id ::= IDSENT))

  def run(ctx: Context)(tokens: Stream[Token]): Program = {
    // TODO: Switch to LL1 when you are ready
    val (grammar, constructor) = (amyGrammarLL1, new ASTConstructorLL1)
    // val (grammar, constructor) = (amyGrammar, new ASTConstructor)

    import ctx.reporter._
    implicit val gc = new GlobalContext()
    implicit val pc = new ParseContext()

    GrammarUtils.isLL1WithFeedback(grammar) match {
      case InLL1() =>
      // info("Grammar is in LL1")
      case other =>
        warning(other)
    }

    val feedback = ParseTreeUtils.parseWithTrees(grammar, tokens.toList)
    feedback match {
      case s: Success[Token] =>
        constructor.constructProgram(s.parseTrees.head)
      case err @ LL1Error(_, Some(tok)) =>
        fatal(s"Parsing failed: $err", tok.obj.position)
      case err =>
        fatal(s"Parsing failed: $err")
    }
  }

}
