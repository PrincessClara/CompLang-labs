package amyc
package parsing

import scala.util.parsing.combinator.syntactical._
import amyc.utils._
import ast.NominalTreeModule._
import scala.io.Source
import java.io.File

// The parser for Amy
// Absorbs tokens from the Lexer and then uses grammarcomp to generate parse trees.
// Defines two different grammars, a naive one which does not obey operator precedence (for demonstration purposes)
// and an LL1 grammar that implements the true syntax of Amy
object Parser extends Pipeline[List[File], Program] {

  object SmartParser extends StandardTokenParsers {
    lexical.reserved += ("object", "abstract", "class", "case", "extends", "def", "int", "String",
      "Boolean", "Unit", "val", "if", "else", "match", "error", "true", "false")
    lexical.delimiters += ("(", ")", ":", "=", "{", "}", ",", ".", ";", "+", "-", "*", "/", "%", "<", "<=",
      "&&", "||", "==", "++", "=>", "!", "_")

    def program: Parser[Program] = rep(moduleDef) ^^ (Program(_))
    def moduleDef: Parser[ModuleDef] = "object" ~ ident ~ "{" ~ rep(abstractClassDef | caseClassDef | funDef) ~ opt(expr) ~ "}" ^^ {
      case "object" ~ id ~ "(" ~ defs ~ expr ~ ")" => ModuleDef(id, defs, expr)
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
    def expr: Parser[Expr] = ident ^^ (Variable(_)) | literal | expr ~ binOp ~ expr ^^ { case a ~ op ~ b => op(a, b) } |
      "!" ~> expr ^^ (Not(_)) | "-" ~> expr ^^ (Neg(_)) | qName ~ "(" ~ repsep(expr, ",") ~ ")" ^^ { case qn ~ "(" ~ exprs ~ ")" => Call(qn, exprs) } |
      expr ~ ";" ~ expr ^^ { case a ~ ";" ~ b => Sequence(a, b) } | "val" ~ param ~ "=" ~ expr ~ ";" ~ expr ^^ { case "val" ~ par ~ "=" ~ a ~ ";" ~ b => Let(par, a, b) } |
      "if" ~ "(" ~ expr ~ ")" ~ "{" ~ expr ~ "}" ~ "else" ~ "{" ~ expr ~ "}" ^^ {
        case "if" ~ "(" ~ cond ~ ")" ~ "{" ~ thn ~ "}" ~ "else" ~ "{" ~ elze ~ "}" => Ite(cond, thn, elze)
      } | expr ~ "match" ~ "{" ~ rep1(cse) ~ "}" ^^ { case scrut ~ "match" ~ "{" ~ cases ~ "}" => Match(scrut, cases) } |
      "error" ~ "(" ~ expr ~ ")" ^^ { case "error" ~ "(" ~ msg ~ ")" => ast.NominalTreeModule.Error(msg) } |
      "(" ~> expr <~ ")"
    def literal: Parser[Literal[_]] = "true" ^^^ BooleanLiteral(true) | "false" ^^^ BooleanLiteral(false) | "(" ~ ")" ^^^ UnitLiteral() |
      numericLit ^^ { case nb => IntLiteral(nb.toInt) } | stringLit ^^^ StringLiteral(stringLit.toString())
    def binOp: Parser[(Expr, Expr) => Expr] = "+" ^^^ Plus | "-" ^^^ Minus | "*" ^^^ Times | "/" ^^^ Div | "%" ^^^ Mod | "<" ^^^ LessThan |
      "<=" ^^^ LessEquals | "&&" ^^^ And | "||" ^^^ Or | "==" ^^^ Equals | "++" ^^^ Concat
    def cse: Parser[MatchCase] = "case" ~ pattern ~ "=>" ~ expr ^^ { case "case" ~ pat ~ "=>" ~ expr => MatchCase(pat, expr) }
    def pattern: Parser[Pattern] = "_" ^^^ WildcardPattern() | literal ^^ (LiteralPattern(_)) | ident ^^ (IdPattern(_)) |
      qName ~ "(" ~ repsep(pattern, ",") ~ ")" ^^ { case qn ~ "(" ~ patterns ~ ")" => CaseClassPattern(qn, patterns) }

    def run(ctx: Context)(files: List[File]): Program = {
      import ctx.reporter._
      
      val source = files.map(Source.fromFile(_).mkString).reduceLeft((a,b) => a + " " + lexical.EOF.chars + " " + b)
      val input = source.replaceAll("(?:/\\*(?:[^*]|(?:\\*+[^*/]))*\\*+/)|(?://.*)","")

      def printTokens(tokens: lexical.Scanner): Any = tokens match {
        case x if (!x.atEnd) => {
          System.out.println(x.first)
          printTokens(x.rest)
        }
      }
      System.out.println(input)
      val tokens = new lexical.Scanner(input)
      printTokens(tokens)
      phrase(program)(tokens).get
    }

  }

  def run(ctx: Context)(files: List[File]): Program = {
    SmartParser.run(ctx)(files)
  }

}
