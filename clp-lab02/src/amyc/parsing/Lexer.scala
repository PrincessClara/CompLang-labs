package amyc
package parsing

import utils._
import scala.io.Source
import java.io.File

// The lexer for Amy.
// Transforms an iterator coming from scala.io.Source to a stream of (Char, Position),
// then uses a functional approach to consume the stream.
object Lexer extends Pipeline[List[File], Stream[Token]] {
  import Tokens._

  /** Maps a string s to the corresponding keyword,
    * or None if it corresponds to no keyword
    */
  private def keywords(s: String): Option[Token] = s match {
    case "abstract" => Some(ABSTRACT())
    case "Boolean"  => Some(BOOLEAN())
    case "case"     => Some(CASE())
    case "class"    => Some(CLASS())
    case "def"      => Some(DEF())
    case "else"     => Some(ELSE())
    case "error"    => Some(ERROR())
    case "extends"  => Some(EXTENDS())
    case "false"    => Some(FALSE())
    case "if"       => Some(IF())
    case "Int"      => Some(INT())
    case "match"    => Some(MATCH())
    case "object"   => Some(OBJECT())
    case "String"   => Some(STRING())
    case "true"     => Some(TRUE())
    case "Unit"     => Some(UNIT())
    case "val"      => Some(VAL())
    case _          => None
  }

  private def lexFile(ctx: Context)(f: File): Stream[Token] = {
    import ctx.reporter._

    // Special character which represents the end of an input file
    val EndOfFile: Char = scala.Char.MaxValue

    val source = Source.fromFile(f)

    // Useful type alias:
    // The input to the lexer will be a stream of characters,
    // along with their positions in the files
    type Input = (Char, Position)

    def mkPos(i: Int) = Position.fromFile(f, i)

    // The input to the lexer
    val inputStream: Stream[Input] =
      source.toStream.map(c => (c, mkPos(source.pos))) #::: Stream((EndOfFile, mkPos(source.pos)))

    /** Gets rid of whitespaces and comments and calls readToken to get the next token.
      * Returns the first token and the remaining input that did not get consumed
      */
    @scala.annotation.tailrec
    def nextToken(stream: Stream[Input]): (Token, Stream[Input]) = {
      require(stream.nonEmpty)

      val (currentChar, currentPos) #:: rest = stream

      // Use with care!
      def nextChar = rest.head._1

      if (Character.isWhitespace(currentChar)) {
        nextToken(stream.dropWhile{ case (c, _) => Character.isWhitespace(c) } )
      } else if (currentChar == '/' && nextChar == '/') {
        // Single-line comment
        nextToken(stream.dropWhile{ case (c, _) => c != '\n' && c != '\r' && c != EndOfFile} )
      } else if (currentChar == '/' && nextChar == '*') {
        // Multi-line comment
        @scala.annotation.tailrec
        def dropComment(stream1: Stream[Input]): Stream[Input] = {
          val (c1, p) #:: rest1 = stream1.dropWhile{ case (c, _) => c != '*' && c != EndOfFile }
          if (rest1.head._1 == '/') rest1
          else dropComment(rest1)
        }
        nextToken(dropComment(rest))
      } else {
        readToken(stream)
      }
    }

    /** Reads the next token from the stream. Assumes no whitespace or comments at the beginning.
      * Returns the first token and the remaining input that did not get consumed.
      */
    def readToken(stream: Stream[Input]): (Token, Stream[Input]) = {
      require(stream.nonEmpty)

      val (currentChar, currentPos) #:: rest = stream

      // Use with care!
      def nextChar = rest.head._1

      // Returns input token with correct position and uses up one character of the stream
      def useOne(t: Token) = (t.setPos(currentPos), rest)
      // Returns input token with correct position and uses up two characters of the stream
      def useTwo(t: Token) = (t.setPos(currentPos), rest.tail)

      currentChar match {
        case `EndOfFile` => useOne(EOF())

        // Reserved word or Identifier
        case _ if Character.isLetter(currentChar) =>
          val (wordLetters, afterWord) = stream.span { case (ch, _) =>
            Character.isLetterOrDigit(ch) || ch == '_'
          }
          val word = wordLetters.map(_._1).mkString
          // Hint: Decide if it's a letter or reserved word (use our infrastructure!),
          // and return the correct token, along with the remaining input stream.
          // Make sure you set the correct position for the token.
          val token = keywords(word)
          if (token == None) (ID(word).setPos(currentPos), afterWord)
          else (token.get.setPos(currentPos), afterWord)

        // Int literal
        case _ if Character.isDigit(currentChar) =>
          // Hint: Use a strategy similar to the previous example.
          // Make sure you fail for integers that do not fit 32 bits.
          val (digits, afterNumber) = stream.span { case (ch, _) =>
            Character.isDigit(ch)
          }
          val numberString = digits.map(_._1).mkString
          
          val number: BigInt = BigInt(numberString)
          if (number.isValidInt) (INTLIT(number.toInt).setPos(currentPos), afterNumber)
          else {
            error("Integer value is too big (overflow)", currentPos)
            (BAD().setPos(currentPos), afterNumber)
          }

        // String literal
        case '"' =>
          val (stringLetters, afterString) = rest.span { case (ch, _) =>
            ch != '"'
          }
          val strLiteral = stringLetters.map(_._1).mkString
          
          (STRINGLIT(strLiteral).setPos(currentPos), afterString.tail)
          
        case ';' =>
          useOne(SEMICOLON())
        case '+' if nextChar == '+' =>
          useTwo(CONCAT())
        case '+' =>
          useOne(PLUS())
        case '-' =>
          useOne(MINUS())
        case '*' =>
          useOne(TIMES())
        case '/' =>
          useOne(DIV())
        case '%' =>
          useOne(MOD())
        case '<' if nextChar == '=' =>
          useTwo(LESSEQUALS())
        case '<' =>
          useOne(LESSTHAN())
        case '&' if nextChar == '&' =>
          useTwo(AND())
        case '|' if nextChar == '|' =>
          useTwo(OR())
        case '=' if nextChar == '=' =>
          useTwo(EQUALS())
        case '=' if nextChar == '>' =>
          useTwo(RARROW())
        case '=' =>
          useOne(EQSIGN())
        case '!' =>
          useOne(BANG())
        case '{' =>
          useOne(LBRACE())
        case '}' =>
          useOne(RBRACE())
        case '(' =>
          useOne(LPAREN())
        case ')' =>
          useOne(RPAREN())
        case ',' =>
          useOne(COMMA())
        case ':' =>
          useOne(COLON())
        case '.' =>
          useOne(DOT())
        case '_' =>
          useOne(UNDERSCORE())

        case _ =>
          error("Invalid token", currentPos)
          (BAD().setPos(currentPos), rest)
      }
    }

    // To lex a file, call nextToken() until it returns the empty Stream as "rest"
    def tokenStream(s: Stream[Input]): Stream[Token] = {
      if (s.isEmpty) Stream()
      else {
        val (token, rest) = nextToken(s)
        token #:: tokenStream(rest)
      }
    }

    tokenStream(inputStream)
  }

  // Lexing all input files means putting the tokens from each file one after the other
  def run(ctx: Context)(files: List[File]): Stream[Token] = {
    files.toStream flatMap lexFile(ctx)
  }
}

/** Extracts all tokens from input and displays them */
object DisplayTokens extends Pipeline[Stream[Token], Unit] {
  def run(ctx: Context)(tokens: Stream[Token]): Unit = {
    tokens.toList foreach { t => println(s"$t(${t.position.withoutFile})") }
  }
}
