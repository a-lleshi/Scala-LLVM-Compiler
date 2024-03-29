// A tokeniser (Lexer) for the Fun language by Abdurrahman Lleshi
//==================================
//
// call with 
//
//     amm fun_tokens.sc fact.fun
//     amm fun_tokens.sc defs.fun
//     amm fun_tokens.sc hanoi.fun
//     amm fun_tokens.sc mand.fun
//     amm fun_tokens.sc mand2.fun
//     amm fun_tokens.sc sqr.fun



import scala.language.implicitConversions    
import scala.language.reflectiveCalls 

abstract class Rexp 
case object ZERO extends Rexp
case object ONE extends Rexp
case class CHAR(c: Char) extends Rexp
case class ALT(r1: Rexp, r2: Rexp) extends Rexp 
case class SEQ(r1: Rexp, r2: Rexp) extends Rexp 
case class STAR(r: Rexp) extends Rexp 
case class RECD(x: String, r: Rexp) extends Rexp
case class RANGE(cs: Set[Char]) extends Rexp // A set of characters - for ranges e.g. [c1,c2,...,cn]
case class PLUS(r: Rexp) extends Rexp // One or more repetitions of r
case class OPTIONAL(r: Rexp) extends Rexp // Optional r
case class NTIMES(r: Rexp, n: Int) extends Rexp // Exactly n-times
  
abstract class Val
case object Empty extends Val
case class Chr(c: Char) extends Val
case class Sequ(v1: Val, v2: Val) extends Val
case class Left(v: Val) extends Val
case class Right(v: Val) extends Val
case class Stars(vs: List[Val]) extends Val
case class Rec(x: String, v: Val) extends Val
case class Opt(v: Val) extends Val

   
// some convenience for typing in regular expressions
def charlist2rexp(s : List[Char]): Rexp = s match {
  case Nil => ONE
  case c::Nil => CHAR(c)
  case c::s => SEQ(CHAR(c), charlist2rexp(s))
}
implicit def string2rexp(s : String) : Rexp = 
  charlist2rexp(s.toList)

implicit def RexpOps(r: Rexp) = new {
  def | (s: Rexp) = ALT(r, s)
  def % = STAR(r)
  def ~ (s: Rexp) = SEQ(r, s)
}

implicit def stringOps(s: String) = new {
  def | (r: Rexp) = ALT(s, r)
  def | (r: String) = ALT(s, r)
  def % = STAR(s)
  def ~ (r: Rexp) = SEQ(s, r)
  def ~ (r: String) = SEQ(s, r)
  def $ (r: Rexp) = RECD(s, r)
}

def nullable (r: Rexp) : Boolean = r match {
  case ZERO => false
  case ONE => true
  case CHAR(_) => false
  case ALT(r1, r2) => nullable(r1) || nullable(r2)
  case SEQ(r1, r2) => nullable(r1) && nullable(r2)
  case STAR(_) => true
  case RECD(_, r1) => nullable(r1)
  case RANGE(_) => false
  case PLUS(r) => nullable(r)
  case OPTIONAL(r) => true
  case NTIMES(r, i) => if (i == 0) true else nullable(r)
}

def der (c: Char, r: Rexp) : Rexp = r match {
  case ZERO => ZERO
  case ONE => ZERO
  case CHAR(d) => if (c == d) ONE else ZERO
  case ALT(r1, r2) => ALT(der(c, r1), der(c, r2))
  case SEQ(r1, r2) => 
    if (nullable(r1)) ALT(SEQ(der(c, r1), r2), der(c, r2))
    else SEQ(der(c, r1), r2)
  case STAR(r) => SEQ(der(c, r), STAR(r))
  case RECD(_, r1) => der(c, r1)
  case RANGE(cs) => if (cs.contains(c)) ONE else ZERO
  case PLUS(r) => SEQ(der(c, r), STAR(r))
  case OPTIONAL(r) => der(c, r)
  case NTIMES(r, i) => if (i == 0) ZERO else SEQ(der(c, r), NTIMES(r, i-1))
}


// extracts a string from value
def flatten(v: Val) : String = v match {
  case Empty => ""
  case Chr(c) => c.toString
  case Left(v) => flatten(v)
  case Right(v) => flatten(v)
  case Sequ(v1, v2) => flatten(v1) + flatten(v2)
  case Stars(vs) => vs.map(flatten).mkString
  case Rec(_, v) => flatten(v)
  case Opt(v) => flatten(v)
}

// extracts an environment from a value;
// used for tokenise a string
def env(v: Val) : List[(String, String)] = v match {
  case Empty => Nil
  case Chr(c) => Nil
  case Left(v) => env(v)
  case Right(v) => env(v)
  case Sequ(v1, v2) => env(v1) ::: env(v2)
  case Stars(vs) => vs.flatMap(env)
  case Rec(x, v) => (x, flatten(v))::env(v)
  case Opt(v) => env(v)
}

// The Injection Part of the lexer

def mkeps(r: Rexp) : Val = r match {
  case ONE => Empty
  case ALT(r1, r2) => 
    if (nullable(r1)) Left(mkeps(r1)) else Right(mkeps(r2))
  case SEQ(r1, r2) => Sequ(mkeps(r1), mkeps(r2))
  case STAR(r) => Stars(Nil)
  case RECD(x, r) => Rec(x, mkeps(r))
  case PLUS(r) => Stars(List(mkeps(r))) 
  case OPTIONAL(r) => Stars(Nil)
  case NTIMES(r, n) => Stars(List.fill(n)(mkeps(r)))
}

def inj(r: Rexp, c: Char, v: Val) : Val = (r, v) match {
  case (STAR(r), Sequ(v1, Stars(vs))) => Stars(inj(r, c, v1)::vs)
  case (SEQ(r1, r2), Sequ(v1, v2)) => Sequ(inj(r1, c, v1), v2)
  case (SEQ(r1, r2), Left(Sequ(v1, v2))) => Sequ(inj(r1, c, v1), v2)
  case (SEQ(r1, r2), Right(v2)) => Sequ(mkeps(r1), inj(r2, c, v2))
  case (ALT(r1, r2), Left(v1)) => Left(inj(r1, c, v1))
  case (ALT(r1, r2), Right(v2)) => Right(inj(r2, c, v2))
  case (CHAR(d), Empty) => Chr(c) 
  case (RECD(x, r1), _) => Rec(x, inj(r1, c, v))
  case (RANGE(_), Empty) => Chr(c)
  case (PLUS(r), Sequ(v1, Stars(vs))) => Stars(inj(r, c, v1)::vs)
  case (OPTIONAL(r), v) => Stars(inj(r, c, v)::Nil)
  case (NTIMES(r, n), Sequ(v1, Stars(vs))) => Stars(inj(r, c, v1)::vs)
  // case _ => { println ("Injection error") ; sys.exit(-1) } 
}

// some "rectification" functions for simplification
def F_ID(v: Val): Val = v
def F_RIGHT(f: Val => Val) = (v:Val) => Right(f(v))
def F_LEFT(f: Val => Val) = (v:Val) => Left(f(v))
def F_ALT(f1: Val => Val, f2: Val => Val) = (v:Val) => v match {
  case Right(v) => Right(f2(v))
  case Left(v) => Left(f1(v))
}
def F_SEQ(f1: Val => Val, f2: Val => Val) = (v:Val) => v match {
  case Sequ(v1, v2) => Sequ(f1(v1), f2(v2))
}
def F_SEQ_Empty1(f1: Val => Val, f2: Val => Val) = 
  (v:Val) => Sequ(f1(Empty), f2(v))
def F_SEQ_Empty2(f1: Val => Val, f2: Val => Val) = 
  (v:Val) => Sequ(f1(v), f2(Empty))
def F_RECD(f: Val => Val) = (v:Val) => v match {
  case Rec(x, v) => Rec(x, f(v))
}
def F_ERROR(v: Val): Val = throw new Exception("error")

def simp(r: Rexp): (Rexp, Val => Val) = r match {
  case ALT(r1, r2) => {
    val (r1s, f1s) = simp(r1)
    val (r2s, f2s) = simp(r2)
    (r1s, r2s) match {
      case (ZERO, _) => (r2s, F_RIGHT(f2s))
      case (_, ZERO) => (r1s, F_LEFT(f1s))
      case _ => if (r1s == r2s) (r1s, F_LEFT(f1s))
                else (ALT (r1s, r2s), F_ALT(f1s, f2s)) 
    }
  }
  case SEQ(r1, r2) => {
    val (r1s, f1s) = simp(r1)
    val (r2s, f2s) = simp(r2)
    (r1s, r2s) match {
      case (ZERO, _) => (ZERO, F_ERROR)
      case (_, ZERO) => (ZERO, F_ERROR)
      case (ONE, _) => (r2s, F_SEQ_Empty1(f1s, f2s))
      case (_, ONE) => (r1s, F_SEQ_Empty2(f1s, f2s))
      case _ => (SEQ(r1s,r2s), F_SEQ(f1s, f2s))
    }
  }
  // case RECD(x, r1) => {
  //   val (r1s, f1s) = simp(r1)
  //   (RECD(x, r1s), F_RECD(f1s))
  // }
  case r => (r, F_ID)
}

// lexing functions including simplification
def lex_simp(r: Rexp, s: List[Char]) : Val = s match {
  case Nil => if (nullable(r)) mkeps(r) else { println ("Lexing Error") ; sys.exit(-1) } 
  case c::cs => {
    val (r_simp, f_simp) = simp(der(c, r))
    inj(r, c, f_simp(lex_simp(r_simp, cs)))
  }
}

def lexing_simp(r: Rexp, s: String) = env(lex_simp(r, s.toList))


// The Lexing Rules for the Fun Language

// def PLUS(r: Rexp) = r ~ r.%

 
val KEYWORD: Rexp = "if" | "then" | "else" | "write" | "def" | "val"
val OP: Rexp = "+" | "-" | "*" | "%" | "/" | "==" | "!=" | ">" | "<" | "<=" | ">=" | ":=" | "&&" | "||" | "="
val LETTER: Rexp = RANGE(("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ").toSet)
val SYMBOL: Rexp = LETTER | ("." | "_" | ">" | "<" | "=" | ";" | "," | "\\" | ":" | "-").%
val DIGIT: Rexp = RANGE(("0123456789").toSet)
val WHITESPACE: Rexp = PLUS(" " | "\n" | "\t" | "\r")
val LPARA: Rexp = "(" | "{"
val RPARA: Rexp = ")" | "}"
val PAREN: Rexp = LPARA | RPARA
val SEMI: Rexp = ";"
val STRING: Rexp = "\"" ~ (SYMBOL | WHITESPACE | DIGIT).% ~ "\""
val ID: Rexp = PLUS(LETTER) ~ PLUS("_" | LETTER | DIGIT).%
val NUM: Rexp = PLUS(DIGIT)
val ALL = SYMBOL | DIGIT | OP | " " | ":" | ";" | "\"" | "=" | "," | "(" | ")" | "{" | "}" 
val ALL2 = ALL | "\n"
val COMMENT = ("/*" ~ ALL2.% ~ "*/") | ("//" ~ ALL.% ~ "\n") | ("//" ~ ALL.% ~ "\"" ~ ALL.% ~ "\"")
val TYPE: Rexp = "Int" | "Double" | "Void"
val COLON: Rexp = ":"
val DOUBLE: Rexp = OPTIONAL("-") ~ PLUS(DIGIT) ~ "." ~ PLUS(DIGIT)
val INT: Rexp = OPTIONAL("-") ~ PLUS(DIGIT)
val CHAR2: Rexp = "\'" ~ (WHITESPACE | SYMBOL | DIGIT) ~ "\'"
val COMMA: Rexp = ","

val FUN_REGS = (("k" $ KEYWORD) | 
                  ("t" $ TYPE) |
                  ("id" $ ID) |
                  ("o" $ OP) | 
                  ("s" $ SEMI) |
                  ("co" $ COMMA) |
                  ("c" $ COLON) |
                  ("ch" $ CHAR2) |   
                  ("p" $ PAREN ) |
                  ("d" $ DOUBLE) | 
                  ("i" $ INT) | 
                  ("st" $ STRING) |
                  ("w" $ (WHITESPACE | COMMENT ))).%




// The tokens for the Fun language

abstract class Token extends Serializable 
case object T_SEMI extends Token
case object T_COMMA extends Token
case object T_LPAREN extends Token
case object T_RPAREN extends Token
case object T_COLON extends Token
// case object T_VOID extends Token
// case object T_QUOTE extends Token

case class T_ID(s: String) extends Token
case class T_STRING(s: String) extends Token
case class T_OP(s: String) extends Token
case class T_NUM(n: Int) extends Token
case class T_KWD(s: String) extends Token
case class T_DOUBLE(n: Double) extends Token
case class T_INT(n: Int) extends Token
case class T_PAREN(s: String) extends Token
case class T_TYPE(s: String) extends Token
case class T_CHAR(n: Int) extends Token

val token : PartialFunction[(String, String), Token] = {
  case ("k", s) => T_KWD(s)
  case ("t", s) => T_TYPE(s)
  case ("id", s) => T_ID(s)
  case ("o", s) => T_OP(s)
  case ("s", _) => T_SEMI
  case ("co", _) => T_COMMA
  case ("c", _) => T_COLON
  case ("d", s) => T_DOUBLE(s.toDouble)
  case ("i", s) => T_INT(s.toInt)
  case ("p", s) => T_PAREN(s)
  case ("ch", s) => T_CHAR(s.charAt(1).toInt)
  case ("st", s) => T_STRING(s.substring(1, s.length - 1))
}


def tokenise(s: String) : List[Token] = {
  val tks = lexing_simp(FUN_REGS, StringContext.processEscapes(s)).collect(token)
  if (tks.length != 0) tks
  else { println (s"Tokenise Error") ; sys.exit(-1) }     
}

// pre-2.5.0 ammonite 
// import ammonite.ops._

// post 2.5.0 ammonite
// import os._

//@doc("Tokenising a file.")
@main
def main(fname: String) = {
  println(tokenise(os.read(os.pwd / fname)))
}      