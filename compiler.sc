// A Small LLVM Compiler for a Simple Functional Language by Abdurrahman Lleshi
// (includes an external lexer and parser)
//
// All .fun files taken from keats folder!
// All .ll files generated from .fun files using this script, can use lli to test them!
//
//================================
// WARNING: defs.fun is not supported only parsing and lexing supported!
//           - Was due to not being marked for coursework 5 pdf
//================================
//
// call with below to output .ll file in terminal
//
//     amm fun_llvm.sc main fact.fun
//     amm fun_llvm.sc main hanoi.fun
//     amm fun_llvm.sc main mand.fun
//     amm fun_llvm.sc main mand2.fun
//     amm fun_llvm.sc main sqr.fun
//
//================================
//
// call with below commands to generate .ll file (Already done for all files in the folder!!)
//
//     amm fun_llvm.sc write fact.fun
//     amm fun_llvm.sc write hanoi.fun
//     amm fun_llvm.sc write mand.fun
//     amm fun_llvm.sc write mand2.fun
//     amm fun_llvm.sc write sqr.fun
//
//================================
//
// You can interpret an .ll file using lli, for example
//
//      lli fact.ll
//      lli hanoi.ll
//      lli mand.ll
//      lli mand2.ll
//      lli sqr.ll
//


import $file.fun_tokens, fun_tokens._
import $file.fun_parser, fun_parser._ 

type TyEnv = Map[String, String]

var type_map: TyEnv = Map(
  "Int" -> "i32",
  "Bool" -> "i1",
  "Void" -> "Void",
  "Double" -> "double",
  "new_line" -> "Void",
  "print_star" -> "Void",
  "print_int" -> "Void",
  "print_char" -> "Void",
  "print_space" -> "Void",
  "skip" -> "Void",
)

// for generating new labels
var counter = -1

def Fresh(x: String) = {
  counter += 1
  x ++ "_" ++ counter.toString()
}

// Internal CPS language for FUN
abstract class KExp
abstract class KVal

// case class KVar(s: String) extends KVal
case class KVar(s: String , ty: String = "UNDEF") extends KVal
case class KNum(i: Int) extends KVal
case class Kop(o: String, v1: KVal, v2: KVal) extends KVal
case class KCall(o: String, vrs: List[KVal]) extends KVal
case class KWrite(v: KVal) extends KVal
case class KFNum(i: Double) extends KVal
case class KFConst(s: String) extends KVal
case class KConst(s: String) extends KVal
case class KBool(b: Boolean) extends KVal
case class KCharConst(i: Int) extends KVal
case class KLet(x: String, e1: KVal, e2: KExp) extends KExp {
  override def toString = s"LET $x = $e1 in \n$e2" 
}
case class KIf(x1: String, e1: KExp, e2: KExp) extends KExp {
  def pad(e: KExp) = e.toString.replaceAll("(?m)^", "  ")

  override def toString = 
     s"IF $x1\nTHEN\n${pad(e1)}\nELSE\n${pad(e2)}"
}
case class KReturn(v: KVal) extends KExp


def typ_val (v: KVal , ts: TyEnv ) : String = v match {
  case KNum(_) => "Int"
  case KFNum(_) => "Double"
  case KCharConst(_) => "Int"  
  case KVar(x, _) => ts(x)
  case Kop(o, v1, v2) => typ_val(v1, ts)
  case KCall(o, vrs) => ts(o)
  case KWrite(v) => typ_val(v, ts)
  case KConst(s) => ts(s)
  case _ => "UNDEF"
}

def typ_exp (a: KExp , ts: TyEnv ) : String = a match {
  case KLet(x, e1, e2) => typ_val(e1, ts)
  case KIf(x1, e1, e2) => typ_exp(e1, ts)
  case KReturn(v) => typ_val(v, ts)
  case _ => "UNDEF"
}

// CPS translation from Exps to KExps using a
// continuation k.
def CPS(e: Exp)(k: KVal => KExp) : KExp = e match {

  case Var(s) => {
    if(s.head.isUpper) {
      val z = Fresh("tmp")
      KLet(z, KConst(s), k(KVar(z)))
    } else {
      k(KVar(s))
    }
  }

  case Num(i) => k(KNum(i))
  case FNum(i) => k(KFNum(i))
  case ChConst(i) => k(KCharConst(i))

  case Aop(o, e1, e2) => {
    val z = Fresh("tmp")
    CPS(e1)(y1 => 
      CPS(e2)(y2 => {
        // type_map += (z -> typ_val(y1, type_map))
        KLet(z, Kop(o, y1, y2), k(KVar(z)))
      }))
  }

  case If(Bop(o, b1, b2), e1, e2) => {
    val z = Fresh("tmp")
    CPS(b1)(y1 => 
      CPS(b2)(y2 => {
        // type_map += (z -> typ_val(y1, type_map))
        KLet(z, Kop(o, y1, y2), KIf(z, CPS(e1)(k), CPS(e2)(k)))
      }))
  }

  case Call(name, args) => {
    def aux(args: List[Exp], vs: List[KVal]) : KExp = args match {
      case Nil => {
        val z = Fresh("tmp")
        KLet(z, KCall(name, vs), k(KVar(z)))
      }
      case e::es => CPS(e)(y => aux(es, vs ::: List(y)))
    }
    aux(args, Nil)
  }

  case Sequence(e1, e2) => 
    CPS(e1)(_ => CPS(e2)(y2 => k(y2)))

  case Write(e) => {
    val z = Fresh("tmp")
    CPS(e)(y => KLet(z, KWrite(y), k(KVar(z))))
  }
}    


//initial continuation
def CPSi(e: Exp) = CPS(e)(KReturn)

// convenient string interpolations 
// for instructions, labels and methods
import scala.language.implicitConversions
import scala.language.reflectiveCalls

implicit def sring_inters(sc: StringContext) = new {
    def i(args: Any*): String = "   " ++ sc.s(args:_*) ++ "\n"
    def l(args: Any*): String = sc.s(args:_*) ++ ":\n"
    def m(args: Any*): String = sc.s(args:_*) ++ "\n"
}


// mathematical and boolean operations
def compile_op(op: String) = op match {
  case "+" => "add i32 "
  case "*" => "mul i32 "
  case "-" => "sub i32 "
  case "/" => "sdiv i32 "
  case "%" => "srem i32 "
  case "==" => "icmp eq i32 "
  case "!=" => "icmp ne i32 "
  case "<=" => "icmp sle i32 "     // signed less or equal
  case "<"  => "icmp slt i32 "     // signed less than
}

def compile_dop (op: String ) = op match {
  case "+" => "fadd double "
  case "*" => "fmul double "
  case "-" => "fsub double "
  case "/" => "fdiv double "
  case "%" => "frem double "
  case "==" => "fcmp oeq double "
  case "!=" => "fcmp one double "
  case "<=" => "fcmp ole double "
  case "<" => "fcmp olt double "
}

// compile type expressions
def compile_type(s: String) = s match {
  case "Int" => "i32"
  case "Double" => "double"
  case "Void" => "void"
  case _ => s
}

// compile K values
def compile_val(v: KVal, types: TyEnv) : String = v match {
  case KNum(i) => s"$i"
  case KFNum(i) => s"$i"
  case KCharConst(c) => s"$c"
  case KVar(s, _) => s"%$s"
  // case KConst(s) => s"load i32, i32* @${s}"
  // case KFConst(s) => s"load double, double* @${s}"
  case KConst(s) => {
    val compType = compile_type(types(s));
    s"load $compType, $compType* @$s" 
  }

  case Kop(op, x1, x2) => {
    typ_val(x1, types) match {
      case "Double" => s"${compile_dop(op)} ${compile_val(x1, types)}, ${compile_val(x2, types)}"
      case _ => s"${compile_op(op)} ${compile_val(x1, types)}, ${compile_val(x2, types)}"
    }
  }

  case KCall(x1, args) => {
    val args_compile_type = args.map(x => compile_type(typ_val(x, types)))
    val args_compile_val = args.map(x => compile_val(x, types)) 
    if (args_compile_type.isEmpty) {
      s"call ${compile_type(types(x1))} @$x1()"
    } else {
        val args_compile = args_compile_type.zip(args_compile_val).map(x => x._1 + " " + x._2 + ", ").mkString
        s"call ${compile_type(types(x1))} @$x1(${args_compile.dropRight(2)})"
    }
  }

  case KWrite(x1) =>
    s"call i32 @printInt (i32 ${compile_val(x1, types)})"
}

// compile K expressions
def compile_exp(a: KExp, types: TyEnv) : String = a match {
  case KReturn(v) => {
    if (typ_val(v, types) == "Void") {
      i"ret void"
    } else {
      i"ret ${compile_type(typ_val(v, types))} ${compile_val(v, types)}"
    }
  }

  case KLet(x: String, v: KVal, e: KExp) => v match {
    case KCall(x1, vrs) => types(x1) match {
      case "Void" => i"${compile_val(v, types)}" ++ compile_exp(e, types + (x -> types(x1)))
      case _ => i"%$x = ${compile_val(v, types)}" ++ compile_exp(e, types + (x -> types(x1)))
    }
    case _ => i"%$x = ${compile_val(v, types)}" ++ compile_exp(e, types + (x -> typ_val(v, types)))
  }

  case KIf(x, e1, e2) => {
    val if_br = Fresh("if_branch")
    val else_br = Fresh("else_branch")
    i"br i1 %$x, label %$if_br, label %$else_br" ++
    l"\n$if_br" ++
    compile_exp(e1, types) ++
    l"\n$else_br" ++ 
    compile_exp(e2, types)
  }
}

// compile function for declarations and main
def compile_decl(d: Decl, types: TyEnv) : (String, TyEnv) = d match {
  case Def(name, args, typ, body) =>{
    (m"define ${compile_type(typ)} @$name(${args.map(arg => s"${compile_type(arg._2)}  %${arg._1}").mkString(", ")}) {" ++
    compile_exp(CPSi(body), types + (name -> typ) ++ (types ++ args.map(arg => (arg._1 -> arg._2)))) ++ 
    m"}\n", types + (name -> typ))
  }

  case Main(body) => {
    (m"define i32 @main() {" ++
    compile_exp(CPS(body)(_ => KReturn(KNum(0))), types) ++
    m"}\n", types)
  }

  case Const(name, var1) => {
    (i"@$name = global i32 $var1", types + (name -> "Int"))
  }
  
  case FConst(name, var1) => {
    (i"@$name = global double $var1", types + (name -> "Double"))
  }
}


val prelude = """
declare i32 @printf(i8*, ...)

@.str = private constant [4 x i8] c"%d\0A\00"
@.str_nl = private constant [2 x i8] c"\0A\00"
@.str_star = private constant [2 x i8] c"*\00"
@.str_space = private constant [2 x i8] c" \00"
@.str_char = private constant [2 x i8] c"%c"

define void @new_line() #0 {
  %t0 = getelementptr [2 x i8], [2 x i8]* @.str_nl, i32 0, i32 0
  %1 = call i32 (i8*, ...) @printf(i8* %t0)
  ret void
}

define void @print_star() #0 {
  %t0 = getelementptr [2 x i8], [2 x i8]* @.str_star, i32 0, i32 0
  %1 = call i32 (i8*, ...) @printf(i8* %t0)
  ret void
}

define void @print_space() #0 {
  %t0 = getelementptr [2 x i8], [2 x i8]* @.str_space, i32 0, i32 0
  %1 = call i32 (i8*, ...) @printf(i8* %t0)
  ret void
}

define void @print_int(i32 %x) {
   %t0 = getelementptr [4 x i8], [4 x i8]* @.str, i32 0, i32 0
   call i32 (i8*, ...) @printf(i8* %t0, i32 %x) 
   ret void
}

define void @print_char(i32 %x) {
   %t0 = getelementptr [2 x i8], [2 x i8]* @.str_char, i32 0, i32 0
   call i32 (i8*, ...) @printf(i8* %t0, i32 %x) 
   ret void
}

define void @skip() #0 {
  ret void
}

; END OF BUILD-IN FUNCTIONS (prelude)
"""

def compile(prog: List[Decl], types: TyEnv) : String = prog match {
  case Nil => ""
  case head::tail => {
    val (code, new_types) = compile_decl(head, types)
    code ++ compile(tail, new_types)
  }
} 

def compile_prog(prog: List[Decl]) : String =
  prelude ++ compile(prog, type_map)


// pre-2.5.0 ammonite 
// import ammonite.ops._

// post 2.5.0 ammonite
// import os._


@main
def main(fname: String) = {
    val path = os.pwd / fname
    val file = fname.stripSuffix("." ++ path.ext)
    val tks = tokenise(os.read(path))
    val ast = parse_tks(tks)
    println(compile_prog(ast))
}

@main
def write(fname: String) = {
    val path = os.pwd / fname
    val file = fname.stripSuffix("." ++ path.ext)
    val tks = tokenise(os.read(path))
    val ast = parse_tks(tks)
    val code = compile_prog(ast)
    os.write.over(os.pwd / (file ++ ".ll"), code)
}

// @main
// def run(fname: String) = {
//     val path = os.pwd / fname
//     val file = fname.stripSuffix("." ++ path.ext)
//     write(fname)  
//     os.proc("llc", "-filetype=obj", file ++ ".ll").call()
//     os.proc("gcc", file ++ ".o", "-o", file ++ ".bin").call()
//     os.proc(os.pwd / (file ++ ".bin")).call(stdout = os.Inherit)
//     println(s"done.")
// }

// @main
// def testing() = {
//   println("Lexing...\n")
//   val tks = tokenise(os.read(os.pwd / "mand.fun"))
//   println(tks + "\n")
//   println("Parsing...\n")
//   val ast = parse_tks(tks)
//   println(ast + "\n")
//   println("Compiling...\n")
//   val code = compile_prog(ast)
//   println(code + "\n")
//   println("Writing...")
//   os.write.over(os.pwd / "mand.ll", code)
//   // println("Assembling...")
//   // os.proc("llc", "-filetype=obj", "mand.ll").call()
// }


