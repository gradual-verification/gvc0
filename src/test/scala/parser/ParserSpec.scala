import org.scalatest.funsuite._
import gvc.parser._
import fastparse.Parsed.{Success, Failure}

class ParserSpec extends AnyFunSuite {
  test("empty program") {
    val Success(defs, _) = Parser.parseProgram("\n")
    assert(defs == List.empty)
  }

  test("isPrime example") {
    // Taken from https://bitbucket.org/c0-lang/docs/wiki/Computing_primes_in_Python_and_C0
    val Success(defs, _) = Parser.parseProgram("""
      bool isPrime(int n)
      {
        if (n < 2) return false;
        if (n == 2) return true;
        if (n % 2 == 0) return false;
        for (int factor = 3; factor <= n/factor; factor += 2) {
          if (n % factor == 0)
            return false;
        }
        return true;
      }
    """)

    val List(MethodDefinition(methodId, methodReturn, methodArgs, methodBody, _)) = defs
    assert(methodId == "isPrime")

    val List(MemberDefinition(argId, _)) = methodArgs
    assert(argId == "n")

    val Some(BlockStatement(statements, _, _)) = methodBody
    assert(statements.length == 5)
  }

  test("line comments") {
    val Success(List(), _) = Parser.parseProgram("""
      // this is a test
      // another test
    """)
  }

  test("multi-line comments") {
    val Success(List(), _) = Parser.parseProgram("""
      /*
        This is a comment
      */
    """)
  }

  test("nested multi-line comments") {
    val Success(List(), _) = Parser.parseProgram("""
      /*
        /* This is a comment */
      */
    """)
  }
}