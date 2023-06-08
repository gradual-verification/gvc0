import org.scalatest.funsuite._
import gvteal.parser._
import fastparse.Parsed.Success

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

    val List(method: MethodDefinition) = defs
    assert(method.id == "isPrime")

    val List(arg: MemberDefinition) = method.arguments
    assert(arg.id == "n")

    assert(method.body.get.body.length == 5)
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