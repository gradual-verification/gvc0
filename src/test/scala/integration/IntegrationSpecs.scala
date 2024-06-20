package gvc.specs.integration

import org.scalatest.funsuite._
import gvc.transformer._
import gvc.specs._

class IntegrationSpecs extends AnyFunSuite with BaseFileSpec {
  val testDirs = List(
    // The test files are copied with some modifications in the test header
    // from tests/fp-basic in the cc0 repository
    "fp-basic",
    "cases",
    "ir",
    "viper"
  )

  val exclusions = Set(
    // PARSING
    // TODO: fix big number handling
    "fp-basic/lexer02.c0",
    "fp-basic/lexer03.c0",
    "fp-basic/lexer04.c0",
    "fp-basic/parallel-decl.c0",
    // TODO: while(true); should be a parse error
    "fp-basic/semi.c0",
    // Arrays
    "cases/length.c0",
    "fp-basic/annoc.c0",
    "fp-basic/annok.c0",
    "fp-basic/annoj.c0",
    "fp-basic/annog.c0",
    // RESOLVING
    // TODO: implement #use
    "fp-basic/libfuns1.c0",
    "fp-basic/libfuns2.c0",
    "fp-basic/pragma1.c0",
    "fp-basic/usetest0.c0",
    "fp-basic/usetest.c0",
    // TYPE CHECKING

    // WELL-FORMEDNESS

    // UNSUPPORTED STUFF
    // Modulus operator
    "fp-basic/arith03.c0",
    "fp-basic/arith04.c0",
    "fp-basic/arith05.c0",
    "fp-basic/arith06.c0",
    "fp-basic/arith07.c0",
    "fp-basic/compound2.c0",
    "fp-basic/compound6.c0",
    "fp-basic/safediv.c0",
    // Bit shifts
    "fp-basic/arith08.c0",
    "fp-basic/arith09.c0",
    "fp-basic/arith10.c0",
    "fp-basic/compound3.c0",
    "fp-basic/compound4.c0",
    "fp-basic/compound5.c0",
    "fp-basic/compound7.c0",
    "fp-basic/compound8.c0",
    // Early returns
    "fp-basic/init05.c0",
    // Not used as test file
    "fp-basic/pragma1_aux.c0"
  )

  val testFiles = testDirs
    .flatMap(TestUtils.groupResources(_))
    .filterNot(f => exclusions.contains(f.name + ".c0"))

  testFiles.foreach { input =>
    test("test " + input.name) {
      val src = input(".c0").read
      if (src.startsWith("//test error")) {
        assertThrows[ParserException](TestUtils.program(src))
      } else if (src.startsWith("//test resolve_error")) {
        assertThrows[ResolverException](TestUtils.program(src))
      } else if (src.startsWith("//test type_error")) {
        assertThrows[TypeCheckerException](TestUtils.program(src))
      } else if (src.startsWith("//test validation_error")) {
        assertThrows[ValidatorException](TestUtils.program(src))
      } else if (src.startsWith("//test unsupported")) {
        assertThrows[TransformerException](TestUtils.program(src))
      } else {
        val program = TestUtils.program(src)
        assertFile(input.get(".ir.c0"), program.irSource)
        assertFile(input.get(".vpr"), program.silverSource)

        // Ensure that all successfully parsed program can also be woven
        program.weave
      }
    }
  }
}
