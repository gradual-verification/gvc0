package gvc

import scala.collection.mutable.ListBuffer
import scala.io.Source
import gvc.parser.Parser
import fastparse.Parsed.{Failure, Success}
import gvc.analyzer._
import gvc.transformer._
import viper.silicon.Silicon
import viper.silver.verifier
import viper.silver.verifier
import gvc.weaver.Weaver

object Main extends App {

  lazy val silicon = {
    val z3Path = sys.env.get("Z3_EXE")
    z3Path match {
      case Some(z3Path) => {
        val reporter = viper.silver.reporter.StdIOReporter()
        val silicon = Silicon.fromPartialCommandLineArguments(Seq("--z3Exe", z3Path), reporter, Seq())
        silicon.start()
        silicon
      }
      case None => {
        println(s"Unable to locate z3. Configure the Z3_EXE variable with the location of the executable.")
        sys.exit(1)
      }
    }
  }

  val files = ListBuffer[String]()
  var printC0 = false
  var printSilver = false

  for (arg <- args) arg match {
    case "--c0" => printC0 = true
    case "--silver" => printSilver = true
    case flag if flag.startsWith("--") => {
      println(s"Invalid flag '$flag'")
      sys.exit(1)
    }
    case file => files += file
  }

  println(s"Verifying ${files.length} file(s)")
  files.foreach(verifyFile)

  silicon.stop()

  def verifyFile(name: String): Unit = {
    val src = Source.fromFile(name).mkString
    val parsed = Parser.parseProgram(src) match {
      case fail: Failure => {
        println(s"Parse error in '$name':")
        println(fail.trace().longAggregateMsg)
        sys.exit(2)
      }
      case Success(value, index) => value
    }
    
    val errors = new ErrorSink()
    val resolved = Resolver.resolveProgram(parsed, errors)
    TypeChecker.check(resolved, errors)
    AssignmentValidator.validate(resolved, errors)
    ReturnValidator.validate(resolved, errors)
    SpecificationValidator.validate(resolved, errors)
    ImplementationValidator.validate(resolved, errors)

    if (!errors.errors.isEmpty) {
      println(s"Error(s) in '$name':")
      println(errors.errors.map(_.toString()).mkString("\n"))
      sys.exit(0)
    }

    var ir = Transformer.programToIR(resolved)

    val silver = SilverOutput.program(ir)

    // TODO: Implement printer for whole program
    val c0 = ir.methods.collect { case m: IR.MethodImplementation => m }
      .map(CNaughtPrinter.printMethod(_))
      .mkString("\n")

    if (printC0) {
      println(s"C0 output for '$name':")
      println(c0)
    }

    if (printSilver) {
      println(s"Silver output for '$name':")
      println(silver.toString())
    }

    println(s"Verifying '$name'...")

    silicon.verify(silver) match {
      case verifier.Success => {
        println(s"Verified successfully!")
        for ((exp, checks) <- viper.silicon.state.runtimeChecks.getChecks) {
          println("Runtime checks required for " + exp.toString() + ":")
          println(checks.map(_.toString()).mkString(" && "))
          println(checks.map(_.getClass.toString()))
        }

        ir = Weaver.weave(ir, silver)
      }
      case verifier.Failure(errors) => {
        println(s"Verification errors in '$name':")
        println(errors.map(_.readableMessage).mkString("\n"))
      }
    }
  }
}