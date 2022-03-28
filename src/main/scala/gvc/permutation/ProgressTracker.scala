package gvc.permutation

abstract class ProgressTracker(activity: String) {
  def increment(): Unit

  override def toString: String =
    s"[ ${Output.blue(activity)} ]"

  def update(): Unit = {
    print(s"\r${Output.formatInfo(this.toString)}")
  }
  def percentage(top: Int, bot: Int): String = {
    if (bot == 0) "100%"
    else Math.ceil((top / bot.toDouble) * 100).toInt.toString + "%"
  }
}

class VerificationTracker(perPath: Int, maxPaths: Int)
    extends ProgressTracker("Verifying") {
  private var timeouts = 0
  private var failures = 0
  private var currentPath = 0
  private var currentPerm = 1
  private var allPerms = 0

  update()

  override def increment(): Unit = {
    currentPerm += 1
    allPerms += 1
    if (currentPerm > perPath) {
      currentPath += 1
      currentPerm %= perPath
    }
    update()
  }

  def error(): Unit = {
    failures += 1
  }

  def timeout(): Unit = {
    timeouts += 1
  }

  override def toString: String = {
    val timeoutColor: (String) => String =
      if (timeouts > 0) Output.red else Output.green
    val failureColor: (String) => String =
      if (failures > 0) Output.red else Output.green

    val successValue =
      super.percentage(allPerms - (failures + timeouts), perPath)
    val success: String =
      if (successValue == "100%") Output.green(successValue)
      else Output.yellow(successValue)

    super.toString() + List(
      s"Path: ${Output.blue(s"$currentPath/$maxPaths")}",
      s"Step: ${Output.blue(s"$currentPerm/$perPath")}",
      s"Remaining Steps: ${Output.blue((perPath - currentPerm).toString)}",
      s"Success Overall: $success",
      s"Failures: ${failureColor(failures.toString)}",
      s"Timeouts: ${timeoutColor(timeouts.toString)}"
    ).foldLeft("")(_ + " — " + _)
  }
}
sealed trait VerificationType { val name: String }
object VerificationType {
  case object Gradual extends VerificationType { val name = "Gradual" }
  case object Dynamic extends VerificationType { val name = "Dynamic" }
}

class ExecutionTracker(maxPrograms: Int, verType: VerificationType)
    extends ProgressTracker("Compiling & Executing") {
  private var progress = 0
  private var cc0Failures = 0
  private var execFailures = 0
  update()

  def cc0Error(): Unit = {
    cc0Failures += 1
  }
  def execError(): Unit = {
    execFailures += 1
  }
  override def increment(): Unit = {
    progress += 1
    update()
  }

  override def toString: String = {
    val execFailureColor: (String) => String =
      if (execFailures > 0) Output.red else Output.green
    val cc0FailureColor: (String) => String =
      if (execFailures > 0) Output.red else Output.green
    val successValue =
      super.percentage(progress - (cc0Failures + execFailures), progress)
    val success: String =
      if (successValue == "100%") Output.green(successValue)
      else Output.yellow(successValue)

    super.toString() + List(
      s"[ ${Output.purple(s"${verType.name} Verification")} ]",
      s"Program: ${Output.blue(s"$progress/$maxPrograms")}",
      s"Success: ${success}",
      s"CC0 Failures: ${cc0FailureColor(cc0Failures.toString)}",
      s"Execution Failures: ${execFailureColor(execFailures.toString)}"
    ).foldLeft("")(_ + " — " + _)
  }
}
