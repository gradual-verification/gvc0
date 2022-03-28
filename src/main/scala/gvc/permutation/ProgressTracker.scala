package gvc.permutation

abstract class ProgressTracker(activity: String) {
  def increment(): Unit

  override def toString: String =
    s"[$activity]"

  def update(): Unit = {
    print(s"\r${this.toString}")
  }
  def percentage(top: Int, bot: Int): String = {
    if (bot == 0) "100%"
    else Math.floor((top / bot.toDouble) * 100).toString + "%"
  }
}

class VerificationTracker(perPath: Int, maxPaths: Int)
    extends ProgressTracker("Verifying") {
  private var timeouts = 0
  private var failures = 0
  private var currentPath = 0
  private var currentPerm = 1
  update()

  override def increment(): Unit = {
    currentPerm += 1
    if (currentPerm > perPath) {
      currentPath += 1
      currentPerm %= perPath
    }
    update()
  }

  def error(): Unit = {
    failures += 1
    increment()
  }

  def timeout(): Unit = {
    timeouts += 1
    increment()
  }

  override def toString: String =
    super.toString() + List(
      s"Path: $currentPath/$maxPaths",
      s"Step: $currentPerm/$perPath",
      s"Remaining Steps: ${perPath - currentPerm}",
      s"Success: ${super.percentage(currentPerm - (failures + timeouts), currentPerm)}",
      s"Failures: $failures",
      s"Timeouts: $timeouts"
    ).foldLeft("")(_ + " — " + _)
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
    increment()
  }
  def execError(): Unit = {
    execFailures += 1
    increment()
  }
  override def increment(): Unit = {
    progress += 1
    update()
  }

  override def toString: String =
    super.toString() + List(
      s"[${verType.name} Verification]",
      s"Program: $progress/$maxPrograms",
      s"Success: ${super.percentage(progress - (cc0Failures + execFailures), progress)}",
      s"CC0 Failures: $cc0Failures",
      s"Execution Failures: $execFailures"
    ).foldLeft("")(_ + " — " + _)
}
