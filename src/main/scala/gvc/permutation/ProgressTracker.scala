package gvc.permutation

abstract class ProgressTracker(activity: String) {
  def increment(): Unit

  override def toString: String =
    s"[ ${Output.blue(activity)} ]"

  def update(): Unit = {
    print(s"\r${Output.formatInfo(this.toString)}")
  }
  def percentage(top: Double, bot: Double): Double =
    if (top == 0)
      top
    else { Math.ceil(top / bot * 100) }

  def formatTime(millis: Long): String = {
    if (millis < 1000 * 60) {
      s"${Math.round(millis / 1000 * 100) / 100} sec"
    } else if (millis < 1000 * 60 * 60) {
      s"${Math.round((millis / (1000 * 60)) * 100) / 100} min"
    } else if (millis < 1000 * 60 * 60 * 24) {
      s"${Math.round(millis / (1000 * 60 * 60) * 100) / 100} hr"
    } else {
      s"${Math.round(millis / (1000 * 60 * 60 * 24) * 100) / 100} days"
    }
  }
}

class VerificationTracker(perPath: Int, maxPaths: Int)
    extends ProgressTracker("Verifying") {
  private var timeouts = 0
  private var failures = 0
  var currentPath = 0
  private var currentPerm = 0
  private var allPerms = 0
  private var unique = 0
  private var startTime = System.currentTimeMillis()
  private var averagePerStep: Long = 0
  override def increment(): Unit = {
    val elapsed = System.currentTimeMillis() - startTime
    if (averagePerStep == 0) {
      averagePerStep = elapsed
    } else {
      averagePerStep = averagePerStep + ((elapsed - averagePerStep) / allPerms)
    }
    currentPerm += 1
    allPerms += 1
    if (currentPerm == perPath) {
      currentPath += 1
    }
    if (currentPerm > (perPath + 1)) {
      currentPerm %= perPath
    }
    update()
    if (currentPath == maxPaths) println("\n")
    startTime = System.currentTimeMillis()
  }

  def incrementUnique(): Unit = {
    increment()
    unique += 1
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
      super.percentage(allPerms - (failures + timeouts), perPath * maxPaths)
    val success: String =
      if (successValue.toInt == 100) Output.green(s"$successValue%")
      else Output.yellow(s"$successValue%")
    val toCompletion =
      ((perPath - currentPerm + ((maxPaths - currentPath) * perPath)) * averagePerStep)
    super.toString() + List(
      s"Path: ${Output.blue(s"$currentPath/$maxPaths")}",
      s"Step: ${Output.blue(s"$currentPerm/$perPath")}",
      s"Remaining Steps: ${Output.blue((perPath - currentPerm).toString)}",
      s"Unique Programs: ${Output.blue(s"$unique")}",
      s"Success Overall: $success",
      s"Failures: ${failureColor(failures.toString)}",
      s"Timeouts: ${timeoutColor(timeouts.toString)}",
      s"ETC: ${super.formatTime(toCompletion)}"
    ).foldLeft("")(_ + " — " + _)
  }
}
sealed trait ExecutionType { val name: String }
object ExecutionType {
  case object Gradual extends ExecutionType {
    val name = "Gradual Verification"
  }
  case object FullDynamic extends ExecutionType {
    val name = "Full Dynamic Verification"
  }
  case object FramingOnly extends ExecutionType {
    val name = "Only Framing Checks"
  }
  case object Unverified extends ExecutionType {
    val name = "Unverified"
  }
}

class ExecutionTracker(maxPrograms: Int, execType: ExecutionType)
    extends ProgressTracker("Compiling & Executing") {
  private var progress = 0
  private var cc0Failures = 0
  private var execFailures = 0

  private var startTime = System.currentTimeMillis()
  private var averagePerStep: Long = 0
  update()

  def cc0Error(): Unit = {
    cc0Failures += 1
  }
  def execError(): Unit = {
    execFailures += 1
  }
  override def increment(): Unit = {
    val elapsed = System.currentTimeMillis() - startTime
    if (averagePerStep == 0) {
      averagePerStep = elapsed
    } else {
      averagePerStep = (averagePerStep + elapsed) / 2
    }
    progress += 1
    update()
    startTime = System.currentTimeMillis()
  }

  override def toString: String = {
    val execFailureColor: (String) => String =
      if (execFailures > 0) Output.red else Output.green
    val cc0FailureColor: (String) => String =
      if (cc0Failures > 0) Output.red else Output.green
    val successValue =
      super.percentage(progress - (cc0Failures + execFailures), progress)
    val success: String =
      if (successValue.toInt == 100) Output.green(s"$successValue%")
      else Output.yellow(s"$successValue%")

    val toCompletion = ((maxPrograms - progress) * averagePerStep)
    super.toString() + List(
      s"[ ${Output.purple(s"${execType.name}")} ]",
      s"Program: ${Output.blue(s"$progress/$maxPrograms")}",
      s"Success: ${success}",
      s"CC0 Failures: ${cc0FailureColor(cc0Failures.toString)}",
      s"Execution Failures: ${execFailureColor(execFailures.toString)}",
      s"ETC: ${super.formatTime(toCompletion)}",
      if (progress == maxPrograms) "\n" else ""
    ).foldLeft("")(_ + " — " + _)
  }

}
