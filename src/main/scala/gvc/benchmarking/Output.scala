package gvc.benchmarking

import java.util.Calendar

object Output {
  private val errorHeader = s"[${red("x")}] —"
  private val successHeader = s"[${green("✓")}] —"
  private val infoHeader = s"[${purple("*")}] —"

  def success(input: String): Unit = println(formatSuccess(input))

  def formatSuccess(input: String): String = s"$successHeader $input"

  def error(input: String): Unit = println(formatError(input))

  def formatError(input: String): String = s"$errorHeader $input"

  def info(input: String): Unit = println(formatInfo(input))

  def formatInfo(input: String): String = s"$infoHeader $input"

  def green(input: String): String = s"${Console.GREEN}$input${Console.RESET}"

  def purple(input: String): String =
    s"${Console.MAGENTA}$input${Console.RESET}"

  def red(input: String): String = s"${Console.RED}$input${Console.RESET}"

  def blue(input: String): String = s"${Console.BLUE}$input${Console.RESET}"

  def yellow(input: String): String = s"${Console.YELLOW}$input${Console.RESET}"

  def printTiming(fn: () => Unit): Unit = {
    val startTime = Calendar.getInstance().getTime
    this.info(startTime.toString)
    fn()
    val stopTime = Calendar.getInstance().getTime
    val difference = stopTime.getTime - startTime.getTime
    Output.info(stopTime.toString)
    Output.info(s"Time elapsed: ${Timeout.formatMilliseconds(difference)}")
  }

}
