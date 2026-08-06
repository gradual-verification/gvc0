package gvc.transformer

object Helpers {
  private def nameOptions(baseName: String) =
    Iterator.from(0)
      .map({
        case 0 => baseName
        case n => baseName + n
      })

  def findAvailableName(names: Iterable[String], baseName: String): String =
    nameOptions(baseName).find(name => !names.exists(_ == name)).get
}