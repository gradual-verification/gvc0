package gvteal.transformer
import scala.collection.MapLike

object Helpers {
  private def nameOptions(baseName: String) =
    Iterator.from(0)
      .map({
        case 0 => baseName
        case n => baseName + n
      })

  def findAvailableName(map: MapLike[String, _, _], baseName: String): String =
    nameOptions(baseName).find(!map.contains(_)).get

  def findAvailableName(names: Seq[String], baseName: String): String =
    nameOptions(baseName).find(!names.contains(_)).get
}