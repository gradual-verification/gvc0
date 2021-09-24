Here's what the current README instructs users to setup for gvc0:
```
git
|-gvc0
    |-silicon(sym)
    |-silver(sym)
|-silicon
|-silver
```
In this configuration, running `sbt compile` in the `gvc0` directory gives the following error:

```
[error] /Users/icmccorm/git/test/gvc0/silicon/common/src/main/scala/io/package.scala:16:12: object apache is not a member of package org
[error] import org.apache.commons.io.FilenameUtils
[error] 
[error] /Users/icmccorm/git/test/gvc0/silicon/common/src/main/scala/io/package.scala:54:47: not found: value FilenameUtils
[error]     val directory = targetDirectory.getOrElse(FilenameUtils.getFullPath(fileStr)).toString
```
I traced this issue to Silicon. Looking at the documentation, it seems like Silicon needs to have a symlink to Silver as well. So, I modified the directory structure like so:
```
git
|-gvc0
    |-silicon(sym)
    |-silver(sym)
|-silicon
    |-silver(sym)
|-silver
```
When I compile this, it's successful. I noticed that the logs indicate Silver is being looked at twice:
```
[info] loading settings for project gvc from build.sbt ...
[info] loading settings for project silver from build.sbt ...
[info] loading settings for project silicon from build.sbt ...
[info] loading settings for project silver from build.sbt ...
```
When I check `gvc0`'s `build.sbt` file, I'm seeing the following:
```
lazy val silver = project in file("silver")
lazy val silicon = (project in file("silicon"))
  .dependsOn(silver)
```
I noticed that this is also being done in Silicon's build file:
```
// Import general settings from Silver
lazy val silver = project in file("silver")

lazy val common = (project in file("common"))
  .dependsOn(silver)
```
I removed the `lazy val silver` from `gvc0`'s build file, and I tried a slightly different configuration of the file structure to see if it would affect anything:
```
git
|-gvc0
    |-silicon(sym)
|-silicon
    |-silver(sym)
|-silver
```
This compiles successfully in the same amount of time. To make first-time setup easier, I propose that we use the configuration above and that we remove Silver as a direct dependency of `gvc0`. This shouldn't break anyone's current configuration.