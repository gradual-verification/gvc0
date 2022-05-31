import benchexec.tools.template

import benchexec.util as util
class Tool(benchexec.tools.template.BaseTool):

    def executable(self, tool_locator=None):
        return util.find_executable("run_gvc0.sh")
    def name(self):
        return "gvc0"
    def cmdline(self, executable, options, task, propertyfile, rlimits):
        print(task)
        return ["java", "-Xss15m", "-jar",
            executable,
        ] + options + task
    def version(self, executable):
        return "1.0.0"