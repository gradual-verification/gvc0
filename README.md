# `gvc0`: Gradually Verified C0

TODO: Get a better name

## Setup
Clone the gradual verification forks of [Silver](https://github.com/gradual-verification/silver-gv) and [Silicon](https://github.com/gradual-verification/silicon-gv).

Add a symlink to Silver within the Silicon directory
```
cd ./silicon-gv
ln -s ../silver-gv silver
```
Add a symlink to Silicon within the gvc0 directory.
```
cd ./gvc0
ln -s ../silicon-gv silicon
```
Install [z3](https://github.com/Z3Prover/z3/releases) and set the Z3_PATH environment variable to the location of the executable.

In order to run gradually verified programs, you will also need to install [cc0](https://bitbucket.org/c0-lang/docs/wiki/Downloads), a compiler for c0.

## Running

By default, running the frontend will statically verify the input program and compile the resulting output, including the required dynamic verification. To run the frontend in SBT while developing:

```
sbt
  > run [OPTION...] SOURCEFILE

where OPTION is
  -h         --help           Give short usage message and exit
  -d <type>  --dump=<type>    Print the generated code and exit, where <type> specifies
                              the type of code to print: ir, silver, c0
  -o <file>  --output=<file>  Place the executable output into <file>
  -v         --only-verify    Stop after static verification
  -s         --save-files     Save the intermediate files produced (IR, Silver, C0, and C)
  -x         --exec           Execute the compiled file
```

As described above, the last option, executing the compiled file, requires first installing [cc0](https://bitbucket.org/c0-lang/docs/wiki/Downloads).

## Testing

A number of tests use resource files for the input and expected output. When modifying the output, it can become cumbersome to manually edit these files. Instead, you can overwrite all expected output files with by running the following command in an `sbt` shell:

    testOnly ** -- -Dupdate_files=true

Note that you will need to manually verify any modified files before committing to ensure that the new output is correct.

## Architecture

See the [architecture docs](docs/).
