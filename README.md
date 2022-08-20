# `gvc0`: Gradually Verified C0

![Build](https://github.com/gradual-verification/gvc0/actions/workflows/build.yml/badge.svg)

TODO: Get a better name

## Setup

Clone the gradual verification forks of [Silver](https://github.com/gradual-verification/silver-gv)
and [Silicon](https://github.com/gradual-verification/silicon-gv).

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

Install [z3](https://github.com/Z3Prover/z3/releases) and set the Z3_PATH environment variable to the location of the
executable.

In order to run gradually verified programs, you will also need to
install [cc0](https://bitbucket.org/c0-lang/docs/wiki/Downloads), a compiler for c0.

## Running

By default, running the frontend will statically verify the input program and compile the resulting output, including
the required dynamic verification. To run the frontend in SBT while developing:

```
sbt
  > run [OPTION...] SOURCEFILE
  
where OPTION is
  -h            --help                         Give short usage message and exit
  -d <type>     --dump=<type>                  Print the generated code and exit, where <type> specifies
                                               the type of code to print: ir, silver, c0
  -o <file>     --output=<file>                Place the executable output into <file>
  -v            --only-verify                  Stop after static verification
  -s            --save-files                   Save the intermediate files produced (IR, Silver, C0, and C)
  -x            --exec                         Execute the compiled file
  -t <n(s|m)>   --timeout=<n(s|m)>             Specify a timeout for the verifier in seconds (s) or minutes (m).

                --config=<config.xml>          Execute a benchmark using the specified configuration file

                --populate                     Populate the benchmarking database using options from the specified configuration file.
                --execute                      Execute programs and store results in the database using options from the specified configuration file.
                --execute-benchmark            Identical to --execute, but only selects programs belonging to pre-configured benchmark sets.
                --recreate=<id>                Specify a permutation to recreate from the database using options from the specified configuration file.
                --export                       Data is filtered using options from the specified configuration file.
                --export-benchmark             Identical to --export, but only selects data corresponding to pre-configured benchmark sets.
                --export-errors                Identical to --export, but generates a list of all errors. 
                
                --version=<version>            Specify the version string identifying the current verifier. Overrides config.
                --hardware=<hardware>          Specify an identifier for current hardware platform. Overrides config.
                --nickname=<nickname>          Specify a nickname for the current hardware platform. Overrides config.
                
                --db-url=<url>                 Specify the URL for the benchmarking database. Overrides config.
                --db-user=<username>           Specify the user for the benchmarking database. Overrides config.
                --db-pass=<password>           Specify the password for the benchmarking database. Overrides config.
```

As described above, the last option, executing the compiled file, requires first
installing [cc0](https://bitbucket.org/c0-lang/docs/wiki/Downloads).

A limitation is that code position information is not yet passed to the back-end verifier, so static verification errors
don't yet come with line numbers. An (imperfect) workaround is to use the `-s` option to generate a `.vpr` (Viper) file
and then run the resulting code through the verifier. This gives you line numbers in the Viper program, which is often
mappable to the original source.

How do you run a `.vpr` file through the verifier? First, set the environmental variable `Z3_EXE` to the location of
z3 (this is in addition to the Z3_PATH variable mentioned above). Change to `../silicon-gv`. Finally,
run `sbt "run <path-to-vpr-file>"`.

## Limitations

The current implementation has a number of limitations:

* No support for strings.
* Conditional expressions are supported in logical formulas (in place of ||, so that the condition tells you which
  branch is true). But conditional expressions are not supported in program text.
* A return statement within an if statement will only work correctly with verification if there is no code following the
  if statement.

## Testing

A number of tests use resource files for the input and expected output. When modifying the output, it can become
cumbersome to manually edit these files. Instead, you can overwrite all expected output files with by running the
following command in an `sbt` shell:

    testOnly ** -- -Dupdate_files=true

Note that you will need to manually verify any modified files before committing to ensure that the new output is
correct.

### Types of tests

- **Unit tests**: (Such as `ParserSpec.scala`) Explicitly test a function by calling it, asserting output, etc.
- **Integration tests**: (Executed by `IntegrationSpecs.scala`) Run an input file through the parser, IR, and weaver,
  but without running the verifier. Files in `fp-basic`, `cases`, `ir` and `viper` folders are run in this manner. These
  test input `.c0` files can optionally have corresponding `.vpr` or `.ir.c0` files that are used to assert the output
  of the Silver code or the IR code, respectively. *should be renamed to indicate that verifier tests are the actual
  integration tests*
- **Baseline tests**: (In the `baseline` folder, executed by `BaselineSpec.scala`) Used to check the baseline dynamic
  verification code; takes `.c0` files as input and optional `.baseline.c0` files to assert output. The name *baseline*
  refers to a baseline level of verification.
- **Verifier tests**:  (In `verifier` and `quant-study` folder, executed by `CompilerSpec.scala`) Extends integration
  tests to run the verifier on the file and feeding that result to the weaver, run the C0 compiler on the weaver output,
  and then run the program, making sure it exits with code 0.

## Architecture

See the [architecture docs](docs/).
