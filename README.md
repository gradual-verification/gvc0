# `gvc0`: Gradually Verified C0

TODO: Get a better name

## Setup
Clone the gradual verification forks of [Silver](https://github.com/gradual-verification/silver-gv) and [Silicon](https://github.com/gradual-verification/silver-gv).

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


## Running

Run the C0 frontend and verify using Silicon in SBT:

```sh
sbt
  run <file.c0> [--c0] [--silver] [--weave]
```

Use `--c0` or `--silver` to print the generated C0 or Silver source code, respectively. Use `--weave` to insert the required runtime checks and print the resulting C0 source code.
