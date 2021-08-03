# `gvc0`: Gradually Verified C0

TODO: Get a better name

## Setup

Link the Silver and Silicon repositories, using their gradual verification forks:
```sh
ln -s ../silver-gv silver
ln -s ../silicon-gv silicon
```

## Running

Run the C0 frontend and verify using Silicon in SBT:

```sh
sbt
  run <file.c0> [--c0] [--silver]
```

Use `--c0` or `--silver` to print the generated C0 or Silver source code, respectively.
