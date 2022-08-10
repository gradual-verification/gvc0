# Parallel Benchmarking Pipeline

The parallel benchmarking tool consists of multiple sub-tools, or stages, that are used in
sequence to populate the benchmarking database with programs, execute those programs in parallel,
monitor the progress of ongoing execution, and pull data upon completion.

## Configuration Files

Each benchmarking option requires a `--config=<file>` command-line parameter
for a `.xml` configuration file. This shared format is used for each stage of
the pipeline, so a single file should be reused as much as possible.

### Platform Identification

The outermost enclosing tag is `<benchmark>`, within which there are multiple sections.
The preamble includes information that describes either the current machine, or the source
of queries data. This includes `<version>`, `<hardware>`, and `<nickname>` tags, each of which
takes a string indicating the version of the verifier, the CPU of the machine, and an arbitrary
nickname for a particular machine. Each of these may or may not be required depending on the
stage of the pipeline.

For configuration via GitHub actions, the command line options `--version=` and `--nickname=` override
what is provided in the configuration file.

### Input

The `<source-dir>` field takes a relative path to a directory containing programs for use in
populating the database and recreating permutations from pulled from the database. In a default
configuration with the contents of this repository, the path provided should be:
`./src/test/resources/quant-study`.

### Database Credentials

The `<db>` enclosing tag provides multiple fields for specifying credentials used to connect to the benchmarking
database. For example,

```
<db>
        <username>user</username>
        <url>jdbc:mysql://localhost:3306/[database_name]</url>
        <password>...</password>
</db>
```

Note that the `jdbc:mysql:` prefix is required.

### Quantity & Workload

Within the outermost `<benchmark>` tag, the `<quantity>` tag takes
an integer number of paths, either to populate the database with
or to pull from the database.

The `<workload>` tag provides a specification for the stress values used
when executing particular programs within the database. Within it, the `<iterations>`
tag takes an integer number of iterations to be used for each timing measurement.

The `<stress>` enclosing tag contains workload values used for an individual program,
or as the default for all programs. Within this tag, a singular stress value can be provided
with `<singular>`. If more than one stress value is necessary, a comma separated list can be provided
within the `<list>` tag. A parameterized list of stress values can be provided with the
`<bounded>` parent tag, which includes `<upper>`, `<lower>`, and `<step>` to mark the range of values
to interpolate between at the given step size. Consider the following sample configuration:

```
<workload>
    <stress>
        <bounded>
            <lower>10</lower>
            <upper>20</upper>
            <step>2</step>
        </bounded>
    </stress>
    <iterations>10</iterations>
<workload/>
```

This would result in each measurement being taken from 10 iterations, and for measurements to occur
at stress values 10, 12, 14, 16, 18, and 20.

Separate stress configurations can also be provided for individual programs
by using the `<by-program>` enclosing tag. This tag takes multiple `<p>` enclosing tags,
each of which provides a set of program names to `<match>`, and a `<stress>` configuration to
use for them. Each `<match>` tag takes a comma-separated list of program names. The wildcard `*` indicates that
a particular configuration should be used as the default for all programs that don't match any other item.

For example, the following configuration would execute the programs `list` and `bst`
at the stress value 18:

```
    <workload>
        ...
        <by-program>
            <p>
                <match>list, bst</match>
                <stress>
                    <singular>18</singular>
                </stress>
            </p>
        </by-program>
        ...
    </workload>
```

If both `<stress>` and `<by-program>` are used within a `workload` tag, the contents of `<stress>` will be used
as the default configuration for programs that aren't matched within `<by-program>`. If the wildcard `*` is also used
within `<by-program>`, an error will occur to prompt the user to indicate which default stress
configuration should be used. A default configuration isn't necessary, and will result in any unmatched
programs being excluded.

## Pipeline Stages

### Populator

The populator mode is indicated by `--populate`. For each program in
the provided `<source-dir>`, it generates the number of paths indicated
by `<quantity>`. It also populates a default preconfigured benchmark entitled
`default`, which consists of the permutations at the 20, 40, 60, and 80% completion
increments along the first path entered into the database. It starts with the same random
seed each time, so to increment the current number of paths by `n`, the initial value used within quantity
should be incremented by `n`.

### Executor

The executor mode is indicated by `--execute` and `--execute-benchmark`, where the latter only
applies to programs that are registered with a particular preconfigured benchmark. This mode requires
a `<version>`, `<hardware>`, `<nickname>` and `<workload>` configuration, and will
benchmark all programs within the database that have yet to ran with that configuration.

Though `<nickname>` is required, it is not used to differentiate between results that are present and not present;
e.g., if a program has already been executed by a configuration that only differs from the current configuration
by its `<nickname>`, then the executor with the current configuration will not choose to rerun that program.

Unlike all other modes, executor is designed to be safely run in parallel.

### Monitor

The monitor mode is indicated by `--monitor` and only requires database credentials to be run.
It prints a status report of the contents of the database with the following subheadings:
"Database Contents", "Completed Programs", "Completed Mass Benchmarks", "Completed Preconfigured Benchmarks".

### Recreator

The recreator mode is indicated by `--recreate=[n]`. It requires a `<version>`, a `<source-dir>`, `<db>` credentials,
and
it takes the unique ID associated with a particular permutation of a program within the database.
It will attempt to recreate the permutation's partial specification, and if successful, will output it
as `recreated_[n].c0`
in the current directory. After that point, it will attempt to verify and execute the program using any other command
line options
that are provided.

### Exporter

The exporter mode is indicated by `--export` and requires `<workload>`, `<quantity>`, `<version>`, `<hardware>` and
database credentials in its provided configuration. It pulls all data from the database
corresponding to that workload, hardware, and version, with an upper limit on the number of paths pulled
given by the `<quantity>` tag. Similar to executor, `--export-benchmark` is also available, which will only
export data corresponding to each preconfigured benchmark. Additionally, `--export-errors` will provide a CSV list
of error information corresponding to programs that produced errors during verification, compilation, or execution.

Only benchmarks and paths that are fully completed can be exported from the database, where 'completed' indicates
that no static or dynamic errors have occurred for any of the containing programs. All paths and benchmarks listed under
the "Completed Mass Benchmarks" and "Completed Preconfigured Benchmarks" in the monitor mode are valid for export.

The output of the exporter mode is a folder in the current directory marked with the name of the mode ran and the
current date,
as well as the version hardware configuration corresponding to the data pulled. For `--export`, this will contain three
files:
`static_performance.csv`, `dynamic_performance.csv`, `path_index.csv`, and `program_index.csv`.
The static and dynamic performance files contain IDs that correspond to programs and permutations.
The path index specifies the paths that each permutation belongs to, as well as where on that path it occures.
The program index provides the name of the program associated with each program ID.

For `--export-benchmark`, files are produced with the name `[benchmark_name]_performance.csv` for each benchmark.
These are formatted identically to the `dynamic_performance.csv` produced by `--export`. Though no path index is
provided,
`program_index.csv` is generated with mappings for every program in the database.

The `--export-error` configuration provides a single `errors.csv` file listing the type and message corresponding to
each error,
as well as the permutation, hardware, and version IDs that triggered the error.