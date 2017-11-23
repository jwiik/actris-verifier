# Actris verifier

Actris is a prototype contract-based verifier for dynamic dataflow programs. The verifier was developed as part of a research project at Åbo Akademi University. The principles behind the tool have been documented and published in the paper:

J. Wiik and P. Boström. [Specification and Automated Verification of Dynamic Dataflow Networks](https://doi.org/10.1007/978-3-319-66197-1_9). In: Software Engineering and Formal Methods: 15th International Conference, SEFM 2017, Proceedings, LNCS. Springer, 2017.

The tool is written in Scala and to some extent based on the Chalice verifer by Microsoft Research.

## Compiling

The tool is compiled using Scala Build Tool (SBT). Hence, SBT must be installed before compiling. To compile the tool, use the following command in SBT:

```
> compile
```

It is then possible to create a distributable package using:

```
> pack
```

The distribution is created in the folder ```target/pack```. This folder can be renamed and/or moved as the user wishes.

## Running

To run the tool, issue the following command, assuming that the tool is available on the path:

```
actris <input_source_file>
```

## Eclipse

SBT can also generate Eclipse project files. The project can then be import into Eclipse / Scala-IDE for development.

To generate Eclipse file, issue the following command in SBT:

```
> eclipse
```

## Build status

[![Build Status](https://travis-ci.org/jwiik/actris-verifier.svg?branch=master)](https://travis-ci.org/jwiik/actris-verifier)
