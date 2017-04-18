# Actris verifier

Actris is a prototype contract-based verifier for dynamic dataflow programs. The verifier was developed as part of a research project at Åbo Akademi University.

The tools is written in Scala and to some extent based on the Chalice verifer by Microsoft Research.

## Compiling

The tool is compiled using Scala Build Tool (SBT). Hence, SBT must be installed before compiling. To compile the tool, use the following commands:

```
sbt compile
```

It is then possible to create a distributable package using:

```
sbt pack
```

The distribution is created in the folder ```target/pack```.
