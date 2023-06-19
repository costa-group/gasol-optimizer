GASOL
=====
[![License: GPL v3](https://img.shields.io/badge/License-GPLv3-blue.svg)](https://github.com/costa-group/gasol-optimizer/blob/main/LICENSE)
![version](https://img.shields.io/badge/version-0.3.0-green)

GASOL is a generic framework that optimizes smart contracts by applying the technique called *super-optimization* that consists in optimizing basic blocks (sequences of EVM instructions). For each basic block, GASOL tries to find a sequence of EVM instructions that produces the same state as the original block, but consumes a smaller amount of gas or decreases the amount of bytes. 

## Installation (Ubuntu)
GASOL is implemented in Python and runs Python3. It only needs [pandas](https://pandas.pydata.org/) and [networkx](https://pypi.org/project/networkx/) libraries to be run. In order to install it, run one of the following commands:


A. Clone the GitHub repository in the desired directory of your machine using the command
```
git clone https://github.com/costa-group/gasol-optimizer.git
```
B. Download a zip folder with the source code that is available [here](https://github.com/costa-group/gasol-optimizer/archive/refs/heads/main.zip) and decompress it in the desired directory by executing `unzip gasol-optimizer-main.zip`

## Usage

GASOL can optimize either a single sequence of assembly EVM instructions or all basic blocks obtained from an assembly (in what follows asm) json that has been generated from a Solidity file by executing the following command:

```
solc [options] --combined-json asm SOLIDITY_FILE 1> asmjson_filename
```

The following sections detail how to interact with GASOL to enable different settings and optimize the different input formats.

### General settings

By default, GASOL uses the SMT solver [OptiMathSAT](http://optimathsat.disi.unitn.it/), with a timeout of 2s per block. This timeout can be changed using `-tout` flag followed by the new timeout in seconds.

GASOL allows two different optimization criteria: gas and bytes-size. By default, the gas criterion is enabled. The byte-size criterion can be enabled using the `-size` flag. In general, enabling the gas size criterion leads to increasing the bytes-size, whereas the byte-size criterion tends to reduce (slightly) the gas consumption. Byte-size criteria also takes longer.

The flags `-storage` and `-partition` determine how blocks are split. This decision has an impact in the overall performance, the amount of blocks that time out and the gains from the optimization. See the final section [_Splitting blocks_](#splitting-blocks) for more details.

### Assembly file

In order to execute GASOL on an asm json file, run the following command from the root directory of the repository:
```
./gasol_asm.py asmjson_filename
```
where *asmjson_filename* is the name of the file where the asm json is stored. A set of asm json files to test the prototype is available [here](https://github.com/costa-group/gasol-optimizer/tree/main/examples/jsons-solc). 

GASOL will analyze all basic blocks of the provided code. Note that it may take some time to finish the execution.
We recommend enabling `-storage` (the fastest option) or `-partition` (slower, but tends to produce better results) when optimizing asm files.

As a result of the optimization, another asm json with the optimized blocks is generated. 
By default, this file is stored in the same folder from which the executable
was invoked. Its file name corresponds to the initial asm json file name after adding
the suffix *_optimized*. This output file can be specified using `−o` flag:

```
./gasol_asm.py asmjson_filename −o solution_filename
```

For instance, to execute GASOL on the asm file examples/jsons-solc/0x20e7Efc18f4D03670EDC2FD86b840AB2D01E030D.json_solc with a timeout of 5 seconds per block, the bytes-size criterion enabled and the flag `-storage` activated, run the following command:
```
./gasol_asm.py examples/jsons-solc/0x20e7Efc18f4D03670EDC2FD86b840AB2D01E030D.json_solc -tout 5 -storage -size
```

A csv file that contains additional information from the optimization
process is generated as well. By default, this file is stored in the same folder from which
the executable was invoked. The file name can be specified using flag `−csv`.

### Isolated sequence of EVM bytecode

In order to execute GASOL on a plain sequence of EVM bytecode, run the following command from the root directory of the repository:
```
./gasol_asm.py block_filename -bl
```
where *block_filename* is the name of the file where the code is stored. Note that the code has to be stored as a sequence of EVM instructions separated by blanks or in different lines. See the examples [here](https://github.com/costa-group/gasol-optimizer/tree/main/examples/blocks) for more details.

For instance, to execute GASOL on the EVM block stored in the file *examples/blocks/redundant_swap.txt* with the gas criterion enabled, run the following command:
```
./gasol_asm.py examples/blocks/redundant_swap.txt -bl
```
Hence, it will output the optimized block in the console and its inferred gas and bytes-size associated:

```
Initial sequence (basic block per line):
SWAP1 SWAP4 DUP5 SWAP2 SWAP1

Optimized sequence (basic block per line):
DUP2 SWAP5

Total time: 0.06 s

Optimized code stored in redundant_swap_optimized.txt
Optimality results stored in redundant_swap_statistics.csv

Estimated initial gas: 15
Estimated gas optimized: 6

Estimated initial size in bytes: 5
Estimated size optimized in bytes: 2

Initial number of instructions: 5
Final number of instructions: 2
```

### Neural-guided Superoptimization (NGS)

GASOL can enable ML techniques to speed up the superoptimization process and 
improve the optimization results for large blocks. These techniques are implemented 
in a separate repository, [gasol_ml](https://github.com/costa-group/gasol_ml), 
which must be imported as a submodule using the following commands:

```
git submodule init
git submodule update
```

`gasol_ml` contains a [requirements](https://github.com/costa-group/gasol_ml/blob/master/requirements.txt)
file with the libraries needed to enable the ML modules.
There are two ML models that can be enabled for each optimization criteria: 
a classification model that filters blocks that are likely not to be optimized further and 
a regression model that infers the number of instructions of the optimal solution 
in order to speed up the search. The first model can be enabled using `-opt-model` 
and the second one with `-bound-model`. 
For instance, to execute GASOL on the previous asm file using both models, run the following command:

```
./gasol_asm.py examples/jsons-solc/0x20e7Efc18f4D03670EDC2FD86b840AB2D01E030D.json_solc -tout 5 -storage -size -opt-model -bound-model
```

The classifier can skip blocks that could obtain additional savings, but in general the 
loss is nearly negligible and the overall time is decreased in more than half. The regression model 
can return bounds that are too low, which results in not finding any equivalent solution. 
Nevertheless, it still achieves significant additional savings and decreases the overall time slightly. 
We recommend using both models combined, as the bound regression compensates the loss of savings from the classifier.

### Optimization from a log file

An optional log file can be generated when executing GASOL on an asm json file. It is enabled by setting the flag `−log`:

```
./gasol_asm.py asmjson_filename -log
```

It ensures that the same optimization output is obtained if the log file is provided when invoking GASOL. This feature has been included for verification purposes. 
More information on the usage of log files can be found in section [Why log files?](#why-log-files).

Log files are stored in the same folder in which GASOL was invoked, sharing the same name but with the *.log* extension. The file name can be specified using `-dest-log`. 

In order to execute GASOL providing a log file, run the following command from the root directory of the repository:

```
./ gasol−asm.py asmjson_filename −optimize-from−log log_file
```

For instance, to optimize the previous example using a log file, run the following commands:

```
./gasol_asm.py examples/jsons-solc/0x20e7Efc18f4D03670EDC2FD86b840AB2D01E030D.json_solc -tout 5 -storage -size -log -dest-log 0x20_test.log
./gasol_asm.py examples/jsons-solc/0x20e7Efc18f4D03670EDC2FD86b840AB2D01E030D.json_solc -storage -size -optimize-from-log 0x20_test.log
```

Note that the same criterion and block-splitting policy must be enabled in order to generate the same optimized file.

## Documentation
You can find further documentation about the GASOL project [here](https://github.com/costa-group/gasol-optimizer/tree/main/reports).

## Publications
* [A Max-SMT Superoptimizer for EVM handling Memory and Storage](https://link.springer.com/content/pdf/10.1007/978-3-030-99524-9_11.pdf). Elvira Albert, Pablo Gordillo, Alejandro Hernández-Cerezo and Albert Rubio. 28th International Conference on Tools and Algorithms for the Construction and Analysis of Systems, TACAS 2022. Proceedings, volume 13243 of Lecture Notes in Computer Science, pages 201-2019. Springer, 2022.

* [Super-Optimization of Smart Contracts](https://dl.acm.org/doi/pdf/10.1145/3506800). Elvira Albert, Pablo Gordillo, Alejandro Hernández-Cerezo, Albert Rubio and Maria A. Schett.  ACM Transactions on Software Engineering and Methodology, 31 Issue 4(70):1-29, 2022.

## Additional information

In this final section, explanations on relevant aspects of the tool are discussed. These explanations aim to explore the more technical details of some options found in the tool:

### Splitting blocks

When considering the basic blocks, there are three ways to split them:

* The first option consists of considering basic blocks directly, without splitting the block at STORE operations (MSTORE, SSTORE or MSTORE8). Larger pieces of code are considered, and thus, it (possibly) leads to further optimizations but also results in more timeouts. This option is enabled by default.

* The second option is the one enabled in previous versions of GASOL and splits a block into subblocks whenever a STORE operation is found. This leads to smaller blocks, but it is also the fastest option and the one that timeouts the least. 
It can be enabled using the `-storage` flag.

* The third option is a halfway approach from the previous ones. It relies on the fact that there exists huge basic blocks that are virtually impossible to optimize using the SMT solver. In these cases, this option leads GASOL to split at some STORE instructions to prevent analyzing huge blocks. It can be enabled using the `-partition` flag.

### Why log files?

Log files have been introduced as a mechanism to prove a certain file has been 
indeed optimized using the GASOL tool. 
SMT solvers are not deterministic, and thus, optimizing more than once a file using the same settings does not necessarily 
generate the same optimized code.
The log file records the decisions made by the solver and allows rebuilding the same optimized code.

An additional check is performed by the SMT solver to ensure both the log file and the optimized code have not been tampered. 
If the log file cannot be verified, GASOL will detect it and no optimized code will be generated.

### Intermediate files

During the execution, a folder called *gasol_(uuid4)* will be created in */tmp/* folder, where uuid4 is a randomly generated identifier to ensure each execution of gasol has its own folder. This folder stores intermediate files generated during the whole  optimization process. By default, it is erased once the whole process is over. However, it is possible to avoid this behavior by setting the flag `-intermediate`.
In that case, the concrete name for the intermediate files' folder is notified after the whole execution is over.
It is also possible to generate these intermediate files without applying the superoptimization process using the flag `-backend`.

We can find the following subfolders:

1. *disasms* contains the sequence of instructions in plain text for each analyzed sub-block.
    
1. *jsons* contains the Stack and Memory Specification (SMS) representation for each analyzed sub-block. This representation is
later used by the Max-SMT encoder to perform the optimization.
    
1. *smt_encoding* contains all necessary files to generate the
optimized EVM bytecode. These files include: a smt2 encoding file
that contains the Max-SMT problem, an instruction file that links
the numerical representation of each opcode in the Max-SMT
encoding with the corresponding opcode, an opcode file that
follows the same idea but links the associated hexadecimal value
instead and a gas file that links the numerical representation
with the inferred gas cost associated.  This way, all relevant
information can be conveyed from these files.


## Contributors
* Elvira Albert
* Pablo Gordillo
* Alejandro Hernández-Cerezo
* Albert Rubio
