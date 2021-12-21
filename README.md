
GASOL
=====
[![License: GPL v3](https://img.shields.io/badge/License-GPLv3-blue.svg)](https://github.com/costa-group/gasol-optimizer/blob/main/LICENSE)
![version](https://img.shields.io/badge/version-0.1.3-green)

GASOL is a generic framework that optimizes smart contracts by applying the technique called "super-optimization" that consists in optimizing basic blocks (sequences of EVM instructions). GASOL tries to find, for each basic block, a sequence of EVM instructions that produces the same stack as the original block, but consumes a smaller amount of gas.

## Documentation
You can find documentation further about the Gasol project [here](https://github.com/costa-group/gasol-optimizer/tree/main/reports)

## Installation (Ubuntu)
GASOL is implemented in Python and runs Python3. It does not need any additional library. In order to install it, run one of the following commands:


A. Clone the GitHub repository in the desired directory of you machine using the command
```
git clone https://github.com/costa-group/gasol-optimizer.git
```
B. Download a zip folder with the source code that is available [here](https://github.com/costa-group/gasol-optimizer/archive/refs/heads/main.zip) and decompress it in the desired directory by executing `unzip gasol-optimizer-main.zip`

## Usage
GASOL can optimize either a single sequence of assembly EVM instructions (block) or all basic blocks obtained from an assembly (in what follows asm) json that has been generated from a Solidity file by executing the following command:
```
solc --combined-json asm solidity_file.sol
```

By default, GASOL uses [OptiMathSAT](http://optimathsat.disi.unitn.it/) as SMT solver with a timeout of 10s per block. This timeout can be changed using `-tout` flag followed
by the new timeout in seconds.

A. In order to execute GASOL on a asm json file, run the following command from the root directory of the repository:
```
./gasol_asm.py asmjson_filename
```
where asmjson_filename is the name of the file where the asm json is stored. A set of asm json files to test the prototype is available [here](https://github.com/costa-group/gasol-optimizer/tree/main/examples/jsons-solc). GASOL will analyze all basic blocks of the provided smart contracts. Note that it may take some time to finish the execution. 


As a result of the optimization, another asm json with the optimized blocks is generated. 
By default, this file is stored in the same folder from which the executable
was invoked. Its file name corresponds to the initial asm json file name after adding
the suffix *_optimized*. This output file can be specified using −o flag:

```
./gasol_asm.py asmjson_filename −o solution_filename
```

For instance, to execute GASOL on the asm file examples/jsons-solc/0x20e7Efc18f4D03670EDC2FD86b840AB2D01E030D.json_solc with a timeout of 5 seconds per block run the following command:
```
./gasol_asm.py examples/jsons-solc/0x20e7Efc18f4D03670EDC2FD86b840AB2D01E030D.json_solc -tout 5
```

B. In order to execute GASOL on a basic block, run the following command from the root directory of the repository:
```
./gasol_asm.py block_filename -bl
```
where block_filename is the name of the file where the basic block is stored. Note that the basic block has to be stored as a sequence of EVM instructions separated by blanks. See the examples [here](https://github.com/costa-group/gasol-optimizer/tree/main/examples/blocks) for more details. In this case, though the optimized block can be found in the same directory mentioned above, it is also displayed in the console.

For instance, to execute GASOL on the EVM block stored in the file examples/blocks/test.disasm_blk run the following command:
```
./gasol_asm.py examples/blocks/test.disasm_blk -bl
```
Hence, it will output the optimized block in the console and its inferred gas associated:
```
RULES  : 0
block0_instruction.json
Executing oms for file block0
Estimated initial cost: 22
Initial sequence: ['PUSH1 0x04', 'PUSH1 0x04', 'PUSH1 0x04', 'POP', 'POP', 'DUP1', 'DUP3', 'ADD']
Estimated new cost: 12
Optimized sequence: ['PUSH1 0x4', 'DUP2', 'DUP2', 'ADD']
```

C. An optional log file can be generated when executing GASOL on an asm json file. It is enabled by setting the flag −−generate−log:

```
./gasol_asm.py asmjson_filename --generate-log
```

It ensures that the same optimization output is obtained 
if the log file is provided when invoking GASOL. This feature has been included for verification purposes in Etherscan.
It is stored in /tmp/gasol/*asmjson_filename*.log. In order to execute GASOL providing a log file, 
run the following command from the root directory of the repository:

```
./ gasol−asm.py asmjson_filename −optimize−gasol−from−log−file log_file
```

The output file follows the same convention described in A, but adding the suffix *_optimized_from_log* instead.

For instance, to optimize the asm file examples/jsons-solc/0x20e7Efc18f4D03670EDC2FD86b840AB2D01E030D.json_solc and optimize it again using the log file run the following command:

```
./gasol_asm.py examples/jsons-solc/0x20e7Efc18f4D03670EDC2FD86b840AB2D01E030D.json_solc --generate-log
./gasol_asm.py examples/jsons-solc/0x20e7Efc18f4D03670EDC2FD86b840AB2D01E030D.json_solc -optimize-gasol-from-log-file /tmp/gasol/0x20e7Efc18f4D03670EDC2FD86b840AB2D01E030D.log 
```
