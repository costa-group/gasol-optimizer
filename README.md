
GASOL
=====
[![License: GPL v3](https://img.shields.io/badge/License-GPLv3-blue.svg)](https://github.com/costa-group/gasol-optimizer/blob/main/LICENSE)
![version](https://img.shields.io/badge/version-0.1-green)

GASOL is a generic framework that optimizes smart contracts by applying the technique called "super-optimization" that consists in optimizing basic blocks (sequences of EVM instructions). GASOL tries to find, for each basic block, a sequence of EVM instructions that produces the same stack as the original block, but consumes a smaller amount of gas.


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

By default, GASOL uses [OptiMathSAT](http://optimathsat.disi.unitn.it/) as SMT solver with a timeout of 10s per block.

A. In order to execute GASOL on a asm json file, run the following command from the root directory of the repository:
```
./gasol_asm.py asmjson_filename
```
where asmjson_filename is the name of the file where the asm json is stored. A set of asm json files to test the prototype is available [here](https://github.com/costa-group/gasol-optimizer/tree/main/examples/jsons-solc). GASOL will analyze all basic blocks of the provided smart contracts. Note that it may take some time to finish the execution. 

The optimized version for each block is stored in the directory /tmp/gasol/solutions. There, you are going to find a directory for each of the contracts contained in the analyzed Solidity file. Each of these directories has a folder called disasm with the optimized assembly version of the blocks.

For instance, to execute GASOL on the smart contract stored in the solidity file examples/solidity/0x363c421901B7BDCa0f2a17dA03948D676bE350E4.sol run the following commands:
```
solc --combined-json asm examples/solidity/0x363c421901B7BDCa0f2a17dA03948D676bE350E4.sol 1> 0x363c421901B7BDCa0f2a17dA03948D676bE350E4.json_solc
./gasol_asm.py 0x363c421901B7BDCa0f2a17dA03948D676bE350E4.json_solc
```
It generates two directories in /tmp/gasol/solutions (MerkleDistributor and MerkleProof respectively) that contain the optimized blocks.

B. In order to execute GASOL on a basic block, run the following command from the root directory of the repository:
```
./gasol_asm.py block_filename -bl
```
where block_filename is the name of the file where the basic block is stored. Note that the basic block has to be stored as a sequence of EVM instructions separated by blanks. See the examples [here](https://github.com/costa-group/gasol-optimizer/tree/main/examples/blocks) for more details. In this case, though the optimized block can be found in the same directory mentioned above, it is also displayed in the console.

For instance, to execute GASOL on the EVM block stored in the file examples/blocks/test.disasm_blk run the following command:
```
./gasol-asm.py example/block/test.disasm_blk
```
Hence, it will output the optimized block in the console:
```
Executing oms for file block0
OPTIMIZED BLOCK: ['PUSH1 4 ', 'DUP2 ', 'DUP2 ', 'ADD ']
```
