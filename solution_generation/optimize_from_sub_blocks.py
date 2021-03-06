from typing import List, Dict
from sfs_generator.asm_block import AsmBlock
from sfs_generator.asm_bytecode import AsmBytecode
from copy import deepcopy
import global_params.constants as constants



def rebuild_optimized_asm_block(previous_block : AsmBlock, sub_block_list : List[str],
                                optimize_blocks_by_name : Dict[str, List[AsmBytecode]]) -> AsmBlock:
    optimized_instructions = []

    previous_instructions = previous_block.instructions
    instr_idx = 0

    previously_optimized = False

    # Tag and JUMPDEST were skipped in sub block list, and hence, we need to skip it when analyzing the optimization
    while instr_idx < len(previous_instructions) and previous_instructions[instr_idx].to_plain() != sub_block_list[0][0]:
        # print(previous_instructions[instr_idx].to_plain(), sub_block_list[0][0])
        optimized_instructions.append(deepcopy(previous_instructions[instr_idx]))
        instr_idx += 1

    for sub_block_idx, sub_block in enumerate(sub_block_list):
        if sub_block_idx == 0:
            considered_sub_block = sub_block
        else:
            # If it has several blocks, the block has been split. Thus, we need to add the split instruction
            # (final instruction from previous block, or first instruction from current block)
            assert sub_block[0] in previous_instructions[instr_idx-1].to_plain()

            if previously_optimized:
                optimized_instructions.append(previous_instructions[instr_idx-1])

            considered_sub_block = sub_block[1:]

        optimized_block_name = previous_block.block_name + "_" + str(sub_block_idx)
        if optimized_block_name in optimize_blocks_by_name and optimize_blocks_by_name[optimized_block_name] is not None:
            previously_optimized = True
            optimized_instructions.extend(optimize_blocks_by_name[optimized_block_name])

            for disasm in considered_sub_block:
                # print(disasm, previous_instructions[instr_idx].to_plain())
                assert disasm in previous_instructions[instr_idx].to_plain()
                instr_idx += 1

        else:
            previously_optimized = False
            for disasm in considered_sub_block:
                # print(disasm, previous_instructions[instr_idx].to_plain())
                assert disasm in previous_instructions[instr_idx].to_plain()
                optimized_instructions.append(previous_instructions[instr_idx])
                instr_idx += 1

    # Remaining instructions
    while instr_idx < len(previous_instructions):
        optimized_instructions.append(previous_instructions[instr_idx])
        instr_idx += 1

    optimized_block = deepcopy(previous_block)
    optimized_block.instructions = optimized_instructions
    return optimized_block
