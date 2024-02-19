from typing import Dict, List
from sfs_generator.asm_block import AsmBlock


def csv_from_asm_block(old_block: AsmBlock, new_block: AsmBlock, gasol_checker: True,
                       gasol_checker_reason: str, forves_checker: True) -> Dict:
    stats = {"block_id": old_block.block_name, "old_instrs": old_block.to_plain(), "new_instrs": new_block.to_plain(),
             "old_gas": old_block.gas_spent, "new_gas": new_block.gas_spent, "old_size": old_block.bytes_required,
             "new_size": new_block.bytes_required, "old_length": old_block.bytes_required,
             "new_length": new_block.bytes_required, "gasol_checker": gasol_checker,
             "gasol_checker_reason": gasol_checker_reason, "forves_checker": forves_checker}
    for measure in ["gas", "size", "length"]:
        stats[f"saved_{measure}"] = stats[f"old_{measure}"] - stats[f"new_{measure}"]

    return stats
