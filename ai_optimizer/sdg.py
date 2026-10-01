from typing import Dict, List
from graphviz import Digraph
import json
import math

class Sdg:
    nodes: Dict[str, List[str]]
    reverse: List[str]

    def __init__(self, sfs_block) -> None:

        self.constants_pool = {}
        self.graph = self.complete_dependencies(sfs_block["src_ws"], sfs_block["tgt_ws"], sfs_block["user_instrs"], sfs_block["instr_dependencies"])
        self.state_graph = sfs_block["dependencies"]
        self.original_seq = sfs_block["original_instrs"]

    def complete_dependencies(self, initial_stack, final_stack, instrs, dep):

        push_n = 0

        graph = {}

        for i, elem in enumerate(final_stack):
            
            out_dependencies = [instr["id"] for instr in instrs if elem in instr["outpt_sk"]]
            
            if elem in initial_stack:
                direct_inputs = [f"Input_{initial_stack.index(elem)}"]
            else:
                direct_inputs = []

            graph[f"Output_{i}"] = {
                "label": f"Output_{i}",
                "elem": elem,
                "type": "output",
                "deps": out_dependencies + direct_inputs
            }

        for i, elem  in enumerate(initial_stack):
            graph[f"Input_{i}"] = {
                "label": f"Input_{i}",
                "elem": elem, 
                "type": "input",
                "deps": [],
            }

        for instr in instrs:

            if "PUSH" in instr["disasm"]:
                graph[f"CONSTANT_{push_n}"] = {
                    "label": f"CONSTANT_{push_n}",
                    "elem": push_n,
                    "type": "constant",
                    "deps": [],
                }
                if len(instr["disasm"].split()) > 1:
                    self.constants_pool[f"CONSTANT_{push_n}"] = str(instr["value"][0])
                else:
                    self.constants_pool[f"CONSTANT_{push_n}"] = hex(instr["value"][0]).replace("0x", "")
                dep[instr["id"]] += [f"CONSTANT_{push_n}"]
                push_n += 1



            input_elements = [f"Input_{i}" for i, elem in enumerate(instr["inpt_sk"]) if elem in initial_stack]
            graph[instr["id"]] = {
                "elem": f"0x{instr["opcode"]}",
                "type": "opcode",
                "deps": dep[instr["id"]] + input_elements,
                "gas": instr["gas"],
                "delta": len(instr["outpt_sk"])-len(instr["inpt_sk"]),
                "is_state": instr["storage"],
                "label": instr["disasm"]
            }

        return graph


    
    def generate_dot(self):

        self.dot = Digraph()

        outputs = {}

        for key, value in self.graph.items():
            style = {'color': 'black',
                     'fill': 'lightblue'}

            if value["type"] == "input":
                style["fill"] = "yellow"

            if value["type"] == "output":
                style["fill"] = "red"

            if value["type"] == "constant":
                style["fill"] = "green"

            self.dot.node(key, f"{key} ", color=style['color'], fillcolor=style['fill'], style='filled')

            for node in value["deps"]:
                self.dot.edge(node, key)

        for origin, end in self.state_graph:
            self.dot.edge(origin, end, color="blue")

    def generate_json(self, filename=None):
        data_graph = self.graph
        state_graph = self.state_graph
        nodes = []
        edges = []
        
        # Mapping table to convert string keys ('ADD_0') to integer IDs
        key_to_id = {}
        
        # Helper to get/create ID
        def get_id(key):
            if key not in key_to_id:
                key_to_id[key] = len(key_to_id)
            return key_to_id[key]


        # 1. Process all nodes in the data_graph
        for key, info in data_graph.items():
            node_id = get_id(key)
            node_type = info['type'].upper()
            elem = info['elem']
            
            # Categorical Type ID: SOURCE=1, OPCODE=2, SINK=3
            type_id = 1 if node_type == 'INPUT' else 2 if node_type == "OPCODE" else 3 if node_type == 'OUTPUT' else 4 # CONSTANT
            
            # Extract Stack Position for Source/Sink (e.g., s(25) -> 25)
            stack_pos = 0
            if type_id == 1 or type_id == 2:
                stack_pos = key.split("_")[-1]


            log_gas = 0
            delta = 0
            if type_id == 2:
                raw_gas = info["gas"]
                log_gas = math.log(raw_gas) if raw_gas > 0 else 0
                
                delta = info["delta"]

            nodes.append({
                "id": node_id,
                "type": node_type,
                "label": info["label"],
                "features": [
                    type_id, 
                    stack_pos, 
                    round(log_gas, 2), 
                    delta,
                    1 if node_type == 'OPCODE' and info["is_state"] else 0 # IsStateful
                ]
            })

            # 2. Add Data Flow Edges
            for dep in info['deps']:
                edges.append({
                    "src": get_id(dep),
                    "dst": node_id,
                    "type": "DATA"
                })

        # 3. Add State Dependency Edges (The State Spine)
        for pair in state_graph:
            edges.append({
                "src": get_id(pair[0]),
                "dst": get_id(pair[1]),
                "type": "STATE",
                "desc": "Sequential consistency constraint"
            })

        value_to_constant = {v: k for k, v in self.constants_pool.items()}       
        seq_with_constants = []
        
        for word in self.original_seq.split():
            # If the value matches a constant, replace it; otherwise, keep the original word
            if word in value_to_constant:
                seq_with_constants.append(value_to_constant[word])
            else:
                seq_with_constants.append(word)


        result ={
            "original_seq": self.original_seq,
            "nodes": sorted(nodes, key=lambda x: x['id']),
            "edges": edges,
            "constants": self.constants_pool,
            "seq_with_constants": " ".join(seq_with_constants)
        }
 
        if filename is not None:
            try:
                with open(filename, 'w', encoding='utf-8') as f:
                    json.dump(result, f, indent=2)
                print(f"Successfully saved DFG to {filename}")
            except Exception as e:
                print(f"Error saving JSON: {e}")

        return result



    def render_graph(self):
        self.generate_dot()
        self.dot.render("graph", format='dot')
        self.dot.render("graph", format='png')