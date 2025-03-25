from collections import defaultdict, deque
from typing import Dict, List, Tuple
from graphviz import Digraph
import copy

class InstrNode:
    id: str
    prev_instr: List

    def __init__(self, id, prev_instr) -> None:
        self.id = id
        self.prev_instr = prev_instr

    def __str__(self) -> str:
        return f"id: {self.id}, prev_instr: {self.prev_instr}"

    def __repr__(self) -> str:
        return f"id: {self.id}, prev_instr: {self.prev_instr}"

class DAG:
    nodes: Dict[str, List[str]]
    reverse: List[str]

    def __init__(self, dep, code_with_id, extended: bool = False) -> None:

        if extended:
            self.nodes = dep
            self.reverse = self.reverse_topological_order(self.nodes)
            self.nodes, self.id_to_pos = self.extend_dag(code_with_id)
            self.generate_dot(self.nodes, "extended")
            self.reverse = self.reverse_topological_order(self.nodes)

        else:
            self.nodes = dep
            self.generate_dot(self.nodes, "normal")
            self.reverse = self.reverse_topological_order(self.nodes)


            id_to_pos = defaultdict(list)

            for id, pos, siz in code_with_id:
                id_to_pos[id].append((pos, siz))

            self.id_to_pos = {k: sorted(v, key=lambda x: x[1] ) for k, v in id_to_pos.items()}


    
    def generate_dot(self, graph, name):

        dot = Digraph()

        for id in graph.keys():
            dot.node(id, id)

        for id, prev_nodes in graph.items():
            for node in prev_nodes:
                dot.edge(node, id)


        dot.render(name, format='dot')
        #dot.render(name, format='png', view=True)

    def reverse_topological_order(self, graph):
        # Compute in-degree of each node
        in_degree = defaultdict(int)
        for node in graph:
            for neighbor in graph[node]:
                in_degree[neighbor] += 1

        # Initialize queue with nodes with 0 in-degree
        queue = deque([node for node in graph if in_degree[node] == 0])
        topo_order = []

        while queue:
            node = queue.popleft()
            topo_order.append(node)

            # Decrease in-degree for neighbors
            for neighbor in graph[node]:
                in_degree[neighbor] -= 1
                if in_degree[neighbor] == 0:
                    queue.append(neighbor)

        # Reverse the topological order to get the inverse order
        return topo_order[::-1]

    def extend_dag(self, code_with_id:  List[Tuple[str, int, int]] ):

        push_counts = {}
        id_to_pos = {}

        extended_dag = copy.deepcopy(self.nodes)

        for instr, pos, size in code_with_id:
            if instr.startswith("PUSH"):
                if instr in push_counts.keys():
                    id_to_pos[f"{instr}_{push_counts[instr]}"] = (pos, size)
                    push_counts[instr] += 1
                else:
                    id_to_pos[instr] = (pos, size)
                    push_counts[instr] = 1

            else:
                id_to_pos[instr] = (pos, size)


            if instr not in extended_dag.keys():
                continue
            for dep in extended_dag[instr]:
                if dep.startswith("PUSH"):
                    if dep in push_counts.keys():
                        new_dep = dep
                        if push_counts[dep] > 1:
                            new_dep = f"{dep}_{push_counts[dep] - 1}"
                        extended_dag[new_dep] = []
                        extended_dag[instr].remove(dep)
                        extended_dag[instr].append(new_dep)


        return extended_dag, id_to_pos
