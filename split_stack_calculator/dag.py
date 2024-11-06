from collections import defaultdict, deque
from typing import Dict, List
from graphviz import Digraph

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
    nodes: Dict
    reverse: List

    def __init__(self, dep) -> None:

        self.nodes = dep

        self.generate_dot()

        self.reverse = self.reverse_topological_order()

        print("reverse: ", self.reverse)

    
    def generate_dot(self):

        dot = Digraph()

        for id in self.nodes.keys():
            dot.node(id, id)

        for id, prev_nodes in self.nodes.items():
            for node in prev_nodes:
                dot.edge(node, id)


        dot.render('output_graph', format='dot')
        dot.render('output_graph', format='png', view=True)

    def reverse_topological_order(self):
        # Compute in-degree of each node
        in_degree = defaultdict(int)
        for node in self.nodes:
            for neighbor in self.nodes[node]:
                in_degree[neighbor] += 1

        # Initialize queue with nodes with 0 in-degree
        queue = deque([node for node in self.nodes if in_degree[node] == 0])
        topo_order = []

        while queue:
            node = queue.popleft()
            topo_order.append(node)

            # Decrease in-degree for neighbors
            for neighbor in self.nodes[node]:
                in_degree[neighbor] -= 1
                if in_degree[neighbor] == 0:
                    queue.append(neighbor)

        # Reverse the topological order to get the inverse order
        return topo_order[::-1]
